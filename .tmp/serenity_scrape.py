#!/usr/bin/env -S uv run
# /// script
# requires-python = ">=3.12"
# dependencies = ["twikit==2.3.3", "python-dotenv>=1.0"]
# ///
"""serenity_scrape.py — refresh the thesis DB from X (@aleabitoreddit).

The writer half of the thesis DB; `serenity_tweets.py` is the reader. This walks the
target's timeline newest-first, stops once it has proven it is caught up, and upserts
into the same `tweets` table the reader queries.

WHY THIS SCRIPT SHEBANGS `uv run` INSTEAD OF `python3`
	It is the one script in this repo with a dependency outside `scripts/.venv`.
	twikit drags in a Js2Py fork, m3u8, webvtt-py and pyotp — a scraping-only tree
	that must never be able to break the analysis install. So the deps live in the
	PEP 723 block above and `scripts/requirements.txt` stays clean.

	twikit is pinned `==2.3.3`, not `>=`: this script monkeypatches a private
	constructor in that version and depends on its hardcoded GraphQL query ids. A
	silent minor bump could turn the patch into a no-op — or a crash at 09:00 KST
	with nobody watching.

USAGE
	uv run scripts/serenity_scrape.py
	uv run scripts/serenity_scrape.py --dry-run
	uv run scripts/serenity_scrape.py --max-dups 0      # full re-walk, gap repair
"""

from __future__ import annotations

import argparse
import asyncio
import json
import os
import re
import sqlite3
import sys
from datetime import datetime, timedelta, timezone

DEFAULT_DB = os.path.join(
	os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "data", "analysis_Serenity.db"
)
DEFAULT_ENV_FILE = os.path.join(
	os.path.dirname(os.path.dirname(os.path.abspath(__file__))), ".env"
)
TARGET_USER = "aleabitoreddit"
COOKIE_KEYS = ("X_AUTH_TOKEN", "X_CT0", "X_TWID")
PAGE_SIZE = 20
RATE_LIMIT_DELAY = 2
MAX_RETRIES = 3
RETRY_BACKOFF_BASE = 2

# Errors are classified by CLASS NAME, not isinstance. That is deliberate: everything
# twikit-shaped is confined to _default_client_factory so this module imports cleanly
# under scripts/.venv (which has no twikit) and stays testable. These names are
# twikit's public error surface — see twikit/errors.py.
#
# The split itself is the fix for the notebook's real retry bug: it retried EVERY
# exception, so a permanently dead cookie burned three requests and six seconds of
# backoff before it said anything, and a permanent 404 did the same on every run.
RETRYABLE_ERRORS = frozenset({
	"TooManyRequests", "RequestTimeout", "ServerError",
	# httpx transport failures — network flakiness, worth another go.
	"TransportError", "ConnectError", "ConnectTimeout", "ReadTimeout", "ReadError",
	"WriteTimeout", "PoolTimeout", "RemoteProtocolError", "TimeoutException",
})

# Anything not listed here is `fetch_failed` — a generic, still-red outcome.
ERROR_CODES = {
	"SessionInitError": "session_init_failed",
	"Unauthorized": "cookies_rejected",
	"Forbidden": "cookies_rejected",
	"AccountLocked": "account_locked",
	"UserNotFound": "user_not_found",
	"UserUnavailable": "user_not_found",
	"AccountSuspended": "user_not_found",
	"TooManyRequests": "rate_limited",
}


class ScrapeError(Exception):
	"""An error the CLI reports as JSON with a remedy, never as a traceback."""

	def __init__(self, code: str, detail: str):
		super().__init__(detail)
		self.code = code
		self.detail = detail


class SessionInitError(Exception):
	"""twikit could not build the signature X requires on every GraphQL call."""

# The corpus stores created_at as a KST ISO string, and serenity_tweets.py compares it
# as a STRING. A varying offset would silently break that ordering, so every row gets
# a fixed +09:00 regardless of what X sent.
_KST = timezone(timedelta(hours=9))
_X_TIME_FORMAT = "%a %b %d %H:%M:%S %z %Y"

# Matches a cashtag only when a LETTER follows the `$`, which is what keeps `$217`
# and `$30s` out of the corpus. Frozen on purpose — see the characterization tests
# in tests/260817/corpus/test_scrape.py before touching it.
_TICKER_RE = re.compile(r"\$([A-Za-z]+)")


def _to_kst(raw: str) -> str:
	"""X's wire timestamp -> the corpus's KST ISO string.

	Deliberately lets ValueError escape: if X changes its format, that must surface as
	a loud failure, never as a quietly skipped tweet.
	"""
	return datetime.strptime(raw, _X_TIME_FORMAT).astimezone(_KST).strftime("%Y-%m-%dT%H:%M:%S+09:00")


def _extract_tickers(content: str) -> list[str]:
	"""Cashtags in first-appearance order, uppercased, de-duplicated."""
	if not content:
		return []
	found = (m.group(1).upper() for m in _TICKER_RE.finditer(content))
	return list(dict.fromkeys(found))


# --- Progress -------------------------------------------------------------------
#
# stdout is one JSON document and nothing else — the workflow's Summary step parses
# it — so every human-facing line goes to stderr. Plain print, not `logging`: this
# repo uses no logger anywhere, and there is one destination, one level and one
# boolean here, so a Formatter + StreamHandler would just be `print` with ceremony.
#
# The heartbeat is per PAGE. Never per tweet: 20 lines a page is unreadable, and it
# would put post content into a world-readable Actions log.

_QUIET = False


def _say(message: str) -> None:
	if not _QUIET:
		print(f"[{datetime.now(_KST):%H:%M:%S}] {message}", file=sys.stderr, flush=True)


def _full_content(tweet) -> str:
	"""The long-form note body when there is one, else full_text.

	This is the whole reason a long thesis is not stored cut off at 280 chars.
	"""
	note = (tweet._data or {}).get("note_tweet")
	if note:
		text = note.get("note_tweet_results", {}).get("result", {}).get("text")
		if text:
			return text
	return tweet.full_text or ""


def _classify_type(tweet) -> str:
	"""post | reply | subscriber.

	`exclusivityInfo` is checked FIRST on purpose: a paid post made inside a thread
	is still a paid post, and filing it as a plain reply would drop it out of every
	subscriber-only slice of the corpus.
	"""
	if (tweet._data or {}).get("exclusivityInfo"):
		return "subscriber"
	if tweet.in_reply_to:
		return "reply"
	return "post"


def _media_urls(tweet) -> list[str]:
	return [u for u in (getattr(m, "media_url", None) for m in (tweet.media or [])) if u]


# --- The DB --------------------------------------------------------------------

def _init_db(conn: sqlite3.Connection) -> None:
	conn.execute("""
		CREATE TABLE IF NOT EXISTS tweets (
			id TEXT PRIMARY KEY,
			user TEXT NOT NULL,
			type TEXT NOT NULL CHECK(type IN ('post', 'reply', 'subscriber')),
			created_at TEXT NOT NULL,
			content TEXT,
			tickers TEXT DEFAULT '[]',
			media TEXT DEFAULT '[]'
		)
	""")
	conn.commit()


def _existing_ids(conn: sqlite3.Connection) -> set[str]:
	return {row[0] for row in conn.execute("SELECT id FROM tweets")}


def _db_stats(conn: sqlite3.Connection) -> dict:
	by_type = {r[0]: r[1] for r in conn.execute("SELECT type, COUNT(*) FROM tweets GROUP BY type")}
	newest = conn.execute("SELECT MAX(created_at) FROM tweets").fetchone()[0]
	return {
		"totals": {"total": sum(by_type.values()), **by_type},
		"newest_at": newest,
	}


def _save(conn: sqlite3.Connection, tweet, target: str, dry_run: bool = False) -> tuple[bool, str, str]:
	"""INSERT OR IGNORE one tweet. Returns (was_inserted, type, created_at).

	`cur.rowcount` — NOT `conn.total_changes`, which is the connection's CUMULATIVE
	lifetime counter and so is permanently truthy after the first insert. The
	notebook used it, which is why its "saved N" was really "rows attempted".

	The caller has already established the id is unknown (from the preloaded id set),
	so a dry run can report the would-be insert without touching the DB.
	"""
	tweet_type = _classify_type(tweet)
	created_at = _to_kst(tweet.created_at)
	content = _full_content(tweet)
	if dry_run:
		return True, tweet_type, created_at
	cur = conn.execute(
		"INSERT OR IGNORE INTO tweets (id, user, type, created_at, content, tickers, media)"
		" VALUES (?,?,?,?,?,?,?)",
		(
			tweet.id,
			tweet.user.screen_name if tweet.user else target,
			tweet_type,
			created_at,
			content,
			json.dumps(_extract_tickers(content)),
			json.dumps(_media_urls(tweet)),
		),
	)
	return cur.rowcount == 1, tweet_type, created_at


# --- Cookies -------------------------------------------------------------------

def _load_cookies(env_file: str | None) -> tuple[dict, str]:
	"""The three X cookies, process env first and the .env file as fallback.

	Returns (cookies, source). The SOURCE is reported; the VALUES never are. If a
	stale token is exported in the runner service's environment, env-first
	precedence silently wins — naming the source is the only way to see that.
	"""
	from_env = {k: os.environ.get(k) for k in COOKIE_KEYS}
	if all(from_env.values()):
		return _as_cookie_dict(from_env), "env"

	if env_file and os.path.exists(env_file):
		from dotenv import dotenv_values  # lazy: keeps module import free of deps
		values = dotenv_values(env_file)
		merged = {k: from_env.get(k) or values.get(k) for k in COOKIE_KEYS}
		if all(merged.values()):
			return _as_cookie_dict(merged), "env_file"

	return {}, "missing"


def _as_cookie_dict(values: dict) -> dict:
	return {
		"auth_token": values["X_AUTH_TOKEN"],
		"ct0": values["X_CT0"],
		"twid": values["X_TWID"],
	}


# --- Error classification ------------------------------------------------------

def _is_retryable(exc: BaseException) -> bool:
	if isinstance(exc, (OSError, TimeoutError)):
		return True
	return type(exc).__name__ in RETRYABLE_ERRORS


def _error_code(exc: BaseException) -> str:
	return ERROR_CODES.get(type(exc).__name__, "fetch_failed")


def _safe_reason(exc: BaseException) -> str:
	"""A ONE-LINE exception summary safe for a PUBLIC Actions log.

	Truncated because twikit can echo a request back at us, and this repo's logs and
	job summaries are world-readable. Whitespace-collapsed because X's 401 body
	carries embedded newlines, and `detail` is rendered into a markdown blockquote
	and passed through a GitHub step output — a raw newline breaks both, cutting the
	message off at exactly the part that says what to do.
	"""
	return f"{type(exc).__name__}: {' '.join(str(exc).split())[:200]}"


def _detail_for(code: str, exc: BaseException | None, args) -> str:
	env_file = args.env_file
	keys = " / ".join(COOKIE_KEYS)
	remedies = {
		"cookies_missing": (
			f"No X cookies found. Set {keys} in the environment, or put them in "
			f"{env_file} (pass --env-file to point elsewhere)."
		),
		"cookies_rejected": (
			f"X rejected the cookies. Log in at x.com, open DevTools -> Application "
			f"-> Cookies -> x.com, and replace {keys} in {env_file}."
		),
		"account_locked": (
			"X is challenging this session. Open x.com in a browser and clear the "
			f"challenge FIRST, then re-copy {keys} into {env_file} — new cookies "
			"alone will not fix a locked account."
		),
		"user_not_found": (
			f"X has no reachable timeline for @{args.user} (renamed, suspended, or "
			"protected). Confirm the handle and pass --user if it changed."
		),
		"empty_timeline": (
			"X returned an empty timeline with no error. That is a shadow-limited or "
			f"partly-invalidated session, not a quiet day — refresh the cookies "
			f"({keys}) in {env_file} and re-run."
		),
		"rate_limited": (
			f"X rate-limited the walk and it did not finish, so the corpus may have a "
			f"gap. Re-run with --max-dups 0 once the limit clears."
		),
		"session_init_failed": (
			"twikit could not derive the x-client-transaction-id X requires on every "
			"GraphQL call, so no request was made. Two causes look identical here: "
			f"(1) the cookies are stale — refresh {keys} in {env_file}; (2) X moved its "
			"web bundle again, in which case _patch_twikit_transaction() in this file "
			"needs updating (check https://x.com/home for a module map entry named "
			"'ondemand.s'). Try the cookies first."
		),
	}
	detail = remedies.get(code, "The walk did not finish, so the corpus may have a gap. Re-run with --max-dups 0.")
	return f"{detail} ({_safe_reason(exc)})" if exc is not None else detail


async def _fetch_with_retry(coro_fn, report: dict | None):
	"""Retry transient failures only; surface permanent ones on the first attempt."""
	for attempt in range(MAX_RETRIES + 1):
		try:
			return await coro_fn()
		except Exception as exc:
			if not _is_retryable(exc) or attempt == MAX_RETRIES:
				raise
			if report is not None:
				report["retries"] += 1
			_say(f"  warn {report['tab'] if report else 'user'} {_safe_reason(exc)} — "
			     f"retry {attempt + 1}/{MAX_RETRIES}")
			await asyncio.sleep(RETRY_BACKOFF_BASE ** (attempt + 1))


# --- The walk ------------------------------------------------------------------

def _new_report(tab: str) -> dict:
	return {
		"tab": tab,
		"pages": 0,
		"seen": 0,
		"skipped_other_users": 0,
		"duplicates": 0,
		"new": 0,
		"retries": 0,
		"stopped_reason": None,
		"caught_up": False,
		"error": None,
	}


async def _walk_tab(user, tab: str, conn, existing: set[str], args, totals: dict) -> dict:
	report = _new_report(tab)
	consecutive_dups = 0

	try:
		page = await _fetch_with_retry(lambda: user.get_tweets(tab, count=PAGE_SIZE), report)
	except Exception as exc:
		report["stopped_reason"] = "fetch_failed"
		report["error"] = _error_code(exc)
		report["exception"] = _safe_reason(exc)
		_say(f"{tab} failed on the first page: {_safe_reason(exc)}")
		return report

	# An empty FIRST page is not an exhausted timeline. A shadow-limited or partly
	# invalidated session returns 200 with nothing in it and raises nothing, and
	# reading that as "exhausted" would go green having fetched nothing — forever,
	# and indistinguishable from a quiet day. This is the one detector the notebook
	# never had, and the failure it closes is the worst kind: silent and indefinite.
	if not page:
		report["pages"] = 0
		report["stopped_reason"] = "empty_first_page"
		report["error"] = "empty_timeline"
		_say(f"{tab} returned an empty first page — treating as a dead session, not a quiet day")
		return report

	while page:
		report["pages"] += 1
		for tweet in page:
			screen_name = tweet.user.screen_name if tweet.user else None
			if screen_name and screen_name.lower() != args.user.lower():
				# The Replies timeline drags in other people's tweets.
				report["skipped_other_users"] += 1
				continue
			report["seen"] += 1
			if tweet.id in existing:
				report["duplicates"] += 1
				consecutive_dups += 1
				if args.max_dups and consecutive_dups >= args.max_dups:
					break
				continue
			# CONSECUTIVE, so a stray known id inside a burst of new ones must not
			# read as "caught up" and cut the walk short.
			consecutive_dups = 0
			inserted, tweet_type, created_at = _save(conn, tweet, args.user, args.dry_run)
			existing.add(tweet.id)
			if inserted:
				report["new"] += 1
				totals["by_type"][tweet_type] = totals["by_type"].get(tweet_type, 0) + 1
				if not totals["newest_saved_at"] or created_at > totals["newest_saved_at"]:
					totals["newest_saved_at"] = created_at
		# Commit per page: a crash on page 4 must not discard pages 1-3.
		if not args.dry_run:
			conn.commit()
		_say(f"{tab} p{report['pages']}  seen {report['seen']}  new {report['new']}  "
		     f"dup {report['duplicates']}  (consecutive dup {consecutive_dups})")

		if args.max_dups and consecutive_dups >= args.max_dups:
			# Crossing the known/unknown boundary with max_dups of margin is a PROOF
			# of currency, not a heuristic — the only stop reason that earns it
			# besides running the timeline out.
			report["stopped_reason"] = "duplicate_threshold"
			report["caught_up"] = True
			break

		if report["pages"] >= args.max_pages:
			# Truncated, so this run did not prove currency. Red on purpose.
			report["stopped_reason"] = "page_cap"
			break

		try:
			page = await _fetch_with_retry(page.next, report)
		except Exception as exc:
			report["stopped_reason"] = "fetch_failed"
			report["error"] = _error_code(exc)
			report["exception"] = _safe_reason(exc)
			_say(f"{tab} died mid-walk after {report['pages']} pages: {_safe_reason(exc)}")
			break
	else:
		report["stopped_reason"] = "timeline_exhausted"
		report["caught_up"] = True

	_say(f"{tab} stopped: {report['stopped_reason']}")
	return report


# --- Orchestration -------------------------------------------------------------

async def _scrape(args, client_factory) -> dict:
	"""Always returns a complete document — a failure adds `error`/`detail` rather
	than replacing it, so partial counts survive and the Summary step has one code
	path. You need to know 7 rows landed before it died."""
	started = datetime.now(_KST)
	cookies, cookie_source = _load_cookies(args.env_file)
	tabs: list[dict] = []
	totals = {"by_type": {}, "newest_saved_at": None}
	account = None
	failure: ScrapeError | None = None

	conn = sqlite3.connect(args.db)
	try:
		_init_db(conn)
		existing = _existing_ids(conn)
		db_before = len(existing)
		_say(f"db {args.db} — {db_before} existing rows")
		_say(f"target @{args.user} · cookies from {cookie_source} · "
		     f"max-dups {args.max_dups} · max-pages {args.max_pages}"
		     + (" · DRY RUN" if args.dry_run else ""))

		try:
			if not cookies:
				raise ScrapeError("cookies_missing", _detail_for("cookies_missing", None, args))

			client = client_factory()
			client.set_cookies(cookies)
			user = await _fetch_with_retry(
				lambda: client.get_user_by_screen_name(args.user), None
			)
			account = {
				"name": getattr(user, "name", None),
				"screen_name": getattr(user, "screen_name", args.user),
				"followers": getattr(user, "followers_count", None),
				"statuses": getattr(user, "statuses_count", None),
			}
			_say(f"account: {account['name']} (@{account['screen_name']}) "
			     f"followers {account['followers']:,} · statuses {account['statuses']:,}"
			     if isinstance(account["followers"], int) else f"account: @{account['screen_name']}")

			for tab in _tabs_to_walk(args):
				tabs.append(await _walk_tab(user, tab, conn, existing, args, totals))
		except ScrapeError as exc:
			failure = exc
		except Exception as exc:
			code = _error_code(exc)
			failure = ScrapeError(code, _detail_for(code, exc, args))

		stats = _db_stats(conn)
	finally:
		conn.close()

	# A tab that failed carries its own code; surface the first one at the top level
	# so the workflow's remedy card and ::error:: annotations work uniformly.
	if failure is None:
		broken = next((t for t in tabs if t["error"]), None)
		if broken:
			failure = ScrapeError(
				broken["error"], _detail_for(broken["error"], None, args)
			)

	doc = {
		"user": args.user,
		"db": args.db,
		"dry_run": args.dry_run,
		"cookie_source": cookie_source,
		"started_at": started.strftime("%Y-%m-%dT%H:%M:%S+09:00"),
		"elapsed_seconds": round((datetime.now(_KST) - started).total_seconds(), 1),
		"account": account,
		"new_rows": sum(t["new"] for t in tabs),
		"new_by_type": totals["by_type"],
		"newest_saved_at": totals["newest_saved_at"],
		"tabs": tabs,
		"db_before": db_before,
		"db_totals": stats["totals"],
		"db_newest_at": stats["newest_at"],
		"db_lag_hours": _lag_hours(stats["newest_at"]),
	}
	if failure is not None:
		doc["error"] = failure.code
		doc["detail"] = failure.detail
	doc["invariants_ok"] = failure is None and bool(tabs) and all(t["caught_up"] for t in tabs)
	return doc


def _tabs_to_walk(args) -> list[str]:
	"""Tweets always; Replies only on request.

	The Replies tab 404s: twikit 2.3.3 hardcodes a stale GraphQL query id
	(`vMkJyzx1wdmvOeeNG0n6Wg/UserTweetsAndReplies`, client/gql.py:50) while
	`UserTweets` on line 49 still resolves. Leaving it on would paint the schedule
	permanently red, and a permanently red schedule is one you stop reading.

	It costs almost nothing to lose: self-thread replies already arrive via the
	Tweets tab carrying `in_reply_to`, and the corpus holds 2 reply rows against
	1,609 posts. The flag stays as the way to retest a live upstream defect.
	"""
	return ["Tweets", "Replies"] if args.include_replies else ["Tweets"]


def _lag_hours(newest_at: str | None) -> float | None:
	"""How stale the corpus is. REPORTED, never gated on — it measures his posting
	cadence, not this pipeline, and a quiet week turning the job red would train
	everyone to ignore the emails."""
	if not newest_at:
		return None
	try:
		newest = datetime.strptime(newest_at, "%Y-%m-%dT%H:%M:%S%z")
	except ValueError:
		return None
	return round((datetime.now(_KST) - newest).total_seconds() / 3600, 1)


# Carried verbatim from the notebook. twikit 2.3.3's User.__init__ reads legacy keys
# directly and dies on KeyError when X omits them, so every key it touches gets a
# default seeded first. Do NOT tidy this up: it is a patch against one exact version's
# private constructor, which is also why the PEP 723 block pins twikit ==2.3.3 — a
# minor bump could make this a no-op, or a crash.
_LEGACY_DEFAULTS = {
	'created_at': '', 'name': '', 'screen_name': '', 'profile_image_url_https': '',
	'location': '', 'description': '', 'pinned_tweet_ids_str': [],
	'verified': False, 'possibly_sensitive': False, 'can_dm': False, 'can_media_tag': False,
	'want_retweets': False, 'default_profile': False, 'default_profile_image': False,
	'has_custom_timelines': False, 'is_translator': False, 'translator_type': 'none',
	'followers_count': 0, 'fast_followers_count': 0, 'normal_followers_count': 0,
	'friends_count': 0, 'favourites_count': 0, 'listed_count': 0,
	'media_count': 0, 'statuses_count': 0, 'withheld_in_countries': [],
}


# --- Patch 2: X moved the bundle twikit signs its requests with -------------------
#
# Every GraphQL call carries an `x-client-transaction-id`, which twikit derives from
# a hash scraped out of X's own web bundle. In August 2026 X migrated the ROOT page
# (https://x.com) to a new "x-web" shell that has no module map on it at all, so
# twikit 2.3.3 dies at startup — `Couldn't get KEY_BYTE indices` — before it makes a
# single API call. That is what stopped the notebook: the corpus went quiet on
# 2026-07-25 and nothing said so.
#
# https://x.com/home still serves the old shell, module map and all. Verified live:
# /home is ~275 KB with 234 ondemand references, and the chain (module map -> bundle
# hash -> ondemand.s.<hash>a.js -> key byte indices) resolves end to end. So the fix
# is the page we look at, plus the two patterns that read it.
#
# Only ClientTransaction.init is replaced. get_key / get_key_bytes / get_animation_key
# / generate_transaction_id stay upstream's.

HOME_PAGE_URL = "https://x.com/home"

# X's module map: `,59924:"ondemand.s"` gives the module index, and a second entry
# `,59924:"048b040"` maps that index to the bundle hash. Upstream 2.3.3 looks for
# `"ondemand.s":"<hash>"`, a shape X no longer emits.
_ONDEMAND_MODULE_RE = re.compile(r""",(\d+):["']ondemand\.s["']""")
_ONDEMAND_HASH_TEMPLATE = r',{}:"([0-9a-f]+)"'
# `\w{1,2}`, not upstream's `\w{1}` — the minified variable holding the key bytes is
# not guaranteed to be a single character between builds.
_INDICES_RE = re.compile(r"\(\w{1,2}\[(\d{1,2})\],\s*16\)")


def _ondemand_filename(page_text: str) -> str | None:
	"""The ondemand.s bundle hash from X's home page, or None if the map is gone."""
	module = _ONDEMAND_MODULE_RE.search(page_text)
	if not module:
		return None
	hash_match = re.search(_ONDEMAND_HASH_TEMPLATE.format(module.group(1)), page_text)
	return hash_match.group(1) if hash_match else None


def _key_byte_indices(js_text: str) -> list[int]:
	"""The key-byte indices baked into the ondemand bundle, in order."""
	return [int(m.group(1)) for m in _INDICES_RE.finditer(js_text)]


def _patch_twikit_transaction() -> None:
	import bs4
	import twikit.x_client_transaction.transaction as _transaction

	if getattr(_transaction.ClientTransaction.init, "_serenity_patched", False):
		return

	async def _patched_init(self, session, headers):
		response = await session.request(method="GET", url=HOME_PAGE_URL, headers=headers)
		home = bs4.BeautifulSoup(response.content, "lxml")
		page_text = str(home)

		filename = _ondemand_filename(page_text)
		if not filename:
			raise SessionInitError(
				f"no 'ondemand.s' module map at {HOME_PAGE_URL} "
				f"({len(page_text)} chars) — stale cookies, or X changed its bundle"
			)

		bundle = await session.request(
			method="GET",
			url=f"https://abs.twimg.com/responsive-web/client-web/ondemand.s.{filename}a.js",
			headers=headers,
		)
		indices = _key_byte_indices(bundle.text)
		if len(indices) < 2:
			raise SessionInitError(
				f"ondemand.s.{filename} yielded {len(indices)} key-byte indices, need at least 2"
			)

		self.home_page_response = home
		self.DEFAULT_ROW_INDEX, self.DEFAULT_KEY_BYTES_INDICES = indices[0], indices[1:]
		self.key = self.get_key(response=home)
		self.key_bytes = self.get_key_bytes(key=self.key)
		self.animation_key = self.get_animation_key(key_bytes=self.key_bytes, response=home)

	_patched_init._serenity_patched = True
	_transaction.ClientTransaction.init = _patched_init


def _patch_twikit_user() -> None:
	import twikit.user as _twikit_user

	if getattr(_twikit_user.User.__init__, "_serenity_patched", False):
		return
	_orig_user_init = _twikit_user.User.__init__

	def _patched_user_init(self, client, data):
		data.setdefault('is_blue_verified', False)
		legacy = data.setdefault('legacy', {})
		for _k, _v in _LEGACY_DEFAULTS.items():
			legacy.setdefault(_k, _v)
		legacy.setdefault('entities', {}).setdefault('description', {}).setdefault('urls', [])
		_orig_user_init(self, client, data)

	_patched_user_init._serenity_patched = True
	_twikit_user.User.__init__ = _patched_user_init


def _default_client_factory():
	"""The real twikit client, with the 2.3.3 legacy-key patch applied first.

	Everything twikit-shaped lives behind this function on purpose: the tests run
	under scripts/.venv, which has no twikit, so importing this module must stay
	free of it.
	"""
	from twikit import Client
	_patch_twikit_user()
	_patch_twikit_transaction()
	return Client("en-US")


def _emit(data) -> None:
	json.dump(data, sys.stdout, ensure_ascii=False, indent=2)
	print()


class JsonArgumentParser(argparse.ArgumentParser):
	"""Keep argparse failures inside the CLI's JSON-only contract.

	The workflow parses stdout as JSON unconditionally. argparse's default writes
	usage to stderr and raises SystemExit(2), which would leave stdout empty and the
	Summary step with nothing to render. Mirrors serenity_harness.py.
	"""

	def error(self, message):
		raise ScrapeError("invalid_arguments", message)


def _parse_args(argv):
	# Flat CLI, no subparser. The module-level subcommand convention in this repo
	# exists to satisfy _fetch.py's uniform (module, [verb]) contract; this tool is
	# not a pipeline module and has exactly one verb, so a required subparser with
	# one choice would be ceremony living in the workflow file forever.
	p = JsonArgumentParser(description="Refresh the Serenity thesis DB from X.")
	p.add_argument("--db", default=DEFAULT_DB, help=f"Path to the DB (default {DEFAULT_DB})")
	p.add_argument("--env-file", default=DEFAULT_ENV_FILE,
	               help=f"Cookie fallback when not in the environment (default {DEFAULT_ENV_FILE})")
	p.add_argument("--user", default=TARGET_USER, help=f"Target handle (default {TARGET_USER})")
	p.add_argument("--max-dups", type=int, default=10,
	               help="Stop after N consecutive already-known ids (default 10). "
	                    "0 disables the early stop and re-walks the whole timeline — "
	                    "the repair path after a run that did not prove it was caught up.")
	p.add_argument("--max-pages", type=int, default=100,
	               help=f"Hard cap on pages per tab, {PAGE_SIZE} tweets each (default 100). "
	                    "Guards against a cursor that never terminates.")
	p.add_argument("--include-replies", action="store_true",
	               help="Also walk the Replies tab (default off — it 404s on twikit 2.3.3)")
	p.add_argument("--dry-run", action="store_true",
	               help="Fetch and classify, write nothing (default off)")
	p.add_argument("--quiet", action="store_true",
	               help="Suppress the stderr progress lines (default off)")
	return p.parse_args(argv)


def main(argv=None, client_factory=None) -> int:
	global _QUIET
	try:
		args = _parse_args(argv)
	except ScrapeError as exc:
		_emit({"error": exc.code, "detail": exc.detail, "invariants_ok": False})
		return 2

	_QUIET = args.quiet
	doc = asyncio.run(_scrape(args, client_factory or _default_client_factory))
	_emit(doc)
	return 0 if doc["invariants_ok"] else 1


if __name__ == "__main__":
	sys.exit(main())
