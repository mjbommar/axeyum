#!/usr/bin/env python3
"""Flag registry entries whose justification predates the code it protects.

This is the check the config registry exists for. `MAX_ONLINE_LRA_ATOMS` rested
on a measurement taken 2026-08-03 of an 8 GiB abort; `MAX_LRA_CACHED_COEFFICIENTS`,
the bound that caps exactly that cost, landed 2026-08-06 — three days later. The
measurement described a tree in which the thing it protected against was
unbounded, and it stood for thirteen months because nothing could compare a date
against a diff.

For every DATED entry in `crates/axeyum-solver/src/config_registry.rs`, this asks
git whether anything the justification `rests_on` changed strictly after the day
that measurement was taken. If so, the measurement describes a tree that no
longer exists and the entry is STALE.

    exit 0  no dated entry is stale
    exit 1  at least one dated entry is stale   <- the finding
    exit 2  the registry could not be read, or a self-check failed

`--list` prints the whole registry (dated and undated) and exits 0; use it to
see the surface rather than to gate on it.

WHY `git log -G` AND NOT A FILE MTIME: a file's mtime says nothing after a fresh
clone, and a whole-file `git log` on a 9,000-line dispatcher is stale every day
for reasons that have nothing to do with the bound. `-G<symbol>` matches commits
whose DIFF mentions the symbol, which is the closest available proxy for "the
code this measurement was about changed".

WHAT IT CANNOT SEE: a semantic dependency nobody wrote down. The check is only
as good as each entry's `rests_on`, which is why an entry may not be dated
without naming one (enforced by `dated_justifications_are_well_formed`). A
justification that rests on nothing cannot go stale, so it would be a date that
means nothing.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
REGISTRY_RS = REPO / "crates" / "axeyum-solver" / "src" / "config_registry.rs"

ENTRY_RE = re.compile(r"^    ConfigEntry \{$")
# `re.MULTILINE` is load-bearing: this is applied to a multi-line blob, and
# without it `^`/`$` anchor to the whole string, every field silently fails to
# match, and the parser returns zero entries. The self-check in `main` caught
# exactly that on this script's first run — a "0 stale" report that would
# otherwise have been indistinguishable from a clean bill of health.
FIELD_RE = re.compile(r"^\s{8}(\w+):\s*(.*?),?$", re.MULTILINE)
STR_RE = re.compile(r'^"((?:[^"\\]|\\.)*)"')
# The `\s*,?\s*` before the closing paren is load-bearing: rustfmt breaks a
# multi-argument `sym(...)` across lines AND adds a trailing comma, so a regex
# ending in `\s*\)` matches nothing. Without it every dated entry parsed with an
# EMPTY `rests_on`, and the checker reported "no dated justification is stale"
# for all 24 of them — a checker that could not fire, printing exactly what a
# working one prints. The positive control below is what caught it.
SYM_RE = re.compile(
    r'sym\(\s*"((?:[^"\\]|\\.)*)"\s*,\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)'
)
FILE_RE = re.compile(r'file\(\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)')
# `@@ -<old>[,n] +<new>[,n] @@` -- the line numbers a diff body line belongs to.
HUNK_RE = re.compile(r"^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@")

# Per-process memoisation of the two git questions. Keyed by exactly the inputs
# that determine the answer, and cleared by `--repo` because that changes which
# repository the answers describe.
_PATCH_CACHE: dict[tuple[str, str], str | None] = {}
_COMMITS_CACHE: dict[tuple[str, str], list[tuple[str, str, str]]] = {}
_LINES_CACHE: dict[tuple[str, str], list[tuple[str, int, str]] | None] = {}
_FILE_CACHE: dict[tuple[str, str], list[str] | None] = {}
_FLAGS_CACHE: dict[tuple[str, str], list[bool] | None] = {}
_REV_CACHE: dict[str, str | None] = {}


@dataclass
class Entry:
    name: str = ""
    module: str = ""
    value: str = ""
    unit: str = ""
    location: str = ""
    measured_on: str | None = None
    measured_at_commit: str | None = None
    rests_on: list[tuple[str, str | None]] = field(default_factory=list)

    @property
    def key(self) -> str:
        return f"{self.module}::{self.name}"


def _unquote(s: str) -> str:
    m = STR_RE.match(s.strip())
    return m.group(1).replace('\\"', '"').replace("\\\\", "\\") if m else ""


def parse_registry(path: Path) -> list[Entry]:
    """Parse the `ConfigEntry` literals out of the registry source.

    Deliberately structural rather than clever: a `ConfigEntry {` line opens an
    entry and the matching `    },` closes it. The count is cross-checked against
    the raw literal count below, so a parse that silently skipped an entry is a
    self-check failure rather than a quietly shorter report.
    """
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    entries: list[Entry] = []
    i = 0
    while i < len(lines):
        if not ENTRY_RE.match(lines[i]):
            i += 1
            continue
        e = Entry()
        i += 1
        depth = 1
        buf: list[str] = []
        while i < len(lines) and depth > 0:
            line = lines[i]
            if line.rstrip() == "    },":
                depth = 0
                break
            buf.append(line)
            i += 1
        blob = "\n".join(buf)
        for m in FIELD_RE.finditer(blob):
            k, v = m.group(1), m.group(2)
            if k == "name":
                e.name = _unquote(v)
            elif k == "module":
                e.module = _unquote(v)
            elif k == "value":
                e.value = _unquote(v)
            elif k == "unit":
                e.unit = _unquote(v)
        # `undated("loc")` or a multi-line `dated(...)` call.
        und = re.search(r'undated\(\s*"((?:[^"\\]|\\.)*)"\s*\)', blob)
        if und:
            e.location = und.group(1)
        else:
            dated = re.search(r"justification: dated\(\s*\n(.*?)\n\s{8}\),", blob, re.S)
            if dated:
                body = dated.group(1)
                strs = re.findall(r'"((?:[^"\\]|\\.)*)"', body.split("&[")[0])
                if len(strs) >= 2:
                    e.location, e.measured_on = strs[0], strs[1]
                if len(strs) >= 3:
                    e.measured_at_commit = strs[2]
                deps_part = body.split("&[", 1)[1] if "&[" in body else ""
                for p, s in SYM_RE.findall(deps_part):
                    e.rests_on.append((p, s))
                for p in FILE_RE.findall(deps_part):
                    e.rests_on.append((p, None))
        if e.name and e.module:
            entries.append(e)
        i += 1
    return entries


def introducing_commit(path: str, symbol: str | None) -> str | None:
    """The oldest commit whose diff to `path` mentions `symbol`.

    Used to exclude a constant's OWN introduction from its OWN staleness; see
    the narrow exclusion in `main`.
    """
    cmd = ["git", "-C", str(REPO), "log", "--reverse", "--format=%h"]
    if symbol:
        cmd.append(f"-G{re.escape(symbol)}")
    cmd += ["--", path]
    out = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if out.returncode != 0:
        return None
    shas = out.stdout.split()
    return shas[0] if shas else None


DEF_RE_TEMPLATE = (
    r"^\s*(?:pub\s*(?:\([^)]*\)\s*)?)?(?:default\s+)?(?:const\s+|async\s+|unsafe\s+|"
    r"extern\s+\"[^\"]*\"\s+)*(?:fn|struct|enum|union|trait|type|const|static)\s+"
    r"{sym}\b"
)


ACCEPTED_PATH = REPO / "artifacts" / "config-registry-accepted-staleness.tsv"


def _read_accepted() -> dict[tuple[str, str], str] | None:
    """The accepted-staleness ledger, or `None` when the file does not exist.

    Three tab-separated columns: the entry key, the `path::symbol` it rests on,
    and a REASON. The reason is required and must be non-empty -- a baseline of
    bare identifiers is a mute backlog, and the whole point of this file is that
    someone looked at each row and wrote down what they found.

    WHY A RATCHET AND NOT A CLEAN BILL. On 2026-09-15 this gate reported 11 stale
    rows. Teaching it to notice a rewritten function body (`definition_changed`)
    took that to 24 across 14 entries -- 13 rows that had been stale and
    invisible. Clearing 24 means re-running fourteen corpus measurements, and the
    two ways to make the gate green without doing that are both forbidden: moving
    the dates is the rubber stamp this check exists to prevent, and deleting the
    `rests_on` entries is the same thing with extra steps.

    So the backlog is written down instead, with a reason per row, and the gate
    fails on any row that is NOT in it -- and equally on any row in it that is no
    longer stale, so the file cannot quietly accumulate lines that describe
    nothing. It can fail in both directions, which is the property that separates
    a ratchet from a suppression list.
    """
    if not ACCEPTED_PATH.exists():
        return None
    out: dict[tuple[str, str], str] = {}
    for n, raw in enumerate(ACCEPTED_PATH.read_text(encoding="utf-8").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        parts = raw.split("\t")
        if len(parts) < 3 or not parts[2].strip():
            print(f"FAIL: {ACCEPTED_PATH.name}:{n} needs three tab-separated "
                  f"columns ending in a non-empty reason.", file=sys.stderr)
            raise SystemExit(2)
        out[(parts[0].strip(), parts[1].strip())] = parts[2].strip()
    return out


def _print_stale(stale, verbose: bool) -> None:
    for e, path, symbol, rows in stale:
        what = f"{path}::{symbol}" if symbol else path
        print(f"  {e.key}\n    measured {e.measured_on} ({e.location}), "
              f"rests on {what}")
        if not rows:
            print("    definition drift: the symbol's definition at HEAD is not "
                  "the one that was measured")
        else:
            for h, d, s in rows[: (None if verbose else 3)]:
                print(f"      {h} {d} {s[:96]}")


def _rev_on(date: str) -> str | None:
    """The last commit on or before `date 23:59:59` — the tree a measurement saw."""
    if date not in _REV_CACHE:
        out = subprocess.run(
            ["git", "-C", str(REPO), "rev-list", "-1",
             f"--before={date} 23:59:59", "HEAD"],
            capture_output=True, text=True, check=False,
        )
        sha = out.stdout.strip()
        _REV_CACHE[date] = sha if out.returncode == 0 and sha else None
    return _REV_CACHE[date]


def _definition_code(rev: str, path: str, symbol: str) -> list[str] | None:
    """`symbol`'s definition at `rev`, as code lines with comments and blank lines
    removed, or `None` when it cannot be located unambiguously.

    Extent is brace-matched over comment- and string-stripped text, so a brace in
    a doc comment or a literal cannot close the item early. A `const`/`static`/
    `type` runs to its `;`.
    """
    lines = _file_at(rev, path)
    if lines is None:
        return None
    code: list[str] = []
    in_block = in_raw = in_str = False
    for raw in lines:
        stripped, in_block, in_raw, in_str = _scan_rust_line(
            raw, in_block, in_raw, in_str
        )
        code.append(stripped)
    pat = re.compile(DEF_RE_TEMPLATE.format(sym=re.escape(symbol)))
    starts = [i for i, c in enumerate(code) if pat.match(c)]
    if len(starts) != 1:
        # Zero (a method, a macro-generated item, a renamed symbol) or several
        # (overloads in separate `impl` blocks). Either way this check declines
        # rather than guessing which one the measurement meant.
        return None
    i = starts[0]
    if re.match(r"^\s*(?:pub\s*(?:\([^)]*\)\s*)?)?(?:const|static|type)\s+", code[i]):
        j = i
        while j < len(code) and ";" not in code[j]:
            j += 1
        body = code[i:j + 1]
    else:
        depth, j, opened = 0, i, False
        while j < len(code):
            if not opened and ";" in code[j] and "{" not in code[j]:
                break  # a trait method signature or a `fn` declaration
            depth += code[j].count("{") - code[j].count("}")
            if "{" in code[j]:
                opened = True
            if opened and depth <= 0:
                break
            j += 1
        if j >= len(code):
            return None
        body = code[i:j + 1]
    return [" ".join(b.split()) for b in body if b.strip()]


def definition_changed(date: str, path: str, symbol: str) -> bool | None:
    """Is `symbol`'s definition different at HEAD from the tree `date` measured?

    `None` means "could not compare" -- the symbol was not locatable on one side
    -- and the caller must not read that as "unchanged".

    WHY THIS EXISTS, and it is the gate's largest blind spot rather than a
    refinement. `git log -G<symbol>` matches commits whose PATCH TEXT mentions
    the symbol. For a CONSTANT that is a good proxy, because its uses spell its
    name. For a FUNCTION it is close to backwards: the body is where the
    behaviour lives and the body does not repeat the function's own name, so a
    complete rewrite is invisible unless a changed line happens to mention it.

    Measured 2026-09-15 on this registry's own red rows. `ee36e0421` gave
    `lra.rs::decide_within` a `deadline` parameter and deadline polls, and the
    function went from 163 lines to a 7-line wrapper. Of the FIVE changed lines
    in that commit mentioning `decide_within`, three are `///` doc comments and
    two are calls inside `#[cfg(test)]` code. So the pickaxe reported
    `SIMPLEX_FIRST_AT_CONSTRAINTS` stale for its comments and its tests, and
    would have reported it CLEAN had the commit been tidier -- while the
    measurement genuinely no longer describes the function.

    That is the shape this repository calls a checker that cannot fail: it was
    red for a reason unrelated to its subject, so the red carried no information
    either way.
    """
    old = _rev_on(date)
    if old is None:
        return None
    before = _definition_code(old, path, symbol)
    after = _definition_code("HEAD", path, symbol)
    if before is None or after is None:
        return None
    return before != after


def _strip_rust_strings_and_line_comment(line: str) -> tuple[str, bool]:
    """Return `(code-only text, ambiguous)` for one Rust source line.

    Removes double-quoted string literals (honouring backslash escapes) and any
    trailing `//` comment. `ambiguous` is True when the line carries a construct
    a SINGLE diff line cannot resolve -- a block-comment delimiter, a raw-string
    prefix, or an unterminated quote -- and the caller must then decline to call
    an occurrence non-code.
    """
    ambiguous = "/*" in line or "*/" in line or 'r"' in line or 'r#"' in line
    out: list[str] = []
    i, n, in_str = 0, len(line), False
    while i < n:
        c = line[i]
        if in_str:
            if c == "\\":
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if c == "/" and i + 1 < n and line[i + 1] == "/":
            break
        out.append(c)
        i += 1
    if in_str:
        ambiguous = True
    return "".join(out), ambiguous


def symbol_occurs_in_code(line: str, symbol: str) -> bool:
    """Whether `symbol` appears in `line` as CODE, not inside a string or comment.

    WHY THIS EXISTS: `git log -G<symbol>` matches the symbol anywhere in a diff
    line, including inside a string literal. On 2026-09-10 that made this gate
    report `simplex.rs::MAX_TABLEAU_CELLS` stale because a commit had added two
    `.expect("1x1 tableau is far below MAX_TABLEAU_CELLS")` messages to a TEST.
    The constant's value, its doc comment and its uses were untouched.

    That is the failure mode this repository calls a gate that manufactures a
    finding, and it is expensive in a specific way: it costs the gate its
    authority. A checker that fires on a string literal trains its readers to
    skim past the entries that are real.

    This module's own header states the subject: "code this measurement was
    about changed". A mention inside a string or a comment is not that.

    Conservative in the direction that keeps findings: anything unresolvable
    from one diff line counts as code.
    """
    code, ambiguous = _strip_rust_strings_and_line_comment(line)
    if ambiguous:
        return True
    return re.search(rf"\b{re.escape(symbol)}\b", code) is not None


def _patch(sha: str, path: str) -> str | None:
    """`sha`'s zero-context patch for `path`, or `None` if git could not show it.

    Cached: the same commit is asked about once per dependency that names it,
    and `f6303ee7a -- lra.rs` alone was fetched six times in one run.
    """
    key = (sha, path)
    if key not in _PATCH_CACHE:
        out = subprocess.run(
            ["git", "-C", str(REPO), "show", "--format=", "--unified=0", sha, "--", path],
            capture_output=True, text=True, check=False,
        )
        _PATCH_CACHE[key] = out.stdout if out.returncode == 0 else None
    return _PATCH_CACHE[key]


def _changed_line_bodies(sha: str, path: str) -> list[str] | None:
    """The added/removed line bodies of `sha`'s patch for `path`, `None` if git
    could not show it.

    Split out and cached because the hunk-header filtering does not depend on the
    symbol, while `_commit_changes_symbol_in_code` is asked about the SAME commit
    once per dependency naming it. Re-splitting `f6303ee7a`'s 566-line patch for
    each of the five symbols that rest on `lra.rs` is four scans of the same text.
    """
    key = (sha, path)
    if key not in _LINES_CACHE:
        # Not reached for a commit `_commits_touching` enumerated -- that call
        # fills this cache for every commit in one `git log -p`. This is the
        # fallback for a commit asked about on its own.
        patch = _patch(sha, path)
        if patch is None:
            _LINES_CACHE[key] = None
        else:
            _LINES_CACHE[key] = _bodies(patch)
    return _LINES_CACHE[key]


def _bodies(patch: str) -> list[tuple[str, int, str]]:
    """The added/removed lines of a zero-context patch as `(side, lineno, body)`.

    `side` is `"+"` or `"-"` and `lineno` is the line's number in the side of the
    diff it belongs to -- the post-image for `+`, the pre-image for `-`. The
    number is carried because two of the three "is this occurrence really code"
    questions cannot be answered from the line's own text: see
    `_non_code_line_flags`.
    """
    out: list[tuple[str, int, str]] = []
    old_n = new_n = 0
    for line in patch.splitlines():
        m = HUNK_RE.match(line)
        if m:
            old_n, new_n = int(m.group(1)), int(m.group(2))
            continue
        if not line or line[0] not in "+-" or line.startswith(("+++", "---")):
            continue
        if line[0] == "+":
            out.append(("+", new_n, line[1:]))
            new_n += 1
        else:
            out.append(("-", old_n, line[1:]))
            old_n += 1
    return out


def _file_at(rev: str, path: str) -> list[str] | None:
    """`path`'s lines at `rev`, or `None`. Cached."""
    key = (rev, path)
    if key not in _FILE_CACHE:
        out = subprocess.run(
            ["git", "-C", str(REPO), "show", f"{rev}:{path}"],
            capture_output=True, text=True, check=False,
        )
        _FILE_CACHE[key] = out.stdout.splitlines() if out.returncode == 0 else None
    return _FILE_CACHE[key]


def _non_code_line_flags(rev: str, path: str) -> list[bool] | None:
    """Per line of `path` at `rev`: does the line BEGIN somewhere that is not the
    code this registry measures?

    Two cases, both of which `symbol_occurs_in_code` exists to exclude and
    neither of which a SINGLE diff line can decide. Index 0 is unused so the list
    is addressed by 1-based line number.

    1. INSIDE A MULTI-LINE STRING LITERAL. `_strip_rust_strings_and_line_comment`
       is per-line, so it removes a string opened and closed on one line and is
       blind to a continuation line of one that is not. Measured instance:
       `a4642ce8d`'s only two mentions of `dpll_lia.rs::MAX_PRE_SAT_CNF_VARS` are
       the lines

           >{MAX_PRE_SAT_CNF_VARS}, moderate_envelope<={envelope_atoms}/\\

       inside a `format!` whose literal spans six lines. There is no quote
       character on that line, so the per-line filter saw bare code, and the
       constant was reported stale by a commit that did not touch it -- the exact
       false positive that function's docstring says costs the gate its authority.

    2. INSIDE A `#[cfg(test)]` ITEM. A test that CALLS a function cannot change
       what that function computes, so a mention there is not "the code this
       measurement was about" any more than a mention in a comment is. Measured
       instance: `ac43d6031` changed 28 lines of `lra.rs`, all 28 inside
       `mod give_up_reason_tests`, and made three registry rows stale.

    Regions are computed from the file AT THAT COMMIT, on the correct side of the
    diff, because `#[cfg(test)]` boundaries move.

    Deliberately conservative in the direction that KEEPS findings: an
    unparseable file returns `None` and the caller falls back to the per-line
    filter, and the test-region walk only claims a region it can brace-match.
    """
    key = (rev, path)
    if key in _FLAGS_CACHE:
        return _FLAGS_CACHE[key]
    lines = _file_at(rev, path)
    if lines is None:
        _FLAGS_CACHE[key] = None
        return None
    n = len(lines)
    flags = [False] * (n + 2)

    # Pass 1: string / block-comment continuation. `starts_inside[i]` is whether
    # line i BEGINS inside a literal or block comment opened on an earlier line.
    code: list[str] = []
    in_block = False
    in_raw = False
    in_str = False
    for i, raw_line in enumerate(lines):
        if in_block or in_raw or in_str:
            flags[i + 1] = True
        stripped, in_block, in_raw, in_str = _scan_rust_line(
            raw_line, in_block, in_raw, in_str
        )
        code.append(stripped)

    # Pass 2: `#[cfg(test)]` items, bounded by brace depth over the stripped text
    # so a brace inside a string or comment cannot close a module early.
    for i, raw_line in enumerate(lines):
        if raw_line.strip() != "#[cfg(test)]":
            continue
        j, depth, opened = i + 1, 0, False
        while j < n:
            depth += code[j].count("{") - code[j].count("}")
            if "{" in code[j]:
                opened = True
            if opened and depth <= 0:
                break
            if not opened and ";" in code[j]:
                break
            j += 1
        if j >= n:
            continue  # unbalanced: claim nothing
        for k in range(i, min(j + 1, n)):
            flags[k + 1] = True

    _FLAGS_CACHE[key] = flags
    return flags


def _scan_rust_line(
    line: str, in_block: bool, in_raw: bool, in_str: bool
) -> tuple[str, bool, bool, bool]:
    """Strip one Rust line of strings/comments, carrying multi-line state.

    Returns the code-only text and the state the NEXT line begins in. Raw strings
    are tracked only coarsely (any `r"`/`r#"` opens, the matching `"`/`"#`
    closes), which is enough for brace counting and for the continuation flag.
    """
    out: list[str] = []
    i, n = 0, len(line)
    while i < n:
        if in_block:
            j = line.find("*/", i)
            if j < 0:
                return "".join(out), True, in_raw, in_str
            i, in_block = j + 2, False
            continue
        if in_raw:
            j = line.find('"', i)
            if j < 0:
                return "".join(out), in_block, True, in_str
            i, in_raw = j + 1, False
            continue
        if in_str:
            while i < n:
                if line[i] == "\\":
                    i += 2
                    continue
                if line[i] == '"':
                    i += 1
                    in_str = False
                    break
                i += 1
            if in_str:
                return "".join(out), in_block, in_raw, True
            continue
        c = line[i]
        if c == "r" and line.startswith(('r"', 'r#"', 'r##"'), i):
            in_raw = True
            i += line[i:].find('"') + 1
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if c == "/" and i + 1 < n and line[i + 1] == "/":
            break
        if c == "/" and i + 1 < n and line[i + 1] == "*":
            in_block, i = True, i + 2
            continue
        out.append(c)
        i += 1
    return "".join(out), in_block, in_raw, in_str


def _commits_touching(date: str, path: str) -> list[tuple[str, str, str]]:
    """Every commit touching `path` strictly after `date` — NO pickaxe.

    The per-symbol `-G` filter is applied in Python by `commits_after`, over the
    patch it has to read anyway for `_commit_changes_symbol_in_code`. Measured
    2026-09-15 on 140 `rests_on` pairs: 140 `git log -G<symbol>` invocations cost
    7.3 s of a 14.6 s run, because the pickaxe re-walks history once per SYMBOL
    while the set of candidate COMMITS depends only on (date, path). Enumerating
    once per (date, path) and testing symbols against the cached patch is the
    same question asked once instead of 140 times.

    This is a speed change and NOT a semantic one: `-G<re.escape(symbol)>` keeps
    a commit whose patch has an added or removed line containing `symbol`, which
    is exactly the `symbol not in body` test in `_commit_changes_symbol_in_code`.
    The equivalence is not asserted — `--self-test` runs both implementations
    over every dependency in the registry and requires identical rows, and it is
    what caught BOTH divergences this rewrite actually had (see
    `_commit_changes_symbol_in_code` for the first).

    `--no-merges` is the second. `git log -G` generates no patch for a merge, so
    the pickaxe never matched one; `git show` DOES produce one, so without this
    flag the merge `bec2cf65b` was attributed four separate staleness rows it had
    not caused. Excluding merges is also the right answer independently: a merge
    commit's content belongs to the branch commit that wrote it, and counting
    merges would restale every entry in the registry each time a lane merges main.

    THE BLIND SPOT THIS INHERITS: a change made only in a conflict resolution (an
    "evil merge") exists in no non-merge commit, so neither the pickaxe nor this
    sees it. That was already true before this rewrite; it is written down here
    rather than fixed because fixing it means diffing every merge against both
    parents, which is a different and much more expensive question.
    """
    key = (date, path)
    if key not in _COMMITS_CACHE:
        # ONE `git log -p` carries the commit list AND every patch, so the
        # per-commit `git show` calls disappear: 51 log + 353 show invocations
        # became 51. Each commit is introduced by a NUL-prefixed header line,
        # which cannot occur inside a patch body.
        out = subprocess.run(
            ["git", "-C", str(REPO), "log", "--no-merges",
             "--after", f"{date} 23:59:59",
             "--format=%x00%h\t%cs\t%s", "-p", "--unified=0", "--", path],
            capture_output=True, text=True, check=False,
        )
        if out.returncode != 0:
            raise RuntimeError(f"git log failed for {path}: {out.stderr.strip()}")
        rows: list[tuple[str, str, str]] = []
        sha = None
        buf: list[str] = []

        def flush() -> None:
            if sha is not None:
                _LINES_CACHE[(sha, path)] = _bodies("\n".join(buf))

        for line in out.stdout.splitlines():
            if line.startswith("\0"):
                flush()
                buf = []
                parts = line[1:].split("\t", 2)
                sha = parts[0] if parts else None
                if len(parts) == 3:
                    rows.append((parts[0], parts[1], parts[2]))
                continue
            buf.append(line)
        flush()
        _COMMITS_CACHE[key] = rows
    return _COMMITS_CACHE[key]


def _commit_changes_symbol_in_code(sha: str, path: str, symbol: str) -> bool:
    """Whether `sha` changed a line where `symbol` appears as code, in `path`.

    A commit whose every added/removed mention of the symbol sits in a string or
    a comment did not change the code the measurement rests on. A failure to
    look keeps the commit.

    A commit whose patch does not mention the symbol AT ALL is dropped, and that
    line is load-bearing. It used to `return not saw_occurrence` -- i.e. KEEP --
    because the only callers were commits `git log -G<symbol>` had already
    matched, so "no visible occurrence" meant "matched for a reason the +/- lines
    do not show" (a rename, a mode change) and keeping was the conservative
    reading. Once `_commits_touching` enumerates every commit that touched the
    file, that same `return True` keeps every commit that has nothing to do with
    the symbol. `--self-test` caught exactly that on this rewrite's first run:
    64 of 140 dependency pairs disagreed with the pickaxe, every one of them in
    the direction of MORE staleness, which is the direction that looks like
    diligence.
    """
    bodies = _changed_line_bodies(sha, path)
    if bodies is None:
        return True
    flags: dict[str, list[bool] | None] = {}
    for side, lineno, body in bodies:
        if symbol not in body:
            continue
        if side not in flags:
            flags[side] = _non_code_line_flags(
                sha if side == "+" else f"{sha}^", path
            )
        side_flags = flags[side]
        if side_flags is not None and lineno < len(side_flags) and side_flags[lineno]:
            # The occurrence is a continuation line of a multi-line string, or
            # sits in a `#[cfg(test)]` item. Same judgement as a mention inside a
            # one-line string or a comment, which this filter already drops.
            continue
        if symbol_occurs_in_code(body, symbol):
            return True
    return False


def commits_after(date: str, path: str, symbol: str | None) -> list[tuple[str, str, str]]:
    """Commits touching `path` strictly after `date`, optionally mentioning `symbol`.

    `--after "<date> 23:59:59"` rather than `--since=<date>`: a commit landing on
    the same day as the measurement is not evidence the measurement is stale, and
    `--since` would flag every entry dated today against its own landing commit.
    """
    rows = _commits_touching(date, path)
    if symbol:
        # Two filters, in cost order over ONE cached patch per commit. The first
        # is what `-G<symbol>` computed before (`_commits_touching` deliberately
        # does not pickaxe -- see its docstring for the measurement); the second
        # keeps only the commits that changed the symbol as CODE. See
        # `symbol_occurs_in_code` for the false positive that one removes and why
        # it costs the gate more than it saves.
        rows = [r for r in rows if _commit_changes_symbol_in_code(r[0], path, symbol)]
    return rows


def pickaxe_commits_after(date: str, path: str, symbol: str | None) -> list[tuple[str, str, str]]:
    """`commits_after`'s pre-2026-09-15 implementation, kept as the CONTROL.

    Not called by the gate. `the_pickaxe_and_the_python_filter_agree` runs this
    and `commits_after` over every dependency the registry declares and requires
    identical rows, so the speed change above is held to being a speed change.
    A rewritten filter whose only evidence was "the report looks the same" would
    be a filter nobody compared.
    """
    cmd = [
        "git", "-C", str(REPO), "log",
        "--after", f"{date} 23:59:59",
        "--format=%h\t%cs\t%s",
    ]
    if symbol:
        cmd.append(f"-G{re.escape(symbol)}")
    cmd += ["--", path]
    out = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if out.returncode != 0:
        raise RuntimeError(f"git log failed for {path}: {out.stderr.strip()}")
    rows = []
    for line in out.stdout.splitlines():
        parts = line.split("\t", 2)
        if len(parts) == 3:
            rows.append((parts[0], parts[1], parts[2]))
    if symbol:
        rows = [r for r in rows if _commit_changes_symbol_in_code(r[0], path, symbol)]
    return rows


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--list", action="store_true", help="print the registry and exit 0")
    ap.add_argument("--verbose", action="store_true", help="name the commits that made an entry stale")
    ap.add_argument(
        "--self-test",
        action="store_true",
        help="run `commits_after` and the pre-2026-09-15 pickaxe implementation "
             "over EVERY dependency the registry declares and require identical "
             "rows, then exit 0/1 on that comparison alone. This is the control "
             "for the speed change in `_commits_touching`: the two must answer "
             "the same question, and a report that merely looks unchanged is "
             "not evidence that they do.",
    )
    ap.add_argument(
        "--repo",
        type=Path,
        default=None,
        help="repository root to query with git (default: this script's own "
             "parent-of-parent). Exists so this check's CONTROL can run a "
             "deliberately mutated COPY of this script against the real "
             "history without placing that mutant in a shared worktree -- a "
             "mutant on disk in the shared checkout is in every other lane's "
             "build, and the failures it causes look like their bug.",
    )
    ap.add_argument(
        "--accepted",
        type=Path,
        default=None,
        help="accepted-staleness ledger to read (default: the in-tree one). "
             "Exists for the same reason as --registry: this ratchet's own "
             "CONTROLS must be able to delete and add a row WITHOUT putting a "
             "mutated file in a shared worktree, where it is in every other "
             "lane's build. A ratchet that has never been shown to fire in "
             "both directions is a suppression list.",
    )
    ap.add_argument(
        "--registry",
        type=Path,
        default=None,
        help="registry source to read (default: the in-tree one). Exists so this "
             "check's own POSITIVE CONTROL can be run against a deliberately "
             "backdated copy without mutating a shared checkout. A staleness "
             "checker that has never been shown to fire is indistinguishable "
             "from one that cannot.",
    )
    args = ap.parse_args()

    if args.accepted is not None:
        global ACCEPTED_PATH
        ACCEPTED_PATH = args.accepted

    if args.repo is not None:
        global REPO, REGISTRY_RS
        REPO = args.repo.resolve()
        REGISTRY_RS = REPO / "crates" / "axeyum-solver" / "src" / "config_registry.rs"
        # The caches hold answers ABOUT A REPOSITORY. Pointing at a different
        # one without clearing them would serve the previous repository's
        # history to this one's registry -- and the control that runs a mutated
        # copy against the real history is exactly the caller that does this.
        _PATCH_CACHE.clear()
        _COMMITS_CACHE.clear()
        _LINES_CACHE.clear()
        _FILE_CACHE.clear()
        _FLAGS_CACHE.clear()
        _REV_CACHE.clear()

    registry_rs = args.registry if args.registry is not None else REGISTRY_RS
    if not registry_rs.exists():
        print(f"FAIL: registry not found at {registry_rs}", file=sys.stderr)
        return 2

    entries = parse_registry(registry_rs)

    # Self-check: the parser must find every `ConfigEntry` literal in the file.
    # A parse that silently dropped entries would report "0 stale" for a reason
    # that has nothing to do with staleness, which is the shape of checker this
    # repository has been bitten by. The needle is split so this line does not
    # count itself.
    needle = "    ConfigEntry" + " {"
    literals = registry_rs.read_text(encoding="utf-8").count(needle)
    if literals != len(entries):
        print(
            f"FAIL (self-check): the file holds {literals} ConfigEntry literals "
            f"but the parser produced {len(entries)} entries. The report below "
            f"would be silently incomplete.",
            file=sys.stderr,
        )
        return 2

    dated = [e for e in entries if e.measured_on]

    if args.self_test:
        pairs = disagreements = 0
        for e in dated:
            for path, symbol in e.rests_on:
                if not (REPO / path).exists():
                    continue
                pairs += 1
                fast = commits_after(e.measured_on, path, symbol)
                slow = pickaxe_commits_after(e.measured_on, path, symbol)
                if fast != slow:
                    disagreements += 1
                    print(f"DISAGREE {e.key} rests on {path}::{symbol}\n"
                          f"    python-filter: {[r[0] for r in fast]}\n"
                          f"    git pickaxe  : {[r[0] for r in slow]}",
                          file=sys.stderr)
        # The denominator is printed beside the zero on purpose: "0 disagreements"
        # over 0 compared pairs is what a self-test that never ran also prints.
        print(f"self-test: {disagreements} disagreement(s) over {pairs} compared "
              f"rests_on pair(s) from {len(dated)} dated entries.")
        if pairs == 0:
            print("FAIL (self-test): compared NOTHING — a control that examines "
                  "an empty population cannot fail.", file=sys.stderr)
            return 2
        return 1 if disagreements else 0
    undated = [e for e in entries if not e.measured_on]

    if args.list:
        for e in sorted(entries, key=lambda x: x.key):
            when = e.measured_on or "UNDATED"
            print(f"{when}\t{e.key}\t= {e.value}\t[{e.unit}]\t{e.location}")
        print(f"\n{len(entries)} entries, {len(dated)} dated, {len(undated)} undated",
              file=sys.stderr)
        return 0

    stale: list[tuple[Entry, str, str | None, list[tuple[str, str, str]]]] = []
    for e in dated:
        for path, symbol in e.rests_on:
            if not (REPO / path).exists():
                print(f"FAIL: {e.key} rests on a missing path {path}", file=sys.stderr)
                return 2
            rows = commits_after(e.measured_on, path, symbol)
            # A constant's OWN introducing commit cannot make its OWN
            # justification stale: a decision is recorded, then the code
            # implementing it lands, and that ordering is the healthy one.
            # Measured: ADR-0360 is dated 2026-07-22 and `5b4c5b404` INTRODUCED
            # all three `MAX_MBQI_FREE_INT_*` constants on 2026-07-23. This
            # check reported those as three stale entries on its first honest
            # run. They are not stale; the rule was.
            #
            # The exclusion is deliberately NARROW — self-dependency only. A
            # commit that introduces a DIFFERENT constant an entry rests on is
            # exactly the failure this check exists for: `96ff85930` INTRODUCED
            # `MAX_LRA_CACHED_COEFFICIENTS`, and that introduction is what
            # falsified `MAX_ONLINE_LRA_ATOMS`'s 2026-08-03 measurement.
            # Excluding introductions in general would blind this checker to its
            # own founding example, which the positive control would then catch.
            #
            # `rows and` short-circuits a FULL-HISTORY pickaxe that has nothing
            # to exclude: filtering the introducing commit out of an empty list
            # yields an empty list either way. Measured 2026-09-15 with
            # `cProfile`: `introducing_commit` ran 74 times for 7.08 s of an
            # 11.08 s run, and only 9 of those 74 entries had a row to filter.
            if rows and path == e.module and symbol == e.name:
                intro = introducing_commit(path, symbol)
                if intro:
                    rows = [r for r in rows if r[0] != intro]
            if rows:
                stale.append((e, path, symbol, rows))
            elif symbol and definition_changed(e.measured_on, path, symbol):
                # No commit MENTIONED the symbol on a code line, but the symbol's
                # own definition is not what the measurement described. For a
                # function that is the common case rather than the exotic one --
                # see `definition_changed` for the measured instance.
                stale.append((e, path, symbol, []))

    print(f"config registry: {len(entries)} entries, {len(dated)} dated, "
          f"{len(undated)} undated ({100 * len(undated) // max(len(entries), 1)}%).")

    if not stale:
        print(f"No dated justification is stale: nothing any of the {len(dated)} "
              f"dated entries rests on has changed since it was measured.")
        return 0

    current = {(e.key, f"{path}::{symbol}" if symbol else path)
               for e, path, symbol, _ in stale}
    # The ledger's rows name entries in the IN-TREE registry, so it can only be
    # applied to the in-tree registry. Under `--registry <copy>` the stale set is
    # different BY CONSTRUCTION -- that is what the copy is for -- and matching
    # the two would report every difference as a ratchet violation. Measured:
    # with the ratchet applied unconditionally, three checks of the pre-existing
    # `test-config-registry-staleness-control.sh` went red, and two of them went
    # red for the ratchet summary REPLACING the per-row listing they grep, not
    # for anything about staleness. So `--registry` reports plainly, which is
    # also what its controls are written against.
    accepted = None if args.registry is not None else _read_accepted()
    if accepted is not None:
        unexplained = sorted(current - set(accepted))
        repaired = sorted(set(accepted) - current)
        print(f"\nstaleness ratchet: {len(current)} stale row(s), "
              f"{len(accepted)} accepted in {ACCEPTED_PATH.name}, "
              f"{len(unexplained)} unexplained, {len(repaired)} repaired.")
        for key, dep in unexplained:
            print(f"  NEW STALE (not in the accepted baseline)\n"
                  f"    {key}\n    rests on {dep}", file=sys.stderr)
        for key, dep in repaired:
            print(f"  NO LONGER STALE — delete its line from "
                  f"{ACCEPTED_PATH.name}\n    {key}\n    rests on {dep}",
                  file=sys.stderr)
        if unexplained or repaired:
            print("\nThe accepted baseline is a ledger of staleness someone "
                  "looked at and wrote a reason for. A row missing from it is a "
                  "NEW measurement gone stale; a row still in it that is no "
                  "longer stale is a line that has stopped meaning anything. "
                  "Both fail.", file=sys.stderr)
            return 1
        print("No UNEXPLAINED staleness. Every stale row below is accepted in "
              f"{ACCEPTED_PATH.name} with a written reason; that file is the "
              "backlog, and it is meant to shrink.")
        if args.verbose:
            _print_stale(stale, args.verbose)
        return 0

    print(f"\nSTALE: {len(stale)} dated justification(s) predate a change to the "
          f"code they protect.\n")
    for e, path, symbol, rows in stale:
        what = f"{path}::{symbol}" if symbol else path
        print(f"  {e.key}")
        print(f"    measured {e.measured_on} ({e.location}), rests on {what}")
        if not rows:
            print(f"    but {what}'s DEFINITION at HEAD is not the one that was "
                  f"measured")
            print(f"      (no commit changed a code line naming it — a function "
                  f"body does not repeat its own name)")
        else:
            print(f"    but {what} changed {len(rows)} time(s) since:")
            for h, d, s in rows[: (None if args.verbose else 3)]:
                print(f"      {h} {d} {s[:96]}")
            if not args.verbose and len(rows) > 3:
                print(f"      ... {len(rows) - 3} more (--verbose)")
        print()
    print("Re-take the measurement, or narrow the entry's `rests_on` if the "
          "change cannot affect it. Do NOT simply move the date.")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
