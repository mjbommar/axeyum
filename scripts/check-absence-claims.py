#!/usr/bin/env python3
"""Make an absence claim in prose EXPIRE, the way `#[expect(dead_code)]` does.

# The defect

Documentation here records obstacles -- "X does not exist", "grepped for;
absent", "blocked on Y". **Nothing re-checks those claims when the thing
lands.** An absence claim has no expiry, and its authority is exactly what
makes it expensive when it rots. Five went stale in a single day on
2026-08-27 and two cost a full Opus lane each, one of them dispatched by a
document that named itself as the authority.

CLAUDE.md already states the rule this violates -- *"any test named 'every X'
must derive its X from the authority, not from a literal"* -- and applies it
to tests. This is the same rule applied to prose: **a claim about the tree
that does not derive from the tree.**

# The mechanism

`#[expect(dead_code, reason = "...")]` is silent while its condition holds and
**errors the moment it clears**, forcing its own removal. It is colocated with
the thing it describes, so the error names the line you have to edit. This is
that, for prose:

    <!-- absent: CReal.converges_comp_eventually -->
    <!-- absent: CReal.foo, CReal.bar -- optional note after a double dash -->
    <!-- was-absent: CReal.weierstrassMTest -->

An HTML comment renders as nothing in Markdown **and** in rustdoc (a `//!`
doc comment is Markdown), so one grammar covers both surfaces and neither
shows the marker to a reader.

Two directions, both checked, neither able to pass by the run completing:

* **`absent:`** -- a LIVE claim. The gate FAILS when the named declaration is
  PRESENT in the kernel environment. That is the expiry: the moment the
  obstacle clears, the document that records it goes red and names its own
  file and line.
* **`was-absent:`** -- a RESOLVED claim, kept because a diary or a design
  review is a historical record and deleting the obstacle deletes the
  reasoning. The gate FAILS when the named declaration is ABSENT -- a rename
  or a removal must not leave a "this was fixed, see X" note pointing at
  nothing. This is the same both-directions discipline
  `check-shape-duplicates.py` applies to its allowlist.

So correcting a stale claim is a one-word edit (`absent` -> `was-absent`)
that *keeps* the claim under the gate rather than removing it from it.

# Where to put one, and what shape it may take

This is the only place the convention is written down, so it is written in
full. Three rules, and the third is the one that cost a lane (ADR-1250):

1. **Put the marker in the same BLOCK as the claim** -- the same
   blank-line-separated Markdown paragraph or list item, or the same run of
   consecutive Rust comment lines. One blank line between them is one block
   too far and the claim stays bare.
2. **NAME the claim's subject in the marker.** A marker silences only the
   claims whose own sentence (or table row, or list item) names one of the
   declarations the marker names, exactly or up to spelling. A marker for `X`
   is not an answer about `Y` in the paragraph next to it.
3. **A marker MAY be written across several lines.** It is an HTML comment,
   so wrapping it at the column the surrounding prose wraps at is correct, and
   a marker carrying a note usually has to. Names may wrap too, including
   inside a `//!` doc comment -- the comment prefix on a continuation line is
   stripped before the names are read.

Rule 3 held only from 2026-08-31. Before that, the body's `.*?` was matched
one line at a time, so a wrapped marker matched NOTHING -- not merely
unattached, invisible: unchecked against the kernel, silencing nothing, and
absent from the marker count. That is the exact mirror of a checker that
cannot fail. Its practical cost is that the ONLY remaining way to retire a
resolved claim was `--update-budget`, which is the laundering this gate
exists to prevent, so a lane that followed this convention correctly was left
with no honest move at all.

One caveat that follows from rule 3, and it is the reverse hazard: a code
SPAN cannot quote a multi-line marker, because a span is matched within one
line. **Quote a multi-line example in a fenced block**, never in wrapping
backticks -- otherwise the documentation of the grammar is read as a live
marker, which is the defect the code-span rule was added to prevent, arriving
from the other side.

# Spelling

There is no single spelling. Measured 2026-08-27 over the 483 `CReal`
declarations in the live environment: 324 carry an underscore, 243 an internal
capital, and **119 carry both**. The kernel name is
`CReal.congrOfUniformlyContinuous`; every design document says
`congr_of_uniformly_continuous`. A marker matching only one spelling would
produce a **false green** -- the claim reads as still-valid because the gate
looked for a name that was never the kernel's. So an `absent:` marker is
checked against the exact names AND against a spelling-normalized index
(underscores and apostrophes dropped, case folded), and a normalized-only hit
FAILS while naming the kernel spelling.

# Unanswerable is not absent

A marker naming a root the authority does not carry (a typo'd namespace, or a
prelude this projection does not build) is reported as **unanswerable** and
exits 2, not 0. You cannot receive "still absent" about a subject the tool was
never pointed at -- the same structural positive control `shape_search` uses.

The authority is `kernel_declaration_projection` run FRESH, never a committed
snapshot: `artifacts/autogenesis/kernel-dependency-projection-v1.json` carried
1,644 declarations on 2026-08-27 against a live 1,861, and a stale index is
wrong in the direction that matters -- it reports a newly-landed declaration
as still absent, which is precisely the failure this gate exists to catch.
`authority_declaration_floor` in the census file is the guard against being
handed one anyway.

# Adoption is reported, never implied

A partial rollout reported as complete is the same defect one level up. So the
gate also runs a heuristic CENSUS of absence-claim prose across `docs/`, the
root Markdown, and `crates/**/*.rs` comments, and always prints how many sites
carry a marker and how many do not. Sites that NAME a declaration are the only
ones any authority-derived gate can check; that population is budgeted, so a
new unexpirable claim naming a declaration fails the gate. Sites naming no
declaration are counted and printed but **cannot** be budgeted or checked --
stated here rather than left to be discovered.

Usage::

    python3 scripts/check-absence-claims.py
    python3 scripts/check-absence-claims.py --projection-file captured.tsv
    python3 scripts/check-absence-claims.py --update-budget

Exit 0: every marker's claim still holds, and the census is within budget.
Exit 1: a finding -- a stale `absent:`, a stale `was-absent:`, or the bare
census over budget. Exit 2: the gate could not answer -- the tool failed, the
projection is short, a marker is malformed, or a marker names a root the
authority does not cover.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_CENSUS = REPO_ROOT / "scripts" / "absence-claim-census.json"

# `<!-- absent: A, B -- note -->` / `<!-- was-absent: A -->`. The keyword is
# anchored so `was-absent` cannot be read as `absent` (the two mean opposite
# things and one is a substring of the other, which is the `AxNat`/`Nat`
# hazard in miniature).
#
# `re.DOTALL` is load-bearing, not tidiness. An HTML comment is a MULTI-LINE
# construct and a marker carrying a note wraps at the same 79 columns as the
# prose around it, so writing one across three lines is the natural thing to
# do. Without `DOTALL` the body's `.*?` stops at the newline and the marker
# matches NOTHING -- it is not merely unattached, it is invisible to all three
# readers (the file-level marker pass, the block-level name harvest, and the
# body strip). That is the exact mirror of a checker that cannot fail: a
# marker that cannot attach, failing silently, leaving `--update-budget` --
# the laundering this gate exists to prevent -- as the only way to retire a
# resolved claim. Measured 2026-08-31 across 4,695 scanned files: 68 per-line
# matches against 69 real markers, and the one it could not see was a
# correctly-written `was-absent:` on a resolved claim.
MARKER_RE = re.compile(
    r"<!--\s*(?P<kind>was-absent|absent)\s*:\s*(?P<body>.*?)\s*-->",
    re.IGNORECASE | re.DOTALL,
)
# A leading Rust comment prefix. Stripped from each line ONLY when assembling
# the text a marker is parsed out of: a marker wrapped inside a `//!` doc
# comment carries `//!` at the head of every continuation line, which would
# otherwise land inside the names field and read as a malformed marker.
RUST_COMMENT_PREFIX_RE = re.compile(r"^\s*(?://[/!]?|/\*|\*/?)\s?")
# Names are split off the optional note by a ` -- ` separator.
NOTE_SPLIT_RE = re.compile(r"\s+--\s+")
# A kernel declaration name: a namespace root, a dot, then an identifier.
# Anchored at both ends: `Nat.add` must not match inside `AxNat.add`, and
# `CReal.integral` must not match inside `CReal.integral_const`.
DECL_RE = re.compile(r"(?<![A-Za-z0-9_.'])[A-Z][A-Za-z0-9]*\.[A-Za-z_][A-Za-z0-9_']*")

# Phrases that make a sentence an absence claim. Heuristic BY CONSTRUCTION --
# this is the census half, not the checked half.
CLAIM_PHRASES = [
    r"does\s+not\s+exist",
    r"do\s+not\s+exist",
    r"does\s*n[o']t\s+exist",
    r"\bis\s+absent\b",
    r"\bare\s+absent\b",
    r";\s*absent\b",
    r"\bnot\s+yet\s+(?:landed|built|exist|exists|declared|proved|proven|available|written)",
    r"\bno\s+such\s+(?:lemma|theorem|declaration|helper|function|definition)",
    r"\bthere\s+is\s+no\s+(?:lemma|theorem|declaration|helper|public|in-tree|such)",
    r"\bwe\s+do\s*n[o']?t\s+have\b",
    r"\bis\s+missing\b",
    r"\bwas\s+missing\b",
    r"\bblocked\s+on\b",
    r"\bno\s+in-tree\b",
    r"\bno\s+public\s+(?:lemma|theorem|declaration|helper)",
    r"\bnot\s+a\s+public\s+(?:lemma|theorem|declaration|helper)",
    r"\b(?:has|had)\s+no\s+(?:lemma|theorem|declaration|helper|diagonal|public|reindexing|bridge)",
    r"\bcould\s+not\s+be\s+found\b",
    r"\bcannot\s+be\s+found\b",
    r"\bnothing\s+(?:in-tree|named)\b",
    r"\bgrepped\s+for\b",
]
CLAIM_RE = re.compile("|".join(CLAIM_PHRASES), re.IGNORECASE)

# A `//`, `//!`, `///`, `*` or `/*` line -- Rust prose, not Rust code. A claim
# in a string literal or an identifier is not a claim.
RUST_COMMENT_RE = re.compile(r"^\s*(?://|\*|/\*)")

# A fenced code block, in Markdown or in a `//!` doc comment.
FENCE_RE = re.compile(r"^\s*(?://[/!]?\s*)?(?:```|~~~)")
# An inline code span. Documentation ABOUT this marker grammar has to be able
# to quote it, and the natural way to quote anything here is backticks.
CODE_SPAN_RE = re.compile(r"`[^`]*`")

SCAN_GLOBS = ("docs/**/*.md", "*.md", "crates/**/*.rs")

# --- claim-to-declaration association ---------------------------------------
#
# A claim is paired with the names in its OWN unit, not its whole block. The
# block stays the unit a MARKER attaches to (a marker is written near the
# paragraph it corrects, not spliced into the sentence), but the census's
# question -- "which declaration is this claim about?" -- is answered at
# sentence granularity.
#
# Measured 2026-08-31 over the real tree: block-granular association produced
# 250 bare named sites against 118 sentence-granular ones, and its worst single
# site harvested **93** candidates from one Markdown table -- a claim phrase in
# one row, and every `Root.name` in every other row read as its subject. Two
# independent audits (2026-08-27: 55 of 70 rejected; 2026-08-31: every one of
# the remaining 249 rejected) found the surplus was entirely names cited as
# PRESENT evidence in a neighbouring sentence.

# A sentence ends at `.`/`!`/`?` FOLLOWED BY WHITESPACE. Requiring the
# whitespace is what keeps `nat_prelude.rs:1909`, `Ch.22-23` and a bare
# `Root.name` from splitting a sentence in half.
#
# Deliberately NOT `:` or `;`. Both carry a claim's own subjects across:
#   "(do not exist in the merged tree): `CReal.alternatingBracketUpper`, ..."
#   "neither of which has a ready-made `Nat.gcd_comm` ... (this development
#    has no such lemma; only `gcd_zero_left`, ...)"
# -- the first names its subjects after the colon, the second before the
# semicolon, and both are among the 8 stale claims this gate has caught.
SENTENCE_SPLIT_RE = re.compile(r"(?<=[.!?])\s")

# A line that OPENS a new structural record: a Markdown table row, or a list
# item at any indent, optionally behind a Rust line-comment prefix. A wrapped
# item's continuation lines carry no marker, so they stay with the item they
# continue. `*` is a list bullet in Markdown but a block-comment continuation
# in Rust, so it is a record opener only in Markdown.
RECORD_MD_RE = re.compile(r"^\s*(?:\||[-*+]\s|\d+[.)]\s)")
RECORD_RS_RE = re.compile(r"^\s*(?://[/!]?)?\s*(?:\||[-+]\s|\d+[.)]\s)")


def claim_units(path: str, body: str) -> list[tuple[int, str]]:
    """Split a block body into `(line offset, text)` claim units.

    Records first (a table row or list item is its own assertion), then
    sentences within each record.
    """
    record_re = RECORD_RS_RE if path.endswith(".rs") else RECORD_MD_RE
    units: list[tuple[int, str]] = []
    chunk: list[str] = []
    chunk_start = 0
    for i, line in enumerate(body.splitlines()):
        if chunk and record_re.match(line):
            units.extend(_sentences(chunk_start, chunk))
            chunk = []
        if not chunk:
            chunk_start = i
        chunk.append(line)
    if chunk:
        units.extend(_sentences(chunk_start, chunk))
    return units


def _sentences(start: int, chunk: list[str]) -> list[tuple[int, str]]:
    text = "\n".join(chunk)
    out: list[tuple[int, str]] = []
    pos = 0
    for piece in SENTENCE_SPLIT_RE.split(text):
        out.append((start + text.count("\n", 0, pos), piece))
        pos += len(piece) + 1
    return out


class CensusFormatError(ValueError):
    """`scripts/absence-claim-census.json` is malformed."""


class MarkerError(ValueError):
    """A marker in a scanned file cannot be interpreted."""


class ProjectionError(ValueError):
    """The authority could not be read, or is too short to be trusted."""


@dataclass(frozen=True)
class Marker:
    path: str
    line: int
    kind: str  # "absent" | "was-absent"
    names: tuple[str, ...]
    note: str


@dataclass(frozen=True)
class ClaimSite:
    path: str
    line: int
    text: str
    candidates: tuple[str, ...]
    annotated: bool

    def names(self, authority: "Authority") -> tuple[str, ...]:
        """The candidates whose namespace root the authority actually carries.

        Derived from the authority rather than from a literal list of roots:
        a hand-written root list is the defect this whole gate is about, one
        level down, and it would silently classify `CLAUDE.md` and `PLAN.md`
        (both of which match `Root.identifier`) as declaration names.
        """
        return tuple(n for n in self.candidates if n.split(".", 1)[0] in authority.roots)


@dataclass(frozen=True)
class Authority:
    """The set of declaration names the kernel actually carries."""

    exact: frozenset[str]
    normalized: dict[str, str]  # normalized spelling -> one kernel spelling
    roots: frozenset[str]

    def resolve(self, name: str) -> tuple[bool, str | None]:
        """`(present, kernel_spelling)`. Exact first, then spelling-normalized."""
        if name in self.exact:
            return (True, name)
        hit = self.normalized.get(normalize_spelling(name))
        if hit is not None:
            return (True, hit)
        return (False, None)


def normalize_spelling(name: str) -> str:
    """Fold the two conventions onto one key.

    `CReal.congr_of_uniformly_continuous` and
    `CReal.congrOfUniformlyContinuous` are the same declaration written by two
    layers of this repository. Dropping `_` and `'` and case-folding makes them
    one key. The namespace root is folded too, which is safe because roots are
    compared separately for the unanswerable check.
    """
    return name.replace("_", "").replace("'", "").lower()


def parse_projection(text: str, floor: int) -> Authority:
    """Parse `kernel_declaration_projection` (unfiltered) TSV.

    Rows are `<prelude>\\t<kind>\\t<name>\\t<footprint>\\t...`; one declaration
    appears once per prelude that can see it, so names repeat.
    """
    exact: set[str] = set()
    for raw in text.splitlines():
        if not raw.strip():
            continue
        fields = raw.split("\t")
        if len(fields) < 4:
            raise ProjectionError(
                f"malformed projection row (expected >= 4 tab-separated fields, "
                f"got {len(fields)}): {raw[:160]!r}"
            )
        exact.add(fields[2])
    if len(exact) < floor:
        raise ProjectionError(
            f"the authority carries {len(exact)} distinct declarations but the "
            f"recorded floor is {floor} -- this projection is STALE or truncated. "
            "A short index reports a newly-landed declaration as still absent, "
            "which is the exact failure this gate exists to catch. Rebuild it, "
            "or lower `authority_declaration_floor` deliberately if declarations "
            "were genuinely removed."
        )
    normalized: dict[str, str] = {}
    for name in sorted(exact):
        normalized.setdefault(normalize_spelling(name), name)
    roots = frozenset(n.split(".", 1)[0] for n in exact if "." in n)
    return Authority(frozenset(exact), normalized, roots)


def run_projection(cargo_bin: str = "cargo") -> str:
    """Run the real tool. `--release` is MANDATORY (debug SIGABRTs)."""
    cmd = [
        cargo_bin,
        "run",
        "--release",
        "-q",
        "-p",
        "axeyum-lean-kernel",
        "--example",
        "kernel_declaration_projection",
    ]
    proc = subprocess.run(
        cmd, cwd=REPO_ROOT, capture_output=True, text=True, timeout=3600, check=False
    )
    if proc.returncode != 0:
        raise ProjectionError(
            f"`{' '.join(cmd)}` exited {proc.returncode} -- the tool itself failed, "
            "this is not a finding about any claim:\n"
            f"STDOUT (tail):\n{proc.stdout[-2000:]}\nSTDERR (tail):\n{proc.stderr[-2000:]}"
        )
    return proc.stdout


def parse_marker(path: str, lineno: int, match: re.Match[str]) -> Marker:
    kind = match.group("kind").lower()
    body = match.group("body")
    parts = NOTE_SPLIT_RE.split(body, maxsplit=1)
    names_field = parts[0]
    note = parts[1].strip() if len(parts) > 1 else ""
    names = tuple(n.strip() for n in names_field.split(",") if n.strip())
    if not names:
        raise MarkerError(
            f"{path}:{lineno}: `{kind}:` marker names no declaration. A marker "
            "that names nothing cannot expire; write the declaration name, or "
            "delete the marker and accept that the claim is unchecked."
        )
    for name in names:
        if not DECL_RE.fullmatch(name):
            raise MarkerError(
                f"{path}:{lineno}: {name!r} is not a kernel declaration name "
                "(expected `Root.identifier`, e.g. `CReal.weierstrassMTest`)."
            )
    return Marker(path, lineno, kind, names, note)


def marker_scan_line(path: str, line: str) -> str:
    """One source line, prepared for MARKER parsing.

    Two transformations, both of which must be identical everywhere a marker
    is read or a marker attaches in one place and is checked in another:

    * code spans are blanked, so a marker QUOTED in backticks is documentation
      of the grammar and neither checked nor able to silence a claim;
    * in Rust, a leading `//` / `//!` / `*` prefix is dropped, so a marker
      wrapped inside a doc comment does not carry comment syntax into its
      names field.

    Length is not preserved -- only the LINE, which is all the callers need
    since they locate a match by counting newlines.
    """
    masked = CODE_SPAN_RE.sub(" ", line)
    if path.endswith(".rs"):
        masked = RUST_COMMENT_PREFIX_RE.sub("", masked)
    return masked


def blank_marker(match: re.Match[str]) -> str:
    """Replace a marker with a space, KEEPING its newlines.

    The census locates a claim by index into the marker-stripped body, so
    collapsing a three-line marker to one space would shift every following
    line number in that block by two and print the wrong source text.
    """
    return " " + "\n" * match.group(0).count("\n")


def is_prose_line(path: str, line: str) -> bool:
    """Rust: comments only. Markdown: every line."""
    if path.endswith(".rs"):
        return bool(RUST_COMMENT_RE.match(line))
    return True


def blocks(path: str, lines: list[str]) -> list[tuple[int, list[str]]]:
    """Split a file into prose BLOCKS: `(first line number, lines)`.

    A block is the unit a marker attaches to, and it is the natural one rather
    than an arbitrary line window: in Markdown, a blank-line-separated
    paragraph or list item; in Rust, a run of consecutive comment lines. The
    earlier line-window rule scored a marker written one blank line below its
    own paragraph as attached to nothing, and split one wrapped sentence into
    four overlapping "sites" whose name sets were near-duplicates -- so the
    coverage number it printed was neither stable nor meaningful.
    """
    out: list[tuple[int, list[str]]] = []
    current: list[str] = []
    start = 0
    for i, line in enumerate(lines, start=1):
        prose = is_prose_line(path, line)
        breaks = (not prose) if path.endswith(".rs") else (not line.strip())
        if breaks:
            if current:
                out.append((start, current))
                current = []
            continue
        if not current:
            start = i
        current.append(line)
    if current:
        out.append((start, current))
    return out


def scan(
    root: Path,
    globs: tuple[str, ...] = SCAN_GLOBS,
    excluded: frozenset[str] = frozenset(),
) -> tuple[list[Path], list[Marker], list[ClaimSite], list[MarkerError], int]:
    """Walk the prose surface once, collecting markers AND census sites."""
    files: list[Path] = []
    seen: set[Path] = set()
    for pattern in globs:
        for path in sorted(root.glob(pattern)):
            if not path.is_file() or path in seen:
                continue
            if path.relative_to(root).as_posix() in excluded:
                continue
            seen.add(path)
            files.append(path)

    markers: list[Marker] = []
    sites: list[ClaimSite] = []
    errors: list[MarkerError] = []
    quoted = 0
    for path in files:
        rel = path.relative_to(root).as_posix()
        try:
            text = path.read_text(errors="replace")
        except OSError:
            continue
        lines = text.splitlines()
        # A marker may span lines, so it cannot be read one line at a time.
        # `scan_text` keeps one entry PER SOURCE LINE -- blanked wherever a
        # marker cannot legitimately live -- so `"\n".join(...)` preserves the
        # line numbering exactly while letting the DOTALL regex run across it.
        scan_text: list[str] = []
        fence_runs: list[list[str]] = []
        fence_run: list[str] = []
        in_fence = False
        for line in lines:
            if FENCE_RE.match(line):
                in_fence = not in_fence
                if not in_fence and fence_run:
                    fence_runs.append(fence_run)
                    fence_run = []
                scan_text.append("")
                continue
            if not is_prose_line(rel, line):
                scan_text.append("")
                continue
            # A marker QUOTED in a code span or a code fence is documentation
            # of the grammar, not a claim. Without this, the ADR that defines
            # the marker fails the gate it defines: measured on this gate's
            # first real run, `<!-- was-absent: ... -->` written as an example
            # in ADR-0611 and copied into the generated ADR index was parsed as
            # two live markers naming a declaration called `...`. Counted and
            # reported, never silently dropped -- a swallowed marker is a false
            # green, which is the one outcome this gate must not produce.
            if in_fence:
                fence_run.append(line)
                scan_text.append("")
                continue
            quoted += len(MARKER_RE.findall("".join(CODE_SPAN_RE.findall(line))))
            scan_text.append(marker_scan_line(rel, line))
        if fence_run:
            fence_runs.append(fence_run)
        for run in fence_runs:
            quoted += len(MARKER_RE.findall("\n".join(run)))
        joined = "\n".join(scan_text)
        for match in MARKER_RE.finditer(joined):
            lineno = joined.count("\n", 0, match.start()) + 1
            try:
                markers.append(parse_marker(rel, lineno, match))
            except MarkerError as exc:
                errors.append(exc)
        for start, block in blocks(rel, lines):
            # A marker attaches to its BLOCK, but it only silences the claims
            # it actually NAMES. With one site per block that distinction was
            # unreachable; at sentence granularity a block routinely carries
            # several independent claims, and a marker for one of them must
            # not read as an answer to the others. Measured 2026-08-31: four
            # sites were covered by a marker naming something else.
            #
            # Read from the same per-line-blanked assembly the marker pass
            # uses, so a marker that wraps across lines silences its claim
            # exactly as a single-line one does. Reading raw block lines here
            # instead would reintroduce the defect one level down: the marker
            # would be CHECKED against the kernel and still fail to attach.
            marker_names: set[str] = set()
            marker_scan = "\n".join(marker_scan_line(rel, line) for line in block)
            for match in MARKER_RE.finditer(marker_scan):
                try:
                    parsed = parse_marker(rel, 0, match)
                except MarkerError:
                    continue  # reported by the marker pass above
                marker_names |= set(parsed.names)
            # The marker's own text is stripped before the claim phrases are
            # matched, so a marker's note can quote a claim without the block
            # counting itself as a fresh claim. `blank_marker` keeps the
            # marker's newlines so every later `body_lines[offset]` and
            # `start + offset` still names the source line it came from.
            body = MARKER_RE.sub(blank_marker, "\n".join(block))
            body_lines = body.splitlines()
            for offset, unit in claim_units(rel, body):
                if CLAIM_RE.search(unit) is None:
                    continue
                candidates = tuple(dict.fromkeys(DECL_RE.findall(unit)))
                # Exact first, then spelling-normalized -- the same two-step
                # `Authority.resolve` uses, and for the same reason: a marker
                # written `CReal.congr_of_uniformly_continuous` must cover
                # prose written `CReal.congrOfUniformlyContinuous`.
                exact_hit = bool(set(candidates) & marker_names)
                normalized_hit = bool(
                    {normalize_spelling(n) for n in candidates}
                    & {normalize_spelling(n) for n in marker_names}
                )
                annotated = exact_hit or normalized_hit
                sites.append(
                    ClaimSite(
                        rel,
                        start + offset,
                        body_lines[offset].strip()[:200],
                        candidates,
                        annotated,
                    )
                )
    return files, markers, sites, errors, quoted


def load_census(path: Path) -> dict:
    try:
        raw = path.read_text()
    except OSError as exc:
        raise CensusFormatError(f"cannot read {path}: {exc}") from exc
    try:
        data = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise CensusFormatError(f"{path} is not valid JSON: {exc}") from exc
    if not isinstance(data, dict):
        raise CensusFormatError(f"{path}: top level must be a JSON object")
    for key in ("authority_declaration_floor", "bare_named_claim_budget"):
        value = data.get(key)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise CensusFormatError(f"{path}: {key!r} must be a non-negative integer, got {value!r}")
    excluded = data.get("excluded_paths")
    if not isinstance(excluded, list):
        raise CensusFormatError(f"{path}: 'excluded_paths' must be a JSON list, got {type(excluded).__name__}")
    seen: set[str] = set()
    for i, entry in enumerate(excluded):
        if not isinstance(entry, dict):
            raise CensusFormatError(f"{path}: excluded_paths[{i}] is not an object")
        rel = entry.get("path")
        if not isinstance(rel, str) or not rel.strip():
            raise CensusFormatError(f"{path}: excluded_paths[{i}] has no 'path'")
        if rel in seen:
            raise CensusFormatError(f"{path}: excluded_paths lists {rel!r} more than once")
        seen.add(rel)
        reason = entry.get("reason")
        if not isinstance(reason, str) or not reason.strip():
            raise CensusFormatError(
                f"{path}: excluded_paths[{i}] ({rel!r}) has no non-empty 'reason' -- "
                "an exclusion without a reason is how a gate becomes decoration"
            )
    return data


def check_exclusions(census: dict, root: Path) -> list[str]:
    """An exclusion for a path that no longer exists is STALE.

    Same both-directions discipline as `check-shape-duplicates.py`: a list of
    "this one is fine, because X" is only trustworthy if the entries are
    checked against reality, or it silently accumulates carve-outs for files
    that were renamed or deleted -- and a stale exemption reads as
    still-considered when it is not.
    """
    return [
        entry["path"]
        for entry in census["excluded_paths"]
        if not (root / entry["path"]).exists()
    ]


def evaluate_markers(
    markers: list[Marker], authority: Authority
) -> tuple[list[tuple[Marker, str, str]], list[tuple[Marker, str]], list[tuple[Marker, str]]]:
    """Return `(expired, stale_resolutions, unanswerable)`.

    `expired`: an `absent:` marker whose declaration is PRESENT -- the claim
    has rotted. Carries the kernel spelling actually found, which differs from
    the marker's when the hit was spelling-normalized.

    `stale_resolutions`: a `was-absent:` marker whose declaration is ABSENT --
    a "this was fixed, see X" note pointing at nothing (a rename or removal).

    `unanswerable`: a marker naming a root the authority does not carry. Not a
    finding about the claim; a finding about the question.
    """
    expired: list[tuple[Marker, str, str]] = []
    stale: list[tuple[Marker, str]] = []
    unanswerable: list[tuple[Marker, str]] = []
    for marker in markers:
        for name in marker.names:
            root = name.split(".", 1)[0]
            if root not in authority.roots:
                unanswerable.append((marker, name))
                continue
            present, kernel_name = authority.resolve(name)
            if marker.kind == "absent" and present:
                assert kernel_name is not None
                expired.append((marker, name, kernel_name))
            elif marker.kind == "was-absent" and not present:
                stale.append((marker, name))
    return expired, stale, unanswerable


def main(argv: list[str] | None = None) -> int:  # noqa: PLR0911, PLR0912, PLR0915
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--census", type=Path, default=DEFAULT_CENSUS)
    parser.add_argument(
        "--projection-file",
        type=Path,
        default=None,
        help="read kernel_declaration_projection stdout from this file instead "
        "of invoking cargo (for testing against a captured or synthetic fixture)",
    )
    parser.add_argument("--cargo-bin", default="cargo")
    parser.add_argument("--root", type=Path, default=REPO_ROOT)
    parser.add_argument(
        "--list",
        action="store_true",
        help="also print every marker and every claim site, annotated or not "
        "(the adoption worklist)",
    )
    parser.add_argument(
        "--update-budget",
        action="store_true",
        help="rewrite `bare_named_claim_budget` to the counted value and exit "
        "non-zero if it moved (the `recount-pinned-inventory.py` shape)",
    )
    args = parser.parse_args(argv)

    try:
        census = load_census(args.census)
    except CensusFormatError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2

    stale_exclusions = check_exclusions(census, args.root)
    if stale_exclusions:
        print(
            f"FAIL: {len(stale_exclusions)} excluded path(s) no longer exist -- "
            "a stale carve-out reads as still-considered when it is not:",
            file=sys.stderr,
        )
        for rel in stale_exclusions:
            print(f"  STALE-EXCLUSION  {rel}", file=sys.stderr)
        return 2

    excluded = frozenset(entry["path"] for entry in census["excluded_paths"])
    files, markers, sites, marker_errors, quoted_markers = scan(args.root, excluded=excluded)

    # Vacuity: a gate that scans nothing exits 0 on completion alone.
    if not files:
        print(
            f"FAIL: scanned 0 files under {args.root} -- the gate examined nothing. "
            "A zero-file run cannot be a pass.",
            file=sys.stderr,
        )
        return 2
    if not sites:
        print(
            f"FAIL: the absence-claim detector matched 0 lines across {len(files)} "
            "files. This repository demonstrably contains such claims, so a zero "
            "means the detector broke, not that the prose is clean.",
            file=sys.stderr,
        )
        return 2

    if marker_errors:
        print(f"FAIL: {len(marker_errors)} malformed marker(s):", file=sys.stderr)
        for exc in marker_errors:
            print(f"  {exc}", file=sys.stderr)
        return 2

    if not markers:
        print(
            "FAIL: 0 absence markers found. Every claim would then be checked "
            "against nothing and this gate would pass by completing. Seed at "
            "least one `<!-- absent: Root.name -->` or `<!-- was-absent: "
            "Root.name -->` marker.",
            file=sys.stderr,
        )
        return 1

    floor = census["authority_declaration_floor"]
    if args.projection_file is not None:
        try:
            projection_text = args.projection_file.read_text()
        except OSError as exc:
            print(f"FAIL: cannot read {args.projection_file}: {exc}", file=sys.stderr)
            return 2
    else:
        try:
            projection_text = run_projection(args.cargo_bin)
        except ProjectionError as exc:
            print(f"FAIL: {exc}", file=sys.stderr)
            return 2

    try:
        authority = parse_projection(projection_text, floor)
    except ProjectionError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2

    expired, stale, unanswerable = evaluate_markers(markers, authority)

    named_sites = [s for s in sites if s.names(authority)]
    unnamed_sites = [s for s in sites if not s.names(authority)]
    bare_named = [s for s in named_sites if not s.annotated]
    annotated_named = [s for s in named_sites if s.annotated]

    if args.update_budget:
        recorded = census["bare_named_claim_budget"]
        counted = len(bare_named)
        census["bare_named_claim_budget"] = counted
        args.census.write_text(json.dumps(census, indent=2, sort_keys=True) + "\n")
        if recorded != counted:
            print(
                f"budget updated: bare_named_claim_budget {recorded} -> {counted}",
                file=sys.stderr,
            )
            return 1
        print(f"budget unchanged: bare_named_claim_budget = {counted}")
        return 0

    # --- coverage, printed unconditionally (a partial rollout is never implied)
    print(
        f"authority: {len(authority.exact)} distinct kernel declarations "
        f"(floor {floor}), roots covered: {' '.join(sorted(authority.roots))}"
    )
    print(f"scanned: {len(files)} files under {args.root}")
    print(
        f"markers: {len(markers)} "
        f"({sum(1 for m in markers if m.kind == 'absent')} absent, "
        f"{sum(1 for m in markers if m.kind == 'was-absent')} was-absent), "
        f"naming {sum(len(m.names) for m in markers)} declaration(s)"
        + (
            f"; {quoted_markers} more QUOTED in a code span or fence and read as "
            "documentation of the grammar, not as claims"
            if quoted_markers
            else ""
        )
    )
    print(
        f"census: {len(sites)} absence-claim site(s); "
        f"{len(named_sites)} name a declaration "
        f"({len(annotated_named)} carry a marker, {len(bare_named)} do NOT); "
        f"{len(unnamed_sites)} name no declaration and are STRUCTURALLY UNCHECKABLE "
        "by any authority-derived gate"
    )
    if args.list:
        for marker in markers:
            print(f"  MARKER  {marker.kind:11s} {marker.path}:{marker.line}  {', '.join(marker.names)}")
        for site in sites:
            flag = "ANNOTATED" if site.annotated else ("BARE     " if site.names(authority) else "UNNAMED  ")
            print(f"  {flag}  {site.path}:{site.line}  {site.text[:110]}")
    sys.stdout.flush()

    ok = True

    if unanswerable:
        print(
            f"FAIL: {len(unanswerable)} marker name(s) in a root the authority "
            "does not carry -- UNANSWERABLE, not absent:",
            file=sys.stderr,
        )
        for marker, name in unanswerable:
            print(f"  UNANSWERABLE  {marker.path}:{marker.line}  {name}", file=sys.stderr)
        print(
            f"  Covered roots: {' '.join(sorted(authority.roots))}. Fix the "
            "namespace, or the projection does not build the prelude you mean.",
            file=sys.stderr,
        )
        return 2

    if expired:
        ok = False
        print(
            f"FAIL: {len(expired)} absence claim(s) have EXPIRED -- the "
            "declaration is present in the kernel:",
            file=sys.stderr,
        )
        for marker, claimed, kernel_name in expired:
            spelling = "" if claimed == kernel_name else f"  (kernel spelling: {kernel_name})"
            note = f"  note: {marker.note}" if marker.note else ""
            print(f"  EXPIRED  {marker.path}:{marker.line}  {claimed}{spelling}{note}", file=sys.stderr)
        print(
            "  The prose at that line claims this does not exist. It does. Correct\n"
            "  the sentence, then change `absent:` to `was-absent:` so the record\n"
            "  stays under the gate instead of leaving it.",
            file=sys.stderr,
        )

    if stale:
        ok = False
        print(
            f"FAIL: {len(stale)} resolved-claim record(s) point at a declaration "
            "that is NOT present:",
            file=sys.stderr,
        )
        for marker, name in stale:
            print(f"  DANGLING  {marker.path}:{marker.line}  {name}", file=sys.stderr)
        print(
            "  A `was-absent:` marker records that an obstacle cleared. If the\n"
            "  declaration is gone, it was renamed or removed and the prose now\n"
            "  points at nothing -- update the name, or reopen the claim.",
            file=sys.stderr,
        )

    budget = census["bare_named_claim_budget"]
    if len(bare_named) > budget:
        ok = False
        print(
            f"FAIL: {len(bare_named)} unexpirable absence claim(s) naming a "
            f"declaration, over the budget of {budget}:",
            file=sys.stderr,
        )
        for site in bare_named[: budget + 20][-20:]:
            print(f"  BARE  {site.path}:{site.line}  {' '.join(site.names(authority))}", file=sys.stderr)
        print(
            "  Annotate the new one with `<!-- absent: Root.name -->` so it can\n"
            f"  expire, or run --update-budget to record a deliberate increase.",
            file=sys.stderr,
        )

    if ok:
        print(
            f"OK: {len(markers)} marker(s) checked against the kernel; every "
            "claim still holds. "
            f"Marker coverage of checkable claim sites: "
            f"{len(annotated_named)}/{len(named_sites)}."
        )
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
