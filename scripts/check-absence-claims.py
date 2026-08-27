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

# Spelling

There is no single spelling: of 483 `CReal` declarations, most carry an
underscore, many an internal capital, and 117 carry both. The kernel name is
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
1,644 declarations on 2026-08-27 against a live 1,860, and a stale index is
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
MARKER_RE = re.compile(
    r"<!--\s*(?P<kind>was-absent|absent)\s*:\s*(?P<body>.*?)\s*-->",
    re.IGNORECASE,
)
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
    r"\bhas\s+no\s+(?:lemma|theorem|declaration|helper|diagonal|public)",
    r"\bcould\s+not\s+be\s+found\b",
    r"\bcannot\s+be\s+found\b",
    r"\bnothing\s+(?:in-tree|named)\b",
    r"\bgrepped\s+for\b",
]
CLAIM_RE = re.compile("|".join(CLAIM_PHRASES), re.IGNORECASE)

# A `//`, `//!`, `///`, `*` or `/*` line -- Rust prose, not Rust code. A claim
# in a string literal or an identifier is not a claim.
RUST_COMMENT_RE = re.compile(r"^\s*(?://|\*|/\*)")

SCAN_GLOBS = ("docs/**/*.md", "*.md", "crates/**/*.rs")


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
    names: tuple[str, ...]
    annotated: bool


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


def is_prose_line(path: str, line: str) -> bool:
    """Rust: comments only. Markdown: every line."""
    if path.endswith(".rs"):
        return bool(RUST_COMMENT_RE.match(line))
    return True


def scan(root: Path, globs: tuple[str, ...] = SCAN_GLOBS) -> tuple[list[Path], list[Marker], list[ClaimSite], list[MarkerError]]:
    """Walk the prose surface once, collecting markers AND census sites."""
    files: list[Path] = []
    seen: set[Path] = set()
    for pattern in globs:
        for path in sorted(root.glob(pattern)):
            if not path.is_file() or path in seen:
                continue
            seen.add(path)
            files.append(path)

    markers: list[Marker] = []
    sites: list[ClaimSite] = []
    errors: list[MarkerError] = []
    for path in files:
        rel = path.relative_to(root).as_posix()
        try:
            text = path.read_text(errors="replace")
        except OSError:
            continue
        lines = text.splitlines()
        marker_lines: set[int] = set()
        for i, line in enumerate(lines, start=1):
            for match in MARKER_RE.finditer(line):
                try:
                    markers.append(parse_marker(rel, i, match))
                    marker_lines.add(i)
                except MarkerError as exc:
                    errors.append(exc)
        for i, line in enumerate(lines, start=1):
            if not is_prose_line(rel, line):
                continue
            if MARKER_RE.search(line):
                continue
            if not CLAIM_RE.search(line):
                continue
            # A marker within two lines either side annotates this claim; prose
            # wraps, and the marker is conventionally put on its own line above
            # or below the sentence it expires.
            annotated = any(j in marker_lines for j in range(i - 2, i + 3))
            names = tuple(dict.fromkeys(DECL_RE.findall(line)))
            sites.append(ClaimSite(rel, i, line.strip()[:200], names, annotated))
    return files, markers, sites, errors


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
    return data


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

    files, markers, sites, marker_errors = scan(args.root)

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

    named_sites = [s for s in sites if s.names]
    unnamed_sites = [s for s in sites if not s.names]
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
    )
    print(
        f"census: {len(sites)} absence-claim site(s); "
        f"{len(named_sites)} name a declaration "
        f"({len(annotated_named)} carry a marker, {len(bare_named)} do NOT); "
        f"{len(unnamed_sites)} name no declaration and are STRUCTURALLY UNCHECKABLE "
        "by any authority-derived gate"
    )

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
            print(f"  BARE  {site.path}:{site.line}  {' '.join(site.names)}", file=sys.stderr)
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
