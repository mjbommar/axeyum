#!/usr/bin/env python3
"""Fail when a documented limit's justification names a basis that is gone.

`scripts/check-config-registry-staleness.py` asks whether the code an entry
`rests_on` **changed** after its measurement date. That question needs history,
a date, and a symbol somebody wrote down as a dependency. It cannot see the
failure that motivated this script:

    crates/axeyum-solver/src/dpll_lia.rs::MAX_PRE_SAT_ARITH_ATOMS was justified,
    in prose, by "BatSat allocate[d] past an 8 GiB process ceiling ... before
    its cooperative deadline poll" (d599b682f, 2026-08-08). ADR-1703
    (317be80fe, 2026-09-05) took BatSat off every shipping path: IncrementalSat
    -- the exact object BoolSkeletonSolver holds -- is now NativeIncrementalCdcl,
    and BatSat survives only behind the non-default `batsat-reference` feature
    as a measurement oracle.

Not one line of `dpll_lia.rs` changed, so no `rests_on` dependency could fire.
The justification simply stopped describing anything, and nothing noticed for
28 days. Two further instances of the same shape were found the same month, each
by accident: `lra_theory::MAX_ONLINE_LRA_ATOMS` (fixed by ADR-1752) and the
`euf` Ackermann-pairs threshold.

So this asks the other question: **does the thing this reasoning NAMES still
exist?** — about the tree as it is now, needing no history and no date.

    exit 0  every declared basis resolves
    exit 1  at least one basis is gone            <- the finding
    exit 2  the registry could not be read, or a self-check failed

Modes:

    (default)   check every declared basis
    --list      print the basis surface and exit 0
    --audit     DISCOVERY, not a gate: scan every registered constant's
                definition-site doc comment for identifiers that occur nowhere
                in `crates/`, i.e. a basis named in prose that was never
                declared and is already dangling. Exits 1 on a hit.

WHAT THIS CANNOT SEE: a basis nobody wrote down. `--audit` is the partial
answer to that and it is partial on purpose -- it can only see names, not
claims. An entry whose justification rests on an unstated assumption is invisible
to both halves of this contract, which is why `Basis` is a REQUIRED argument of
`dated(...)` rather than an optional field.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

# The repository this check reads. Mutable because the control suite runs a
# SCRATCH COPY of this script (step 6 deletes one guard at a time), and a repo
# root derived from `__file__` would then point at the scratch directory --
# where every path lookup fails and every commit lookup misses, so a defanged
# checker reports NINE findings instead of the one its mutation removed. That
# is not a weaker control, it is a control that measures the wrong thing while
# looking busy. `--repo` makes the subject explicit.
REPO = Path(__file__).resolve().parent.parent
REGISTRY_RS = REPO / "crates" / "axeyum-solver" / "src" / "config_registry.rs"
ADR_DIR = REPO / "docs" / "research" / "09-decisions"


def _set_repo(root: Path) -> None:
    """Point the check at `root` instead of this script's own directory."""
    global REPO, ADR_DIR
    REPO = root.resolve()
    ADR_DIR = REPO / "docs" / "research" / "09-decisions"

# An ADR in any of these states no longer justifies anything.
DEAD_ADR_STATES = ("superseded", "rejected", "withdrawn", "retired", "abandoned")

ENTRY_OPEN = re.compile(r"^    ConfigEntry \{$")
NAME_RE = re.compile(r'^        name: "([^"]*)",$', re.MULTILINE)
MODULE_RE = re.compile(r'^        module: "([^"]*)",$', re.MULTILINE)

# The four `Basis` constructors. Written with `\s*` between arguments because
# rustfmt breaks a two-argument call across lines and adds a trailing comma --
# the exact shape that made the sibling staleness checker parse every dated
# entry with an EMPTY dependency list and report a clean bill of health for all
# 24 of them. The self-check below is what would catch a repeat.
ADR_RE = re.compile(r'\badr\(\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)')
DOC_RE = re.compile(r'\bdoc\(\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)')
LIVE_RE = re.compile(
    r'\blive\(\s*"((?:[^"\\]|\\.)*)"\s*,\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)'
)
COMMIT_RE = re.compile(
    r'\bcommit\(\s*"((?:[^"\\]|\\.)*)"\s*,\s*"((?:[^"\\]|\\.)*)"\s*,?\s*\)'
)


@dataclass
class Entry:
    name: str = ""
    module: str = ""
    bases: list[tuple[str, str, str]] = field(default_factory=list)

    @property
    def key(self) -> str:
        return f"{self.module}::{self.name}"


def parse_registry(path: Path) -> tuple[list[Entry], int]:
    """Return the entries and the raw count of `ConfigEntry {` literals.

    Structural rather than clever, deliberately: a `ConfigEntry {` line opens an
    entry and the matching `    },` closes it. The caller cross-checks the entry
    count against the literal count, so a parse that silently dropped an entry
    is a self-check failure and not a quietly shorter report.
    """
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    entries: list[Entry] = []
    i = 0
    while i < len(lines):
        if not ENTRY_OPEN.match(lines[i]):
            i += 1
            continue
        i += 1
        buf: list[str] = []
        while i < len(lines) and lines[i].rstrip() != "    },":
            buf.append(lines[i])
            i += 1
        blob = "\n".join(buf)
        e = Entry()
        m = NAME_RE.search(blob)
        if m:
            e.name = m.group(1)
        m = MODULE_RE.search(blob)
        if m:
            e.module = m.group(1)
        for adr_id in ADR_RE.findall(blob):
            e.bases.append(("AdrLive", adr_id, ""))
        for p in DOC_RE.findall(blob):
            e.bases.append(("DocPath", p, ""))
        for ident, in_path in LIVE_RE.findall(blob):
            e.bases.append(("LiveSymbol", ident, in_path))
        for sha, subject in COMMIT_RE.findall(blob):
            e.bases.append(("CommitSubject", sha, subject))
        if e.name and e.module:
            entries.append(e)
        i += 1
    needle = "    ConfigEntry" + " {"
    return entries, text.count(needle)


def count_basis_literals(path: Path) -> int:
    """How many basis constructor calls the file's own text holds.

    Counted independently of the entry parse so the two can disagree. Only calls
    with a string literal count; the `const fn adr(id: &'static str)` definitions
    do not match, because they have no quoted first argument.
    """
    text = path.read_text(encoding="utf-8")
    return (
        len(ADR_RE.findall(text))
        + len(DOC_RE.findall(text))
        + len(LIVE_RE.findall(text))
        + len(COMMIT_RE.findall(text))
    )


def adr_path(adr_id: str) -> Path | None:
    m = re.fullmatch(r"ADR-(\d+)", adr_id)
    if not m:
        return None
    hits = sorted(ADR_DIR.glob(f"adr-{m.group(1)}-*.md"))
    return hits[0] if hits else None


def check_basis(kind: str, a: str, b: str) -> str | None:
    """`None` when the basis resolves; otherwise why it does not."""
    if kind == "AdrLive":
        p = adr_path(a)
        if p is None:
            return f"{a}: no such ADR file under docs/research/09-decisions/"
        m = re.search(r"^Status:\s*(.+)$", p.read_text(encoding="utf-8"), re.MULTILINE)
        if not m:
            return f"{a}: {p.name} has no `Status:` line"
        status = m.group(1).strip().lower()
        for dead in DEAD_ADR_STATES:
            if dead in status:
                return f"{a} is {m.group(1).strip()} — the decision behind this bound was overturned"
        return None

    if kind == "DocPath":
        return None if (REPO / a).exists() else f"{a}: no such path"

    if kind == "LiveSymbol":
        target = REPO / b
        if not target.exists():
            return f"{b}: no such path (basis symbol {a})"
        cmd = ["grep", "-rlF", "--", a, str(target)]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode == 0 and out.stdout.strip():
            return None
        if out.returncode > 1:
            return f"grep failed on {b}: {out.stderr.strip()}"
        return f"{a} no longer occurs in {b} — the justification names a mechanism that is gone"

    if kind == "CommitSubject":
        out = subprocess.run(
            ["git", "-C", str(REPO), "log", "-1", "--format=%s", a],
            capture_output=True,
            text=True,
            check=False,
        )
        if out.returncode != 0:
            return f"{a}: no such commit"
        subject = out.stdout.strip()
        if b not in subject:
            return f"{a}: subject is now {subject!r}, which no longer contains {b!r}"
        return None

    return f"unknown basis kind {kind}"


# ---------------------------------------------------------------------------
# --audit: names in prose that resolve to nothing


IDENT = re.compile(r"\b(?:[A-Z][a-z0-9]+){2,}\b|\b[A-Z][A-Z0-9_]{4,}\b")
CONST_SITE = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+{name}\s*:",
)


def definition_doc(module: str, name: str) -> str:
    p = REPO / module
    if not p.exists():
        return ""
    lines = p.read_text(encoding="utf-8").splitlines()
    pat = re.compile(rf"^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+{re.escape(name)}\s*:")
    for i, ln in enumerate(lines):
        if pat.match(ln):
            j, doc = i - 1, []
            while j >= 0 and lines[j].lstrip().startswith("//"):
                doc.append(lines[j].lstrip().lstrip("/").strip())
                j -= 1
            return "\n".join(reversed(doc))
    return ""


def audit(entries: list[Entry]) -> int:
    cache: dict[str, bool] = {}

    def anywhere(ident: str) -> bool:
        if ident not in cache:
            out = subprocess.run(
                ["grep", "-rlF", "--include=*.rs", "--", ident, "crates/"],
                cwd=REPO,
                capture_output=True,
                text=True,
                check=False,
            )
            cache[ident] = bool(out.stdout.strip())
        return cache[ident]

    scanned = 0
    hits: list[tuple[str, list[str]]] = []
    for e in entries:
        doc = definition_doc(e.module, e.name)
        if not doc:
            continue
        scanned += 1
        gone = sorted({i for i in IDENT.findall(doc) if not anywhere(i)})
        if gone:
            hits.append((e.key, gone))

    print(
        f"audit: read the definition-site doc comment of {scanned} of "
        f"{len(entries)} registered constants."
    )
    if scanned == 0:
        print(
            "FAIL (self-check): no doc comment was read, so this audit examined "
            "nothing. An empty result from a tool that never reached its subject "
            "is indistinguishable from a clean one.",
            file=sys.stderr,
        )
        return 2
    if not hits:
        print("Every identifier named in those doc comments still occurs in crates/.")
        return 0
    print(f"\nDANGLING: {len(hits)} entr(ies) name an identifier that occurs nowhere.\n")
    for key, gone in hits:
        print(f"  {key}")
        for g in gone:
            print(f"    {g}")
    print(
        "\nEither the name is stale (the justification points at something that "
        "is gone) or it is prose a reader would mistake for a symbol. Declare it "
        "as a `Basis`, or reword it."
    )
    return 1


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--list", action="store_true", help="print the basis surface, exit 0")
    ap.add_argument(
        "--audit",
        action="store_true",
        help="discovery mode: doc-comment identifiers that resolve to nothing",
    )
    ap.add_argument(
        "--repo",
        type=Path,
        default=None,
        help="repository root to resolve paths, ADRs and commits against "
        "(default: this script's own parent directory). Required when running "
        "a scratch COPY of this script, whose location says nothing about the "
        "tree it is checking.",
    )
    ap.add_argument(
        "--registry",
        type=Path,
        default=REGISTRY_RS,
        help="registry source to read (default: the in-tree one). Exists so this "
        "check's POSITIVE CONTROL can run against a deliberately broken copy "
        "without mutating a shared checkout: a basis checker that has never "
        "been shown to fire is indistinguishable from one that cannot.",
    )
    args = ap.parse_args()
    if args.repo is not None:
        default_registry = args.registry == REGISTRY_RS
        _set_repo(args.repo)
        if default_registry:
            args.registry = (
                REPO / "crates" / "axeyum-solver" / "src" / "config_registry.rs"
            )

    if not args.registry.exists():
        print(f"FAIL: registry not found at {args.registry}", file=sys.stderr)
        return 2

    entries, literal_count = parse_registry(args.registry)
    if literal_count != len(entries):
        print(
            f"FAIL (self-check): the file holds {literal_count} ConfigEntry "
            f"literals but the parser produced {len(entries)}. The report below "
            f"would be silently incomplete.",
            file=sys.stderr,
        )
        return 2

    parsed_bases = sum(len(e.bases) for e in entries)
    written_bases = count_basis_literals(args.registry)
    if parsed_bases != written_bases:
        print(
            f"FAIL (self-check): the file holds {written_bases} basis "
            f"constructor call(s) but only {parsed_bases} were attributed to an "
            f"entry. Some basis is written down and checked by nothing — the "
            f"exact shape of a gate that cannot fire.",
            file=sys.stderr,
        )
        return 2

    if args.audit:
        return audit(entries)

    with_basis = [e for e in entries if e.bases]

    if args.list:
        for e in sorted(with_basis, key=lambda x: x.key):
            for kind, a, b in e.bases:
                extra = f" in {b}" if kind == "LiveSymbol" else (f" ~ {b!r}" if b else "")
                print(f"{e.key}\t{kind}\t{a}{extra}")
        print(
            f"\n{parsed_bases} basis declaration(s) across {len(with_basis)} of "
            f"{len(entries)} entries",
            file=sys.stderr,
        )
        return 0

    gone: list[tuple[str, str, str, str]] = []
    for e in sorted(with_basis, key=lambda x: x.key):
        for kind, a, b in e.bases:
            why = check_basis(kind, a, b)
            if why:
                gone.append((e.key, kind, a, why))

    print(
        f"admission-limit basis: {parsed_bases} declaration(s) across "
        f"{len(with_basis)} of {len(entries)} registry entries."
    )
    if not gone:
        print("Every basis resolves: nothing a dated justification names has disappeared.")
        return 0

    print(f"\nGONE: {len(gone)} basis declaration(s) no longer resolve.\n")
    for key, kind, a, why in gone:
        print(f"  {key}")
        print(f"    {kind}({a}): {why}")
        print()
    print(
        "Re-take the measurement against what the code does NOW, and re-state "
        "the basis. Do NOT delete the basis to make this pass: an unjustified "
        "bound that nothing reports is the state this check exists to end."
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
