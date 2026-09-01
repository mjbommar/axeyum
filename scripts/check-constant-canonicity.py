#!/usr/bin/env python3
"""One canonical definition per mathematical object -- gated, not hoped for.

The hazard
==========

Nothing in this repository objects to a SECOND definition of a mathematical
constant.  A lane that cannot find `CReal.pi` (CLAUDE.md's "THE LEMMA YOU
NEED USUALLY EXISTS") builds `CReal.piMachin`, the kernel type-checks it --
a `Definition` is admitted once it is well-typed, and every `CReal`-valued
constant has the identical type `CReal` -- and from then on the development
has two pi's whose relationship nothing states.  Every downstream theorem is
about one of them and silently not about the other.

Neither existing instrument sees it:

* `check-shape-duplicates.py` groups declarations by admitted TYPE SHAPE.
  Measured 2026-08-31: 15 duplicate groups, zero of which contain any
  constant.  A type-based detector over constants is either useless (one
  group holding every `CReal` value) or blind.  It is blind.
* `CReal.Equiv` is UNDECIDABLE, so there is no mechanical test for "is this
  constructed real the same real as that one".

So the adjudication is necessarily declarative.  What this gate does is make
the POPULATION derived and the adjudication mandatory, in both directions.

What is derived and what is declared
====================================

DERIVED from `kernel_declaration_projection --release` (the authority: every
declaration in every constructed prelude, with its canonical type, its kind,
and its per-declaration dependency sets):

* the set of constants -- every `definition` whose canonical type contains no
  arrow (nullary) and whose head symbol is a DATA carrier, not a `Prop`.
  The `Prop` test is itself derived: the head symbol's own declaration is
  looked up and its result sort read.  `Nat.lt_well_founded :
  WellFounded.{1} AxNat AxNat.lt` is a nullary definition, but `WellFounded`
  lands in `Prop`, so it is a PROOF -- definitional proof irrelevance makes a
  duplicate of it harmless, and it needs no adjudication.  Nothing here is a
  hand-written exemption list.
* each constant's carrier, checked against the registry's `carrier` column.
* whether a claimed `bridge` theorem EXISTS, is a theorem, and STATES a
  relation between the two constants -- read from the projection's
  `direct_type_declarations` column (the declarations the theorem's TYPE
  mentions), never its proof-term dependencies.  A theorem that merely uses
  both constants somewhere inside its proof is not a bridge.

DECLARED in `artifacts/trust-closure/canonical-constants.tsv`, because the
kernel cannot decide it:

* which mathematical object each constant denotes, and which constant is
  canonical for that object.

Guards (each kills exactly one registered control)
==================================================

  G1  UNADJUDICATED    a constant in the kernel with no registry row
  G2  STALE            a registry row naming a constant the kernel lacks
  G3  CARRIER-MISMATCH the row's carrier is not the kernel's type
  G4  AMBIGUOUS        two `canonical` rows for one (carrier, object)
  G5  ORPHAN-ALTERNATE an `alternate` whose object has no canonical
  G6  MISSING-BRIDGE   an `alternate` naming no bridge theorem
  G7  ABSENT-BRIDGE    a bridge that is not a theorem in the kernel
  G8  VACUOUS-BRIDGE   a bridge whose STATED TYPE does not mention both
  G9  NO-REASON        a row with an empty `reason`
  G10 NAME-COLLISION   two same-carrier constants whose names prefix-match
                       registered to DIFFERENT objects, with no explicit
                       `distinct-from:<object>` in the reason
  G11 DUPLICATE-ROW    two rows for one constant
  G12 EMPTY-AUTHORITY  zero constants parsed -- a broken tool, not a pass

G10 is the one that fires on the motivating case without anyone having
thought about it in advance: `CReal.pi` and `CReal.piMachin` prefix-match, so
registering the second as its own object is refused until the author writes
`distinct-from:pi` in the reason -- an explicit, attributable, reviewable
claim that these are different real numbers.  It is a HEURISTIC and its
evasion is obvious (`CReal.machinConstant` does not prefix-match `pi`); it is
here because it costs twenty lines and covers the realistic naming, not
because it is a proof of anything.  G1 is the guard that has no evasion.

What this gate does NOT guarantee
=================================

It cannot check that a `canonical` row's claim is TRUE.  A lane may register
`CReal.piMachin` as object `pi-machin` with `distinct-from:pi` and pass.
What changes is that the duplication stops being an omission and becomes a
written false claim, in a reviewed file, attributable to a commit -- the same
standing `scripts/shape-duplicates-allowlist.json` has, which this repository
already accepts as the bar for an undecidable adjudication.

Usage::

    python3 scripts/check-constant-canonicity.py
    python3 scripts/check-constant-canonicity.py --projection-file captured.tsv
    python3 scripts/check-constant-canonicity.py --registry my-registry.tsv

Exit 0: every constant adjudicated, every row live, every bridge checked.
Exit 1: a finding.  Exit 2: the tool or the registry is broken -- NOT a
finding about constants.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_REGISTRY = REPO_ROOT / "artifacts" / "trust-closure" / "canonical-constants.tsv"

COLUMNS = ("carrier", "constant", "object", "role", "bridge", "reason")
ROLES = ("canonical", "alternate")
NO_BRIDGE = "-"
# Below this length a name stem prefixes far too much to mean anything
# (`e` would collide with every constant whose name starts with `e`).
MIN_STEM = 2


class ProjectionFormatError(ValueError):
    """`kernel_declaration_projection` output does not have the expected shape."""


class RegistryError(ValueError):
    """`artifacts/trust-closure/canonical-constants.tsv` is malformed."""


@dataclass(frozen=True)
class Decl:
    """One declaration row of the authority, deduplicated across preludes."""

    name: str
    kind: str
    type_deps: frozenset[str]
    canonical_type: str


@dataclass(frozen=True)
class Row:
    carrier: str
    constant: str
    object: str
    role: str
    bridge: str
    reason: str
    lineno: int


def parse_projection(text: str) -> dict[str, Decl]:
    """Parse `kernel_declaration_projection` stdout into name -> Decl.

    A name occurs once per prelude that declares it (`CReal.one` is in
    `creal`, `complex` and `cpoint`), with an identical canonical type --
    verified 2026-08-31 across all 17 nullary definitions.  Type-dependency
    sets are UNIONED across preludes so a bridge stated in one prelude is
    visible whichever prelude re-declares it.
    """
    decls: dict[str, Decl] = {}
    for lineno, line in enumerate(text.splitlines(), start=1):
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) != 8:
            raise ProjectionFormatError(
                f"line {lineno}: expected 8 tab-separated fields, got {len(fields)}: {line!r}"
            )
        _label, kind, name, _footprint, type_deps_field, _all_deps, _thm_deps, ctype = fields
        type_deps = frozenset(d for d in type_deps_field.split(",") if d)
        prior = decls.get(name)
        if prior is None:
            decls[name] = Decl(name, kind, type_deps, ctype)
            continue
        if prior.kind != kind or prior.canonical_type != ctype:
            raise ProjectionFormatError(
                f"line {lineno}: {name} is declared twice with different kind/type "
                f"({prior.kind}/{prior.canonical_type!r} vs {kind}/{ctype!r}) -- "
                "the authority is inconsistent, this is not a finding about constants"
            )
        decls[name] = Decl(name, kind, prior.type_deps | type_deps, ctype)
    return decls


def head_symbol(canonical_type: str) -> str:
    """The leading applied constant of a rendered type.

    `render_lean` emits flat curried applications: `CReal` -> `CReal`,
    `WellFounded.{1} AxNat AxNat.lt` -> `WellFounded`.  Universe suffixes
    (`.{1}`) are stripped so the head can be looked up in the environment.
    """
    stripped = canonical_type.strip()
    if not stripped:
        return ""
    head = stripped.lstrip("(").split()[0]
    return head.split(".{")[0]


def result_sort(canonical_type: str) -> str:
    """The rightmost result of a rendered (possibly arrow) type."""
    ty = canonical_type.strip()
    while True:
        idx = ty.rfind("-> ")
        if idx < 0:
            break
        ty = ty[idx + 3 :].strip().rstrip(")").strip()
    return ty


def is_proof_valued(canonical_type: str, decls: dict[str, Decl]) -> bool:
    """True when this nullary type lands in `Prop` -- a proof, not a constant.

    Derived, not exempted: the head symbol's own declaration is looked up and
    its result sort read.  A duplicate proof of one `Prop` is harmless under
    definitional proof irrelevance, so it needs no canonicity adjudication.
    """
    head = head_symbol(canonical_type)
    if head == "Prop":
        return True
    carrier = decls.get(head)
    if carrier is None:
        return False
    return result_sort(carrier.canonical_type) == "Prop"


def constants(decls: dict[str, Decl]) -> dict[str, Decl]:
    """Every nullary DATA-valued definition -- the population, derived."""
    return {
        name: d
        for name, d in decls.items()
        if d.kind == "definition"
        and "->" not in d.canonical_type
        and not is_proof_valued(d.canonical_type, decls)
    }


def stem(constant: str) -> str:
    """Normalized comparable stem of a declaration name: last component,
    lowercased, alphanumerics only.  `CReal.piMachin` -> `pimachin`."""
    last = constant.rsplit(".", 1)[-1]
    return "".join(ch for ch in last.lower() if ch.isalnum())


def load_registry(path: Path) -> list[Row]:
    try:
        raw = path.read_text()
    except OSError as exc:
        raise RegistryError(f"cannot read {path}: {exc}") from exc
    rows: list[Row] = []
    header_seen = False
    for lineno, line in enumerate(raw.splitlines(), start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != len(COLUMNS):
            raise RegistryError(
                f"{path}:{lineno}: expected {len(COLUMNS)} tab-separated fields "
                f"{COLUMNS}, got {len(fields)}: {line!r}"
            )
        if not header_seen:
            if tuple(f.strip() for f in fields) != COLUMNS:
                raise RegistryError(
                    f"{path}:{lineno}: first data line must be the header {COLUMNS}, got {fields!r}"
                )
            header_seen = True
            continue
        carrier, constant, obj, role, bridge, reason = (f.strip() for f in fields)
        if role not in ROLES:
            raise RegistryError(f"{path}:{lineno}: role must be one of {ROLES}, got {role!r}")
        rows.append(Row(carrier, constant, obj, role, bridge, reason, lineno))
    if not header_seen:
        raise RegistryError(f"{path}: no header line {COLUMNS} found")
    return rows


def run_projection(cargo_bin: str = "cargo") -> str:
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
        cmd, cwd=REPO_ROOT, capture_output=True, text=True, timeout=1800, check=False
    )
    if proc.returncode != 0:
        raise RuntimeError(
            f"`{' '.join(cmd)}` exited {proc.returncode} -- the tool itself failed, "
            f"this is not a finding about constants:\nSTDERR:\n{proc.stderr[-4000:]}"
        )
    return proc.stdout


def evaluate(pop: dict[str, Decl], rows: list[Row], decls: dict[str, Decl]) -> list[str]:
    """Return one human-readable finding per violated guard instance."""
    findings: list[str] = []

    # G11 duplicate rows.
    seen: dict[str, Row] = {}
    for row in rows:
        if row.constant in seen:
            findings.append(
                f"G11 DUPLICATE-ROW  {row.constant} is registered twice "
                f"(lines {seen[row.constant].lineno} and {row.lineno})"
            )
        else:
            seen[row.constant] = row

    # G1 a constant with no row.
    for name in sorted(pop):
        if name not in seen:
            findings.append(
                f"G1 UNADJUDICATED  {name} : {pop[name].canonical_type} is a new "
                "constant with no registry row. Say which mathematical object it "
                "denotes. If that object ALREADY has a canonical constant, this "
                "should be a THEOREM relating the two, not a second definition."
            )

    # G2 stale rows / G3 carrier mismatch.
    for row in rows:
        decl = pop.get(row.constant)
        if decl is None:
            findings.append(
                f"G2 STALE  line {row.lineno}: {row.constant} is not a constant in "
                "the kernel environment (renamed, removed, or now takes arguments)"
            )
            continue
        if row.carrier != decl.canonical_type:
            findings.append(
                f"G3 CARRIER-MISMATCH  line {row.lineno}: {row.constant} is registered "
                f"under carrier {row.carrier!r} but the kernel types it {decl.canonical_type!r}"
            )

    # G9 empty reason.
    for row in rows:
        if not row.reason:
            findings.append(
                f"G9 NO-REASON  line {row.lineno}: {row.constant} carries no reason -- "
                "a registry entry without one is how a gate becomes decoration"
            )

    # G4 two canonicals for one object.
    canonical_of: dict[tuple[str, str], Row] = {}
    for row in rows:
        if row.role != "canonical":
            continue
        key = (row.carrier, row.object)
        if key in canonical_of:
            findings.append(
                f"G4 AMBIGUOUS  {row.carrier} object {row.object!r} has TWO canonical "
                f"constants: {canonical_of[key].constant} (line {canonical_of[key].lineno}) "
                f"and {row.constant} (line {row.lineno}). Exactly one is the definition "
                "of record; the other is an alternate with a bridge theorem."
            )
        else:
            canonical_of[key] = row

    # G5/G6/G7/G8 alternates.
    for row in rows:
        if row.role != "alternate":
            continue
        canonical = canonical_of.get((row.carrier, row.object))
        if canonical is None:
            findings.append(
                f"G5 ORPHAN-ALTERNATE  line {row.lineno}: {row.constant} is an alternate "
                f"for {row.carrier} object {row.object!r}, which has no canonical constant"
            )
            continue
        if not row.bridge or row.bridge == NO_BRIDGE:
            findings.append(
                f"G6 MISSING-BRIDGE  line {row.lineno}: {row.constant} is an alternate "
                f"for {canonical.constant} and names no bridge theorem. An alternate "
                "construction is only admissible once a theorem relates it to the "
                "canonical one."
            )
            continue
        bridge = decls.get(row.bridge)
        if bridge is None or bridge.kind != "theorem":
            what = (
                "is not declared at all" if bridge is None else f"is a {bridge.kind}, not a theorem"
            )
            findings.append(
                f"G7 ABSENT-BRIDGE  line {row.lineno}: bridge {row.bridge} for "
                f"{row.constant} {what} in the kernel environment"
            )
            continue
        missing = {row.constant, canonical.constant} - bridge.type_deps
        if missing:
            findings.append(
                f"G8 VACUOUS-BRIDGE  line {row.lineno}: {row.bridge}'s STATED TYPE does "
                f"not mention {sorted(missing)} -- it relates nothing. A bridge must "
                "state the relation between the alternate and the canonical constant; "
                "using both somewhere inside a proof term is not a bridge."
            )

    # G10 prefix-matching names registered to different objects.
    by_carrier: dict[str, list[Row]] = {}
    for row in rows:
        by_carrier.setdefault(row.carrier, []).append(row)
    for carrier, group in sorted(by_carrier.items()):
        for i, left in enumerate(group):
            for right in group[i + 1 :]:
                if left.object == right.object:
                    continue
                left_stem, right_stem = stem(left.constant), stem(right.constant)
                if len(left_stem) <= len(right_stem):
                    short, long_, shorter, other = left_stem, right_stem, left, right
                else:
                    short, long_, shorter, other = right_stem, left_stem, right, left
                if len(short) < MIN_STEM or not long_.startswith(short):
                    continue
                token = f"distinct-from:{shorter.object}"
                if token in other.reason or f"distinct-from:{other.object}" in shorter.reason:
                    continue
                findings.append(
                    f"G10 NAME-COLLISION  {carrier}: {left.constant} ({left.object!r}) and "
                    f"{right.constant} ({right.object!r}) have prefix-matching names but are "
                    "registered as DIFFERENT mathematical objects. If that is really so, say "
                    f"it explicitly: put `{token}` in {other.constant}'s reason. If it is not, "
                    "one of them is an alternate and needs a bridge theorem."
                )

    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY)
    parser.add_argument(
        "--projection-file",
        type=Path,
        default=None,
        help="read kernel_declaration_projection stdout from this file instead "
        "of invoking cargo (for testing against a captured or synthetic fixture)",
    )
    parser.add_argument("--cargo-bin", default="cargo")
    args = parser.parse_args(argv)

    try:
        rows = load_registry(args.registry)
    except RegistryError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2

    if args.projection_file is not None:
        try:
            text = args.projection_file.read_text()
        except OSError as exc:
            print(f"FAIL: cannot read {args.projection_file}: {exc}", file=sys.stderr)
            return 2
    else:
        try:
            text = run_projection(args.cargo_bin)
        except (RuntimeError, subprocess.SubprocessError) as exc:
            print(f"FAIL: {exc}", file=sys.stderr)
            return 2

    try:
        decls = parse_projection(text)
    except ProjectionFormatError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 2

    pop = constants(decls)
    if not pop:
        print(
            "FAIL: the authority reports ZERO nullary data-valued definitions. "
            "This kernel declares `CReal.zero`, `Int.one` and others, so an empty "
            "population means the projection did not run or its format moved -- "
            "a broken gate, not a clean one.",
            file=sys.stderr,
        )
        return 2

    findings = evaluate(pop, rows, decls)

    proofs = sum(
        1
        for d in decls.values()
        if d.kind == "definition"
        and "->" not in d.canonical_type
        and is_proof_valued(d.canonical_type, decls)
    )
    carriers = sorted({d.canonical_type for d in pop.values()})
    alternates = sum(1 for r in rows if r.role == "alternate")

    if findings:
        print(f"FAIL: {len(findings)} constant-canonicity finding(s):", file=sys.stderr)
        for finding in findings:
            print(f"  {finding}", file=sys.stderr)
        print(
            f"\n  registry: {args.registry}\n"
            "  See docs/research/09-decisions/"
            "adr-1320-one-canonical-definition-per-mathematical-object.md",
            file=sys.stderr,
        )
        return 1

    print(
        f"constant-canonicity: OK -- {len(pop)} constants over {len(carriers)} carriers "
        f"({', '.join(carriers)}), {len(rows)} adjudicated, {alternates} bridged alternate(s), "
        f"{proofs} nullary Prop-valued definition(s) excluded as proofs"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
