#!/usr/bin/env python3
"""S2 — universal trust and circularity audit, computed from the admitted term.

ADR-0717's risk 4 is **contamination**: *"the target proof, an equivalent
imported theorem, an axiom, opaque, or quotient enters the dependency
closure"*, and the ADR says plainly that an empty axiom footprint addresses
only part of it. The 2026-08-30 safety-matrix census
(`docs/plan/status/382-l0-safety-matrix.md`) measured how little of the ledger
is protected against that shape: **circularity 38 / 2117**,
**per_theorem_footprint 59 / 2117**, against **env_footprint 1859 / 2117** — so
almost all trust evidence is a *batch* claim ("this whole prelude has no
axioms") with a fan-out reaching 463 facts on one command. A prelude-wide sweep
cannot see a target entering its own closure, and it cannot see an equivalent
theorem standing in for the target.

This computes the closure from the environment the kernel actually admitted —
`Kernel::declaration_dependencies` — and never from a fact's authored
`depends_on`, a doc comment, or a head-symbol match.

# The four guards, and why they are four

The phase exit requires that target injection, indirect target injection, axiom
insertion, and checker-population deletion each fail through a **different**
guard. That wording is not pedantry: six of seven guards in one suite in this
repository were once removable with everything still green, because they all
rejected through one shared check. So the guards below are deliberately
disjoint in what they look at, and `scripts/tests/test-trust-closure.sh`
deletes each one and requires that exactly one fixture dies.

- `guard_self_occurrence` — the subject theorem appears in its OWN transitive
  declaration closure. Looks only at identity of the subject.
- `guard_alias_occurrence` — a DIFFERENT theorem whose canonical kernel type is
  byte-identical to the subject's appears in the closure. Looks only at the
  identity map, which is derived by grouping `Declaration::Theorem` rows by
  `Kernel::render_lean` of their type — never hand-authored, so it cannot
  encode a wish. Restricted to `theorem` kind on purpose: `AxReal.add` and
  `AxReal.mul` share the rendered type `AxReal -> AxReal -> AxReal` and are not
  equivalent statements, they are different opaque constants of the same
  arity. Axioms are `guard_forbidden_trust`'s business, not this one's.
- `guard_forbidden_trust` — an `Axiom`, `Opaque` or `Quotient` is reachable.
  Looks only at declaration KIND in the closure.
- `guard_population` — the enforced population itself. Looks at no closure at
  all. This is the one that exists because the other three cannot fail when
  there is nothing to check: a checker that cannot fail is worse than no
  checker, and deleting the subjects is the cheapest way to get a green run.

# Why the carrier asymmetry is safe here

`Nat.le_total`, `Int.le_total` and `Rat.le_total` are all proved theorems in
this kernel while `CReal.le_total` is **absent**, and that asymmetry is real
and load-bearing (ADR-0716). An identity map that treated carriers as
interchangeable would collapse them and be wrong. This one cannot: the three
render as `(x0 : AxNat) -> ...`, `(x0 : Int) -> ...` and `(x0 : Rat) -> ...`,
which are three distinct strings, so they land in three distinct classes.
`scripts/tests/test-trust-closure.sh` pins that as a positive control against
the real environment rather than a fixture, because it is the case a plausible
"normalize the carrier" refactor would break.

# What a subject is, and the primed-name gap this closes

A subject is a `kernel-lean` fact with `epistemic_status` in {proved, computed}
whose kernel declaration can be identified. The identification, in order:

1. `formal.kernel_theorem` when the KEY is present — authoritative including a
   `null` value, which means "not about exactly one kernel theorem";
2. an unambiguous `evidence[].kernel_declaration`;
3. the dotted-name regex over the fact's own `checker_command`s, reusing
   `scripts/check-fact-depends-derived.py`'s.

Step 2 is new here and it is not cosmetic. That regex deliberately excludes an
apostrophe (a primed Lean name would otherwise absorb a checker command's
closing quote), and its own comment records that "0 of the 312 theorems this
kernel declares contain a prime. If a primed name ever appears, this must
handle quoting rather than widening the class back." One has appeared:
`F:nat-bitwise-bit`'s subject is `Nat.bitwise_bit'`, and extraction yields
`Nat.bitwise_bit`, which no declaration bears. Reading `kernel_declaration`
resolves it exactly, with no widening of the regex.

# Usage

```sh
python3 scripts/check-trust-closure.py            # gate form
python3 scripts/check-trust-closure.py --update    # regenerate the pinned artifacts
python3 scripts/check-trust-closure.py --json      # one machine-readable line
```

`--projection FILE` reads a pre-captured
`kernel_declaration_projection` TSV instead of running the example; the control
suite uses it, and so should anyone re-running this against a captured
environment. `--facts DIR` and `--population FILE` exist for the same reason.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import pathlib
import subprocess
import sys
from dataclasses import dataclass, field
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "artifacts/trust-closure"
DEFAULT_FACTS = ROOT / "artifacts/facts"
DEFAULT_POPULATION = ARTIFACTS / "population.json"
DEFAULT_IDENTITY_MAP = ARTIFACTS / "identity-map.tsv"
DEFAULT_EQUIVALENT_PAIRS = ARTIFACTS / "equivalent-pairs.tsv"

KERNEL_ROUTES = {"kernel-lean"}
SETTLED = {"proved", "computed"}
TRUSTED_KINDS = {"axiom", "opaque", "quotient"}

# Opaques and quotients that the project has accepted into its trusted surface.
# EMPTY, and that is the measured state rather than an aspiration: the
# environment this reads has 30 axioms (all `AxReal.*`) and **zero** opaques and
# **zero** quotients. `Quot.sound` is the reason a `Quotient` counts as trusted
# surface at all -- CLAUDE.md's own note that `Axiom` alone is not the trusted
# surface, since `Opaque` has no proof body and `Quotient` admits `Quot.sound`.
OWNED_OPAQUES_AND_QUOTIENTS: frozenset[str] = frozenset()


def _load_depends_derived_module() -> Any:
    """Reuse `check-fact-depends-derived.py`'s subject extraction rather than
    copying its regex.

    That regex carries five separate measured corrections in its comments (the
    `AxReal`-before-`Real` ordering, the `(?<![A-Za-z])` boundary, the
    multi-segment name class, the excluded apostrophe, the added constructed
    carriers). Re-deriving it here would leave two copies to drift apart, and
    this repository has already paid for that shape: "re-deriving it beside the
    original leaves two proofs of one fact that must stay in sync while the
    kernel happily verifies both."
    """
    path = ROOT / "scripts/check-fact-depends-derived.py"
    spec = importlib.util.spec_from_file_location("_axeyum_depends_derived", path)
    if spec is None or spec.loader is None:  # pragma: no cover - import plumbing
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@dataclass
class Declaration:
    name: str
    kind: str
    footprint_size: int
    direct: tuple[str, ...]
    canonical_type: str
    labels: set[str] = field(default_factory=set)


@dataclass
class GuardResult:
    name: str
    scanned: int
    hits: int
    failures: list[str]


def projection_rows(path: pathlib.Path | None) -> str:
    """`kernel_declaration_projection` output: the whole constructed surface.

    Run through `cargo run --release`, matching every other in-tree caller.
    `--release` is MANDATORY for this example by its own doc comment: it builds
    `creal`/`complex`/`cpoint`, whose `Kernel::add_declaration` recursion
    overflows a debug build's per-frame budget. A SIGABRT here is that resource
    limit, not a broken proof.
    """
    if path is not None:
        return path.read_text(encoding="utf-8")
    proc = subprocess.run(
        [
            "cargo", "run", "-q", "--release", "-p", "axeyum-lean-kernel",
            "--example", "kernel_declaration_projection",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=3600,
        check=True,
    )
    return proc.stdout


def parse_projection(text: str) -> dict[str, Declaration]:
    """`name -> Declaration`, merged across prelude groups.

    Preludes nest, so one declaration appears under several labels with
    identical content; a disagreement between two labels would mean the
    environment is not what this assumes and is raised rather than absorbed.
    """
    out: dict[str, Declaration] = {}
    for line in text.splitlines():
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) < 8:
            raise ValueError(
                f"projection row has {len(fields)} fields, expected 8: {line[:120]!r}"
            )
        label, kind, name, footprint, _type_deps, direct, _theorem_deps, ctype = (
            fields[0], fields[1], fields[2], fields[3], fields[4], fields[5],
            fields[6], "\t".join(fields[7:]),
        )
        deps = tuple(d for d in direct.split(",") if d)
        existing = out.get(name)
        if existing is None:
            out[name] = Declaration(
                name=name,
                kind=kind,
                footprint_size=int(footprint),
                direct=deps,
                canonical_type=ctype,
                labels={label},
            )
            continue
        if existing.kind != kind or existing.canonical_type != ctype:
            raise ValueError(
                f"{name} disagrees between prelude groups "
                f"{sorted(existing.labels)} and {label}"
            )
        existing.labels.add(label)
    return out


def closures(decls: dict[str, Declaration]) -> dict[str, frozenset[str]]:
    """Transitive `declaration_dependencies` closure, EXCLUDING the node itself
    unless it is genuinely reachable from its own dependencies.

    That exclusion is the whole point: `guard_self_occurrence` asks whether the
    subject is reachable *from its own direct dependencies*, so seeding the
    closure with the subject would make the guard vacuously true for every
    subject and it could never fail.

    Iterative rather than recursive. The admitted environment is acyclic by
    construction -- `Kernel::add_declaration` can only reference already-admitted
    names -- but a MUTATED projection is exactly the input this must survive,
    and a recursive walk on an injected self-edge would blow the stack instead
    of reporting the injection.
    """
    memo: dict[str, frozenset[str]] = {}
    for start in decls:
        stack = [start]
        order: list[str] = []
        seen = {start}
        while stack:
            node = stack.pop()
            order.append(node)
            for dep in decls[node].direct if node in decls else ():
                if dep not in seen:
                    seen.add(dep)
                    stack.append(dep)
        reach: set[str] = set()
        for node in order:
            for dep in decls[node].direct if node in decls else ():
                reach.add(dep)
        memo[start] = frozenset(reach)
    # The loop above computes reachability from `start` over the nodes it
    # explored, which is the closed set: every node reachable from `start` was
    # pushed, so unioning each explored node's direct edges is exactly the
    # transitive closure of `start`'s successors.
    return memo


def identity_classes(decls: dict[str, Declaration]) -> dict[str, list[str]]:
    """`canonical type -> [theorem name]` for types borne by 2+ THEOREMS.

    Derived, never authored. Two theorems whose `Kernel::render_lean` types are
    byte-identical state the same proposition, so one standing in for the other
    inside a closure is the indirect-target-injection shape ADR-0717 names.

    `theorem` kind only. See the module doc: `AxReal.add`/`AxReal.mul` share a
    rendered type and are not equivalent statements.
    """
    by_type: dict[str, list[str]] = {}
    for name, decl in decls.items():
        if decl.kind != "theorem":
            continue
        by_type.setdefault(decl.canonical_type, []).append(name)
    return {t: sorted(n) for t, n in by_type.items() if len(n) >= 2}


def subject_of(fact: dict[str, Any], depends_derived: Any) -> str | None:
    """The kernel declaration a fact is about. See the module doc for the order."""
    formal = fact.get("formal") or {}
    if "kernel_theorem" in formal:
        value = formal["kernel_theorem"]
        return value if isinstance(value, str) and value else None
    named = {
        e["kernel_declaration"]
        for e in fact.get("evidence") or []
        if isinstance(e.get("kernel_declaration"), str) and e["kernel_declaration"]
    }
    if len(named) == 1:
        return next(iter(named))
    return depends_derived.theorem_of(fact)


def load_facts(directory: pathlib.Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for path in sorted(directory.glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        out[data["id"]] = data
    return out


@dataclass
class Subjects:
    resolved: dict[str, str]           # fact id -> declaration name
    unresolved: list[str]              # kernel-route facts naming nothing
    absent: list[tuple[str, str]]      # named a declaration the environment lacks
    kernel_facts: int


def collect_subjects(
    facts: dict[str, dict[str, Any]],
    decls: dict[str, Declaration],
    depends_derived: Any,
) -> Subjects:
    resolved: dict[str, str] = {}
    unresolved: list[str] = []
    absent: list[tuple[str, str]] = []
    kernel_facts = 0
    for ident, data in sorted(facts.items()):
        if data.get("proof_route") not in KERNEL_ROUTES:
            continue
        if data.get("epistemic_status") not in SETTLED:
            continue
        kernel_facts += 1
        name = subject_of(data, depends_derived)
        if name is None:
            unresolved.append(ident)
        elif name not in decls:
            absent.append((ident, name))
        else:
            resolved[ident] = name
    return Subjects(resolved, unresolved, absent, kernel_facts)


# --------------------------------------------------------------------------
# The four guards. Each looks at a different thing; see the module doc.
# --------------------------------------------------------------------------


def guard_self_occurrence(
    subjects: Subjects,
    decls: dict[str, Declaration],
    reach: dict[str, frozenset[str]],
) -> GuardResult:
    """G1 — target injection: the subject is reachable from its own dependencies.

    In a well-formed environment this is impossible, which is precisely why it
    must be checked rather than assumed: the assumption is doing the work, and
    nothing else in the ledger tests it. If this ever fires it is a serious
    finding and the fact's status is not this script's to change -- report it.
    """
    failures: list[str] = []
    hits = 0
    for ident, name in sorted(subjects.resolved.items()):
        if name in reach.get(name, frozenset()):
            hits += 1
            failures.append(
                f"TARGET-IN-ITS-OWN-CLOSURE {ident}: `{name}` is reachable from its "
                f"own dependency closure, so its proof rests on itself"
            )
    return GuardResult("self_occurrence", len(subjects.resolved), hits, failures)


def observed_equivalent_pairs(
    subjects: Subjects,
    reach: dict[str, frozenset[str]],
    classes: dict[str, list[str]],
) -> list[tuple[str, str, str]]:
    """`(fact id, subject, equivalent found in its closure)`, sorted.

    Shared by the guard and by `--update` so the disclosed backlog is exactly
    what the guard would otherwise reject -- never more, never less -- by
    construction rather than by keeping two traversals in sync.
    """
    member_of: dict[str, list[str]] = {}
    for names in classes.values():
        for name in names:
            member_of[name] = [other for other in names if other != name]
    out: list[tuple[str, str, str]] = []
    for ident, name in sorted(subjects.resolved.items()):
        equivalents = member_of.get(name)
        if not equivalents:
            continue
        for found in sorted(set(equivalents) & reach.get(name, frozenset())):
            out.append((ident, name, found))
    return out


def guard_alias_occurrence(
    subjects: Subjects,
    decls: dict[str, Declaration],
    reach: dict[str, frozenset[str]],
    classes: dict[str, list[str]],
    disclosed: set[tuple[str, str, str]],
) -> GuardResult:
    """G2 — indirect target injection: an equivalent statement stands in.

    `member_of` maps a theorem to the other members of its identity class. A
    subject whose closure contains one of them did not prove its statement; it
    proved a renaming of one, and the ledger is counting one proposition twice.

    # The backlog is DISCLOSED, not approved, and it may only shrink

    This guard found **13 such occurrences on its first run over the committed
    ledger**, in 13 of the 15 identity classes the environment contains — and
    in all 15 classes BOTH members are ledger facts. So 30 proved facts state
    15 propositions, and for 13 of them one member's proof term literally
    contains the other. `F:rat-weak-law-of-large-numbers` and
    `F:rat-chebyshev-samplemean-uncorrelated` are the same theorem;
    `F:int-characterization-le-total` is proved from `Int.le_total`.

    Those pre-date this guard and are not this lane's to resettle: an S2 audit
    does not get to edit a fact's `epistemic_status`. They are written to
    `artifacts/trust-closure/equivalent-pairs.tsv` as a **ratcheting backlog**.
    A pair not on that list rejects, so no new duplicate can land quietly; a
    pair on the list that no longer occurs ALSO rejects, so the list cannot
    outlive its subject and a resolution has to be recorded. Neither direction
    can be satisfied by adding a line without changing what the tree contains.
    """
    observed = observed_equivalent_pairs(subjects, reach, classes)
    failures: list[str] = []
    hits = 0
    for ident, name, found in observed:
        if (ident, name, found) in disclosed:
            continue
        hits += 1
        failures.append(
            f"EQUIVALENT-IN-CLOSURE {ident}: `{name}`'s closure contains "
            f"`{found}`, whose canonical kernel type is byte-identical -- the "
            f"target was not proved, an equivalent was renamed. If this is "
            f"intended, it belongs on the disclosed backlog with the duplicate "
            f"acknowledged, not in the ledger as a second result"
        )
    stale = sorted(disclosed - set(observed))
    for ident, name, found in stale:
        hits += 1
        failures.append(
            f"STALE-DISCLOSURE {ident}: the backlog records `{name}` reaching "
            f"`{found}` and it no longer does. That is progress and must be "
            f"recorded: re-run with --update so the ratchet cannot drift back"
        )
    return GuardResult("alias_occurrence", len(subjects.resolved), hits, failures)


def guard_forbidden_trust(
    subjects: Subjects,
    decls: dict[str, Declaration],
    reach: dict[str, frozenset[str]],
) -> GuardResult:
    """G3 — axiom insertion, and unowned opaques/quotients.

    A kernel-route fact declaring `axiom_footprint: []` claims to rest on
    nothing assumed. This reads what the closure actually reaches and requires
    the two to agree. An `Opaque` or `Quotient` outside
    `OWNED_OPAQUES_AND_QUOTIENTS` is rejected whatever the fact declares: those
    are trusted surface with no proof body, and `Quot.sound` is why a
    `Quotient` counts.
    """
    failures: list[str] = []
    hits = 0
    facts_by_id = subjects.resolved
    for ident, name in sorted(facts_by_id.items()):
        reached = sorted(
            d for d in reach.get(name, frozenset())
            if d in decls and decls[d].kind in TRUSTED_KINDS
        )
        unowned = [
            d for d in reached
            if decls[d].kind in {"opaque", "quotient"}
            and d not in OWNED_OPAQUES_AND_QUOTIENTS
        ]
        if unowned:
            hits += 1
            failures.append(
                f"UNOWNED-TRUSTED-SURFACE {ident}: `{name}`'s closure reaches "
                f"{', '.join('`' + d + '`' for d in unowned)}, which no owned set "
                f"admits"
            )
            continue
        if reached:
            hits += 1
            failures.append(
                f"AXIOM-IN-CLOSURE {ident}: `{name}`'s closure reaches "
                f"{len(reached)} trusted declaration(s) "
                f"({', '.join('`' + d + '`' for d in reached[:6])}"
                f"{', ...' if len(reached) > 6 else ''})"
            )
    return GuardResult("forbidden_trust", len(facts_by_id), hits, failures)


def guard_population(subjects: Subjects, pinned: dict[str, Any]) -> GuardResult:
    """G4 — checker-population deletion.

    The other three guards iterate the subject population, so deleting the
    population makes all three pass while checking nothing. That is the exact
    failure this repository has measured most often, and it is why this guard
    looks at no closure at all.

    Three independent rejections: an empty population; a population below the
    recorded floor (a ratchet, so growth is free and shrinkage is not); and a
    subject naming a declaration the environment does not contain, which is how
    a rename or deletion shows up rather than as a count.
    """
    failures: list[str] = []
    count = len(subjects.resolved)
    if count == 0:
        failures.append(
            "EMPTY-POPULATION: 0 subjects resolved. Zero executed cases is failure, "
            "not a green run -- a checker that cannot fail is worse than no checker"
        )
    floor = int(pinned.get("min_subjects", 0))
    if count < floor:
        failures.append(
            f"POPULATION-BELOW-FLOOR: {count} subjects against a recorded floor of "
            f"{floor}. Facts or their kernel bindings were removed from the enforced "
            f"set; re-run with --update only if the removal is intended"
        )
    ratio_floor = float(pinned.get("min_ratio", 0.0))
    ratio = count / subjects.kernel_facts if subjects.kernel_facts else 0.0
    # 1e-9 because both sides are floats: the floor is stored rounded DOWN to
    # four places and the ratio is recomputed, so an exact-equality run must
    # not fail on the last bit.
    if ratio < ratio_floor - 1e-9:
        failures.append(
            f"COVERAGE-BELOW-FLOOR: {ratio:.4f} of kernel-route settled facts resolve "
            f"to a declaration, against a recorded floor of {ratio_floor:.4f}"
        )
    for ident, name in subjects.absent:
        failures.append(
            f"SUBJECT-ABSENT {ident}: names `{name}`, which the admitted environment "
            f"does not declare -- a deleted or renamed subject must not read as a "
            f"checked one"
        )
    return GuardResult("population", subjects.kernel_facts, len(failures), failures)


# --------------------------------------------------------------------------


def render_equivalent_pairs(pairs: list[tuple[str, str, str]]) -> str:
    lines = [
        "# Derived by scripts/check-trust-closure.py --update. Do not hand-edit.",
        "# DISCLOSED, NOT APPROVED. Each row is a ledger fact whose kernel subject",
        "# is proved from a sibling declaration with a byte-identical canonical",
        "# type -- one proposition, counted twice. The guard rejects any pair not",
        "# listed AND any listed pair that no longer occurs, so this file can only",
        "# shrink without a deliberate, recorded update.",
        "# fact\tsubject\tequivalent-reached-in-closure",
    ]
    for ident, name, found in sorted(pairs):
        lines.append(f"{ident}\t{name}\t{found}")
    return "\n".join(lines) + "\n"


def parse_equivalent_pairs(text: str) -> set[tuple[str, str, str]]:
    out: set[tuple[str, str, str]] = set()
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 3:
            raise ValueError(f"equivalent-pairs row is not 3 fields: {line[:120]!r}")
        out.add((fields[0], fields[1], fields[2]))
    return out


def render_identity_map(classes: dict[str, list[str]]) -> str:
    lines = [
        "# Derived by scripts/check-trust-closure.py --update. Do not hand-edit.",
        "# Theorems whose Kernel::render_lean canonical type is byte-identical.",
        "# size\tmembers\tcanonical-type",
    ]
    for ctype, names in sorted(classes.items(), key=lambda kv: (sorted(kv[1]), kv[0])):
        lines.append(f"{len(names)}\t{','.join(names)}\t{ctype}")
    return "\n".join(lines) + "\n"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--projection", type=pathlib.Path, default=None)
    parser.add_argument("--facts", type=pathlib.Path, default=DEFAULT_FACTS)
    parser.add_argument("--population", type=pathlib.Path, default=DEFAULT_POPULATION)
    parser.add_argument(
        "--identity-map", type=pathlib.Path, default=DEFAULT_IDENTITY_MAP
    )
    parser.add_argument(
        "--equivalent-pairs", type=pathlib.Path, default=DEFAULT_EQUIVALENT_PAIRS
    )
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args(argv)

    depends_derived = _load_depends_derived_module()
    decls = parse_projection(projection_rows(args.projection))
    if not decls:
        print(
            "TRUST_CLOSURE_ERROR|the projection is empty; every check below would "
            "pass vacuously",
            file=sys.stderr,
        )
        return 1
    reach = closures(decls)
    classes = identity_classes(decls)
    facts = load_facts(args.facts)
    subjects = collect_subjects(facts, decls, depends_derived)

    pinned: dict[str, Any] = {}
    if args.population.exists():
        pinned = json.loads(args.population.read_text(encoding="utf-8"))

    if args.update:
        args.identity_map.parent.mkdir(parents=True, exist_ok=True)
        args.identity_map.write_text(render_identity_map(classes), encoding="utf-8")
        args.equivalent_pairs.write_text(
            render_equivalent_pairs(
                observed_equivalent_pairs(subjects, reach, classes)
            ),
            encoding="utf-8",
        )
        ratio = (
            len(subjects.resolved) / subjects.kernel_facts
            if subjects.kernel_facts
            else 0.0
        )
        args.population.write_text(
            json.dumps(
                {
                    "generated_by": "scripts/check-trust-closure.py --update",
                    "min_subjects": max(
                        int(pinned.get("min_subjects", 0)), len(subjects.resolved)
                    ),
                    # Rounded DOWN, never to nearest. `round(0.958292, 4)` is
                    # `0.9583`, which is ABOVE the ratio it was measured from,
                    # so the very next run fails against a floor nothing ever
                    # reached. Measured here the first time this was written.
                    "min_ratio": math.floor(
                        max(float(pinned.get("min_ratio", 0.0)), ratio) * 10000
                    ) / 10000,
                    "min_declarations": max(
                        int(pinned.get("min_declarations", 0)), len(decls)
                    ),
                },
                indent=2,
            )
            + "\n",
            encoding="utf-8",
        )
        print(
            f"TRUST_CLOSURE_UPDATE|subjects={len(subjects.resolved)}|"
            f"declarations={len(decls)}|identity_classes={len(classes)}|"
            f"equivalent_pairs="
            f"{len(observed_equivalent_pairs(subjects, reach, classes))}"
        )
        return 0

    disclosed: set[tuple[str, str, str]] = set()
    disclosure_failure: str | None = None
    if args.equivalent_pairs.exists():
        disclosed = parse_equivalent_pairs(
            args.equivalent_pairs.read_text(encoding="utf-8")
        )
    else:
        disclosure_failure = (
            f"EQUIVALENT-PAIRS-MISSING: {args.equivalent_pairs} does not exist, so "
            f"every observed duplicate would reject with nothing to compare against; "
            f"run --update"
        )

    results = [
        guard_population(subjects, pinned),
        guard_self_occurrence(subjects, decls, reach),
        guard_alias_occurrence(subjects, decls, reach, classes, disclosed),
        guard_forbidden_trust(subjects, decls, reach),
    ]
    failures = [f for r in results for f in r.failures]
    if disclosure_failure is not None:
        failures.append(disclosure_failure)

    # A guard that scanned nothing has measured nothing. Reported per guard so
    # the summary cannot say "green" about a guard that never ran, and counted
    # as a failure so it cannot be read as a pass.
    for result in results:
        if result.scanned == 0:
            failures.append(
                f"GUARD-SCANNED-NOTHING {result.name}: 0 cases examined; an empty "
                f"result is not a negative result"
            )

    # Two separate rejections, written as two `if`s rather than an if/else so
    # that each can be deleted independently by the control suite. An `else:`
    # branch cannot be mutated away without also removing the branch above it,
    # which would make one mutation kill two cases and hide whether the two
    # guards are really distinct.
    identity_map_present = args.identity_map.exists()
    if identity_map_present:
        want = render_identity_map(classes)
        have = args.identity_map.read_text(encoding="utf-8")
        if want != have:
            failures.append(
                "IDENTITY-MAP-DRIFT: the derived identity map differs from "
                f"{args.identity_map.relative_to(ROOT) if args.identity_map.is_relative_to(ROOT) else args.identity_map}. "
                "A new or vanished equivalence class is a review event: re-run with "
                "--update after confirming the pair really does state one proposition"
            )
    if not identity_map_present:
        failures.append(
            f"IDENTITY-MAP-MISSING: {args.identity_map} does not exist; run --update"
        )

    if not pinned:
        failures.append(
            f"POPULATION-PIN-MISSING: {args.population} does not exist, so the "
            f"population floor is unenforced; run --update"
        )

    summary = {
        "declarations": len(decls),
        "identity_classes": len(classes),
        "kernel_facts": subjects.kernel_facts,
        "subjects": len(subjects.resolved),
        "unresolved": len(subjects.unresolved),
        "absent": len(subjects.absent),
        "disclosed_equivalent_pairs": len(disclosed),
        "guards": {r.name: {"scanned": r.scanned, "hits": r.hits} for r in results},
        "failures": len(failures),
    }
    if args.json:
        print(json.dumps(summary, sort_keys=True))
    else:
        if not args.quiet and subjects.unresolved:
            print(
                "  kernel-route settled facts naming no kernel declaration "
                f"(not enforced): {len(subjects.unresolved)}"
            )
        print(
            "TRUST_CLOSURE|declarations={declarations}|identity_classes="
            "{identity_classes}|kernel_facts={kernel_facts}|subjects={subjects}|"
            "unresolved={unresolved}|absent={absent}|"
            "disclosed_equivalent_pairs={disclosed_equivalent_pairs}|"
            "failures={failures}".format(**summary)
        )
        for result in results:
            print(
                f"  guard {result.name:18s} scanned={result.scanned:6d} "
                f"rejected={result.hits}"
            )
    for failure in failures:
        print(f"TRUST_CLOSURE_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
