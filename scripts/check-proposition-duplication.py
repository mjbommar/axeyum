#!/usr/bin/env python3
"""Duplicate-proposition gate — the counting-rule half of S2's L0/S2 finding.

`scripts/check-trust-closure.py` (merged) computed `identity_classes`: sets of
THEOREM declarations whose `Kernel::render_lean` canonical type is byte-
identical, which is the strongest available test that two kernel theorems
state the exact same proposition (a type IS the proposition in this kernel's
propositions-as-types setting, so byte-identical types cannot denote different
Props). It measured **15 such classes, all 15 with both members registered as
ledger facts, and 13 of the 15 with one member's proof closure literally
containing the other** -- so 30 proved facts state 15 propositions, and the
published "2,121 proved facts" headline double-counts every one of them.

S2 deliberately did not repair this (a lane that reports an overstatement does
not also repair it). This script is the repair's gate, not S2's gate: it does
not recompute trust/circularity (that stays check-trust-closure.py's job) and
it does not touch that file. It answers a narrower, adjacent question --
*is every known duplicate identity class LABELED, and does a NEW one entering
the ledger get caught?*

# The counting rule (ADR-0790)

Every one of the 15 classes was read by hand against its `formal.statement`
and its `depends_on`/proof closure before this script existed, and all 15
survived scrutiny as genuine duplicates -- none is a case of "A is proved from
B but states something strictly stronger." Facts are NEVER deleted (ADR-0542):
both members of a pair stay `proved`, with their own evidence intact. Instead,
exactly ONE member of each identity class is designated CANONICAL (no
`equivalent_to` field) and every other member carries
`equivalent_to: ["F:<canonical-id>"]` -- a restatement marker, deliberately
not `supersedes` (nothing is obsolete; both proofs remain independently
checked). See `artifacts/ontology/fact.schema.json`'s `equivalent_to`
property for the exact semantics.

Two headline numbers follow, and BOTH must be quoted together:

  - FACTS SETTLED       = count of `proved`/`computed` facts (unchanged; this
                           is what `scripts/validate-facts.py` already prints)
  - DISTINCT PROPOSITIONS ESTABLISHED
                         = facts settled MINUS the count carrying a non-empty
                           `equivalent_to` (each pair collapses to 1)

# The guards

Each looks at a different failure shape, mutation-verified 1:1 by
`scripts/tests/test-proposition-duplication.sh`:

  - `identity_classes_empty`     -- the identity-class computation produced
                                    NOTHING (decls/projection broken). Fails
                                    even though "no classes" looks superficially
                                    like "no duplicates" -- this project has
                                    known, standing duplicate theorem pairs, so
                                    zero classes means the computation failed,
                                    not that duplication vanished.
  - `identity_classes_below_floor` -- the class count dropped below a pinned
                                    floor (partial breakage a hard zero-check
                                    would miss).
  - `unlabeled_duplicate_pair`   -- an identity class has 2+ SETTLED facts
                                    naming distinct members, and MORE THAN ONE
                                    of them is canonical (no `equivalent_to`).
                                    This is the guard that catches a NEW
                                    duplicate pair entering the ledger.
  - `no_canonical_designated`    -- an identity class has 2+ settled facts and
                                    NONE is canonical (a dangling/cyclic
                                    `equivalent_to` graph).
  - `equivalent_to_target_absent`  -- `equivalent_to` names a fact id that does
                                    not exist in the ledger.
  - `equivalent_to_target_unsettled` -- the named target is not itself
                                    `proved`/`computed`, so it cannot serve as
                                    a canonical survivor.
  - `equivalent_to_chain`        -- the named target ITSELF carries
                                    `equivalent_to` (A -> B -> C), which would
                                    break the "collapse each pair to 1" count.
  - `equivalent_to_different_proposition` -- the fact's own resolved kernel
                                    subject and its target's resolved kernel
                                    subject do NOT share a canonical type. This
                                    is independent of identity-class membership
                                    (it reads `decls` directly), so a bogus
                                    `equivalent_to` slapped onto two unrelated
                                    facts is caught even if no identity class
                                    happens to name them both.

```sh
python3 scripts/check-proposition-duplication.py            # gate form
python3 scripts/check-proposition-duplication.py --update   # raise the pinned floor
python3 scripts/check-proposition-duplication.py --json      # one machine-readable line
```

`--projection FILE` reads a pre-captured `kernel_declaration_projection` TSV
instead of running the example, matching `check-trust-closure.py`'s own
convention; the control suite uses it.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import sys
from dataclasses import dataclass
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "artifacts/identity-classes"
DEFAULT_FACTS = ROOT / "artifacts/facts"
DEFAULT_POPULATION = ARTIFACTS / "population.json"

SETTLED = {"proved", "computed"}
# The floor this repository has NEVER been below since the finding that
# motivated this script: 15 identity classes, all 15 with both members as
# ledger facts. `--update` may only raise it.
FLOOR_DEFAULT = 15


def _load_trust_closure_module() -> Any:
    """Reuse `check-trust-closure.py`'s projection/identity-class machinery
    rather than copying it -- that file is S2's, this one builds alongside it,
    and re-deriving `identity_classes`/`parse_projection` here would leave two
    copies to drift apart (the exact failure this repository's own CLAUDE.md
    warns about under "re-deriving it beside the original")."""
    path = ROOT / "scripts/check-trust-closure.py"
    spec = importlib.util.spec_from_file_location("_axeyum_trust_closure", path)
    if spec is None or spec.loader is None:  # pragma: no cover - import plumbing
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    # Dataclasses inside the loaded module resolve type hints against
    # `sys.modules[cls.__module__]`, so the module must be registered under
    # its own name BEFORE exec_module runs `@dataclass` -- otherwise that
    # lookup returns `None` and dataclass construction raises.
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


@dataclass
class GuardResult:
    name: str
    scanned: int
    hits: int
    failures: list[str]


def load_facts(directory: pathlib.Path) -> dict[str, dict[str, Any]]:
    out: dict[str, dict[str, Any]] = {}
    for path in sorted(directory.glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        out[data["id"]] = data
    return out


def resolve_subject(
    fact: dict[str, Any], decls: dict[str, Any], tc: Any, depends_derived: Any
) -> str | None:
    """The kernel declaration name a fact is about, or None if unresolved.

    Delegates to `check-trust-closure.py`'s own `subject_of` (kernel_theorem,
    then a single named evidence.kernel_declaration, then
    `depends_derived.theorem_of` as a fallback) so this script's notion of
    "what is this fact about" is IDENTICAL to S2's -- a fact this script
    resolves and one S2's guards resolve must never disagree, or the two
    scripts would be counting different things under the same name.
    """
    return tc.subject_of(fact, depends_derived)


def class_membership(classes: dict[str, list[str]]) -> dict[str, str]:
    """`declaration name -> canonical type` for every name in a 2+ class."""
    out: dict[str, str] = {}
    for ctype, names in classes.items():
        for name in names:
            out[name] = ctype
    return out


# ---------------------------------------------------------------------------
# Guards
# ---------------------------------------------------------------------------


def guard_identity_classes_empty(classes: dict[str, list[str]]) -> GuardResult:
    if len(classes) == 0:
        return GuardResult(
            "identity_classes_empty", 1, 1,
            ["IDENTITY-CLASSES-EMPTY the identity-class computation produced "
             "NOTHING -- this project has known, standing duplicate theorem "
             "pairs, so zero classes means the projection or the computation "
             "is broken, not that duplication vanished"],
        )
    return GuardResult("identity_classes_empty", 1, 0, [])


def guard_identity_classes_below_floor(
    classes: dict[str, list[str]], floor: int
) -> GuardResult:
    count = len(classes)
    if count < floor:
        return GuardResult(
            "identity_classes_below_floor", 1, 1,
            [f"IDENTITY-CLASSES-BELOW-FLOOR {count} identity classes, floor is "
             f"{floor}. A pinned floor may only be RAISED (--update); a drop "
             f"means classes vanished silently and needs review, not a lowered pin"],
        )
    return GuardResult("identity_classes_below_floor", 1, 0, [])


def guard_unlabeled_duplicate_pair(
    class_facts: dict[str, list[tuple[str, str, bool]]],
) -> GuardResult:
    failures = []
    hits = 0
    scanned = 0
    for ctype, members in sorted(class_facts.items()):
        if len(members) < 2:
            continue
        scanned += 1
        canonical = [(fid, name) for fid, name, marked in members if not marked]
        if len(canonical) > 1:
            hits += 1
            names = ", ".join(f"{fid}({name})" for fid, name in canonical)
            failures.append(
                f"UNLABELED-DUPLICATE-PAIR identity class `{ctype[:60]}...` has "
                f"{len(canonical)} canonical (unmarked) facts: {names} -- exactly "
                f"one must carry no `equivalent_to` and the rest must point at it"
            )
    return GuardResult("unlabeled_duplicate_pair", scanned, hits, failures)


def guard_no_canonical_designated(
    class_facts: dict[str, list[tuple[str, str, bool]]],
) -> GuardResult:
    failures = []
    hits = 0
    scanned = 0
    for ctype, members in sorted(class_facts.items()):
        if len(members) < 2:
            continue
        scanned += 1
        canonical = [m for m in members if not m[2]]
        if len(canonical) == 0:
            hits += 1
            names = ", ".join(f"{fid}({name})" for fid, name, _ in members)
            failures.append(
                f"NO-CANONICAL-DESIGNATED identity class `{ctype[:60]}...` has "
                f"{len(members)} facts, ALL carrying `equivalent_to` -- {names}. "
                f"Exactly one member must be the canonical survivor"
            )
    return GuardResult("no_canonical_designated", scanned, hits, failures)


def guard_equivalent_to_target_absent(
    facts: dict[str, dict[str, Any]]
) -> GuardResult:
    failures = []
    hits = 0
    scanned = 0
    for fid, data in sorted(facts.items()):
        eq = data.get("equivalent_to") or []
        if not eq:
            continue
        scanned += 1
        target = eq[0]
        if target not in facts:
            hits += 1
            failures.append(
                f"EQUIVALENT-TO-TARGET-ABSENT {fid} names `{target}`, which is "
                f"not a fact in the ledger"
            )
    return GuardResult("equivalent_to_target_absent", scanned, hits, failures)


def guard_equivalent_to_target_unsettled(
    facts: dict[str, dict[str, Any]]
) -> GuardResult:
    failures = []
    hits = 0
    scanned = 0
    for fid, data in sorted(facts.items()):
        eq = data.get("equivalent_to") or []
        if not eq:
            continue
        target = eq[0]
        if target not in facts:
            continue
        scanned += 1
        status = facts[target].get("epistemic_status")
        if status not in SETTLED:
            hits += 1
            failures.append(
                f"EQUIVALENT-TO-TARGET-UNSETTLED {fid} points at `{target}`, "
                f"whose epistemic_status is {status!r}, not in {sorted(SETTLED)}"
            )
    return GuardResult("equivalent_to_target_unsettled", scanned, hits, failures)


def guard_equivalent_to_chain(facts: dict[str, dict[str, Any]]) -> GuardResult:
    failures = []
    hits = 0
    scanned = 0
    for fid, data in sorted(facts.items()):
        eq = data.get("equivalent_to") or []
        if not eq:
            continue
        target = eq[0]
        if target not in facts:
            continue
        scanned += 1
        target_eq = facts[target].get("equivalent_to") or []
        if target_eq:
            hits += 1
            failures.append(
                f"EQUIVALENT-TO-CHAIN {fid} -> {target} -> {target_eq[0]}: the "
                f"target must be terminal (canonical), never itself marked"
            )
    return GuardResult("equivalent_to_chain", scanned, hits, failures)


def guard_equivalent_to_different_proposition(
    facts: dict[str, dict[str, Any]],
    decls: dict[str, Any],
    tc: Any,
    depends_derived: Any,
) -> GuardResult:
    failures = []
    hits = 0
    scanned = 0
    for fid, data in sorted(facts.items()):
        eq = data.get("equivalent_to") or []
        if not eq:
            continue
        target = eq[0]
        if target not in facts:
            continue
        own_subject = resolve_subject(data, decls, tc, depends_derived)
        target_subject = resolve_subject(facts[target], decls, tc, depends_derived)
        if own_subject is None or target_subject is None:
            continue
        if own_subject not in decls or target_subject not in decls:
            continue
        scanned += 1
        own_type = decls[own_subject].canonical_type
        target_type = decls[target_subject].canonical_type
        if own_type != target_type:
            hits += 1
            failures.append(
                f"EQUIVALENT-TO-DIFFERENT-PROPOSITION {fid} (`{own_subject}`) "
                f"claims equivalence to {target} (`{target_subject}`), but their "
                f"canonical kernel types differ -- this is not a restatement"
            )
    return GuardResult("equivalent_to_different_proposition", scanned, hits, failures)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--projection", type=pathlib.Path, default=None)
    parser.add_argument("--facts", type=pathlib.Path, default=DEFAULT_FACTS)
    parser.add_argument("--population", type=pathlib.Path, default=DEFAULT_POPULATION)
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    tc = _load_trust_closure_module()
    depends_derived = tc._load_depends_derived_module()
    decls = tc.parse_projection(tc.projection_rows(args.projection))
    classes = tc.identity_classes(decls)
    facts = load_facts(args.facts)

    pinned: dict[str, Any] = {}
    if args.population.exists():
        pinned = json.loads(args.population.read_text(encoding="utf-8"))
    floor = int(pinned.get("min_identity_classes", 0)) or FLOOR_DEFAULT

    if args.update:
        args.population.parent.mkdir(parents=True, exist_ok=True)
        new_floor = max(floor, len(classes))
        args.population.write_text(
            json.dumps(
                {
                    "generated_by": "scripts/check-proposition-duplication.py --update",
                    "min_identity_classes": new_floor,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        floor = new_floor

    # Build per-class fact membership: canonical type -> [(fact_id, decl_name, marked)]
    member_type = class_membership(classes)
    class_facts: dict[str, list[tuple[str, str, bool]]] = {}
    settled_count = 0
    equivalent_count = 0
    for fid, data in sorted(facts.items()):
        status = data.get("epistemic_status")
        if status in SETTLED:
            settled_count += 1
            if data.get("equivalent_to"):
                equivalent_count += 1
        if status not in SETTLED:
            continue
        if data.get("proof_route") not in tc.KERNEL_ROUTES:
            continue
        subject = resolve_subject(data, decls, tc, depends_derived)
        if subject is None or subject not in member_type:
            continue
        ctype = member_type[subject]
        marked = bool(data.get("equivalent_to"))
        class_facts.setdefault(ctype, []).append((fid, subject, marked))

    results = [
        guard_identity_classes_empty(classes),
        guard_identity_classes_below_floor(classes, floor),
        guard_unlabeled_duplicate_pair(class_facts),
        guard_no_canonical_designated(class_facts),
        guard_equivalent_to_target_absent(facts),
        guard_equivalent_to_target_unsettled(facts),
        guard_equivalent_to_chain(facts),
        guard_equivalent_to_different_proposition(facts, decls, tc, depends_derived),
    ]

    failures: list[str] = []
    for r in results:
        failures.extend(r.failures)

    distinct = settled_count - equivalent_count
    duplicate_classes = sum(1 for v in class_facts.values() if len(v) >= 2)

    summary = {
        "identity_classes": len(classes),
        "duplicate_classes": duplicate_classes,
        "settled_facts": settled_count,
        "equivalent_facts": equivalent_count,
        "distinct_propositions": distinct,
        "failures": len(failures),
    }

    if args.json:
        print(json.dumps(summary, sort_keys=True))
    else:
        print(
            "PROPOSITION_DUPLICATION|identity_classes={identity_classes}|"
            "duplicate_classes={duplicate_classes}|settled_facts={settled_facts}|"
            "equivalent_facts={equivalent_facts}|"
            "distinct_propositions={distinct_propositions}|"
            "failures={failures}".format(**summary)
        )
        for result in results:
            print(
                f"  guard {result.name:36s} scanned={result.scanned:6d} "
                f"rejected={result.hits}"
            )
    for failure in failures:
        print(f"PROPOSITION_DUPLICATION_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
