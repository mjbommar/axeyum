#!/usr/bin/env python3
"""What to work on next, read off the fact ledger.

`validate-facts.py` says whether the ledger is *consistent*. This says what it is
*for*: the end-to-end path from an established foundation to a new result, with
the next move named at every point on it.

Until now nothing consumed `artifacts/facts/` except the validator, so "pick an
open fact whose dependencies are established and dispatch it" -- the loop the
schema is designed around -- existed only in somebody's head. A ledger nothing
selects from is a record, not a queue.

The four bands, in the order the flow runs:

  RESEARCH FRONTIER  open to us AND unsettled in the literature, dependencies
                     established. Genuinely new mathematics if closed. This is
                     the band the project exists to grow.
  IMPORT BACKLOG     open to us, settled elsewhere. Real work, but formalization
                     rather than discovery -- and it must NOT be confused with
                     the frontier, or the loop burns its queue re-deriving the
                     literature. That confusion is why `external_status` exists.
  BLOCKED            open, with dependencies not yet established. Prints what is
                     missing, because those dependencies are the actual next
                     task -- this is where "established foundation" turns into a
                     work order.
  ESTABLISHED HERE, NOT THERE   already closed by us and unsettled outside. The
                     output. Reported so the count is visible rather than
                     anecdotal.

How a fact could be attacked is reported separately from how interesting it is,
in three classes rather than two: DECIDABLE (a procedure we have terminates —
dispatch it), proof-route-only (quantified over an infinite domain, so only a
kernel proof can close it, and saying a route exists is not saying it is
feasible), and no route at all. Collapsing the first two is how a queue comes to
rank Goldbach's conjecture beside a finite colouring problem.

Usage:
    python3 scripts/fact-frontier.py            # the queue
    python3 scripts/fact-frontier.py --band research
    python3 scripts/fact-frontier.py --unlocks  # what each open fact would free
    python3 scripts/fact-frontier.py --json     # content-addressed scheduler input
    python3 scripts/fact-frontier.py --output frontier.json
    python3 scripts/fact-frontier.py --verify frontier.json
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from collections import defaultdict
import pathlib
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
FACTS = ROOT / "artifacts" / "facts"
OPERATIONS = ROOT / "artifacts" / "autogenesis" / "operations.json"
OPERATION_VALIDATOR = ROOT / "scripts" / "validate-autogenesis-operations.py"
CHAIN_CATALOG = ROOT / "scripts" / "create-autogenesis-chain-catalog.py"

# A status asserting we settled it. `axiom` counts: a dependency taken as an
# axiom is available to build on, whatever one thinks of taking it.
SETTLED = {"proved", "computed", "refuted", "axiom"}
# Unsettled in the wider literature. `None` cannot appear once the ledger is
# fully classified, but is treated as unknown rather than as an opportunity --
# an unclassified fact is an unchecked one, and guessing in the optimistic
# direction is how a backlog item gets mistaken for a discovery.
EXTERNAL_UNSETTLED = {"open", "conjectured"}

# How a fact could be attacked, which is NOT the same question as which fragment
# it is written in.
#
# The first version of this file conflated them: it held one DISPATCHABLE set
# containing both `QF_BV` and `Nat`, and so reported Goldbach's conjecture as
# "dispatchable" because its fragment string is `Nat`. Nothing finite settles a
# universal over an infinite domain. A queue that ranks Goldbach beside a
# 625-vertex colouring problem is worse than no queue, and it is the same
# overstatement this repository keeps finding in its own tools -- so the
# distinction is structural here, not a footnote.
#
# DECIDABLE   a decision procedure we have terminates on it. Dispatch and wait.
#
# This is a SEED, not the answer. An authored list of our own capabilities goes
# stale in the direction that hurts most: it under-reports what we can do, and a
# lane reading "NO ROUTE" skips work that is in fact dispatchable. That is not
# hypothetical -- `QF_FP` was missing here while `F:fp8-add-monotone-rne`, whose
# fragment is `QF_FP`, was sitting in the ledger PROVED on `smt-clausal`. The
# tool contradicted the evidence in the very file it was reading.
#
# So the seed is augmented by DEMONSTRATION below: any fragment in which we have
# already settled a fact on a terminating route is decidable by us, and the
# ledger is the record of that. Same rule the axiom ledger just adopted in
# ADR-0465 -- derive the number from the measurement rather than authoring it.
DECIDABLE_SEED = {"QF_BV", "QF_LIA", "QF_LRA", "QF_NIA", "QF_NRA", "QF_UF",
                  "QF_UFLIA", "QF_ABV", "QF_SLIA", "UF"}

# Routes that terminate. A fact settled on one of these is a demonstration that
# its fragment is reachable by search. `kernel-lean` is deliberately EXCLUDED:
# a hand-built kernel proof of a Nat theorem says nothing about any procedure
# terminating, and admitting it here would reintroduce the exact conflation the
# note above describes -- Goldbach's fragment would become "decidable" the moment
# any Nat theorem was proved.
TERMINATING_ROUTES = {"smt-clausal", "smt-term-level", "search-certificate",
                      "cas-certificate"}

# Sentinels that are NOT fragments and must never be admitted, however they were
# settled. `none` means "no fragment applies", so treating it as a capability is
# a category error -- and it is not a theoretical one. The demonstration rule
# above, on its first run, admitted `none` because a conjunctive-query-containment
# fact carries `fragment: "none"` and was settled by `search-certificate`. The
# immediate consequence, printed on screen, was:
#
#     F:collatz-reaches-one    none    DECIDABLE -- dispatch it
#
# which is the exact overstatement the header of this file was written about,
# reintroduced within minutes by the fix for a DIFFERENT overstatement. A rule
# that derives capability from evidence still has to know what counts as evidence.
NOT_A_FRAGMENT = {"none", "None", "unknown", "", None}
# PROOF_ROUTE quantified over an infinite domain: reachable only by constructing
#             a proof in the kernel (induction, a lemma chain), never by search.
#             Being in this class says a route EXISTS, not that it is feasible --
#             Goldbach lives here and will not be closed by it.
PROOF_ROUTE = {"Nat", "Int", "Real"}
# Anything else, `none` included, has no route at all today.

class FrontierError(RuntimeError):
    """A machine frontier artifact is stale, malformed, or unsafe to use."""


def canonical_json(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def digest(value: Any) -> str:
    return hashlib.sha256(canonical_json(value).encode()).hexdigest()


def operation_validator_module():
    spec = importlib.util.spec_from_file_location(
        "validate_autogenesis_operations_for_frontier", OPERATION_VALIDATOR
    )
    if spec is None or spec.loader is None:
        raise FrontierError(f"cannot load {OPERATION_VALIDATOR}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_operation_registry() -> dict[str, Any]:
    module = operation_validator_module()
    try:
        return module.load_registry(OPERATIONS, ROOT)
    except (OSError, json.JSONDecodeError, module.RegistryError) as error:
        raise FrontierError(f"operation registry invalid: {error}") from error


def validate_operation_registry(registry: dict[str, Any]) -> None:
    module = operation_validator_module()
    try:
        module.validate_registry(registry, ROOT)
    except module.RegistryError as error:
        raise FrontierError(f"operation registry invalid: {error}") from error


def load() -> dict[str, dict]:
    facts = {}
    for path in sorted(FACTS.glob("*.json")):
        d = json.loads(path.read_text())
        if d["id"] in facts:
            raise FrontierError(f"duplicate fact id {d['id']!r}")
        facts[d["id"]] = d
    return facts


def settled(fact: dict) -> bool:
    return fact["epistemic_status"] in SETTLED


def decidable_fragments(facts: dict[str, dict]) -> tuple[set[str], dict[str, str]]:
    """Seed plus every fragment we have DEMONSTRABLY settled by a terminating route.

    Returns the set and, for anything admitted by demonstration rather than by
    the seed, the fact that demonstrates it -- so the report can show its work
    instead of asserting a capability.
    """
    admitted = set(DECIDABLE_SEED)
    why: dict[str, str] = {}
    for fact in facts.values():
        if not settled(fact):
            continue
        if fact.get("proof_route") not in TERMINATING_ROUTES:
            continue
        frag = fact["formal"]["fragment"]
        if frag in NOT_A_FRAGMENT:
            continue
        if frag not in admitted:
            admitted.add(frag)
            why[frag] = fact["id"]
        elif frag not in DECIDABLE_SEED and frag not in why:
            why[frag] = fact["id"]
    return admitted, why


def band(fact: dict, facts: dict[str, dict]) -> str:
    status = fact["epistemic_status"]
    external = fact.get("external_status")
    if status in SETTLED:
        return "novel" if external in EXTERNAL_UNSETTLED else "done"
    if status not in {"open", "conjectured", "empirical"}:
        return "done"
    unmet = [d for d in fact["depends_on"] if d not in facts or not settled(facts[d])]
    if unmet:
        return "blocked"
    return "research" if external in EXTERNAL_UNSETTLED else "backlog"


def gate_holds(facts: dict[str, dict]) -> dict[str, list[str]]:
    """`fact id -> [gate script that would break if it closed]`.

    DERIVED by scanning `scripts/` for fact ids, not recorded in the fact. A
    fact does not know what depends on it, and asking authors to remember is the
    same losing bet as hand-written `depends_on`.

    The case this exists for is live. `F:no-integer-square-is-minus-one` is the
    NEGATIVE CONTROL of `check-smt-evidence-certified.py`: it must stay `open`
    and uncertified, because a certification gate whose control has become
    certifiable is no longer testing anything. This queue reported it as
    "DECIDABLE — dispatch it", which is true and, taken alone, an instruction to
    break a gate. Closing it is FINE — the gate says so itself, in the failure it
    raises — but only together with repointing the control at another
    uncertified instance. That coupling was written in the checker and nowhere a
    person picking work would look.

    This is a TEXT SCAN, so it over-reports: a script that merely quotes a fact
    id as a documentation example is flagged alongside one that genuinely reads
    it. That is the right direction to be wrong in — the cost of checking a
    script is small, and the cost of silently closing a gate's control is a gate
    that no longer tests anything. The message says "check", not "breaks".
    """
    held: dict[str, list[str]] = {}
    scripts = ROOT / "scripts"
    for path in sorted(scripts.glob("*.py")) + sorted(scripts.glob("*.sh")):
        # Skip this file: naming the example in the docstring above would
        # otherwise make the queue report itself as a gate the fact backs.
        if path.name == pathlib.Path(__file__).name:
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except OSError:
            continue
        for ident in facts:
            # The bare id, or its instance-file spelling (`F:a-b` -> `a-b.smt2`).
            stem = ident.removeprefix("F:")
            if ident in text or f"{stem}.smt2" in text:
                held.setdefault(ident, []).append(path.name)
    return held


def describe(fact: dict, facts: dict[str, dict], show_unlocks: bool,
             unlocks: dict[str, list[str]], decidable: set[str],
             held: dict[str, list[str]] | None = None) -> str:
    frag = fact["formal"]["fragment"]
    if frag in decidable:
        reach = "DECIDABLE — dispatch it"
    elif frag in PROOF_ROUTE:
        reach = "proof route only — needs a kernel proof, no search will close it"
    else:
        reach = f"NO ROUTE (fragment {frag!r})"
    line = f"  {fact['id']:<40} {frag:<8} {reach}"
    unmet = [d for d in fact["depends_on"] if d not in facts or not settled(facts[d])]
    if unmet:
        line += f"\n      needs first: {', '.join(unmet)}"
    if show_unlocks and unlocks.get(fact["id"]):
        line += f"\n      would unlock: {', '.join(unlocks[fact['id']])}"
    for gate in (held or {}).get(fact["id"], []):
        line += (f"\n      ⚠ NAMED BY {gate} — check that script before closing this. "
                 "It may be load-bearing there (a gate's negative control), or merely "
                 "quoted as an example.")
    return line


def route_class(fragment: str, decidable: set[str]) -> str:
    if fragment in decidable:
        return "decidable"
    if fragment in PROOF_ROUTE:
        return "proof-route-only"
    return "no-route"


def matching_operations(
    fact: dict[str, Any], operations: list[dict[str, Any]]
) -> list[str]:
    formal = fact["formal"]
    return sorted(
        operation["id"]
        for operation in operations
        if operation["scope"] == "authoritative"
        and fact["id"] in operation["applicability"]["fact_ids"]
        and formal["language"] in operation["applicability"]["formal_languages"]
        and formal["fragment"] in operation["applicability"]["fragments"]
    )


def build_machine_frontier(
    facts: dict[str, dict], registry: dict[str, Any] | None = None
) -> dict[str, Any]:
    """Build the content-addressed authoritative queue and selection refusal.

    This snapshot deliberately distinguishes dependency readiness, broad route
    reachability, and an admissible registered operation. Only the last of those
    licenses autonomous dispatch.
    """
    if registry is None:
        registry = load_operation_registry()
    else:
        validate_operation_registry(registry)
    operations = registry["operations"]
    held = gate_holds(facts)
    decidable, demonstrated_by = decidable_fragments(facts)
    unlocks: dict[str, list[str]] = defaultdict(list)
    for fact in facts.values():
        if settled(fact):
            continue
        for dependency in fact["depends_on"]:
            unlocks[dependency].append(fact["id"])

    entries: list[dict[str, Any]] = []
    for fact_id in sorted(facts):
        fact = facts[fact_id]
        fact_band = band(fact, facts)
        if fact_band == "done":
            continue
        missing = sorted(
            dependency
            for dependency in fact["depends_on"]
            if dependency not in facts or not settled(facts[dependency])
        )
        fragment = fact["formal"]["fragment"]
        registered_operation_ids = matching_operations(fact, operations)
        reviewed_gate_mentions = {
            mention
            for operation in operations
            if operation["id"] in registered_operation_ids
            for mention in operation.get("reviewed_gate_mentions", [])
        }
        gate_mentions = set(held.get(fact_id, []))
        entries.append(
            {
                "fact_id": fact_id,
                "fact_sha256": digest(fact),
                "epistemic_status": fact["epistemic_status"],
                "external_status": fact.get("external_status"),
                "fragment": fragment,
                "band": fact_band,
                "dependency_ready": not missing,
                "missing_dependencies": missing,
                "route_class": route_class(fragment, decidable),
                "registered_operation_ids": registered_operation_ids,
                "gate_mentions": sorted(gate_mentions),
                "unreviewed_gate_mentions": sorted(
                    gate_mentions.difference(reviewed_gate_mentions)
                ),
                "stale_reviewed_gate_mentions": sorted(
                    reviewed_gate_mentions.difference(gate_mentions)
                ),
                "would_unlock": sorted(unlocks.get(fact_id, [])),
            }
        )

    priority = {"research": 0, "backlog": 1}
    considered = sorted(
        (
            entry
            for entry in entries
            if entry["band"] in priority and entry["dependency_ready"]
        ),
        key=lambda entry: (priority[entry["band"]], entry["fact_id"]),
    )
    rationale = []
    admissible = []
    for entry in considered:
        reasons = []
        if entry["route_class"] == "no-route":
            reasons.append("no-supported-route")
        if not entry["registered_operation_ids"]:
            reasons.append("no-registered-operation")
        elif len(entry["registered_operation_ids"]) != 1:
            reasons.append("ambiguous-registered-operation")
        if entry["unreviewed_gate_mentions"]:
            reasons.append("gate-coupling-review-required")
        if entry["stale_reviewed_gate_mentions"]:
            reasons.append("stale-gate-coupling-review")
        rationale.append({"fact_id": entry["fact_id"], "rejected_by": reasons})
        if not reasons:
            admissible.append(entry["fact_id"])

    artifact: dict[str, Any] = {
        "schema_version": 1,
        "kind": "axeyum-fact-frontier",
        "authority": "artifacts/facts",
        "ledger": {
            "fact_count": len(facts),
            "ledger_sha256": digest(
                [
                    {"fact_id": fact_id, "fact_sha256": digest(facts[fact_id])}
                    for fact_id in sorted(facts)
                ]
            ),
        },
        "policy": {
            "band_order": ["research", "backlog"],
            "fact_order": "lexicographic-fact-id",
            "settled_statuses": sorted(SETTLED),
            "terminating_routes": sorted(TERMINATING_ROUTES),
            "proof_route_fragments": sorted(PROOF_ROUTE),
            "operation_registry_sha256": digest(registry),
            "registered_operations": sorted(
                operation["id"] for operation in operations
            ),
            "autonomous_dispatch_requires_registered_operation": True,
        },
        "capabilities": {
            "decidable_fragments": sorted(decidable),
            "demonstrated_by": {
                fragment: demonstrated_by[fragment]
                for fragment in sorted(demonstrated_by)
            },
        },
        "entries": entries,
        "selection": {
            "ready_fact_ids": [entry["fact_id"] for entry in considered],
            "admissible_fact_ids": admissible,
            "selected_fact_id": admissible[0] if admissible else None,
            "outcome": "selected" if admissible else "refused-no-admissible-candidate",
            "rationale": rationale,
        },
    }
    artifact["frontier_sha256"] = digest(artifact)
    return artifact


def verify_machine_frontier(actual: dict[str, Any], facts: dict[str, dict]) -> None:
    claimed = actual.get("frontier_sha256")
    unsigned = dict(actual)
    unsigned.pop("frontier_sha256", None)
    if not isinstance(claimed, str) or digest(unsigned) != claimed:
        raise FrontierError("frontier digest is missing or invalid")
    expected = build_machine_frontier(facts)
    if actual != expected:
        raise FrontierError("frontier is stale or does not match the authoritative ledger")


def print_chains(facts: dict) -> int:
    """Settled `B -> A` pairs where A's dependency on B can be RE-DERIVED.

    The Autogenesis programme's first demonstration is: prove B, observe that B
    unlocks A, prove A. Selecting such a chain (its task S0.2) needs pairs whose
    dependency is not merely asserted in a JSON field but readable from the proof
    term — otherwise "B unlocks A" is a claim about the ledger rather than about
    the mathematics.

    Only the `kernel-lean` route qualifies, and that is a measurement, not a
    preference. `scripts/check-fact-depends-derived.py` reads a fact's real
    dependencies out of `Kernel::theorem_dependencies`; for `smt-term-level`,
    `cas-certificate`, `smt-clausal` and `search-certificate` there is no proof
    term to read, so a `depends_on` there is a human assertion.

    Merely filtering authored `depends_on` rows by route is insufficient: the
    dependency checker permits extra mathematical dependencies that the chosen
    proof did not use. This view therefore intersects the ledger edge with the
    kernel's direct theorem-dependency inventory. The content-addressed catalog
    is the scheduler-facing form; this remains its compact human view.
    """
    spec = importlib.util.spec_from_file_location(
        "autogenesis_chain_catalog_for_frontier", CHAIN_CATALOG
    )
    if spec is None or spec.loader is None:
        raise FrontierError(f"cannot load {CHAIN_CATALOG}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    dependencies = module.dependency_module()
    try:
        catalog = module.build_catalog(facts, dependencies.inventory(), dependencies.theorem_of)
    except module.ChainCatalogError as error:
        raise FrontierError(f"proof-derived chain catalog failed: {error}") from error
    coverage = catalog["coverage"]
    print(
        f"  named kernel-lean facts: {coverage['named_kernel_facts']}   "
        f"proof-derived B -> A edges: {coverage['proof_derived_edges']}   "
        f"distinct A: {coverage['distinct_consequents']}"
    )
    print("  (only kernel-lean: elsewhere a `depends_on` is asserted, not derivable)")
    current_a = None
    for candidate in sorted(
        catalog["candidates"],
        key=lambda row: (
            -row["rank"]["consequent_depth"],
            row["consequent"]["fact_id"],
            row["premise"]["fact_id"],
        ),
    ):
        consequent = candidate["consequent"]["fact_id"]
        if consequent != current_a:
            print(f"    depth {candidate['rank']['consequent_depth']}  {consequent}")
            current_a = consequent
        print(f"              <- {candidate['premise']['fact_id']}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--band", choices=["research", "backlog", "blocked", "novel"])
    ap.add_argument("--unlocks", action="store_true",
                    help="show which open facts each entry would unblock")
    machine = ap.add_mutually_exclusive_group()
    machine.add_argument("--json", action="store_true",
                         help="write the content-addressed machine frontier to stdout")
    machine.add_argument("--output", type=Path,
                         help="write the machine frontier to a new file")
    machine.add_argument("--verify", type=Path,
                         help="verify a saved machine frontier against the ledger")
    machine.add_argument("--chains", action="store_true",
                         help="enumerate settled B -> A pairs whose dependency is DERIVABLE")
    args = ap.parse_args()

    if not FACTS.is_dir():
        print("fact-frontier: no artifacts/facts/ directory", file=sys.stderr)
        return 2
    try:
        facts = load()
    except (OSError, json.JSONDecodeError, KeyError, FrontierError) as error:
        print(f"FACT_FRONTIER_ERROR|{error}", file=sys.stderr)
        return 1
    if (args.json or args.output or args.verify or args.chains) and (args.band or args.unlocks):
        ap.error("machine frontier modes cannot be combined with --band or --unlocks")
    if args.json or args.output or args.verify:
        try:
            artifact = build_machine_frontier(facts)
            if args.verify:
                verify_machine_frontier(json.loads(args.verify.read_text()), facts)
                print(f"FACT_FRONTIER_OK|{artifact['frontier_sha256']}")
            elif args.output:
                if args.output.exists():
                    raise FrontierError(f"refusing to overwrite {args.output}")
                args.output.parent.mkdir(parents=True, exist_ok=True)
                args.output.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n")
                print(f"FACT_FRONTIER|{artifact['frontier_sha256']}|{args.output}")
            else:
                print(json.dumps(artifact, indent=2, sort_keys=True))
            return 0
        except (OSError, json.JSONDecodeError, FrontierError) as error:
            print(f"FACT_FRONTIER_ERROR|{error}", file=sys.stderr)
            return 1
    held = gate_holds(facts)

    if args.chains:
        try:
            return print_chains(facts)
        except FrontierError as error:
            print(f"FACT_FRONTIER_ERROR|{error}", file=sys.stderr)
            return 1

    # Reverse dependency edges: proving X frees everything that names X.
    unlocks: dict[str, list[str]] = defaultdict(list)
    for fact in facts.values():
        if fact["epistemic_status"] in SETTLED:
            continue
        for dep in fact["depends_on"]:
            unlocks[dep].append(fact["id"])

    bands: dict[str, list[dict]] = defaultdict(list)
    for fact in facts.values():
        bands[band(fact, facts)].append(fact)

    decidable_set, admitted_by = decidable_fragments(facts)

    titles = {
        "research": "RESEARCH FRONTIER — open to us and unsettled in the literature",
        "backlog": "IMPORT BACKLOG — settled elsewhere, not here (formalization, not discovery)",
        "blocked": "BLOCKED — open, but a dependency is not established yet",
        "novel": "ESTABLISHED HERE, NOT IN THE LITERATURE — the output",
    }
    for key in ("research", "blocked", "backlog", "novel"):
        if args.band and args.band != key:
            continue
        rows = sorted(bands.get(key, []), key=lambda f: f["id"])
        print(f"\n{titles[key]}  [{len(rows)}]")
        if not rows:
            print("  (none)")
            continue
        for fact in rows:
            print(describe(fact, facts, args.unlocks, unlocks, decidable_set, held))

    if not args.band:
        research = bands.get("research", [])
        decidable = [f for f in research if f["formal"]["fragment"] in decidable_set]
        proofish = [f for f in research if f["formal"]["fragment"] in PROOF_ROUTE]
        print(f"\n{len(facts)} facts. Research frontier {len(research)}: "
              f"{len(decidable)} decidable by dispatch, {len(proofish)} needing a "
              f"kernel proof, {len(research) - len(decidable) - len(proofish)} with "
              f"no route.")
        if decidable:
            print("Dispatch next: " + ", ".join(f["id"] for f in sorted(
                decidable, key=lambda f: f["id"])))
        if admitted_by:
            # Show the work rather than asserting the capability: each of these
            # fragments is called decidable because a settled fact demonstrates it.
            print("\nDecidable by demonstration (not by the authored seed):")
            for frag in sorted(admitted_by):
                print(f"  {frag:<10} demonstrated by {admitted_by[frag]}")
        if not research:
            print("The frontier is EMPTY. That is not success -- it means nothing in "
                  "the ledger is both unsettled outside and open here, so the next "
                  "move is to extract or state new propositions, not to solve.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
