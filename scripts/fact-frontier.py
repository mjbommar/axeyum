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

# ADR-0602: a producer contract is a CAPABILITY CLAIM ("facts matching this
# shape are dischargeable via route R"), never a completion claim -- unlike an
# operation, which is a retrospective receipt requiring `epistemic_status:
# "proved"` on every admission arm (doc 288 measured this is exactly why
# admissible stayed 0 while ready stayed 132: nothing prospective can enter a
# system built to certify completed work). `matching_operations` below still
# answers "has this already been discharged and receipted"; `matching_contracts`
# answers a different, new question: "could this be attempted, and by which
# route". Both are read; the two must not be conflated into one count, or the
# ADR's whole distinction collapses back into doc 262's original confusion.
PRODUCER_CONTRACTS_DIR = ROOT / "artifacts" / "autogenesis" / "producer-contracts"
PRODUCER_CONTRACT_VALIDATOR = ROOT / "scripts" / "validate-producer-contracts.py"
CONTRACT_ROUTES = {"kernel-lane", "cas-bridge", "import"}

# Route-capability artifacts, per ADR-0601 SS4 / ADR-0602 SS3. `kernel-lane` is
# always capable (a proving lane always exists in principle). `cas-bridge` and
# `import` are sibling lanes' deliverables, still in flight as of this ADR --
# checking for the artifact rather than importing the sibling lane's module
# keeps this file buildable independently of when either lands, and ABSENT is
# the correct, unsurprising answer until they do. Never raise on absence: an
# optional input that has not landed yet is not this file's error.
CAS_BRIDGE_MANIFEST = ROOT / "artifacts" / "autogenesis" / "cas-bridge-manifest.json"
IMPORT_BACKLOG = ROOT / "artifacts" / "import-backlog.json"

# Doc 291: the first real contract dispatch (doc 290) matched a contract,
# imported cleanly, and the producer honestly DECLINED. Recorded as
# `artifacts/autogenesis/mathlib-int-add-modeq-left-decline-v1.json`, but
# nothing read it back -- so `admissible` kept counting a `(fact, contract)`
# pair a producer had already tried and refused, and the selector would loop
# on it forever. A decline is scoped to the EXACT contract version that
# produced it (`contract_sha256`): editing the contract's recipe/shape is
# what re-opens a fact it previously declined, never a manual clear.
PRODUCER_CONTRACT_DECLINE_VALIDATOR = ROOT / "scripts" / "validate-producer-contract-declines.py"

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


def contract_validator_module():
    spec = importlib.util.spec_from_file_location(
        "validate_producer_contracts_for_frontier", PRODUCER_CONTRACT_VALIDATOR
    )
    if spec is None or spec.loader is None:
        raise FrontierError(f"cannot load {PRODUCER_CONTRACT_VALIDATOR}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_producer_contracts() -> list[dict[str, Any]]:
    """Load and validate `artifacts/autogenesis/producer-contracts/*.json`.

    Validated the same way the operation registry is: through the dedicated
    validator module, never re-implemented here, and -- matching how the
    operation validator always resolves a fact id against the real
    `artifacts/facts/*.json` file on disk rather than whatever `facts` dict a
    caller happens to be iterating over -- always against the REAL committed
    fact ledger, never against a caller's `facts` argument. A contract's
    falsifiability (does its non-example resolve and fail the predicate? does
    the predicate avoid swallowing every open fact?) is a property of the
    contract and the real ledger; it must not depend on which subset of facts
    a particular `build_machine_frontier` call happens to be considering, or
    a test exercising a synthetic 3-fact ledger would spuriously fail contract
    validation for a real, valid, committed contract.

    An empty directory is not an error -- a lane may run this before any
    contract has landed, and "zero contracts" is a fact about the ledger's
    current state, not a malformed input.
    """
    module = contract_validator_module()
    try:
        real_facts = module.load_facts()
        return module.validate_contracts_dir(PRODUCER_CONTRACTS_DIR, facts=real_facts)
    except (OSError, json.JSONDecodeError, module.ContractError) as error:
        raise FrontierError(f"producer contract registry invalid: {error}") from error


def validate_producer_contracts(contracts: list[dict[str, Any]]) -> None:
    """Validate an explicitly-supplied contract list, against the REAL
    ledger -- see `load_producer_contracts` for why."""
    module = contract_validator_module()
    try:
        real_facts = module.load_facts()
        for contract in contracts:
            module.validate_contract(contract, real_facts)
        ids = [contract["id"] for contract in contracts]
        if len(ids) != len(set(ids)):
            raise module.ContractError("duplicate producer contract id in supplied list")
    except module.ContractError as error:
        raise FrontierError(f"producer contract registry invalid: {error}") from error


def decline_validator_module():
    spec = importlib.util.spec_from_file_location(
        "validate_producer_contract_declines_for_frontier", PRODUCER_CONTRACT_DECLINE_VALIDATOR
    )
    if spec is None or spec.loader is None:
        raise FrontierError(f"cannot load {PRODUCER_CONTRACT_DECLINE_VALIDATOR}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_decline_artifacts() -> list[dict[str, Any]]:
    """Load and validate every contract-driven decline artifact under
    `artifacts/autogenesis/` (doc 291).

    Same reasoning as `load_producer_contracts`: validated through the
    dedicated validator module, never re-implemented here, and always against
    the REAL committed fact ledger -- a decline's falsifiability (does its
    `fact_id` resolve? does its `contract` resolve?) is a property of the real
    ledger, not of whatever subset of facts a particular
    `build_machine_frontier` call happens to be considering.

    An empty result is not an error -- most trees will have zero, one, or a
    handful of contract-driven declines, and "no declines yet" is a fact
    about the ledger's current state, not a malformed input.
    """
    module = decline_validator_module()
    try:
        real_facts = module.load_facts()
        return module.validate_declines_dir(facts=real_facts)
    except (OSError, json.JSONDecodeError, module.DeclineError) as error:
        raise FrontierError(f"producer contract decline registry invalid: {error}") from error


def validate_decline_artifacts(declines: list[dict[str, Any]]) -> None:
    """Validate an explicitly-supplied decline list, against the REAL
    ledger -- see `load_decline_artifacts` for why."""
    module = decline_validator_module()
    try:
        real_facts = module.load_facts()
        for decline in declines:
            module.validate_decline(decline, real_facts)
    except module.DeclineError as error:
        raise FrontierError(f"producer contract decline registry invalid: {error}") from error


def live_declined_pairs(
    declines: list[dict[str, Any]], contracts: list[dict[str, Any]]
) -> set[tuple[str, str]]:
    """`(fact_id, contract_id)` pairs with a LIVE decline against them.

    A decline is live only against the EXACT contract version that produced
    it (doc 291's re-dispatch policy): `contract_sha256` must equal the
    CURRENT digest of the contract the decline names. If the contract's
    recipe/shape has since changed (a real capability improvement, not a
    prose edit -- see doc 291), its digest changes and every fact it
    previously declined becomes eligible again with no manual intervention.
    A decline naming a contract that no longer exists at all is likewise not
    live -- there is nothing left for it to suppress admission via.
    """
    contracts_by_id = {contract["id"]: contract for contract in contracts}
    live: set[tuple[str, str]] = set()
    for decline in declines:
        contract_path = ROOT / decline["contract"]
        try:
            referenced = json.loads(contract_path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        contract_id = referenced.get("id")
        current = contracts_by_id.get(contract_id)
        if current is None:
            continue
        if digest(current) == decline["contract_sha256"]:
            live.add((decline["fact_id"], contract_id))
    return live


def route_capability() -> dict[str, bool]:
    """Which ADR-0601 SS4 producer routes can actually be dispatched today.

    `kernel-lane` always can (a proving lane always exists in principle).
    `cas-bridge` and `import` are gated on sibling lanes' own artifacts, which
    may not exist yet in this tree -- absence is read as "not yet capable",
    never as an error, so this file stays buildable independently of when
    either sibling lane lands.
    """
    return {
        "kernel-lane": True,
        "cas-bridge": CAS_BRIDGE_MANIFEST.exists(),
        "import": IMPORT_BACKLOG.exists(),
    }


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


def matching_contracts(
    fact: dict[str, Any], contracts: list[dict[str, Any]], shape_matches
) -> list[str]:
    """Producer contracts whose SHAPE the fact matches (ADR-0602).

    A capability claim, never a completion claim: this says the fact COULD be
    attempted via some route, not that it has been. `shape_matches` is always
    the validator's own function, passed in rather than re-implemented, so the
    frontier and the validator can never silently drift apart on what a shape
    means.
    """
    return sorted(
        contract["id"] for contract in contracts if shape_matches(contract["shape"], fact)
    )


def build_machine_frontier(
    facts: dict[str, dict],
    registry: dict[str, Any] | None = None,
    contracts: list[dict[str, Any]] | None = None,
    declines: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    """Build the content-addressed authoritative queue and selection refusal.

    This snapshot deliberately distinguishes dependency readiness, broad route
    reachability, a RECEIPT (a registered operation, requiring proved work --
    doc 288) and a CONTRACT (a producer's capability claim over open work --
    ADR-0602). Either receipt or contract, together with route capability and a
    clean gate review, licenses autonomous dispatch; the two are read
    separately below and never folded into one count, because folding them is
    exactly the conflation ADR-0602 exists to undo.

    Doc 291 adds a third signal, narrower than either: a DECLINE, a real
    producer attempt against a specific contract that came back honestly
    negative. A decline never widens admission (it cannot make a fact
    admissible); it only narrows the CONTRACT path, and only for the exact
    `(fact, contract)` pair it names while that contract's content matches
    the decline's recorded `contract_sha256` -- see `live_declined_pairs`.

    `contracts=None` means NO contracts, deliberately asymmetric with
    `registry=None` (which auto-loads the real operation registry from disk).
    A caller building a frontier over the full real ledger while overriding
    the operation registry to a controlled subset -- exactly what several
    tests in `scripts/tests/test_fact_frontier.py` do, to isolate one
    operation's effect from the other ~30 real ones -- would otherwise see
    every OTHER seed contract's real matches leak into `admissible_fact_ids`
    with no way to control for it, since there is no third argument in those
    calls to reduce. `main()` and `verify_machine_frontier` are the two call
    sites that need the real, current contract set, and both load it
    explicitly (`load_producer_contracts`) rather than relying on this
    default -- so the CLI's `--json`/`--output`/`--verify` output always
    reflects real contracts, and a caller building a controlled scenario over
    the real ledger is never surprised by one it did not ask for.

    `declines=None` means NO declines, for the identical reason and by the
    identical asymmetry with `registry=None`: a test isolating one contract's
    effect must not have a real, unrelated decline silently subtract from its
    `admissible_fact_ids`. `main()` and `verify_machine_frontier` load the
    real set explicitly (`load_decline_artifacts`).
    """
    if registry is None:
        registry = load_operation_registry()
    else:
        validate_operation_registry(registry)
    operations = registry["operations"]

    contract_module = contract_validator_module()
    if contracts is None:
        contracts = []
    else:
        validate_producer_contracts(contracts)
    if declines is None:
        declines = []
    else:
        validate_decline_artifacts(declines)
    declined_pairs = live_declined_pairs(declines, contracts)
    capable_routes = route_capability()

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
        matched_producer_contract_ids = matching_contracts(
            fact, contracts, contract_module.shape_matches
        )
        producer_contract_route = None
        producer_contract_route_capable = False
        if len(matched_producer_contract_ids) == 1:
            matched_contract = next(
                contract for contract in contracts
                if contract["id"] == matched_producer_contract_ids[0]
            )
            producer_contract_route = matched_contract["route"]
            producer_contract_route_capable = capable_routes.get(
                producer_contract_route, False
            )
        # Doc 291: a matched contract with a LIVE decline against this exact
        # fact does not license admission via that contract -- narrows the
        # CONTRACT path only, never the receipt path, and never widens
        # anything.
        declined_producer_contract_ids = sorted(
            contract_id
            for contract_id in matched_producer_contract_ids
            if (fact_id, contract_id) in declined_pairs
        )
        matched_operations = [
            operation for operation in operations
            if operation["id"] in registered_operation_ids
        ]
        reviewed_gate_mentions = {
            mention
            for operation in matched_operations
            for mention in operation.get("reviewed_gate_mentions", [])
        }
        gate_mentions = set(held.get(fact_id, []))
        # `reviewed_gate_mentions` is authored per OPERATION, over the whole
        # `applicability.fact_ids` it claims -- not per fact. An operation
        # legitimately covering more than one fact (e.g. an Int family and a
        # Nat family merged because their producer/checker/admission/scope are
        # byte-identical) mentions gates that only ever talk about SOME of its
        # facts. Comparing that operation-wide claim against a single fact's
        # own gate mentions makes every fact see the other facts' gates as a
        # stale claim on itself, which is a false positive, not a stale
        # review. So staleness is judged against the SAME scope the review
        # was written over: the union of gate mentions across every fact the
        # matched operation(s) actually name -- a reviewed mention is stale
        # only when no fact under that operation's authority is named by it
        # any more. `unreviewed_gate_mentions` stays a per-fact comparison on
        # purpose: a gate newly naming THIS fact is this fact's problem
        # regardless of what else its operation covers.
        operation_scope_gate_mentions = {
            mention
            for operation in matched_operations
            for scoped_fact_id in operation["applicability"]["fact_ids"]
            for mention in held.get(scoped_fact_id, [])
        }
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
                "matched_producer_contract_ids": matched_producer_contract_ids,
                "producer_contract_route": producer_contract_route,
                "producer_contract_route_capable": producer_contract_route_capable,
                "declined_producer_contract_ids": declined_producer_contract_ids,
                "gate_mentions": sorted(gate_mentions),
                "unreviewed_gate_mentions": sorted(
                    gate_mentions.difference(reviewed_gate_mentions)
                ),
                "stale_reviewed_gate_mentions": sorted(
                    reviewed_gate_mentions.difference(operation_scope_gate_mentions)
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
    # Two independent ways for a fact to be admissible now (ADR-0602): a
    # RECEIPT (exactly one registered operation -- doc 288's retrospective,
    # already-proved path, unchanged) or a CONTRACT (exactly one matched
    # producer contract whose route is actually capable -- the new prospective
    # path). `producer_ok` is deliberately an OR, never a fold of the two into
    # one signal, so the diagnostics below can still tell them apart. Gate
    # review and route reachability apply to EITHER path identically: a fact
    # that would break a gate, or has no supported route at all, is not
    # dispatchable regardless of which producer would take it.
    #
    # The invariant this construction guarantees: `rejected_by` is empty if
    # and only if the entry is admissible. Reasons are only appended inside
    # the branch that actually blocks admission, so an entry admitted via one
    # path never carries a leftover reason from the path it did not need.
    rationale = []
    admissible = []
    admitted_via_operation = 0
    admitted_via_contract = 0
    for entry in considered:
        op_ids = entry["registered_operation_ids"]
        contract_ids = entry["matched_producer_contract_ids"]
        declined_contract_ids = entry["declined_producer_contract_ids"]
        op_ok = len(op_ids) == 1
        contract_ok = (
            len(contract_ids) == 1
            and entry["producer_contract_route_capable"]
            and contract_ids[0] not in declined_contract_ids
        )
        producer_ok = op_ok or contract_ok
        route_ok = entry["route_class"] != "no-route"
        gate_ok = not entry["unreviewed_gate_mentions"] and not entry["stale_reviewed_gate_mentions"]
        is_admissible = producer_ok and route_ok and gate_ok

        reasons = []
        if not route_ok:
            reasons.append("no-supported-route")
        if not producer_ok:
            if not op_ids:
                reasons.append("no-registered-operation")
            elif len(op_ids) != 1:
                reasons.append("ambiguous-registered-operation")
            if not contract_ids:
                reasons.append("no-matched-producer-contract")
            elif len(contract_ids) != 1:
                reasons.append("ambiguous-producer-contract")
            elif not entry["producer_contract_route_capable"]:
                reasons.append("producer-contract-route-unavailable")
            elif contract_ids[0] in declined_contract_ids:
                reasons.append("declined-via-contract")
        if entry["unreviewed_gate_mentions"]:
            reasons.append("gate-coupling-review-required")
        if entry["stale_reviewed_gate_mentions"]:
            reasons.append("stale-gate-coupling-review")
        assert bool(reasons) != is_admissible, (
            "rejected_by must be empty exactly when the entry is admissible"
        )

        rationale.append({"fact_id": entry["fact_id"], "rejected_by": reasons})
        if is_admissible:
            admissible.append(entry["fact_id"])
            if op_ok:
                admitted_via_operation += 1
            if contract_ok:
                admitted_via_contract += 1

    # "no-registered-operation" is one rejection reason, but it hides two very
    # different situations: a fact with NO decision procedure or kernel-proof
    # route at all (registering an operation cannot help until new capability
    # exists), and a fact that IS reachable in principle (decidable by a
    # terminating route, or provable in the kernel) but simply has nothing
    # registered yet. Collapsing them into one count is how "0 admissible" got
    # read as "the registry needs more entries" when the real story is that
    # `route_class` is `no-route` or `proof-route-only` for almost every ready
    # fact -- see docs/autogenesis/ for the measurement this powers. Surfaced
    # here, not just computed ad hoc per report, so the split cannot silently
    # drift from what `route_class` actually says.
    unregistered_by_route: dict[str, int] = defaultdict(int)
    for entry in considered:
        if not entry["registered_operation_ids"]:
            unregistered_by_route[entry["route_class"]] += 1

    # Same split, on the NEW axis ADR-0602 adds: among ready facts with no
    # MATCHED contract at all, how many are stuck on missing math capability
    # versus simply having no contract authored for their shape yet.
    unmatched_by_route: dict[str, int] = defaultdict(int)
    for entry in considered:
        if not entry["matched_producer_contract_ids"]:
            unmatched_by_route[entry["route_class"]] += 1

    # The 6 no-route facts (Collatz, CH, FLT class -- doc 288) are marked as
    # such and never treated as retry candidates: `route_class` is a pure
    # function of the ledger, so they report `no-supported-route` on every
    # run rather than being picked up as if capability might have changed.
    no_route_ready = sorted(
        entry["fact_id"] for entry in considered if entry["route_class"] == "no-route"
    )

    # Doc 291: THREE populations over ready facts, not two. `admissible_count`
    # used to be read as "discharge-capable", but before declines existed it
    # measured only SHAPE-MATCH -- exactly what let the very first contract
    # dispatch (doc 290) loop forever on a fact a producer had already
    # honestly refused. These three are reported side by side so the gap
    # between "matched a shape" and "would actually be attempted again" is a
    # number, not a reading of the code.
    #
    #   shape-matched                  >= 1 matched producer contract
    #   declined-via-all-matching      shape-matched AND every matched
    #                                  contract has a LIVE decline against
    #                                  this fact -- the population that was
    #                                  previously invisible and silently
    #                                  counted as admissible
    #   admissible (matched minus declined)   the existing admissible-via-
    #                                  contract path, now correctly excluding
    #                                  a declined pair (computed above, via
    #                                  `contract_ok`)
    shape_matched_fact_ids = sorted(
        entry["fact_id"] for entry in considered if entry["matched_producer_contract_ids"]
    )
    declined_fact_ids = sorted(
        entry["fact_id"]
        for entry in considered
        if entry["matched_producer_contract_ids"]
        and set(entry["matched_producer_contract_ids"])
        <= set(entry["declined_producer_contract_ids"])
    )
    # Per-contract decline counts: how many LIVE `(fact, contract)` pairs
    # currently suppress admission via each contract. Derived directly from
    # `declined_pairs` -- the source of truth -- rather than re-filtered
    # through `considered`, so a contract's decline count is visible even for
    # a fact that is not (yet, or any longer) dependency-ready.
    declined_by_contract: dict[str, int] = defaultdict(int)
    for _fact_id, contract_id in declined_pairs:
        declined_by_contract[contract_id] += 1

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
            # Still true of the RECEIPT path specifically: an operation-based
            # admission always requires exactly one registered operation. It is
            # no longer the ONLY way to be admissible -- see
            # `autonomous_dispatch_requires_registered_operation_or_producer_contract`,
            # which states the actual (ADR-0602) admissibility rule. Left in
            # place, unrenamed, because "purely additive" is the standing rule
            # for this artifact's keys (doc 288) and nothing reads this as
            # meaning contracts do not exist.
            "autonomous_dispatch_requires_registered_operation": True,
            "producer_contract_routes": sorted(CONTRACT_ROUTES),
            "producer_contract_registry_sha256": digest(contracts),
            "registered_producer_contracts": sorted(
                contract["id"] for contract in contracts
            ),
            "producer_contract_route_capability": dict(sorted(capable_routes.items())),
            "autonomous_dispatch_requires_registered_operation_or_producer_contract": True,
            # Doc 291: a decline is scoped to the exact contract content that
            # produced it (`contract_sha256`), never to the contract's name --
            # so editing a contract's recipe/shape is what re-opens a fact it
            # previously declined. This digest is over the DECLINE artifacts
            # themselves, exactly like `producer_contract_registry_sha256` is
            # over the contracts.
            "producer_contract_decline_registry_sha256": digest(declines),
            "recorded_producer_contract_declines": sorted(
                f"{decline['fact_id']}::{decline['contract']}" for decline in declines
            ),
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
            # Doc 291: declined facts are NAMED, never silently dropped --
            # the same treatment `no_route_ready_fact_ids` already gives
            # facts with no route at all (doc 288's precedent).
            "declined_fact_ids": declined_fact_ids,
        },
        "diagnostics": {
            "ready_count": len(considered),
            # Doc 291: `admissible_count` now correctly excludes a fact whose
            # only matching contract has a live decline against it -- before
            # this, it measured shape-match plus route-capability only, which
            # is exactly why the very first contract dispatch (doc 290)
            # reported the just-declined fact as admissible again on the next
            # run. See `shape_matched_count` / `declined_count` below for the
            # populations this number used to conflate.
            "admissible_count": len(admissible),
            # Doc 291's three populations, side by side (see the comment
            # above their computation): shape-matched is what
            # `admissible_count` used to measure; declined is the population
            # that was previously invisible; admissible (via contract) is
            # `admissible_via_contract_count` below, i.e. shape-matched minus
            # declined for every UNAMBIGUOUS single-contract match.
            "shape_matched_count": len(shape_matched_fact_ids),
            "declined_count": len(declined_fact_ids),
            "declined_by_contract": dict(sorted(declined_by_contract.items())),
            # Among READY facts with NO registered operation at all, how many
            # are stuck on missing MATH CAPABILITY (`no-route` / a kernel proof
            # not yet written, `proof-route-only`) versus stuck on missing
            # PAPERWORK (`decidable` by an already-terminating route, just
            # never wired up). Registering an operation can only ever help the
            # second bucket -- see the note above `unregistered_by_route`.
            "unregistered_by_route_class": dict(sorted(unregistered_by_route.items())),
            # ADR-0602's new axis, same split, over CONTRACT matching rather
            # than operation registration. This is what doc 288 said would
            # actually move `admissible` off zero: `proof-route-only` facts
            # with no contract yet authored for their shape, not a paperwork
            # gap on an already-decidable fragment.
            "unmatched_by_route_class": dict(sorted(unmatched_by_route.items())),
            # How many of the currently admissible facts came from EACH path.
            # Not mutually exclusive by construction (a fact could in
            # principle have both a registered operation and a matching
            # contract); summing the two can exceed `admissible_count` and
            # that is not a bug.
            "admissible_via_operation_count": admitted_via_operation,
            "admissible_via_contract_count": admitted_via_contract,
            # The 6 no-route facts (doc 288: Collatz, CH, excluded-middle,
            # FLT, FOL validity, Gödel incompleteness, Goldbach), named so a
            # reader never has to re-derive "why is this ready fact never
            # selected" from `route_class` by hand.
            "no_route_ready_fact_ids": no_route_ready,
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
    # `build_machine_frontier`'s own `contracts=None`/`declines=None` mean NO
    # contracts/declines (see its docstring); recomputing the CURRENT
    # authoritative frontier for a comparison needs the real, current sets
    # explicitly, exactly as `main()` does when it first builds the artifact
    # being verified.
    expected = build_machine_frontier(
        facts,
        contracts=load_producer_contracts(),
        declines=load_decline_artifacts(),
    )
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
            # Explicit, real contracts and declines -- see
            # `build_machine_frontier`'s docstring on why `contracts=None` /
            # `declines=None` there means NONE, not auto-loaded.
            artifact = build_machine_frontier(
                facts,
                contracts=load_producer_contracts(),
                declines=load_decline_artifacts(),
            )
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
