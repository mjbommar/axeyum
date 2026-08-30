"""Fixture builder for `check-graph-join.py`'s guard functions (L1 phase
G2). Each guard is a pure function over already-loaded dicts, so fixtures
here are small hand-built Python dicts rather than full declaration-graph/
fact-ledger trees -- the same "surgical" philosophy ADR-0800's mutation
fixtures use: every field OTHER than the one property under test is kept
internally consistent, so a guard's removal cannot be rescued by an
unrelated check catching the same mutation by accident.

Used by `scripts/tests/test-graph-join.py` (in-process assertions) and
`scripts/tests/test-graph-join-mutations.sh` (the guard-deletion kill
table).
"""
from __future__ import annotations

import copy

CONTROL_NAME = "Nat.add_comm"
CONTROL_FACT_ID = "F:ml430-nat-add-comm-fixture"
MIRROR_TITLE = "Mathlib v4.30 source proposition Nat.add_comm"


def good_facts_by_id() -> dict[str, dict]:
    return {
        CONTROL_FACT_ID: {
            "id": CONTROL_FACT_ID,
            "title": MIRROR_TITLE,
            "epistemic_status": "proved",
            "proof_route": "kernel-lean",
            "axiom_footprint": [],
            "formal": {
                "language": "lean4-surface",
                "statement": "forall n m, n + m = m + n",
                "fragment": "Nat",
                "kernel_theorem": "Nat.add_comm",
            },
        }
    }


def _empty_dim(population_count: int = 0) -> dict:
    return {
        "population_source": "fixture",
        "population_count": population_count,
        "resolved_count": 0,
        "unresolved_count": 0,
        "resolved": {},
        "unresolved": {},
    }


def good_join() -> dict:
    return {
        "schema_version": 1,
        "kind": "axeyum-graph-join",
        "generated_by": "scripts/gen-graph-join.py",
        "population_id": "fixture-v1",
        "population_authority": "artifacts/declaration-graph/populations/fixture-v1.json",
        "expected_roots": ["Nat.add_comm"],
        "declaration_population_count": 1,
        "dimensions": {
            "fact_ids": {
                "population_source": "declaration-graph",
                "population_count": 1,
                "resolved_count": 1,
                "unresolved_count": 0,
                "resolved": {
                    CONTROL_NAME: {"fact_id": CONTROL_FACT_ID, "basis": "ml430-mirror-title-exact"}
                },
                "unresolved": {},
            },
            "kernel_declarations": {
                "population_source": "fact_ids.resolved",
                "population_count": 1,
                "resolved_count": 1,
                "unresolved_count": 0,
                "resolved": {
                    CONTROL_NAME: {
                        "fact_id": CONTROL_FACT_ID,
                        "kernel_theorem": "Nat.add_comm",
                        "basis": "kernel_theorem-field-explicit",
                    }
                },
                "unresolved": {},
            },
            "statement_vocabulary": _empty_dim(),
            "destination_nodes": _empty_dim(),
            "producers": _empty_dim(),
            "declines": _empty_dim(),
            "trust_footprints": {
                "population_source": "kernel_declarations.resolved",
                "population_count": 1,
                "resolved_count": 1,
                "unresolved_count": 0,
                "resolved": {
                    CONTROL_NAME: {
                        "fact_id": CONTROL_FACT_ID,
                        "kernel_theorem": "Nat.add_comm",
                        "axiom_footprint": [],
                        "in_identity_class": False,
                    }
                },
                "unresolved": {},
            },
        },
        "name_coincidence_candidates": {},
        "notes": {
            "bounded": "fixture",
            "adr_0790_limit_inherited": "fixture",
            "no_name_similarity_creates_identity": "fixture",
        },
    }


def good_rows() -> dict:
    return {"declarations": [{"name": CONTROL_NAME, "kind": "Theorem"}]}


# ---- per-guard bad fixtures -------------------------------------------------


def bad_empty_population_rows() -> dict:
    return {"declarations": []}


def bad_empty_facts() -> dict:
    return {}


def bad_accounting_join() -> dict:
    """Puts the SAME name in both resolved and unresolved of one dimension --
    violates accounting only; every other guard's inputs are untouched."""
    join = copy.deepcopy(good_join())
    dim = join["dimensions"]["fact_ids"]
    dim["unresolved"][CONTROL_NAME] = {"reason": "injected-for-mutation-test"}
    dim["unresolved_count"] = 1
    return join


def bad_stale_artifact_pair() -> tuple[dict, dict]:
    """`committed` disagrees with a `fresh` recomputation."""
    committed = copy.deepcopy(good_join())
    fresh = copy.deepcopy(good_join())
    fresh["declaration_population_count"] = 999
    return committed, fresh


def bad_positive_control_join() -> dict:
    """The control theorem's fact_id resolution is simply absent."""
    join = copy.deepcopy(good_join())
    del join["dimensions"]["fact_ids"]["resolved"][CONTROL_NAME]
    join["dimensions"]["fact_ids"]["resolved_count"] = 0
    join["dimensions"]["fact_ids"]["unresolved"][CONTROL_NAME] = {"reason": "injected-absence"}
    join["dimensions"]["fact_ids"]["unresolved_count"] = 1
    return join


def bad_bare_name_basis_join_and_facts() -> tuple[dict, dict]:
    """A `fact_ids` resolution naming a real fact_id, but that fact's TITLE
    does not carry the required mirror phrase -- i.e. a link that looks
    resolved but has no real title-match evidence behind it. This is the
    shape a name-similarity shortcut would produce."""
    join = copy.deepcopy(good_join())
    facts = copy.deepcopy(good_facts_by_id())
    other_name = "Semigroup.mul_assoc"
    other_fact_id = "F:not-actually-a-mirror"
    facts[other_fact_id] = {
        "id": other_fact_id,
        "title": "Some unrelated fact about Semigroup.mul_assoc",
        "epistemic_status": "proved",
        "proof_route": "kernel-lean",
        "axiom_footprint": [],
        "formal": {"language": "lean4", "statement": "x", "fragment": "none"},
    }
    join["dimensions"]["fact_ids"]["resolved"][other_name] = {
        "fact_id": other_fact_id,
        "basis": "ml430-mirror-title-exact",
    }
    join["dimensions"]["fact_ids"]["resolved_count"] = 2
    join["dimensions"]["fact_ids"]["population_count"] = 2
    return join, facts
