"""Fixtures for `test-structural-index-mutations.sh` (L3 phase D2, ADR-0905).

Small, hand-built in-memory fixtures -- not the real 1,633-declaration
index -- driven through the six `check_*` guards in
`scripts/check-structural-index.py` directly, the same shape
`scripts/tests/graph_join_mutations.py` uses for `check-graph-join.py`.

`good_*` fixtures must pass every guard. Each `bad_<GUARD>` fixture must
fail ONLY its own named guard against the unmutated checker, and flip to
PASS only once that guard's body is replaced with `return []` by the bash
harness.
"""

from __future__ import annotations


def good_records() -> list[dict]:
    return [
        {
            "name": "A.thmOne",
            "theorem_dependencies": ["Shared.helper"],
            "recursors_used": [],
            "definitions_used": [],
        },
        {
            "name": "B.thm2",
            "theorem_dependencies": ["Shared.helper"],
            "recursors_used": [],
            "definitions_used": [],
        },
        {
            "name": "C.other",
            "theorem_dependencies": [],
            "recursors_used": [],
            "definitions_used": [],
        },
    ]


def good_queries() -> list[dict]:
    return [
        {
            "id": "dep-query",
            "query": {"kind": "dependency", "has_dependencies": ["Shared.helper"]},
            "expected_names": ["A.thmOne", "B.thm2"],
        },
        {
            "id": "identity-miss-on-plausible-guess",
            "query": {"kind": "identity", "name": "A.thm_one"},
            "expected_names": [],
        },
        {
            "id": "lexical-hit-on-same-guess",
            "query": {"kind": "lexical", "name_like": "thm_one"},
            "expected_names": ["A.thmOne"],
        },
        {
            "id": "unanswerable-check",
            "query": {
                "kind": "dependency",
                "has_dependencies": ["Shared.helper", "NoSuchDep"],
            },
            "expect_unanswerable": True,
        },
    ]


def good_features(non_held_out_fact_id: str = "F:fixture-not-held-out") -> list[dict]:
    return [
        {
            "fact_id": non_held_out_fact_id,
            "family": "fixture",
            "goal_head": "Eq",
            "hyp_count": 1,
        }
    ]


def bad_empty_index_records() -> list[dict]:
    return []


def bad_fixed_queries() -> list[dict]:
    queries = good_queries()
    queries[0] = dict(queries[0])
    queries[0]["expected_names"] = ["WRONG.name"]
    return queries


def bad_held_out_features(held_out_fact_id: str) -> list[dict]:
    return good_features() + [
        {
            "fact_id": held_out_fact_id,
            "family": "fixture",
            "goal_head": "Eq",
            "hyp_count": 0,
        }
    ]


def bad_goal_feature_leak_features(non_held_out_fact_id: str = "F:fixture-not-held-out") -> list[dict]:
    leaky = dict(good_features(non_held_out_fact_id)[0])
    leaky["proof_value"] = "THIS SHOULD NEVER APPEAR"
    return [leaky]


def bad_signal_separation_queries() -> list[dict]:
    queries = good_queries()
    for i, q in enumerate(queries):
        if q["id"] == "lexical-hit-on-same-guess":
            queries[i] = {
                "id": "lexical-hit-on-same-guess",
                # Deliberately conflating: `name` set to the exact name the
                # lexical guess resolves to, so the row's identity_match
                # becomes True -- exactly the conflation the guard exists to
                # catch.
                "query": {
                    "kind": "lexical",
                    "name_like": "thm_one",
                    "name": "A.thmOne",
                },
                "expected_names": ["A.thmOne"],
            }
    return queries


def bad_absence_unanswerable_queries() -> list[dict]:
    return [q for q in good_queries() if not q.get("expect_unanswerable")]
