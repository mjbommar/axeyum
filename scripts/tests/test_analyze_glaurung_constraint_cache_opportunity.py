import importlib.util
import json
import pathlib
import sys
import unittest


SCRIPT = (
    pathlib.Path(__file__).resolve().parents[1]
    / "analyze-glaurung-constraint-cache-opportunity.py"
)
SPEC = importlib.util.spec_from_file_location("constraint_cache_opportunity", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def line(event_seq: int, event: str, path_id: str, **values: object) -> bytes:
    return (
        json.dumps(
            {"event_seq": event_seq, "event": event, "path_id": path_id, **values},
            sort_keys=True,
        ).encode()
        + b"\n"
    )


def events(checks: list[tuple[str, str, list[str]]]) -> bytes:
    rows = [line(0, "analysis_start", "analysis")]
    sequence = 1
    rows.append(
        line(
            sequence,
            "path_start",
            "path-0",
            parent_path_id=None,
        )
    )
    sequence += 1
    scopes: list[tuple[str, str]] = []
    for check_index, (query, outcome, constraints) in enumerate(checks):
        common = 0
        while (
            common < len(scopes)
            and common < len(constraints)
            and scopes[common][1] == constraints[common]
        ):
            common += 1
        while len(scopes) > common:
            scope_id, _ = scopes.pop()
            rows.append(
                line(
                    sequence,
                    "pop",
                    "path-0",
                    scope_id=scope_id,
                )
            )
            sequence += 1
        for constraint in constraints[common:]:
            scope_id = f"scope-{len(scopes)}-{constraint}"
            rows.append(
                line(
                    sequence,
                    "push",
                    "path-0",
                    scope_id=scope_id,
                    prior_depth=len(scopes),
                )
            )
            sequence += 1
            scopes.append((scope_id, constraint))
            rows.append(
                line(
                    sequence,
                    "assert",
                    "path-0",
                    scope_id=scope_id,
                    constraint_id=constraint,
                )
            )
            sequence += 1
        rows.append(
            line(
                sequence,
                "check",
                "path-0",
                check_id=f"check-{check_index}",
                query_sha256=query,
                outcome=outcome,
                active_constraint_count=len(scopes),
            )
        )
        sequence += 1
    while scopes:
        scope_id, _ = scopes.pop()
        rows.append(line(sequence, "pop", "path-0", scope_id=scope_id))
        sequence += 1
    rows.append(line(sequence, "path_end", "path-0"))
    sequence += 1
    rows.append(line(sequence, "analysis_end", "analysis"))
    return b"".join(rows)


class ConstraintCacheOpportunityTests(unittest.TestCase):
    def test_exact_and_implication_hits_are_separated(self) -> None:
        raw = events(
            [
                ("q-sat-strong", "sat", ["a", "b"]),
                ("q-sat-weak", "sat", ["a"]),
                ("q-unsat-weak", "unsat", ["c"]),
                ("q-unsat-strong", "unsat", ["c", "d"]),
                ("q-unsat-strong", "unsat", ["c", "d"]),
            ]
        )
        result = MODULE.analyze_events(raw)
        cache = result["cache"]
        self.assertEqual(cache["checks"], 5)
        self.assertEqual(cache["sat_superset_hits"], 1)
        self.assertEqual(cache["unsat_subset_hits"], 1)
        self.assertEqual(cache["exact_unsat_hits"], 1)
        self.assertEqual(cache["misses"], 2)

    def test_conflicting_exact_outcome_is_rejected(self) -> None:
        with self.assertRaisesRegex(ValueError, "conflicting exact outcome"):
            MODULE.analyze_events(
                events([("same", "sat", ["a"]), ("same", "unsat", ["a"])])
            )

    def test_canonical_constraint_identity_ignores_textual_query_order(self) -> None:
        raw = events(
            [
                ("query-a-b", "sat", ["a", "b"]),
                ("query-b-a", "sat", ["b", "a"]),
            ]
        )
        textual = MODULE.analyze_events(raw)
        canonical = MODULE.analyze_events(
            raw, exact_identity="canonical-constraint-set"
        )
        self.assertEqual(textual["cache"]["exact_hits"], 0)
        self.assertEqual(canonical["cache"]["exact_sat_hits"], 1)
        self.assertEqual(canonical["cache"]["sat_superset_hits"], 0)

    def test_unsat_subset_cannot_predict_recorded_sat(self) -> None:
        with self.assertRaisesRegex(ValueError, "contradicts recorded SAT"):
            MODULE.analyze_events(
                events([("u", "unsat", ["a"]), ("s", "sat", ["a", "b"])])
            )

    def test_sat_superset_cannot_predict_recorded_unsat(self) -> None:
        with self.assertRaisesRegex(ValueError, "contradicts recorded UNSAT"):
            MODULE.analyze_events(
                events([("s", "sat", ["a", "b"]), ("u", "unsat", ["a"])])
            )

    def test_fork_inherits_scopes_without_aliasing_parent(self) -> None:
        raw = b"".join(
            [
                line(0, "analysis_start", "analysis"),
                line(1, "path_start", "p0", parent_path_id=None),
                line(2, "push", "p0", scope_id="s0", prior_depth=0),
                line(3, "assert", "p0", scope_id="s0", constraint_id="a"),
                line(4, "path_start", "p1", parent_path_id="p0"),
                line(5, "push", "p1", scope_id="s1", prior_depth=1),
                line(6, "assert", "p1", scope_id="s1", constraint_id="b"),
                line(
                    7,
                    "check",
                    "p1",
                    query_sha256="q1",
                    outcome="sat",
                    active_constraint_count=2,
                ),
                line(8, "pop", "p1", scope_id="s1"),
                line(9, "path_end", "p1"),
                line(
                    10,
                    "check",
                    "p0",
                    query_sha256="q0",
                    outcome="sat",
                    active_constraint_count=1,
                ),
                line(11, "pop", "p0", scope_id="s0"),
                line(12, "path_end", "p0"),
                line(13, "analysis_end", "analysis"),
            ]
        )
        result = MODULE.analyze_events(raw)
        self.assertEqual(result["cache"]["sat_superset_hits"], 1)


if __name__ == "__main__":
    unittest.main()
