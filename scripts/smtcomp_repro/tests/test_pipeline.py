"""Deterministic end-to-end test of the aggregation + ranking pipeline.

Builds a synthetic {benchmark: {solver: RawResult}} table (fixed timings, no
solver execution) across two divisions and three solvers, then checks that
`compete.score_everything` computes the division scores, disagreement removal,
and the three competition-wide rankings correctly by hand.
"""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from collections import defaultdict  # noqa: E402

from compete import score_everything  # noqa: E402
from scoring import RawResult, Status, Track  # noqa: E402


def _raw(solver, bench, division, exp, rep, aw, ac):
    return RawResult(
        solver=solver,
        benchmark=bench,
        division=division,
        logic=division,
        expected_status=exp,
        reported_status=rep,
        wall_time=aw,
        cpu_time=ac,
    )


def _build():
    """Two divisions:
    QF_BV: 3 benchmarks. fast solves all quickly; slow solves all slowly;
           buggy gets one WRONG (so unsound in QF_BV).
    QF_LIA: 2 benchmarks. fast + slow solve both; buggy solves one, misses one.
    """
    per = defaultdict(dict)
    S = Status.SAT
    U = Status.UNSAT
    # QF_BV
    per["bv1"]["fast"] = _raw("fast", "bv1", "QF_BV", S, S, 1, 1)
    per["bv1"]["slow"] = _raw("slow", "bv1", "QF_BV", S, S, 8, 8)
    per["bv1"]["buggy"] = _raw("buggy", "bv1", "QF_BV", S, S, 1, 1)
    per["bv2"]["fast"] = _raw("fast", "bv2", "QF_BV", U, U, 2, 2)
    per["bv2"]["slow"] = _raw("slow", "bv2", "QF_BV", U, U, 9, 9)
    per["bv2"]["buggy"] = _raw("buggy", "bv2", "QF_BV", U, S, 1, 1)  # WRONG
    per["bv3"]["fast"] = _raw("fast", "bv3", "QF_BV", S, S, 3, 3)
    per["bv3"]["slow"] = _raw("slow", "bv3", "QF_BV", S, S, 7, 7)
    per["bv3"]["buggy"] = _raw("buggy", "bv3", "QF_BV", S, None, 10, 40)  # no answer
    # QF_LIA
    per["li1"]["fast"] = _raw("fast", "li1", "QF_LIA", S, S, 1, 1)
    per["li1"]["slow"] = _raw("slow", "li1", "QF_LIA", S, S, 4, 4)
    per["li1"]["buggy"] = _raw("buggy", "li1", "QF_LIA", S, S, 2, 2)
    per["li2"]["fast"] = _raw("fast", "li2", "QF_LIA", U, U, 1, 1)
    per["li2"]["slow"] = _raw("slow", "li2", "QF_LIA", U, U, 4, 4)
    per["li2"]["buggy"] = _raw("buggy", "li2", "QF_LIA", U, None, 10, 40)  # miss
    return per


def test_division_scores_and_soundness():
    per = _build()
    rep = score_everything(per, ["fast", "slow", "buggy"], Track.SINGLE_QUERY, 20.0, 4)

    bv = rep["divisions"]["QF_BV"]
    assert bv["n_benchmarks"] == 3
    # fast + slow are sound (e=0); buggy has an error in QF_BV.
    assert set(bv["sound_solvers"]) == {"fast", "slow"}
    assert bv["solvers"]["fast"]["parallel"]["e"] == 0
    assert bv["solvers"]["fast"]["parallel"]["n"] == 3
    assert bv["solvers"]["buggy"]["parallel"]["e"] == 1
    assert bv["solvers"]["buggy"]["parallel"]["n"] == 1  # only bv1 correct
    # PAR-2 ranking: fast (all solved, fastest) first, then slow, then buggy.
    assert bv["ranking_par2"][0] == "fast"
    assert bv["ranking_par2"][-1] == "buggy"

    li = rep["divisions"]["QF_LIA"]
    assert li["n_benchmarks"] == 2
    assert set(li["sound_solvers"]) == {"fast", "slow", "buggy"}
    assert li["solvers"]["buggy"]["parallel"]["n"] == 1  # solved li1, missed li2


def test_par2_penalty_shows_in_wall():
    per = _build()
    rep = score_everything(per, ["fast", "slow", "buggy"], Track.SINGLE_QUERY, 20.0, 4)
    li = rep["divisions"]["QF_LIA"]
    # buggy solved 1 of 2 in QF_LIA -> PAR-2 wall = (solved wall) + 2*T for the miss
    # solved li1 in aw=2 (correct) -> 2 ; missed li2 -> 2*20 = 40 ; total 42
    assert abs(li["solvers"]["buggy"]["par2"]["wall"] - 42.0) < 1e-9


def test_best_overall_ranking_orders_fast_first():
    per = _build()
    rep = score_everything(per, ["fast", "slow", "buggy"], Track.SINGLE_QUERY, 20.0, 4)
    # fast and slow both solve everything cleanly in both divisions -> tie on
    # correctness; buggy has an error in QF_BV (-2 penalty) so it ranks last.
    assert rep["best_overall_ranking"][-1] == "buggy"
    # buggy's overall score must be negative (the -2 error penalty dominates).
    assert rep["best_overall_score"]["buggy"] < 0


def test_largest_contribution_needs_more_than_two_sound():
    per = _build()
    rep = score_everything(per, ["fast", "slow", "buggy"], Track.SINGLE_QUERY, 20.0, 4)
    # QF_BV has only 2 sound solvers -> no largest-contribution ranking.
    assert rep["divisions"]["QF_BV"]["largest_contribution"] is None
    # QF_LIA has 3 sound solvers -> ranking present.
    assert rep["divisions"]["QF_LIA"]["largest_contribution"] is not None


def test_disagreement_removal_on_unknown_status():
    per = _build()
    # Add an unknown-status benchmark where fast says sat, slow says unsat.
    per["u1"]["fast"] = _raw("fast", "u1", "QF_BV", None, Status.SAT, 1, 1)
    per["u1"]["slow"] = _raw("slow", "u1", "QF_BV", None, Status.UNSAT, 1, 1)
    per["u1"]["buggy"] = _raw("buggy", "u1", "QF_BV", None, Status.UNKNOWN, 1, 1)
    rep = score_everything(per, ["fast", "slow", "buggy"], Track.SINGLE_QUERY, 20.0, 4)
    assert rep["n_removed_disagreements"] == 1
    assert "u1" in rep["removed_disagreements"]
    # The removed benchmark must not inflate the division count.
    assert rep["divisions"]["QF_BV"]["n_benchmarks"] == 3


def _run_all():
    g = globals()
    tests = sorted(k for k in g if k.startswith("test_"))
    failed = 0
    for name in tests:
        try:
            g[name]()
            print(f"PASS {name}")
        except Exception as exc:  # noqa: BLE001
            failed += 1
            print(f"FAIL {name}: {exc!r}")
    print(f"\n{len(tests) - failed}/{len(tests)} passed")
    return failed


if __name__ == "__main__":
    sys.exit(1 if _run_all() else 0)
