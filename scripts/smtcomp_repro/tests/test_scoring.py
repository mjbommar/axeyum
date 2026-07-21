"""Hand-verified unit tests for the SMT-COMP scoring engine (scoring.py).

Each test pins one rule from §7 of the SMT-COMP 2026 rules. Run with:
    python3 -m pytest scripts/smtcomp_repro/tests/ -q
or without pytest:
    python3 scripts/smtcomp_repro/tests/test_scoring.py
"""

from __future__ import annotations

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from scoring import (  # noqa: E402
    DEFAULT_CORES,
    DEFAULT_WALL_LIMIT_S,
    DivisionScore,
    RawResult,
    Score,
    Status,
    Track,
    benchmark_score,
    best_overall_score,
    biggest_lead_correctness_rank,
    division_sum,
    find_disagreements,
    largest_contribution_ranks,
    par2_benchmark,
    parallel_better,
    sequential_better,
    sequential_score,
    vbss_correctness,
    vbss_time,
)

T = DEFAULT_WALL_LIMIT_S
M = DEFAULT_CORES


def _r(**kw) -> RawResult:
    base = dict(
        solver="s",
        benchmark="b",
        division="D",
        logic="L",
        expected_status=None,
        reported_status=None,
        wall_time=0.0,
        cpu_time=0.0,
    )
    base.update(kw)
    return RawResult(**base)


# --- §7.1.2 Single Query tuple -------------------------------------------


def test_sq_correct_sat():
    r = _r(expected_status=Status.SAT, reported_status=Status.SAT, wall_time=3.0, cpu_time=10.0)
    s = benchmark_score(r, Track.SINGLE_QUERY)
    assert (s.e, s.n) == (0, 1)
    assert s.w == 3.0 and s.c == 10.0  # solved -> time scores counted


def test_sq_wrong_answer_is_error():
    r = _r(expected_status=Status.UNSAT, reported_status=Status.SAT, wall_time=3.0, cpu_time=10.0)
    s = benchmark_score(r, Track.SINGLE_QUERY)
    assert (s.e, s.n) == (1, 0)
    assert s.w == 0.0 and s.c == 0.0  # not solved -> zero time score


def test_sq_unknown_status_agreement_is_correct():
    # Benchmark status unknown: any sat/unsat answer counts as correct (fn 4).
    r = _r(expected_status=None, reported_status=Status.UNSAT, wall_time=1.0, cpu_time=1.0)
    s = benchmark_score(r, Track.SINGLE_QUERY)
    assert (s.e, s.n) == (0, 1)


def test_sq_unknown_report_scores_zero():
    r = _r(expected_status=Status.SAT, reported_status=Status.UNKNOWN, wall_time=5.0, cpu_time=5.0)
    s = benchmark_score(r, Track.SINGLE_QUERY)
    assert (s.e, s.n) == (0, 0)
    assert s.w == 0.0


def test_sq_no_response_scores_zero():
    r = _r(expected_status=Status.SAT, reported_status=None, wall_time=T, cpu_time=M * T)
    s = benchmark_score(r, Track.SINGLE_QUERY)
    assert (s.e, s.n) == (0, 0)


def test_sq_late_correct_answer_counts_but_cpu_capped():
    # A response counts even past the limit (§7.1.2), but CPU score is zeroed
    # when ac exceeds the CPU limit m*T.
    r = _r(
        expected_status=Status.SAT,
        reported_status=Status.SAT,
        wall_time=T + 5,
        cpu_time=M * T + 5,
    )
    s = benchmark_score(r, Track.SINGLE_QUERY)
    assert (s.e, s.n) == (0, 1)
    assert s.w == T + 5  # wall score keeps the raw value
    assert s.c == 0.0  # over CPU limit -> zeroed


# --- §7.1.1 sequential score ---------------------------------------------


def test_sequential_discards_over_T_cpu():
    par = Score(e=0, n=1, aw=10.0, w=10.0, ac=T + 1, c=T + 1)
    seq = sequential_score(par)
    assert (seq.e, seq.n, seq.c) == (0, 0, 0.0)


def test_sequential_keeps_under_T_cpu():
    par = Score(e=0, n=1, aw=10.0, w=10.0, ac=50.0, c=50.0)
    seq = sequential_score(par)
    assert (seq.e, seq.n, seq.c) == (0, 1, 50.0)


# --- §7.1.4 Unsat-Core tuple ---------------------------------------------


def test_unsat_core_reduction():
    r = _r(
        reported_status=Status.UNSAT,
        num_named_assertions=10,
        unsat_core_size=3,
        core_is_unsat=True,
        wall_time=2.0,
        cpu_time=2.0,
    )
    s = benchmark_score(r, Track.UNSAT_CORE)
    assert s.e == 0 and s.n == 7  # reduction = 10 - 3


def test_unsat_core_sat_is_error():
    r = _r(reported_status=Status.SAT, num_named_assertions=10, unsat_core_size=0)
    s = benchmark_score(r, Track.UNSAT_CORE)
    assert (s.e, s.n) == (1, 0)


def test_unsat_core_not_unsat_is_error():
    r = _r(
        reported_status=Status.UNSAT,
        num_named_assertions=10,
        unsat_core_size=3,
        core_is_unsat=False,
    )
    s = benchmark_score(r, Track.UNSAT_CORE)
    assert (s.e, s.n) == (1, 0)


def test_unsat_core_malformed_is_zero():
    r = _r(reported_status=Status.UNSAT, core_wellformed=False)
    s = benchmark_score(r, Track.UNSAT_CORE)
    assert (s.e, s.n) == (0, 0)


# --- §7.1.5 Model-Validation tuple ---------------------------------------


def test_model_validation_valid():
    r = _r(model_validation="VALID", wall_time=1.0, cpu_time=1.0)
    s = benchmark_score(r, Track.MODEL_VALIDATION)
    assert (s.e, s.n) == (0, 1)


def test_model_validation_invalid_is_error():
    r = _r(model_validation="INVALID")
    s = benchmark_score(r, Track.MODEL_VALIDATION)
    assert (s.e, s.n) == (1, 0)


def test_model_validation_unknown_is_zero():
    r = _r(model_validation="UNKNOWN")
    s = benchmark_score(r, Track.MODEL_VALIDATION)
    assert (s.e, s.n) == (0, 0)


# --- §7.1.3 Incremental tuple --------------------------------------------


def test_incremental_counts_correct():
    r = _r(incremental_correct=7, incremental_any_error=False)
    s = benchmark_score(r, Track.INCREMENTAL)
    assert (s.e, s.n) == (0, 7)


def test_incremental_error_zeros_n():
    r = _r(incremental_correct=7, incremental_any_error=True)
    s = benchmark_score(r, Track.INCREMENTAL)
    assert (s.e, s.n) == (1, 0)


# --- §7.2.2 PAR-2 --------------------------------------------------------


def test_par2_penalizes_unsolved():
    unsolved = benchmark_score(
        _r(expected_status=Status.SAT, reported_status=Status.UNKNOWN, wall_time=T, cpu_time=M * T),
        Track.SINGLE_QUERY,
    )
    p = par2_benchmark(unsolved)
    assert p.w == 2 * T
    assert p.c == 2 * M * T


def test_par2_keeps_solved():
    solved = benchmark_score(
        _r(expected_status=Status.SAT, reported_status=Status.SAT, wall_time=4.0, cpu_time=9.0),
        Track.SINGLE_QUERY,
    )
    p = par2_benchmark(solved)
    assert p.w == 4.0 and p.c == 9.0


# --- §7.2.1 / §7.2.3 orderings -------------------------------------------


def test_parallel_ordering_precedence():
    # fewer errors beats more solved
    a = Score(0, 5, 0, 100, 0, 100)
    b = Score(1, 50, 0, 1, 0, 1)
    assert parallel_better(a, b)
    # equal errors: more solved wins
    a = Score(0, 10, 0, 100, 0, 100)
    b = Score(0, 9, 0, 1, 0, 1)
    assert parallel_better(a, b)
    # equal errors and solved: less wall wins
    a = Score(0, 10, 0, 50, 0, 999)
    b = Score(0, 10, 0, 60, 0, 1)
    assert parallel_better(a, b)


def test_sequential_ordering_uses_cpu_not_wall():
    a = Score(0, 10, 0, 0, 0, 50)
    b = Score(0, 10, 0, 0, 0, 60)
    assert sequential_better(a, b)


# --- §7.2 disagreement removal -------------------------------------------


def test_disagreement_removal_only_unknown_status():
    per_bench = {
        "u1": {
            "x": _r(solver="x", benchmark="u1", expected_status=None, reported_status=Status.SAT),
            "y": _r(solver="y", benchmark="u1", expected_status=None, reported_status=Status.UNSAT),
        },
        "known1": {  # known status disagreement is NOT removed here
            "x": _r(solver="x", benchmark="known1", expected_status=Status.SAT, reported_status=Status.SAT),
            "y": _r(solver="y", benchmark="known1", expected_status=Status.SAT, reported_status=Status.UNSAT),
        },
    }
    bad = find_disagreements(per_bench)
    assert bad == {"u1"}


# --- §7.3.1 Best Overall Ranking -----------------------------------------


def test_best_overall_error_penalty():
    # A division with an error contributes -2 * log10(N).
    ds = [DivisionScore("s", "D", n_benchmarks=100, parallel=Score(1, 40, 0, 0, 0, 0))]
    got = best_overall_score(ds)
    assert math.isclose(got, -2.0 * math.log10(100))


def test_best_overall_clean_division():
    # (n/N)^2 * log10(N); N=100, n=50 -> 0.25 * 2 = 0.5
    ds = [DivisionScore("s", "D", n_benchmarks=100, parallel=Score(0, 50, 0, 0, 0, 0))]
    got = best_overall_score(ds)
    assert math.isclose(got, 0.25 * math.log10(100))


def test_best_overall_sums_divisions():
    ds = [
        DivisionScore("s", "D1", n_benchmarks=100, parallel=Score(0, 100, 0, 0, 0, 0)),  # 1*2=2
        DivisionScore("s", "D2", n_benchmarks=10, parallel=Score(0, 5, 0, 0, 0, 0)),  # .25*1=.25
    ]
    got = best_overall_score(ds)
    assert math.isclose(got, 1.0 * math.log10(100) + 0.25 * math.log10(10))


# --- §7.3.2 Biggest Lead ------------------------------------------------


def test_biggest_lead_correctness_rank():
    assert math.isclose(biggest_lead_correctness_rank(99, 49), 100 / 50)


# --- §7.3.3 Largest Contribution / virtual best solver -------------------


def test_vbss_correctness_takes_max_of_solved():
    # two solvers; per-benchmark max of n over solvers that solved it
    per = {
        "b1": {"x": Score(0, 1, 0, 0, 0, 0), "y": Score(0, 1, 0, 0, 0, 0)},
        "b2": {"x": Score(0, 0, 0, 0, 0, 0), "y": Score(0, 1, 0, 0, 0, 0)},
        "b3": {"x": Score(0, 0, 0, 0, 0, 0), "y": Score(0, 0, 0, 0, 0, 0)},  # neither
    }
    assert vbss_correctness(per, {"x", "y"}) == 2  # b1 + b2


def test_vbss_time_min_and_empty_is_1200():
    per = {
        "b1": {"x": Score(0, 1, 0, 10, 0, 10), "y": Score(0, 1, 0, 4, 0, 4)},  # min wall 4
        "b2": {"x": Score(0, 0, 0, 0, 0, 0)},  # unsolved -> 1200
    }
    assert vbss_time(per, {"x", "y"}, which="w") == 4 + 1200


def test_largest_contribution_removes_solver():
    # x uniquely solves b2; removing x drops vbss_n from 2 to 1 -> corr rank 0.5
    per = {
        "b1": {"x": Score(0, 1, 0, 5, 0, 5), "y": Score(0, 1, 0, 5, 0, 5), "z": Score(0, 1, 0, 5, 0, 5)},
        "b2": {"x": Score(0, 1, 0, 5, 0, 5), "y": Score(0, 0, 0, 0, 0, 0), "z": Score(0, 0, 0, 0, 0, 0)},
    }
    ranks = largest_contribution_ranks(per, {"x", "y", "z"})
    assert math.isclose(ranks["x"]["n"], 1 - (1 / 2))  # full=2, without x=1
    assert math.isclose(ranks["y"]["n"], 0.0)  # y contributes nothing unique


# --- integration: a 3-solver division end to end ------------------------


def test_division_sum_and_ranking_integration():
    # three benchmarks, one solver solves all fast, another slower, third errs.
    def sq(exp, rep, aw, ac):
        return benchmark_score(
            _r(expected_status=exp, reported_status=rep, wall_time=aw, cpu_time=ac),
            Track.SINGLE_QUERY,
        )

    fast = division_sum([
        sq(Status.SAT, Status.SAT, 1, 1),
        sq(Status.UNSAT, Status.UNSAT, 2, 2),
        sq(Status.SAT, Status.SAT, 3, 3),
    ])
    slow = division_sum([
        sq(Status.SAT, Status.SAT, 10, 10),
        sq(Status.UNSAT, Status.UNSAT, 20, 20),
        sq(Status.SAT, Status.SAT, 30, 30),
    ])
    buggy = division_sum([
        sq(Status.SAT, Status.SAT, 1, 1),
        sq(Status.UNSAT, Status.SAT, 1, 1),  # WRONG
        sq(Status.SAT, Status.SAT, 1, 1),
    ])
    # fast and slow both solve 3, fast has less wall -> fast is better
    assert parallel_better(fast, slow)
    # buggy has an error -> worse than both despite speed
    assert parallel_better(fast, buggy)
    assert parallel_better(slow, buggy)
    assert buggy.e == 1 and buggy.n == 2


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
