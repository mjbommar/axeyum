"""SMT-COMP scoring engine — a faithful replica of the 2026 rules, §7.

This module implements Stage C..E of the pipeline (see README): the per-benchmark
score tuple, the sequential score, the division scores (parallel / PAR-2 /
sequential / 24s / sat / unsat), disagreement removal, and the three
competition-wide rankings (Best Overall, Biggest Lead, Largest Contribution).

Nothing here executes solvers or touches the filesystem — it is pure scoring
over already-collected raw results, so it is deterministic and unit-testable.
Section numbers (e.g. §7.1.2) refer to the SMT-COMP 2026 Rules and Procedures.

Vocabulary (§7.1):
  aw  actual wall-clock time, seconds, in [0, T]
  ac  actual CPU time, seconds, in [0, m*T]
  e   error score: 1 iff the solver produced a wrong/erroneous result, else 0
  n   correctly-solved score: per-track (0/1, a count, or a reduction)
  w   wall-clock time score: aw if correctly solved, else 0
  c   CPU time score: ac if correctly solved, else 0
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from enum import Enum
from typing import Optional


class Track(str, Enum):
    SINGLE_QUERY = "single_query"
    INCREMENTAL = "incremental"
    UNSAT_CORE = "unsat_core"
    MODEL_VALIDATION = "model_validation"
    PARALLEL = "parallel"


class Status(str, Enum):
    """A sat/unsat/unknown verdict, or None-equivalent 'no response'."""

    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"


# Wall-clock time limit T per track, in seconds (§5.2..§5.6: 20 minutes).
DEFAULT_WALL_LIMIT_S = 1200.0
# Cores per solver/benchmark pair (§5.1: 4 cores). m*T is the CPU limit.
DEFAULT_CORES = 4


@dataclass(frozen=True)
class RawResult:
    """One (solver, benchmark) execution outcome — the input to scoring.

    `expected_status` is the SMT-LIB `:status` of the benchmark (None == the
    benchmark's status is 'unknown', which the rules treat specially).
    `reported_status` is what the solver said (None == aborted with no verdict).
    """

    solver: str
    benchmark: str
    division: str
    logic: str
    expected_status: Optional[Status]
    reported_status: Optional[Status]
    wall_time: float  # aw
    cpu_time: float  # ac
    # --- track-specific extras ---
    # Unsat-Core track: size of the returned core and the number N of named
    # top-level assertions; `core_wellformed`/`core_is_unsat` from validation.
    unsat_core_size: Optional[int] = None
    num_named_assertions: Optional[int] = None
    core_wellformed: bool = True
    core_is_unsat: Optional[bool] = None
    # Model-Validation track: the Dolmen verdict for this result.
    model_validation: Optional[str] = None  # "VALID" | "INVALID" | "UNKNOWN"
    # Incremental track: number of correct check-sat answers, and whether any
    # answered check-sat was wrong.
    incremental_correct: int = 0
    incremental_any_error: bool = False


@dataclass(frozen=True)
class Score:
    """A benchmark score tuple ⟨e, n, aw, w, ac, c⟩ (§7.1)."""

    e: int
    n: float
    aw: float
    w: float
    ac: float
    c: float

    def __add__(self, other: "Score") -> "Score":
        return Score(
            self.e + other.e,
            self.n + other.n,
            self.aw + other.aw,
            self.w + other.w,
            self.ac + other.ac,
            self.c + other.c,
        )


ZERO = Score(0, 0, 0.0, 0.0, 0.0, 0.0)


def _status_correct(expected: Optional[Status], reported: Status) -> bool:
    """A sat/unsat report is correct if it agrees with the benchmark status,
    or the benchmark status is unknown (§7.1.2 footnote 4)."""
    if reported not in (Status.SAT, Status.UNSAT):
        return False
    if expected is None:  # benchmark status unknown -> treat as correct
        return True
    return expected == reported


def benchmark_score(
    r: RawResult,
    track: Track,
    wall_limit: float = DEFAULT_WALL_LIMIT_S,
    cores: int = DEFAULT_CORES,
) -> Score:
    """Stage C: raw result -> ⟨e, n, aw, w, ac, c⟩ per the track rules (§7.1).

    Note (§7.1.2): a response counts even under abnormal/late termination — so
    `aw`/`ac` can exceed the limit, but `w`/`c` are zeroed unless *correctly
    solved*, and PAR-2 (§7.2.2) further penalizes unsolved benchmarks.
    """
    aw = r.wall_time
    ac = r.cpu_time
    cpu_limit = cores * wall_limit

    if track in (Track.SINGLE_QUERY, Track.PARALLEL):
        # §7.1.2
        if r.reported_status in (Status.SAT, Status.UNSAT):
            if _status_correct(r.expected_status, r.reported_status):
                e, n = 0, 1
            else:
                e, n = 1, 0
        else:  # unknown, or aborted without response
            e, n = 0, 0

    elif track == Track.INCREMENTAL:
        # §7.1.3 — n is the count of correct check-sat answers before timeout.
        if r.incremental_any_error:
            e, n = 1, 0
        else:
            e, n = 0, r.incremental_correct

    elif track == Track.UNSAT_CORE:
        # §7.1.4
        if (
            r.reported_status == Status.UNKNOWN
            or r.reported_status is None
            or not r.core_wellformed
        ):
            e, n = 0, 0
        elif r.reported_status == Status.SAT or r.core_is_unsat is False:
            # Erroneous per §5.4: check-sat said sat, or the core is not unsat.
            e, n = 1, 0
        else:
            # reduction = N - |core|
            assert r.num_named_assertions is not None
            assert r.unsat_core_size is not None
            e = 0
            n = r.num_named_assertions - r.unsat_core_size

    elif track == Track.MODEL_VALIDATION:
        # §7.1.5, verdict from the Dolmen model validator (§5.5).
        v = r.model_validation
        if v == "INVALID":
            e, n = 1, 0
        elif v == "VALID":
            e, n = 0, 1
        else:  # UNKNOWN / missing
            e, n = 0, 0
    else:
        raise ValueError(f"unknown track {track}")

    # w/c: the time score counts only when the benchmark was correctly solved.
    solved = e == 0 and n > 0
    w = aw if solved else 0.0
    c = ac if (solved and ac <= cpu_limit) else 0.0
    return Score(e, n, aw, w, ac, c)


def sequential_score(
    parallel: Score,
    wall_limit: float = DEFAULT_WALL_LIMIT_S,
) -> Score:
    """§7.1.1 sequential benchmark score ⟨e_S, n_S, c_S⟩ (carried in a Score with
    aw=w=0 unused): impose a virtual CPU limit of T. If c > T the result is
    discarded (all zero); otherwise identical to the parallel score."""
    if parallel.c > wall_limit:
        return Score(0, 0, 0.0, 0.0, parallel.ac, 0.0)
    return Score(parallel.e, parallel.n, 0.0, 0.0, parallel.ac, parallel.c)


def par2_benchmark(
    s: Score,
    wall_limit: float = DEFAULT_WALL_LIMIT_S,
    cores: int = DEFAULT_CORES,
) -> Score:
    """§7.2.2 PAR-2: penalize w and c by 2×limit for unsolved benchmarks."""
    solved = s.e == 0 and s.n > 0
    w = s.w if solved else 2.0 * wall_limit
    c = s.c if solved else 2.0 * cores * wall_limit
    return Score(s.e, s.n, s.aw, w, s.ac, c)


# --------------------------------------------------------------------------
# Division scoring (§7.2)
# --------------------------------------------------------------------------


def division_sum(scores: list[Score]) -> Score:
    """Component-wise sum of benchmark scores over a division (§7.2.1/§7.2.3)."""
    total = ZERO
    for s in scores:
        total = total + s
    return total


def parallel_better(a: Score, b: Score) -> bool:
    """§7.2.1 ordering: fewer errors > more solved > less wall > less CPU."""
    return (a.e, -a.n, a.w, a.c) < (b.e, -b.n, b.w, b.c)


def sequential_better(a: Score, b: Score) -> bool:
    """§7.2.3 ordering: fewer errors > more solved > less CPU."""
    return (a.e, -a.n, a.c) < (b.e, -b.n, b.c)


def parallel_sort_key(s: Score) -> tuple:
    return (s.e, -s.n, s.w, s.c)


def sequential_sort_key(s: Score) -> tuple:
    return (s.e, -s.n, s.c)


# --------------------------------------------------------------------------
# Competition-wide rankings (§7.3)
# --------------------------------------------------------------------------


@dataclass
class DivisionScore:
    """A solver's aggregated score in one division, for one scoring system."""

    solver: str
    division: str
    n_benchmarks: int  # N^D: benchmarks used in the division
    parallel: Score  # Σ benchmark scores (parallel)


def best_overall_score(division_scores: list[DivisionScore]) -> float:
    """§7.3.1 Best Overall Ranking overall score for one solver.

    overall = Σ_D nn^D · log10(N^D),  nn^D = (n^D/N^D)^2 if e^D=0 else -2,
    summed over the competitive divisions D the solver entered.
    """
    total = 0.0
    for d in division_scores:
        N = d.n_benchmarks
        if N <= 0:
            continue
        if d.parallel.e > 0:
            nn = -2.0
        else:
            nn = (d.parallel.n / N) ** 2
        total += nn * math.log10(N)
    return total


def biggest_lead_correctness_rank(n_first: float, n_second: float) -> float:
    """§7.3.2 correctness rank of a division = (n_1+1)/(n_2+1) for the top two
    solvers ranked by correctness score n."""
    return (n_first + 1.0) / (n_second + 1.0)


def vbss_correctness(
    per_benchmark: dict[str, dict[str, Score]],
    sound_solvers: set[str],
) -> float:
    """§7.3.3 virtual-best-solver correctness score over a division:
    vbss_n(D,S) = Σ_b max{ n_b^s : s∈S, n_b^s > 0 } (empty max -> 0)."""
    total = 0.0
    for _b, by_solver in per_benchmark.items():
        vals = [by_solver[s].n for s in sound_solvers if s in by_solver and by_solver[s].n > 0]
        if vals:
            total += max(vals)
    return total


def vbss_time(
    per_benchmark: dict[str, dict[str, Score]],
    sound_solvers: set[str],
    *,
    which: str,
    empty_value: float = 1200.0,
) -> float:
    """§7.3.3 virtual-best-solver CPU/wall score:
    vbss_c(D,S)=Σ_b min{ c_b^s : s∈S, n_b^s>0 }; empty min -> 1200 s.
    `which` is 'c' (CPU) or 'w' (wall)."""
    total = 0.0
    for _b, by_solver in per_benchmark.items():
        vals = []
        for s in sound_solvers:
            if s in by_solver and by_solver[s].n > 0:
                vals.append(by_solver[s].c if which == "c" else by_solver[s].w)
        total += min(vals) if vals else empty_value
    return total


def largest_contribution_ranks(
    per_benchmark: dict[str, dict[str, Score]],
    sound_solvers: set[str],
) -> dict[str, dict[str, float]]:
    """§7.3.3 per-solver contribution ranks in one division (before the n_D/N
    normalization, which is applied by the caller with track-wide totals).

    Returns {solver: {'n': corr_rank, 'c': cpu_rank, 'w': wall_rank}}.
      corr_rank(s) = 1 - vbss_n(D, S-s)/vbss_n(D, S)
      cpu_rank(s)  = 1 - vbss_c(D, S)/vbss_c(D, S-s)
      wall_rank(s) = 1 - vbss_w(D, S)/vbss_w(D, S-s)
    The division is only ranked when |S| > 2 (checked by the caller)."""
    full_n = vbss_correctness(per_benchmark, sound_solvers)
    full_c = vbss_time(per_benchmark, sound_solvers, which="c")
    full_w = vbss_time(per_benchmark, sound_solvers, which="w")
    out: dict[str, dict[str, float]] = {}
    for s in sound_solvers:
        rest = sound_solvers - {s}
        n_wo = vbss_correctness(per_benchmark, rest)
        c_wo = vbss_time(per_benchmark, rest, which="c")
        w_wo = vbss_time(per_benchmark, rest, which="w")
        corr = 1.0 - (n_wo / full_n) if full_n > 0 else 0.0
        cpu = 1.0 - (full_c / c_wo) if c_wo > 0 else 0.0
        wall = 1.0 - (full_w / w_wo) if w_wo > 0 else 0.0
        out[s] = {"n": corr, "c": cpu, "w": wall}
    return out


# --------------------------------------------------------------------------
# Disagreement removal for Single Query (§7.2, "Removal of Disagreements")
# --------------------------------------------------------------------------


def find_disagreements(
    per_benchmark: dict[str, dict[str, RawResult]],
) -> set[str]:
    """Return the benchmarks with *unknown* status on which two solvers that are
    sound-so-far disagree (one sat, one unsat). These are removed from Single
    Query division scoring (but reported for information)."""
    bad: set[str] = set()
    for b, by_solver in per_benchmark.items():
        # Only unknown-status benchmarks are subject to removal.
        if any(r.expected_status is not None for r in by_solver.values()):
            continue
        reported = {r.reported_status for r in by_solver.values()}
        if Status.SAT in reported and Status.UNSAT in reported:
            bad.add(b)
    return bad
