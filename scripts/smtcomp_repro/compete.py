"""End-to-end SMT-COMP reproduction driver.

Ties the pipeline together: collect benchmarks (+ their ground-truth status),
group into divisions, run every solver under the resource-limited runner, score
each result with the scoring engine, then compute the division scores and the
three competition-wide rankings — printing a scoreboard in the SMT-COMP shape.

This is the local, in-tree replica; it never contacts the SMT-COMP infra.

Usage:
    python3 scripts/smtcomp_repro/compete.py \
        --corpus corpus/qfbv-curated \
        --solver axeyum=target/release/examples/smtcomp_cli \
        --solver z3=z3 \
        --track single_query --wall-limit 20 --limit 40 \
        --out /tmp/scoreboard.json
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import sys
from collections import defaultdict
from dataclasses import dataclass
from typing import Optional

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from runner import run_solver_metered  # noqa: E402
from scoring import (  # noqa: E402
    DEFAULT_CORES,
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
    parallel_sort_key,
    sequential_score,
    sequential_sort_key,
)
from smtlib_meta import read_meta  # noqa: E402


@dataclass
class SolverSpec:
    name: str
    cmd_template: list[str]  # {bench} placeholder replaced with the file path

    def cmd(self, bench: str) -> list[str]:
        return [tok.replace("{bench}", bench) for tok in self.cmd_template]


def parse_solver_arg(spec: str) -> SolverSpec:
    """`name=exe arg arg` -> SolverSpec; adds a trailing {bench} if none given."""
    name, _, rest = spec.partition("=")
    toks = rest.split()
    if "{bench}" not in toks:
        toks.append("{bench}")
    return SolverSpec(name=name, cmd_template=toks)


def division_of(logic: Optional[str], mode: str) -> str:
    """Map a logic to its division. `mode='logic'` keeps one division per logic
    (a faithful subset of SMT-COMP's grouping); `mode='mv'` uses the
    Model-Validation Track division grouping (§5.5)."""
    lg = logic or "UNKNOWN"
    if mode == "logic":
        return lg
    if mode == "mv":
        # §5.5 Model-Validation divisions.
        table = {
            "QF_BV": "QF_Bitvec",
            "QF_UF": "QF_Equality",
            "QF_UFBV": "QF_Equality+Bitvec",
            "QF_LIA": "QF_LinearIntArith",
            "QF_NIA": "QF_NonLinearIntArith",
            "QF_LRA": "QF_LinearRealArith",
            "QF_NRA": "QF_NonLinearRealArith",
            "QF_LIRA": "QF_LinearIntArith",
            "QF_IDL": "QF_LinearIntArith",
            "QF_RDL": "QF_LinearRealArith",
            "QF_UFLIA": "QF_Equality+LinearArith",
            "QF_UFLRA": "QF_Equality+LinearArith",
            "QF_UFIDL": "QF_Equality+LinearArith",
            "QF_DT": "QF_DataTypes",
        }
        return table.get(lg, lg)
    return lg


def collect_benchmarks(corpus: str, limit: Optional[int]) -> list[str]:
    files = sorted(glob.glob(os.path.join(corpus, "**", "*.smt2"), recursive=True))
    if limit is not None:
        files = files[:limit]
    return files


def run_all(
    solvers: list[SolverSpec],
    benchmarks: list[str],
    track: Track,
    wall_limit: float,
    mem_limit_bytes: Optional[int],
    cores: int,
    internal_timeout_ms: Optional[int],
    verbose: bool,
) -> dict[str, dict[str, RawResult]]:
    """Return {benchmark: {solver: RawResult}}."""
    per_bench: dict[str, dict[str, RawResult]] = defaultdict(dict)
    total = len(solvers) * len(benchmarks)
    done = 0
    for bench in benchmarks:
        meta = read_meta(bench)
        division = division_of(meta.logic, "logic")
        for spec in solvers:
            cmd = spec.cmd(bench)
            if internal_timeout_ms is not None and spec.name == "axeyum":
                cmd = cmd + ["--timeout-ms", str(internal_timeout_ms)]
            run = run_solver_metered(
                cmd, wall_limit_s=wall_limit, mem_limit_bytes=mem_limit_bytes
            )
            raw = RawResult(
                solver=spec.name,
                benchmark=bench,
                division=division,
                logic=meta.logic or "UNKNOWN",
                expected_status=meta.status,
                reported_status=run.reported if not run.timed_out else None,
                wall_time=run.wall_time,
                cpu_time=run.cpu_time,
                num_named_assertions=meta.num_named,
            )
            per_bench[bench][spec.name] = raw
            done += 1
            if verbose:
                exp = meta.status.value if meta.status else "unknown"
                got = run.reported.value if run.reported else ("timeout" if run.timed_out else "none")
                flag = ""
                if (
                    run.reported in (Status.SAT, Status.UNSAT)
                    and meta.status is not None
                    and run.reported != meta.status
                ):
                    flag = "  <<< WRONG"
                print(
                    f"[{done:>4}/{total}] {spec.name:<8} {os.path.basename(bench):<44} "
                    f"exp={exp:<7} got={got:<7} {run.wall_time:6.2f}s{flag}",
                    file=sys.stderr,
                )
    return per_bench


def score_everything(
    per_bench: dict[str, dict[str, RawResult]],
    solver_names: list[str],
    track: Track,
    wall_limit: float,
    cores: int,
) -> dict:
    """Compute benchmark scores, division scores, and the competition-wide
    rankings. Returns a JSON-able report."""
    # 1. Benchmark score tuples per (solver, benchmark).
    bscore: dict[str, dict[str, Score]] = defaultdict(dict)
    for bench, by_solver in per_bench.items():
        for name, raw in by_solver.items():
            bscore[bench][name] = benchmark_score(raw, track, wall_limit, cores)

    # 2. Disagreement removal (Single Query only, §7.2).
    removed: set[str] = set()
    if track == Track.SINGLE_QUERY:
        removed = find_disagreements(per_bench)

    # 3. Group benchmarks into divisions.
    div_benches: dict[str, list[str]] = defaultdict(list)
    for bench, by_solver in per_bench.items():
        if bench in removed:
            continue
        division = next(iter(by_solver.values())).division
        div_benches[division].append(bench)

    # 4. Per-division: aggregate parallel/PAR-2/sequential per solver, and
    #    determine competitiveness + soundness.
    report_divs = {}
    division_scores_by_solver: dict[str, list[DivisionScore]] = defaultdict(list)
    for division, benches in sorted(div_benches.items()):
        N = len(benches)
        per_solver_par: dict[str, Score] = {}
        per_solver_par2: dict[str, Score] = {}
        per_solver_seq: dict[str, Score] = {}
        sound: set[str] = set()
        # per-benchmark score maps for vbss (only over this division's benches)
        div_bscore = {b: bscore[b] for b in benches}
        for name in solver_names:
            par_list = [bscore[b][name] for b in benches if name in bscore[b]]
            par2_list = [par2_benchmark(s, wall_limit, cores) for s in par_list]
            seq_list = [sequential_score(s, wall_limit) for s in par_list]
            par = division_sum(par_list)
            per_solver_par[name] = par
            per_solver_par2[name] = division_sum(par2_list)
            per_solver_seq[name] = division_sum(seq_list)
            if par.e == 0:
                sound.add(name)
            division_scores_by_solver[name].append(
                DivisionScore(name, division, N, par)
            )

        # Ranking within the division by PAR-2 (parallel ordering).
        ranked = sorted(
            solver_names,
            key=lambda nm: parallel_sort_key(per_solver_par2[nm]),
        )

        # Biggest-lead correctness rank (top two by correctness n).
        by_correct = sorted(
            solver_names, key=lambda nm: -per_solver_par[nm].n
        )
        lead = None
        if len(by_correct) >= 2:
            lead = biggest_lead_correctness_rank(
                per_solver_par[by_correct[0]].n,
                per_solver_par[by_correct[1]].n,
            )

        # Largest-contribution ranks require > 2 sound competitive solvers.
        contribution = None
        if len(sound) > 2:
            contribution = largest_contribution_ranks(div_bscore, sound)

        report_divs[division] = {
            "n_benchmarks": N,
            "competitive": len(solver_names) >= 2,
            "sound_solvers": sorted(sound),
            "ranking_par2": ranked,
            "biggest_lead_correctness_rank": lead,
            "solvers": {
                name: {
                    "parallel": _score_json(per_solver_par[name]),
                    "par2": _score_json(per_solver_par2[name]),
                    "sequential": _score_json(per_solver_seq[name]),
                }
                for name in solver_names
            },
            "largest_contribution": contribution,
        }

    # 5. Best-overall ranking (over competitive divisions the solver entered).
    best_overall = {
        name: best_overall_score(division_scores_by_solver[name])
        for name in solver_names
    }
    best_overall_ranked = sorted(
        solver_names, key=lambda nm: -best_overall[nm]
    )

    return {
        "track": track.value,
        "wall_limit_s": wall_limit,
        "cores": cores,
        "n_benchmarks": len(per_bench),
        "n_removed_disagreements": len(removed),
        "removed_disagreements": sorted(os.path.basename(b) for b in removed),
        "divisions": report_divs,
        "best_overall_score": best_overall,
        "best_overall_ranking": best_overall_ranked,
    }


def raw_to_json(per_bench: dict[str, dict[str, RawResult]]) -> dict:
    """Serialize the raw execution table so execution (hardware-bound, shardable)
    can be separated from scoring (deterministic, central) — mirroring how
    SMT-COMP's BenchExec results feed the central `smtcomp` scoring tool."""
    out: dict[str, dict] = {}
    for bench, by_solver in per_bench.items():
        out[bench] = {}
        for name, r in by_solver.items():
            out[bench][name] = {
                "solver": r.solver,
                "benchmark": r.benchmark,
                "division": r.division,
                "logic": r.logic,
                "expected_status": r.expected_status.value if r.expected_status else None,
                "reported_status": r.reported_status.value if r.reported_status else None,
                "wall_time": r.wall_time,
                "cpu_time": r.cpu_time,
                "num_named_assertions": r.num_named_assertions,
            }
    return out


def raw_from_json(blobs: list[dict]) -> dict[str, dict[str, RawResult]]:
    """Merge one or more raw-result JSON blobs (e.g. from different shards/hosts)
    into a single per-benchmark table."""
    per: dict[str, dict[str, RawResult]] = defaultdict(dict)

    def _st(v):
        return Status(v) if v else None

    for blob in blobs:
        for bench, by_solver in blob.items():
            for name, d in by_solver.items():
                per[bench][name] = RawResult(
                    solver=d["solver"],
                    benchmark=d["benchmark"],
                    division=d["division"],
                    logic=d["logic"],
                    expected_status=_st(d["expected_status"]),
                    reported_status=_st(d["reported_status"]),
                    wall_time=d["wall_time"],
                    cpu_time=d["cpu_time"],
                    num_named_assertions=d.get("num_named_assertions"),
                )
    return per


def _score_json(s: Score) -> dict:
    return {
        "e": s.e,
        "n": s.n,
        "wall": round(s.w, 3),
        "cpu": round(s.c, 3),
        "aw": round(s.aw, 3),
        "ac": round(s.ac, 3),
    }


def print_scoreboard(report: dict) -> None:
    print(f"\n{'='*72}")
    print(f"SMT-COMP reproduction — track={report['track']}  "
          f"T={report['wall_limit_s']}s  cores={report['cores']}")
    print(f"benchmarks={report['n_benchmarks']}  "
          f"removed_disagreements={report['n_removed_disagreements']}")
    print("=" * 72)
    for division, d in report["divisions"].items():
        print(f"\n### division {division}  (N={d['n_benchmarks']}, "
              f"{'competitive' if d['competitive'] else 'non-competitive'})")
        print(f"  {'solver':<10} {'e':>2} {'n':>5} {'PAR2-wall':>12} {'seq-cpu':>10}")
        for name in d["ranking_par2"]:
            s = d["solvers"][name]
            par = s["parallel"]
            par2 = s["par2"]
            seq = s["sequential"]
            print(f"  {name:<10} {par['e']:>2} {par['n']:>5} "
                  f"{par2['wall']:>12.1f} {seq['cpu']:>10.1f}")
        if d["biggest_lead_correctness_rank"] is not None:
            print(f"  biggest-lead correctness rank (top2): "
                  f"{d['biggest_lead_correctness_rank']:.3f}")
        if d["largest_contribution"]:
            print("  largest-contribution correctness ranks:")
            for name, ranks in sorted(
                d["largest_contribution"].items(), key=lambda kv: -kv[1]["n"]
            ):
                print(f"    {name:<10} contrib_n={ranks['n']:.3f}")
    print(f"\n### Best Overall Ranking")
    for name in report["best_overall_ranking"]:
        print(f"  {name:<10} overall_score={report['best_overall_score'][name]:.4f}")
    print()


def main() -> int:
    ap = argparse.ArgumentParser(description="SMT-COMP scoring reproduction")
    ap.add_argument("--corpus", default=None)
    ap.add_argument(
        "--solver", action="append", default=None,
        help="name=exe [args...] ; use {bench} for the benchmark path",
    )
    ap.add_argument("--track", default="single_query",
                    choices=[t.value for t in Track])
    ap.add_argument("--wall-limit", type=float, default=20.0)
    ap.add_argument("--mem-gb", type=float, default=None)
    ap.add_argument("--cores", type=int, default=DEFAULT_CORES)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--internal-timeout-ms", type=int, default=None,
                    help="soft internal timeout passed to axeyum (ms)")
    ap.add_argument("--out", default=None)
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--shard", default=None,
                    help="I/J : run only shard I of J (benchmarks striped)")
    ap.add_argument("--dump-raw", default=None,
                    help="write raw execution results to this JSON and skip scoring")
    ap.add_argument("--score-raw", nargs="+", default=None,
                    help="score these raw-result JSON files instead of executing")
    args = ap.parse_args()

    solvers = [parse_solver_arg(s) for s in args.solver] if args.solver else []
    track = Track(args.track)

    # Score-only mode: merge raw JSON blobs and score centrally (deterministic).
    if args.score_raw:
        blobs = []
        for path in args.score_raw:
            with open(path, "r", encoding="utf-8") as fh:
                blobs.append(json.load(fh))
        per_bench = raw_from_json(blobs)
        names: list[str] = []
        for by in per_bench.values():
            for nm in by:
                if nm not in names:
                    names.append(nm)
        report = score_everything(per_bench, names, track, args.wall_limit, args.cores)
        print_scoreboard(report)
        if args.out:
            with open(args.out, "w", encoding="utf-8") as fh:
                json.dump(report, fh, indent=2)
        return 0

    if not solvers or not args.corpus:
        print("--corpus and --solver required (unless --score-raw)", file=sys.stderr)
        return 1

    benchmarks = collect_benchmarks(args.corpus, args.limit)
    if args.shard:
        i, j = (int(x) for x in args.shard.split("/") if x) if "/" in args.shard \
            else (int(args.shard.split(":")[0]), int(args.shard.split(":")[1]))
        benchmarks = [b for k, b in enumerate(benchmarks) if k % j == i]
    if not benchmarks:
        print(f"no .smt2 benchmarks under {args.corpus}", file=sys.stderr)
        return 1
    mem_limit = int(args.mem_gb * 1024**3) if args.mem_gb else None

    print(f"solvers={[s.name for s in solvers]}  benchmarks={len(benchmarks)}  "
          f"track={track.value}  T={args.wall_limit}s", file=sys.stderr)

    per_bench = run_all(
        solvers, benchmarks, track, args.wall_limit, mem_limit, args.cores,
        args.internal_timeout_ms, verbose=not args.quiet,
    )

    if args.dump_raw:
        with open(args.dump_raw, "w", encoding="utf-8") as fh:
            json.dump(raw_to_json(per_bench), fh, indent=2)
        print(f"wrote raw results {args.dump_raw}", file=sys.stderr)
        return 0

    report = score_everything(
        per_bench, [s.name for s in solvers], track, args.wall_limit, args.cores
    )
    print_scoreboard(report)
    if args.out:
        with open(args.out, "w", encoding="utf-8") as fh:
            json.dump(report, fh, indent=2)
        print(f"wrote {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
