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
from pathlib import Path
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
                if name in per[bench]:
                    raise ValueError(
                        f"duplicate raw result for benchmark={bench!r}, solver={name!r}"
                    )
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


def _without_options(argv: list[str], options_with_values: set[str], flags: set[str]) -> list[str]:
    """Remove exact orchestration-only options from a parsed CLI argument list."""

    cleaned: list[str] = []
    skip_value = False
    for token in argv:
        if skip_value:
            skip_value = False
            continue
        if token in flags:
            continue
        if token in options_with_values:
            skip_value = True
            continue
        if any(token.startswith(f"{option}=") for option in options_with_values):
            continue
        cleaned.append(token)
    if skip_value:
        raise ValueError("orchestration option lacks its value")
    return cleaned


def _parse_host_shards(spec: str | None, shard_count: int) -> list[int]:
    if spec is None:
        return list(range(shard_count))
    tokens = spec.split(",")
    if (
        not tokens
        or any(not token.isascii() or not token.isdigit() for token in tokens)
    ):
        raise ValueError("--host-shards must be canonical comma-separated integers")
    shard_ids = [int(token) for token in tokens]
    if (
        shard_ids != sorted(set(shard_ids))
        or any(str(shard_id) != token for shard_id, token in zip(shard_ids, tokens, strict=True))
        or any(not 0 <= shard_id < shard_count for shard_id in shard_ids)
    ):
        raise ValueError("--host-shards must be sorted, unique, and in range")
    return shard_ids


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
    ap.add_argument("--file-list", default=None,
                    help="run over the .smt2 paths in this file (one per line) "
                         "instead of globbing --corpus")
    ap.add_argument("--shard", default=None,
                    help="I/J : run only shard I of J (benchmarks striped)")
    ap.add_argument("--dump-raw", default=None,
                    help="write raw execution results to this JSON and skip scoring")
    ap.add_argument("--score-raw", nargs="+", default=None,
                    help="score these raw-result JSON files instead of executing")
    ap.add_argument("--run-manifest", default=None,
                    help="canonical v2 resumable run manifest (requires --run-dir)")
    ap.add_argument("--run-dir", default=None,
                    help="immutable resumable evidence directory")
    ap.add_argument("--host-run", action="store_true",
                    help="run every registered shard inside one E2 aggregate cgroup")
    ap.add_argument("--host-shards", default=None,
                    help="canonical shard subset owned by this E3 host allocation")
    ap.add_argument("--host-session-id", default=None,
                    help="preregistered E3 resource session for this host allocation")
    ap.add_argument("--resource-session-id", default=None, help=argparse.SUPPRESS)
    ap.add_argument("--selection-manifest", default=None,
                    help="selection identity artifact required by resumable mode")
    ap.add_argument("--corpus-manifest", default=None,
                    help="corpus identity artifact required by resumable mode")
    ap.add_argument("--environment-manifest", default=None,
                    help="registered environment-class artifact for resumable mode")
    ap.add_argument("--source-identity-manifest", default=None,
                    help="content-bound source identity for a staged E3 runner bundle")
    ap.add_argument("--benchmark-id-marker", default="non-incremental/",
                    help="prefix removed from absolute paths for result identity")
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

    resumable = args.run_manifest is not None or args.run_dir is not None
    if resumable:
        from resume_contract import ContractError
        from resume_fs import validate_bundle_directory
        from resume_runner import (
            execute_resumable,
            export_legacy_raw,
            preflight_resumable,
            sha256_file,
        )
        from resource_enforcement import (
            build_preflight,
            build_resource_completion,
            build_terminal,
            cgroup_snapshot,
            configure_current_cgroup,
            install_preflight,
            install_resource_completion,
            install_terminal,
            new_session_id,
            run_under_systemd,
            run_worker_pool,
            validate_enforcement,
        )

        try:
            if not args.run_manifest or not args.run_dir:
                raise ContractError("--run-manifest and --run-dir are required together")
            if len(solvers) != 1:
                raise ContractError("resumable mode requires exactly one --solver")
            if not args.file_list or args.corpus:
                raise ContractError("resumable mode requires --file-list and forbids --corpus")
            if args.limit is not None or args.out:
                raise ContractError("resumable mode forbids --limit and --out")
            if args.host_run and args.shard:
                raise ContractError("--host-run owns all shards and forbids --shard")
            if args.host_shards is not None and not args.host_run:
                raise ContractError("--host-shards requires --host-run")
            if args.host_session_id is not None and not args.host_run:
                raise ContractError("--host-session-id requires --host-run")
            if not args.host_run and not args.shard:
                raise ContractError("resumable shard mode requires --shard I/J")
            if not all(
                (args.selection_manifest, args.corpus_manifest, args.environment_manifest)
            ):
                raise ContractError(
                    "resumable mode requires selection, corpus, and environment manifests"
                )
            if args.mem_gb is None:
                raise ContractError("resumable mode requires an explicit --mem-gb")
            if track != Track.SINGLE_QUERY:
                raise ContractError("resumable records currently support single_query only")
            spec = solvers[0]
            command_template = list(spec.cmd_template)
            if args.internal_timeout_ms is not None and spec.name == "axeyum":
                command_template.extend(["--timeout-ms", str(args.internal_timeout_ms)])
            root = Path(__file__).resolve().parents[2]
            run_manifest = Path(args.run_manifest)
            run_dir = Path(args.run_dir)
            file_list = Path(args.file_list)
            selection_manifest = Path(args.selection_manifest)
            corpus_manifest = Path(args.corpus_manifest)
            environment_manifest = Path(args.environment_manifest)
            source_identity_manifest = (
                Path(args.source_identity_manifest)
                if args.source_identity_manifest is not None
                else None
            )
            wall_limit_ms = round(args.wall_limit * 1000)
            memory_limit_bytes = round(args.mem_gb * 1024**3)

            if args.host_run:
                claimed = json.loads(run_manifest.read_text(encoding="utf-8"))
                shard_count = claimed.get("identity", {}).get("shard_count")
                if not isinstance(shard_count, int):
                    raise ContractError("run manifest lacks a valid shard count")
                host_shards = _parse_host_shards(args.host_shards, shard_count)
                run, identity, run_hash, _inputs = preflight_resumable(
                    run_manifest=run_manifest,
                    repository_root=root,
                    source_root=Path(__file__).resolve().parent,
                    file_list=file_list,
                    selection_manifest=selection_manifest,
                    corpus_manifest=corpus_manifest,
                    environment_manifest=environment_manifest,
                    solver_id=spec.name,
                    command_template=command_template,
                    track=track.value,
                    wall_limit_ms=wall_limit_ms,
                    memory_limit_bytes=memory_limit_bytes,
                    cores=args.cores,
                    shard_index=None,
                    shard_count=shard_count,
                    benchmark_id_marker=args.benchmark_id_marker,
                    resource_session_id=args.resource_session_id,
                    require_active_enforcement=False,
                    source_identity_manifest=source_identity_manifest,
                )
                enforcement = validate_enforcement(run, require_measurement=True)
                from resource_enforcement import MULTI_HOST_KIND

                multi_host = enforcement["kind"] == MULTI_HOST_KIND
                if multi_host != (args.host_shards is not None):
                    raise ContractError(
                        "E3 enforcement and explicit host-shard allocation must agree"
                    )
                if multi_host and args.dump_raw:
                    raise ContractError("E3 host allocations cannot export raw output")

                if args.resource_session_id is None:
                    if (run_dir / "resource-completion.json").exists():
                        validate_bundle_directory(
                            run_dir,
                            require_output_sidecars=True,
                            require_resource_evidence=True,
                        )
                        if args.dump_raw:
                            export_legacy_raw(run_dir, Path(args.dump_raw))
                        return 0
                    session_id = args.host_session_id or new_session_id(run_hash)
                    inside = [
                        sys.executable,
                        str(Path(__file__).resolve()),
                        *sys.argv[1:],
                        "--resource-session-id",
                        session_id,
                    ]
                    return run_under_systemd(
                        enforcement=enforcement,
                        session_id=session_id,
                        command=inside,
                    )

                session_id = args.resource_session_id
                if args.host_session_id is not None and args.host_session_id != session_id:
                    raise ContractError("outer and active resource session identities differ")
                configure_current_cgroup(enforcement, session_id=session_id)
                initial_snapshot = cgroup_snapshot()
                preflight = build_preflight(
                    run=run,
                    session_id=session_id,
                    environment_class_sha256=sha256_file(environment_manifest),
                    snapshot=initial_snapshot,
                    shard_ids=host_shards,
                )
                install_preflight(run_dir, preflight)
                child_args = _without_options(
                    sys.argv[1:],
                    {
                        "--resource-session-id",
                        "--dump-raw",
                        "--shard",
                        "--host-shards",
                        "--host-session-id",
                    },
                    {"--host-run"},
                )
                commands = [
                    [
                        sys.executable,
                        str(Path(__file__).resolve()),
                        *child_args,
                        "--resource-session-id",
                        session_id,
                        "--shard",
                        f"{shard}/{shard_count}",
                    ]
                    for shard in host_shards
                ]
                try:
                    worker_codes = run_worker_pool(
                        commands, enforcement["worker_slots"]
                    )
                except (ContractError, OSError):
                    worker_codes = [125] * len(host_shards)
                    install_terminal(
                        run_dir,
                        build_terminal(
                            preflight=preflight,
                            final_snapshot=cgroup_snapshot(),
                            enforcement=enforcement,
                            worker_exit_codes=worker_codes,
                        ),
                    )
                    raise
                terminal = build_terminal(
                    preflight=preflight,
                    final_snapshot=cgroup_snapshot(),
                    enforcement=enforcement,
                    worker_exit_codes=worker_codes,
                )
                install_terminal(run_dir, terminal)
                if any(code != 0 for code in worker_codes):
                    return 2
                if multi_host:
                    return 0
                validate_bundle_directory(
                    run_dir,
                    require_output_sidecars=True,
                    require_resource_evidence=False,
                    require_multi_host_evidence=False,
                )
                install_resource_completion(
                    run_dir,
                    build_resource_completion(run=run, run_dir=run_dir),
                )
                validate_bundle_directory(
                    run_dir,
                    require_output_sidecars=True,
                    require_resource_evidence=True,
                )
                if args.dump_raw:
                    export_legacy_raw(run_dir, Path(args.dump_raw))
                    print(f"wrote raw results {args.dump_raw}", file=sys.stderr)
                return 0

            if args.resource_session_id is not None and not args.shard:
                raise ContractError("resource session requires host or shard mode")
            if "/" not in args.shard:
                raise ContractError("resumable mode requires --shard I/J")
            shard_index, shard_count = (int(value) for value in args.shard.split("/", 1))
            complete = execute_resumable(
                run_manifest=run_manifest,
                run_dir=run_dir,
                repository_root=root,
                source_root=Path(__file__).resolve().parent,
                file_list=file_list,
                selection_manifest=selection_manifest,
                corpus_manifest=corpus_manifest,
                environment_manifest=environment_manifest,
                solver_id=spec.name,
                command_template=command_template,
                track=track.value,
                wall_limit_ms=wall_limit_ms,
                memory_limit_bytes=memory_limit_bytes,
                cores=args.cores,
                shard_index=shard_index,
                shard_count=shard_count,
                benchmark_id_marker=args.benchmark_id_marker,
                verbose=not args.quiet,
                resource_session_id=args.resource_session_id,
                source_identity_manifest=source_identity_manifest,
            )
            if complete and args.dump_raw:
                if args.resource_session_id is not None:
                    raise ContractError("shard workers cannot export aggregate raw output")
                export_legacy_raw(run_dir, Path(args.dump_raw))
                print(f"wrote raw results {args.dump_raw}", file=sys.stderr)
            elif args.dump_raw:
                print("run remains incomplete; raw export withheld", file=sys.stderr)
            return 0
        except (ContractError, ValueError, OSError) as exc:
            print(f"resumable run rejected: {exc}", file=sys.stderr)
            return 2

    if not solvers or not (args.corpus or args.file_list):
        print("--corpus or --file-list, and --solver, required (unless --score-raw)",
              file=sys.stderr)
        return 1

    if args.file_list:
        with open(args.file_list, "r", encoding="utf-8") as fh:
            benchmarks = [ln.strip() for ln in fh if ln.strip()]
        if args.limit is not None:
            benchmarks = benchmarks[: args.limit]
    else:
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
