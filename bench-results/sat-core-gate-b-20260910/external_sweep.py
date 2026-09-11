#!/usr/bin/env python3
"""Gate (b) external-engine sweep: run one external SAT binary over a directory
of DIMACS files, one file at a time, under a fixed per-file wall budget.

Deliberately mirrors `crates/axeyum-bench/examples/gate_b_sweep.rs`'s `sweep`
subcommand so the two arms are comparable:

  * one TSV row per file, **appended**, so a long sweep is resumable in
    bounded batches (a file already named in column 1 is skipped);
  * a refusal to append to a TSV whose header is not this tool's header, so a
    file cannot end up with two meanings for the same column;
  * every `sat` verdict is model-checked through the SAME trusted evaluator the
    native arm uses -- `gate_b_sweep verify`, i.e. `CnfFormula::evaluate` --
    rather than by trusting the external solver's own claim.

Exit-code convention is the DIMACS one both CaDiCaL and Kissat follow:
10 = SATISFIABLE, 20 = UNSATISFIABLE, anything else = no verdict.

ONE BIAS THIS DOES NOT CORRECT, stated because it runs in our favour: the
native arm starts its clock AFTER parsing the DIMACS, while an external binary
pays parse time inside its budget. The measured reference advantage is
therefore a LOWER bound.

Usage:
  external_sweep.py <engine_bin> <cnf_dir> <out.tsv> <budget_secs> \
      [max_files] [--taskset 0-7] [--verify <gate_b_sweep binary>]
"""

import os
import subprocess
import sys
import tempfile
import time

HEADER = "file\tverdict\twall_ms\ttimed_out\tmodel_check"


def parse_args(argv):
    positional = []
    taskset = None
    verify = None
    i = 0
    while i < len(argv):
        if argv[i] == "--taskset":
            taskset = argv[i + 1]
            i += 2
        elif argv[i] == "--verify":
            verify = argv[i + 1]
            i += 2
        else:
            positional.append(argv[i])
            i += 1
    if len(positional) < 4:
        sys.exit(__doc__)
    engine, cnf_dir, out_tsv, budget = positional[:4]
    max_files = int(positional[4]) if len(positional) > 4 else None
    return engine, cnf_dir, out_tsv, float(budget), max_files, taskset, verify


def done_set(out_tsv):
    done = set()
    if os.path.exists(out_tsv):
        with open(out_tsv, encoding="utf-8") as handle:
            lines = handle.read().splitlines()
        if lines and lines[0] != HEADER:
            sys.exit(
                f"{out_tsv} has a different header and was written by another "
                f"column set; refusing to append.\n  found:  {lines[0]}\n"
                f"  expect: {HEADER}"
            )
        for line in lines[1:]:
            name = line.split("\t")[0]
            if name:
                done.add(name)
    return done


def main():
    engine, cnf_dir, out_tsv, budget, max_files, taskset, verify = parse_args(
        sys.argv[1:]
    )
    already = done_set(out_tsv)
    files = sorted(f for f in os.listdir(cnf_dir) if f.endswith(".cnf"))
    pending = [f for f in files if f not in already]
    if max_files is not None:
        pending = pending[:max_files]

    need_header = not os.path.exists(out_tsv)
    with open(out_tsv, "a", encoding="utf-8") as out:
        if need_header:
            out.write(HEADER + "\n")
            out.flush()
        for name in pending:
            path = os.path.join(cnf_dir, name)
            cmd = []
            if taskset:
                cmd += ["taskset", "-c", taskset]
            cmd += [engine, "-q", path]
            started = time.monotonic()
            timed_out = False
            try:
                proc = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=budget,
                    check=False,
                )
                code, stdout = proc.returncode, proc.stdout
            except subprocess.TimeoutExpired:
                timed_out = True
                code, stdout = None, ""
            wall_ms = (time.monotonic() - started) * 1000.0

            if code == 10:
                verdict = "sat"
            elif code == 20:
                verdict = "unsat"
            else:
                verdict = "unknown"

            model_check = ""
            if verdict == "sat":
                model_check = "not-checked"
                if verify:
                    with tempfile.NamedTemporaryFile(
                        "w", suffix=".sol", delete=False
                    ) as handle:
                        handle.write(stdout)
                        sol = handle.name
                    try:
                        checked = subprocess.run(
                            [verify, "verify", path, sol],
                            capture_output=True,
                            text=True,
                            check=False,
                        )
                        model_check = (
                            "ok"
                            if checked.returncode == 0
                            else f"FAIL:{checked.stdout.strip()}"
                        )
                    finally:
                        os.unlink(sol)

            out.write(
                f"{name}\t{verdict}\t{wall_ms}\t{str(timed_out).lower()}\t"
                f"{model_check}\n"
            )
            out.flush()
            print(f"{name}\t{verdict}\t{wall_ms:.1f}\t{model_check}", flush=True)


if __name__ == "__main__":
    main()
