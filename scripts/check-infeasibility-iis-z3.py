#!/usr/bin/env python3
"""Independent z3 re-derivation of the infeasibility-explanation measurements.

WHY THIS IS SEPARATE FROM THE GATE. `crates/axeyum-solver/examples/infeasibility_iis.rs`
measures the same four things with our own solver, and it is what the fact
ledger's `checker_command` runs, because the ledger's replay gate must work in a
clean checkout with no C/C++ dependency. This script is the CROSS-ORACLE arm:
it re-derives the core and every leave-one-out verdict with z3 and shares no
code with us. Cross-oracle agreement is the strongest signal this repository
has, so it is committed and named in each fact's `checkers`, rather than left in
a lane's shell history.

It is deliberately NOT a `checker_command`: a gate that needs z3 on PATH would
either fail on a machine without it or -- much worse -- be written to exit 0 when
it found nothing to do, which is the inert-gate pattern this repository has
shipped several times.

Requires `z3` on PATH and FAILS LOUDLY if it is absent.

    python3 scripts/check-infeasibility-iis-z3.py
    python3 scripts/check-infeasibility-iis-z3.py artifacts/instances/infeasibility/roster-icu-night.smt2

Per instance it checks, all against z3 alone:
  * the model is `unsat`;
  * z3's own `(get-unsat-core)` is a subset of the `:named` rows;
  * that core ALONE re-solves to `unsat`;
  * every leave-one-out subset of the core solves to `sat` (IRREDUCIBILITY);
  * the instance MINUS the core solves to `sat` (the contradiction is buried).
Exit status is 0 only if every one of those held for every instance.
"""

import glob
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# Row-name -> assertion body, from the one-line `(assert (! <body> :named <n>))`
# form the generator emits. Anything that does not match that shape is not a row.
ROW = re.compile(r"^\(assert \(! (.*) :named ([A-Za-z0-9_]+)\)\)")


def load(path):
    head, rows = [], []
    with open(path) as handle:
        for line in handle:
            stripped = line.strip()
            match = ROW.match(stripped)
            if match:
                rows.append((match.group(2), stripped.split(";")[0].rstrip()))
            elif stripped.startswith(("(declare-fun", "(set-logic")):
                head.append(stripped)
    return head, rows


def solve(head, rows, names):
    script = "\n".join(head + [t for (n, t) in rows if n in names] + ["(check-sat)"])
    done = subprocess.run(
        ["z3", "-smt2", "-in"], input=script, capture_output=True, text=True, timeout=600
    )
    out = done.stdout.strip().splitlines()
    return out[-1] if out else f"<z3 error: {done.stderr.strip()}>"


def check(path):
    name = os.path.basename(path)
    done = subprocess.run(["z3", "-smt2", path], capture_output=True, text=True, timeout=600)
    out = done.stdout.strip().splitlines()
    if not out or out[0] != "unsat":
        print(f"FAIL {name}: expected unsat, z3 said {out[:1]}")
        return False
    core = out[1].strip("()").split() if len(out) > 1 else []
    head, rows = load(path)
    all_names = [n for n, _ in rows]
    problems = []
    unknown = set(core) - set(all_names)
    if unknown:
        problems.append(f"core names non-rows {sorted(unknown)}")
    if solve(head, rows, set(core)) != "unsat":
        problems.append("the core alone is not unsat")
    for dropped in sorted(core):
        got = solve(head, rows, set(core) - {dropped})
        if got != "sat":
            problems.append(f"dropping {dropped} gave {got}, not sat (core is reducible)")
    if solve(head, rows, set(all_names) - set(core)) != "sat":
        problems.append("the instance minus the core is not sat (contradiction not buried)")
    ratio = 100.0 * len(core) / len(all_names)
    status = "ok  " if not problems else "FAIL"
    print(f"{status} {name:<26} core {len(core):>2} of {len(all_names):>3} rows ({ratio:4.1f}%)")
    for problem in problems:
        print(f"       {problem}")
    return not problems


def main():
    if shutil.which("z3") is None:
        print("check-infeasibility-iis-z3: z3 is not on PATH", file=sys.stderr)
        return 2
    paths = sys.argv[1:] or sorted(
        glob.glob(os.path.join(ROOT, "artifacts/instances/infeasibility/*.smt2"))
    )
    if not paths:
        print("check-infeasibility-iis-z3: no instances found", file=sys.stderr)
        return 2
    version = subprocess.run(["z3", "--version"], capture_output=True, text=True).stdout.strip()
    print(f"oracle: {version}")
    ok = all([check(path) for path in paths])
    print(f"\n{len(paths)} instance(s) cross-checked, {'all agree' if ok else 'DISAGREEMENT'}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
