#!/usr/bin/env python3
"""The control that can actually FAIL for the eager-split transform.

## Why the obvious control is vacuous, measured

The surrogate's first control re-checked the TRANSFORMED file against z3 and
cvc5 and compared to the original's declared `:status`.  It reported 0
disagreements on 29 of 29 -- and it reports 0 disagreements on a DELIBERATELY
BROKEN transform too.  Measured: mutating the case-split scaling so that `a = k`
implies `r = (k+1)*b` instead of `r = k*b` -- a linearization that is simply
wrong -- still produced `sat` from z3 on 5 of 5 files, 0 disagreements.

The reason is structural, not a bug in the checker: these queries are
SATISFIABLE and underconstrained, so a wrong linearization still has a model.
It is just a different model.  A sat-side reference check cannot distinguish a
correct transform from an incorrect one, and reporting its zero as evidence
would be reporting the thing the check prints when it is broken.

## The control with teeth

Run the same transform over the winnable files whose truth is UNSAT.  There a
wrong linearization has somewhere to go: it can admit a model that the original
forbids, and the reference then answers `sat` where the original is `unsat`.
That is a disagreement the checker can see.

Both arms are run in one pass so the finding does not depend on the maintainer
remembering to run the mutant:

  * `correct` -- the shipped transform; every row must stay `unsat`.
  * `mutant`  -- the off-by-one scaling; at least one row MUST flip to `sat`,
                 or this control is itself vacuous and the exit status says so.

Exit status is 0 only when the correct arm has no flips AND the mutant arm has
at least one.  A control that cannot fail is worse than no control, so the
mutant arm's flip count is a REQUIREMENT, not an observation.
"""
import argparse
import concurrent.futures as cf
import csv
import importlib.util
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True,
                      text=True, cwd=HERE).stdout.strip()
D = os.path.join(ROOT, "bench-results/qf-nia-sat-20260913")
CVC5 = "/nas3/data/axeyum/harness/bin/cvc5"

spec = importlib.util.spec_from_file_location(
    "sur", os.path.join(HERE, "qf-nia-sat-eager-split-surrogate.py"))
sur = importlib.util.module_from_spec(spec)
spec.loader.exec_module(sur)

_TRUE_SCALE = sur.scale


def _mutant_scale(k, term):
    """`a = k` wrongly implying `r = (k+1)*b`. The mutation under test."""
    return _TRUE_SCALE(k + 1, term)


def transform_with(path, out_path, mutate):
    sur.scale = _mutant_scale if mutate else _TRUE_SCALE
    try:
        return sur.transform(path, out_path)
    finally:
        sur.scale = _TRUE_SCALE


def one(path, outdir, arm, timeout_s):
    tag = f"{arm}__{os.path.basename(path)}"
    tpath = os.path.join(outdir, tag)
    try:
        stats = transform_with(path, tpath, arm == "mutant")
    except Exception as exc:  # noqa: BLE001
        return {"arm": arm, "file": path, "z3": f"ERR {exc}", "split": -1}
    z3v = sur.run_solver(["z3", f"-T:{timeout_s}", tpath], timeout_s + 30)
    return {"arm": arm, "file": path, "z3": z3v, "split": stats["split"],
            "residual": stats["residual"]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--out", default=os.path.join(D, "transform-control.tsv"))
    ap.add_argument("--limit", type=int, default=10,
                    help="unsat winnable files to use")
    ap.add_argument("--timeout-s", type=int, default=60)
    ap.add_argument("--workers", type=int, default=3)
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)
    rows = list(csv.DictReader(
        open(os.path.join(D, "remaining-winnable.tsv")), delimiter="\t"))
    # Only files the transform actually touches are a test of the transform.
    unsat = [r["file"] for r in rows if r["truth"] == "unsat"][: args.limit]
    print(f"{len(unsat)} unsat winnable files, two arms each", flush=True)

    out = []
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(one, f, args.outdir, arm, args.timeout_s)
                for f in unsat for arm in ("correct", "mutant")]
        for n, fut in enumerate(cf.as_completed(futs), 1):
            out.append(fut.result())
            if n % 5 == 0:
                print(f"  {n}/{len(futs)}", flush=True)
    out.sort(key=lambda r: (r["file"], r["arm"]))
    with open(args.out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["arm", "file", "z3", "split", "residual"],
                           delimiter="\t", extrasaction="ignore")
        w.writeheader()
        w.writerows(out)

    def flips(arm):
        return [r for r in out if r["arm"] == arm and r["z3"] == "sat"]

    touched = [r for r in out if r["arm"] == "correct" and r.get("split", 0) > 0]
    opinion = [r for r in out if r["arm"] == "correct" and r["z3"] in ("sat", "unsat")]
    cf_, mf = flips("correct"), flips("mutant")
    print(f"\nwrote {args.out}")
    print(f"files the transform actually rewrote (split > 0): {len(touched)} of {len(unsat)}")
    print(f"files where z3 has an opinion on the correct arm : {len(opinion)} of {len(unsat)}")
    print(f"correct arm -- unsat files that became `sat`: {len(cf_)}   (must be 0)")
    for r in cf_:
        print("   SOUNDNESS FLIP", os.path.basename(r["file"]))
    print(f"mutant  arm -- unsat files that became `sat`: {len(mf)}   (must be >= 1)")

    ok = True
    if cf_:
        print("\nFAIL: the shipped transform turned an unsat query satisfiable.")
        ok = False
    if not mf:
        print("\nFAIL: the mutant was not caught, so this control is VACUOUS and its "
              "zero on the correct arm means nothing.")
        ok = False
    print("\nCONTROL PASSES" if ok else "\nCONTROL FAILS")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
