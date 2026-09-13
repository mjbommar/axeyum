#!/usr/bin/env python3
"""SIZING SURROGATE for the eager small-domain multiplication split.

## What is being sized, and why a surrogate

The QF_NIA sat half is dominated by one refusal: the pre-lowering CNF clause
estimate (29 of 40 files).  Raising that budget is a MEASURED NEGATIVE -- lane
`agent-nia-diagnosis` lifted it by the estimator's own 9.4x slack and decided
0 of 49, because "the refusal was in front of a search that does not finish
either".  So the budget is not the blocker; the multiplies are.  Every product
in these files has the shape `(* Nl<k> lam<j>)` where the `Nl` factor is pinned
by a top-level conjunct to `[-2, 2]` and the `lam` factor is unbounded.

The standing, never-refuted hypothesis in that lane's notes is an EAGER
small-domain split: case-split each product on its narrow factor so the query
becomes linear, and hand the result to a route that produces models.
`nia_linearize::small_domain_lemmas` already implements the split, but only
inside the RELAXATION -- a one-way device whose own docs say only `unsat`
transfers, so it structurally cannot produce a `sat`.

Rather than build the eager route and then find out, this script performs the
transformation OUTSIDE the solver and runs the existing CLI on the result.  That
makes reachability measurable before any solver code is written.

## Why the transformation is equisatisfiable, not a relaxation

For a product `a*b` where the top-level assertions entail `lo <= a <= hi` with
`hi - lo <= 4`, the rewrite

    a*b   ==>   (ite (= a lo) (lo*b) (ite (= a lo+1) ((lo+1)*b) ... (hi*b)))

is a term-for-term IDENTITY under those bounds: on any model of the original
assertions `a` takes one of the values `lo..hi`, and on that model the `ite`
selects the branch whose value IS `a*b`.  Each branch is a NUMERAL times a term,
so the result is linear.  The rewrite is therefore satisfiability-preserving in
BOTH directions -- unlike the relaxation, a `sat` on the transformed query is a
`sat` on the original, and its model is a model of the original.

Bounds are harvested ONLY from top-level asserted conjuncts, which is what makes
the entailment hold.  A variable whose box is not established that way is left
alone and its products are not split; such a file simply stays nonlinear and is
reported as not fully linearized.

## The controls this script runs

A surrogate that is wrong in the optimistic direction manufactures a target, so
two things are checked rather than assumed:

  * `--verify`: the transformed file is re-checked against z3 and cvc5 and must
    agree with the ORIGINAL's declared `:status`.  A transform that changed
    satisfiability shows up here as a disagreement.
  * `residual_mults`: the count of `*` nodes with two non-numeral operands left
    after the rewrite.  Only a file with 0 is actually handed to a linear route;
    the rest are reported separately and never counted as reachable.
"""
import argparse
import collections
import concurrent.futures as cf
import csv
import os
import re
import subprocess
import sys
import time

CVC5 = "/nas3/data/axeyum/harness/bin/cvc5"
MAX_SMALL_DOMAIN_WIDTH = 4  # matches nia_linearize::MAX_SMALL_DOMAIN_WIDTH


# ---------------------------------------------------------------- s-expressions
def tokenize(text):
    text = re.sub(r";[^\n]*", "", text)
    return re.findall(r"\(|\)|\|[^|]*\||\"[^\"]*\"|[^\s()]+", text)


def parse(tokens, i=0):
    """Iterative s-expression parse: these files nest far past the recursion limit."""
    out, stack = [], []
    cur = out
    while i < len(tokens):
        t = tokens[i]
        i += 1
        if t == "(":
            new = []
            cur.append(new)
            stack.append(cur)
            cur = new
        elif t == ")":
            if not stack:
                break
            cur = stack.pop()
        else:
            cur.append(t)
    return out


def render(node, buf):
    if isinstance(node, str):
        buf.append(node)
        return
    buf.append("(")
    for k, child in enumerate(node):
        if k:
            buf.append(" ")
        render(child, buf)
    buf.append(")")


# ---------------------------------------------------------------------- numerals
def as_int(node):
    """`5`, `(- 5)` -> int; anything else -> None."""
    if isinstance(node, str):
        return int(node) if re.fullmatch(r"-?\d+", node) else None
    if len(node) == 2 and node[0] == "-":
        inner = as_int(node[1])
        return None if inner is None else -inner
    return None


def numeral(k):
    return str(k) if k >= 0 else ["-", str(-k)]


# ------------------------------------------------------------- bound harvesting
def conjuncts(node):
    """Top-level asserted conjuncts, flattening `and`."""
    if isinstance(node, list) and node and node[0] == "and":
        for c in node[1:]:
            yield from conjuncts(c)
    else:
        yield node


def harvest_bounds(asserts):
    """`{var: (lo, hi)}` from top-level conjuncts only -- the entailment the
    rewrite's correctness rests on."""
    lo, hi = {}, {}

    def note_lo(v, k):
        lo[v] = max(lo.get(v, k), k)

    def note_hi(v, k):
        hi[v] = min(hi.get(v, k), k)

    for a in asserts:
        for c in conjuncts(a):
            if not isinstance(c, list) or len(c) != 3:
                continue
            op, x, y = c[0], c[1], c[2]
            xi, yi = as_int(x), as_int(y)
            if op == "<=":
                if xi is not None and isinstance(y, str):
                    note_lo(y, xi)
                elif yi is not None and isinstance(x, str):
                    note_hi(x, yi)
            elif op == ">=":
                if xi is not None and isinstance(y, str):
                    note_hi(y, xi)
                elif yi is not None and isinstance(x, str):
                    note_lo(x, yi)
            elif op == "<":
                if xi is not None and isinstance(y, str):
                    note_lo(y, xi + 1)
                elif yi is not None and isinstance(x, str):
                    note_hi(x, yi - 1)
            elif op == ">":
                if xi is not None and isinstance(y, str):
                    note_hi(y, xi - 1)
                elif yi is not None and isinstance(x, str):
                    note_lo(x, yi + 1)
            elif op == "=":
                if xi is not None and isinstance(y, str):
                    note_lo(y, xi), note_hi(y, xi)
                elif yi is not None and isinstance(x, str):
                    note_lo(x, yi), note_hi(x, yi)
    boxes = {}
    for v in set(lo) & set(hi):
        if lo[v] <= hi[v] and hi[v] - lo[v] <= MAX_SMALL_DOMAIN_WIDTH:
            boxes[v] = (lo[v], hi[v])
    return boxes


# ------------------------------------------------------------------- the rewrite
def scale(k, term):
    """`k * term` as a SUM, never as a `*` node.

    This is not cosmetic. `estimate_blast_clauses` charges `Op::BvMul` a flat
    `8w^2` with no case for a numeral operand -- measured: emitting `(* 2 b)`
    here left the estimate at 82,057,350 against a 64,000,000 ceiling on the
    first file, because three surviving numeral multiplies per split product are
    charged as full multipliers. A real lowering turns a small constant multiple
    into shifts and adds, so emitting it as a sum is what the transformation
    actually costs; leaving it as `*` would size the estimator's blind spot
    instead of the transformation.

    `|k| <= MAX_SMALL_DOMAIN_WIDTH`, so this is at most four additions.
    """
    ti = as_int(term)
    if ti is not None:
        return numeral(k * ti)
    if k == 0:
        return "0"
    mag = abs(k)
    acc = term if mag == 1 else ["+", *([term] * mag)]
    return acc if k > 0 else ["-", "0", acc]


class Rewriter:
    def __init__(self, boxes):
        self.boxes = boxes
        self.split = 0
        self.residual = 0

    def run(self, node):
        """Bottom-up rewrite. Iterative: these terms nest past the recursion limit."""
        if isinstance(node, str):
            return node
        done = {}
        order, stack = [], [(node, False)]
        while stack:
            cur, expanded = stack.pop()
            if isinstance(cur, str):
                continue
            if expanded:
                order.append(cur)
                continue
            stack.append((cur, True))
            for ch in cur:
                if isinstance(ch, list):
                    stack.append((ch, False))
        for cur in order:
            kids = [done[id(c)] if isinstance(c, list) else c for c in cur]
            done[id(cur)] = self.rewrite_node(kids)
        return done[id(node)]

    @staticmethod
    def fold(kids):
        """Light identity folding. Not cosmetic: these generators emit the narrow
        factor wrapped as `(+ 0 Nl2arg133)` and `(* Nl4arg33 1)`, which hides it
        from the narrow-factor test and was measured to leave 78 of 126 residual
        products on the first file. The real pipeline canonicalizes before
        blasting, so folding here compares like with like rather than flattering
        the surrogate."""
        if not kids or not isinstance(kids[0], str):
            return kids
        op = kids[0]
        if op == "+":
            args = [a for a in kids[1:] if as_int(a) != 0]
            if len(args) == 1:
                return args[0]
            if not args:
                return "0"
            return [op, *args]
        if op == "*":
            args = [a for a in kids[1:] if as_int(a) != 1]
            if len(args) == 1:
                return args[0]
            if not args:
                return "1"
            return [op, *args]
        if op == "-" and len(kids) == 3 and as_int(kids[2]) == 0:
            return kids[1]
        return kids

    def rewrite_node(self, kids):
        kids = self.fold(kids)
        if not isinstance(kids, list) or not kids or kids[0] != "*" or len(kids) != 3:
            return kids
        a, b = kids[1], kids[2]
        if as_int(a) is not None or as_int(b) is not None:
            return kids  # already linear
        narrow, other = None, None
        if isinstance(a, str) and a in self.boxes:
            narrow, other = a, b
        elif isinstance(b, str) and b in self.boxes:
            narrow, other = b, a
        if narrow is None:
            self.residual += 1
            return kids
        lo, hi = self.boxes[narrow]
        self.split += 1
        expr = scale(hi, other)
        for k in range(hi - 1, lo - 1, -1):
            expr = ["ite", ["=", narrow, numeral(k)], scale(k, other), expr]
        return expr


def transform(path, out_path):
    forms = parse(tokenize(open(path, errors="replace").read()))
    asserts = [f[1] for f in forms if isinstance(f, list) and f and f[0] == "assert"]
    boxes = harvest_bounds(asserts)
    rw = Rewriter(boxes)
    body = []
    for f in forms:
        if isinstance(f, list) and f and f[0] == "assert":
            body.append(["assert", rw.run(f[1])])
        else:
            body.append(f)
    # The logic is relabelled QF_LIA only when the rewrite actually removed every
    # variable-by-variable product. Declaring QF_LIA over a query that still has
    # one would be a false advertisement to the front door, and the surrogate
    # would then be measuring a mislabelled file rather than the transformation.
    out = []
    for f in body:
        if isinstance(f, list) and f and f[0] == "set-logic" and rw.residual == 0:
            out.append(["set-logic", "QF_LIA"])
        else:
            out.append(f)
    buf = []
    for f in out:
        render(f, buf)
        buf.append("\n")
    open(out_path, "w").write("".join(buf))
    return {"boxes": len(boxes), "split": rw.split, "residual": rw.residual}


# ------------------------------------------------------------------------ solving
def run_solver(cmd, timeout):
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout"
    for line in p.stdout.splitlines():
        s = line.strip()
        if s in ("sat", "unsat", "unknown"):
            return s
    return "none"


STATUS = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")


def one(path, outdir, budget_ms, cli, verify):
    base = os.path.basename(path)
    tpath = os.path.join(outdir, base)
    t0 = time.time()
    try:
        stats = transform(path, tpath)
    except Exception as exc:  # noqa: BLE001
        return {"file": path, "error": f"transform: {exc}", "ours": "none",
                "boxes": -1, "split": -1, "residual": -1, "s": 0,
                "declared": "none", "z3": "-", "cvc5": "-"}
    ttime = time.time() - t0
    declared = STATUS.search(open(path, errors="replace").read())
    declared = declared.group(1) if declared else "none"

    # Run every file, residual products or not. Full linearization is SUFFICIENT
    # for this to pay but not NECESSARY: the refusal being sized is the CNF clause
    # estimate, and replacing a variable-by-variable multiply (~8w^2 clauses) with
    # a five-branch chain of numeral scalings (~w each) can drop the estimate under
    # the ceiling while products remain. Gating the run on residual == 0 would have
    # measured the wrong thing.
    t1 = time.time()
    ours = run_solver(["timeout", "-k", "5", str(budget_ms // 1000 + 30), cli,
                       tpath, "--timeout-ms", str(budget_ms)], budget_ms / 1000 + 60)
    s = time.time() - t1
    z3v = cvcv = "-"
    if verify:
        z3v = run_solver(["z3", "-T:60", tpath], 90)
        cvcv = run_solver([CVC5, "--tlimit", "60000", tpath], 90)
    return {"file": path, "error": "", "ours": ours, "boxes": stats["boxes"],
            "split": stats["split"], "residual": stats["residual"],
            "s": round(s, 1), "transform_s": round(ttime, 1),
            "declared": declared, "z3": z3v, "cvc5": cvcv}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", required=True)
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--cli", required=True)
    ap.add_argument("--budget-ms", type=int, default=24000)
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--verify", action="store_true",
                    help="re-check the TRANSFORMED file against z3 and cvc5")
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)
    files = [l.strip() for l in open(args.list) if l.strip()]
    print(f"{len(files)} files -> {args.outdir}", flush=True)
    rows = []
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futs = [ex.submit(one, f, args.outdir, args.budget_ms, args.cli, args.verify)
                for f in files]
        for n, fut in enumerate(cf.as_completed(futs), 1):
            rows.append(fut.result())
            if n % 5 == 0:
                print(f"  {n}/{len(files)}", flush=True)
    rows.sort(key=lambda r: r["file"])
    cols = ["file", "declared", "ours", "s", "z3", "cvc5", "boxes", "split",
            "residual", "transform_s", "error"]
    with open(args.out, "w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=cols, delimiter="\t", extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)

    print(f"\nwrote {args.out}")
    fully = [r for r in rows if r["residual"] == 0]
    print(f"fully linearized (residual products == 0): {len(fully)} of {len(rows)}")
    print("our verdict on the transformed query:",
          dict(collections.Counter(r["ours"] for r in rows)))
    decided = [r for r in rows if r["ours"] in ("sat", "unsat")]
    print(f"=> REACHABLE (we decide the transformed query): {len(decided)} of {len(rows)}")
    print(f"   of those, fully linearized: "
          f"{sum(1 for r in decided if r['residual'] == 0)}; "
          f"still carrying products: {sum(1 for r in decided if r['residual'] > 0)}")
    bad = [r for r in rows if r["ours"] in ("sat", "unsat")
           and r["declared"] in ("sat", "unsat") and r["ours"] != r["declared"]]
    print(f"verdicts disagreeing with the ORIGINAL's declared :status: {len(bad)}")
    for r in bad:
        print("   DISAGREE", r["ours"], "vs", r["declared"], r["file"])
    if args.verify:
        vb = [r for r in rows if r["z3"] in ("sat", "unsat")
              and r["declared"] in ("sat", "unsat") and r["z3"] != r["declared"]]
        print(f"transform control -- z3 on the TRANSFORMED file vs the ORIGINAL's "
              f":status: {len(vb)} disagreements")
        for r in vb:
            print("   TRANSFORM-DISAGREE z3", r["z3"], "vs", r["declared"], r["file"])
        vc = [r for r in rows if r["cvc5"] in ("sat", "unsat")
              and r["declared"] in ("sat", "unsat") and r["cvc5"] != r["declared"]]
        print(f"transform control -- cvc5 vs :status: {len(vc)} disagreements")
        noop = sum(1 for r in rows if r["z3"] not in ("sat", "unsat")
                   and r["cvc5"] not in ("sat", "unsat"))
        print(f"transform control -- files where NEITHER reference has an opinion "
              f"on the transformed query: {noop} of {len(rows)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
