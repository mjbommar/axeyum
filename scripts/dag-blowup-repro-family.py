#!/usr/bin/env python3
"""The ADR-1940 triage instrument: one `let`-doubling chain per operator class.

A source census of branching `TermId` walkers is a lead generator with no
ordering and three demonstrated blind spots (a `self.name(` method call, an
explicit worklist, and a recursion inside `for arg in args`). This is the
instrument that produced the ordering instead.

Each generated file is `2^(d+1)` root-to-leaf paths over about `d + 2` distinct
arena nodes. A route whose walker is unmemoised DOUBLES its wall time per level;
a memoised route is flat. So:

    python3 scripts/dag-blowup-repro-family.py /tmp/fam
    python3 scripts/dag-blowup-family-sweep.py --dir /tmp/fam \
        --binary target/release/examples/smtcomp_cli --core 6

and every family the sweep marks DOUBLING names a live instance. `perf record`
on that family's deepest file then names the function. Adding an operator class
here is how you extend the triage to a route this does not yet cover.
"""
import os
import sys


def chain(logic, decls, seed, step, final, d):
    lets = "".join(f"(let ((v{i+1} {step.format(v=f'v{i}')})) " for i in range(d))
    body = final.format(v=f"v{d}")
    return (f"(set-logic {logic})\n{decls}\n(assert (let ((v0 {seed})) "
            f"{lets}{body}{')' * d}))\n(check-sat)\n")


# name -> (logic, declarations, v0, step from {v}, final atom over {v})
FAMILIES = {
    "int_add": ("QF_LIA", "(declare-const x Int)", "(+ x 1)",
                "(+ {v} {v})", "(<= {v} 100)"),
    "int_sub": ("QF_LIA", "(declare-const x Int)", "(+ x 1)",
                "(- (+ {v} {v}) {v})", "(<= {v} 100)"),
    "int_mul": ("QF_NIA", "(declare-const x Int)", "(+ x 1)",
                "(* {v} {v})", "(<= {v} 100)"),
    "int_ite": ("QF_LIA", "(declare-const x Int)\n(declare-const p Bool)",
                "(+ x 1)", "(ite p (+ {v} {v}) (- {v} {v}))", "(<= {v} 100)"),
    "eq_chain": ("QF_LIA", "(declare-const x Int)", "(+ x 1)",
                 "(+ {v} {v})", "(= {v} 100)"),
    "real_add": ("QF_LRA", "(declare-const x Real)", "(+ x 1.0)",
                 "(+ {v} {v})", "(<= {v} 100.0)"),
    "real_mul": ("QF_NRA", "(declare-const x Real)", "(+ x 1.0)",
                 "(* {v} {v})", "(<= {v} 100.0)"),
    "nra_add": ("QF_NRA", "(declare-const x Real)\n(declare-const y Real)",
                "(+ x 1.0)", "(+ {v} {v})", "(and (<= {v} 100.0) (= (* y y) 2.0))"),
    "nia_add": ("QF_NIA", "(declare-const x Int)\n(declare-const y Int)",
                "(+ x 1)", "(+ {v} {v})", "(and (<= {v} 100) (= (* y y) 4))"),
    "bool_and": ("QF_UF", "(declare-const p Bool)", "(and p p)",
                 "(and {v} {v})", "{v}"),
    "bool_or": ("QF_UF", "(declare-const p Bool)", "(or p p)",
                "(or {v} {v})", "{v}"),
    "bool_xor": ("QF_UF", "(declare-const p Bool)", "(xor p p)",
                 "(xor {v} {v})", "(not {v})"),
    "bool_implies": ("QF_UF", "(declare-const p Bool)", "(=> p p)",
                     "(=> {v} {v})", "{v}"),
    "bool_not_and": ("QF_UF", "(declare-const p Bool)", "(and p p)",
                     "(and {v} {v})", "(not {v})"),
    "bv_add": ("QF_BV", "(declare-const b (_ BitVec 8))", "(bvadd b #x01)",
               "(bvadd {v} {v})", "(bvule {v} #x64)"),
    "bv_and": ("QF_BV", "(declare-const b (_ BitVec 8))", "(bvand b #x0f)",
               "(bvand {v} {v})", "(bvule {v} #x64)"),
    "bv_mul": ("QF_BV", "(declare-const b (_ BitVec 8))", "(bvadd b #x01)",
               "(bvmul {v} {v})", "(bvule {v} #x64)"),
    "bv_ite": ("QF_BV", "(declare-const b (_ BitVec 8))\n(declare-const p Bool)",
               "(bvadd b #x01)", "(ite p (bvadd {v} {v}) (bvsub {v} {v}))",
               "(bvule {v} #x64)"),
    "str_concat": ("QF_S", "(declare-const s String)", '(str.++ s "a")',
                   "(str.++ {v} {v})", "(= (str.len {v}) 7)"),
    "str_len": ("QF_SLIA", "(declare-const s String)", "(str.len s)",
                "(+ {v} {v})", "(= {v} 8)"),
    "uflia": ("QF_UFLIA", "(declare-const x Int)\n(declare-fun f (Int) Int)",
              "(+ x 1)", "(+ (f {v}) (f {v}))", "(<= {v} 100)"),
    "uflra": ("QF_UFLRA", "(declare-const x Real)\n(declare-fun f (Real) Real)",
              "(+ x 1.0)", "(+ (f {v}) (f {v}))", "(<= {v} 100.0)"),
    "idl": ("QF_IDL", "(declare-const x Int)\n(declare-const y Int)",
            "(- x y)", "(+ {v} {v})", "(<= {v} 100)"),
    "array": ("QF_ALIA", "(declare-const a (Array Int Int))\n(declare-const x Int)",
              "(store a x 1)", "(store {v} (select {v} x) 1)", "(= (select {v} x) 1)"),
    "array_sel": ("QF_ALIA", "(declare-const a (Array Int Int))\n(declare-const x Int)",
                  "(select a x)", "(+ {v} {v})", "(= {v} 8)"),
    "dt": ("QF_DT",
           "(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))\n(declare-const x Int)",
           "(mk x 1)", "(mk (fst {v}) (snd {v}))", "(= (fst {v}) 7)"),
    "quant_lia": ("LIA", "(declare-const x Int)", "(+ x 1)", "(+ {v} {v})",
                  "(forall ((q Int)) (=> (> q 0) (<= {v} (+ q 100))))"),
}


def main():
    if len(sys.argv) < 2:
        sys.exit(f"usage: {sys.argv[0]} <out-dir> [lo] [hi]")
    out = sys.argv[1]
    lo = int(sys.argv[2]) if len(sys.argv) > 2 else 14
    hi = int(sys.argv[3]) if len(sys.argv) > 3 else 32
    os.makedirs(out, exist_ok=True)
    for name, (logic, decls, seed, step, final) in FAMILIES.items():
        for d in range(lo, hi + 1):
            with open(os.path.join(out, f"{name}.{d:02d}.smt2"), "w") as fh:
                fh.write(chain(logic, decls, seed, step, final, d))
    print(f"wrote {len(FAMILIES)} families x {hi - lo + 1} depths into {out}")


if __name__ == "__main__":
    main()
