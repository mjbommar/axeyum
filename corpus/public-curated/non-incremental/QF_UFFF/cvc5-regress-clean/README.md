# QF_UFFF curated slice (committed, reproducible)

Curated, **committed** SMT-LIB `QF_UFFF` (quantifier-free uninterpreted functions
over finite fields) slice for the measured run of `axeyum_solver::check_auto`
(`--backend solver`). This is the **FF + UF combination** seam: the just-landed
finite-field modeling (`GF(p)` → modular `BitVec`, commit `3768c49`) composed with
the existing eager-Ackermann uninterpreted-function path. The classic case is
congruence over a field-valued function — `a = b = c ⇒ f(a) = f(c)` must be UNSAT
when paired with `(not (= (f a) (f c)))`.

- `./` — the **8** clean `(set-logic QF_UFFF)` files from the cvc5 regression suite
  (`references/cvc5/test/regress`, a gitignored shallow clone). These are the
  `cli/regress0/ff/with_uf*.smt2` family (small test prime `GF(17)`, a
  field-valued declared function `f : FF → FF`).

```sh
target/release/axeyum-bench \
  corpus/public-curated/non-incremental/QF_UFFF/cvc5-regress-clean \
  --logic QF_UFFF --backend solver --compare-z3 --timeout-ms 10000 --jobs 4 \
  --out bench-results/baselines/qf-ufff-cvc5-regress-clean-solver-vs-z3-10s.json
```

## How the FF + UF combination composes

The front end models `(_ FiniteField 17)` as `BitVec(5)` (residues `0..17`, with a
`bvult x 17` well-formedness constraint per declared field symbol — see the QF_FF
README for the full `GF(p)` → modular-BitVec table), and a field-valued
`(declare-fun f (FF) FF)` is handled by the **eager Ackermann** UF path: each
application `f(t)` becomes a fresh BV symbol, and for every pair of applications
`f(s)`, `f(t)` a congruence axiom `s = t ⇒ f(s) = f(t)` is asserted. The two
encodings compose with no new IR construct — both reduce to BV, and the combined
BV formula is bit-blasted to SAT.

**Soundness** is denotation-preserving on both halves: the `< p` well-formedness
pins the field domain to exactly `GF(p)`, every field op recomputes a canonical
residue, and the Ackermann congruence axioms are the standard sound EUF reduction.
No wrong sat/unsat is possible.

## Measured baseline (`--backend solver --compare-z3 --timeout-ms 10000`)

| metric | value |
|---|---|
| files | 8 |
| decided | **8** (sat 2, unsat 6) |
| unknown | 0 |
| unsupported | 0 |
| errors | 0 |
| `; EXPECT:` ground-truth **agree** | **8 / 8** |
| Z3-binary oracle compared | 0 (all skipped — see below) |
| model-replay failures | 0 |
| PAR-2 mean (s) | ~0.003 |

Every decided verdict (2 sat: `with_uf4`, `with_uf6`; 6 unsat: the rest) matches the
cvc5 `; EXPECT:` annotation exactly. The whole slice decides — the FF + UF
combination is complete here at small-prime scale, with no unsupported blocker.

### Why the Z3 oracle is skipped (and what the binding gate is)

The standalone **Z3 4.13.3 binary does not support finite fields** — fed a
`QF_UFFF` file verbatim it answers `unsupported` (`unknown sort 'FiniteField'`).
For **pure QF_FF** the harness sidesteps this by routing the oracle through the
*in-repo* `Z3Backend`, which checks axeyum's own modeled-BV translation with the z3
*library* (BV is supported) — a real head-to-head (QF_FF baseline: compared 24,
agree 24). For **QF_UFFF**, that modeled translation contains **uninterpreted
functions** (the Ackermann symbols), which the in-repo `Z3Backend` declines, so the
harness falls back to the z3 binary — which rejects FiniteField. Hence all 8 are
oracle-`skipped` (`summary.oracle`: compared 0, agree 0, **disagree 0**).

The committed soundness gate for this slice is therefore the **cvc5 `; EXPECT:`
ground truth (8/8 agree)**, exactly as the QF_FF / QF_DT / QF_AX slices rely on the
oracle (or EXPECT) rather than `:status`. A standalone z3 binary built with the FF
theory, or an in-repo `Z3Backend` extended to BV+Ackermann, would make a direct
head-to-head possible; both are out of scope for corpus curation.

### Ground-truth annotation: `; EXPECT:` (not `:status`)

These files carry `; EXPECT: sat|unsat` (cvc5's regress convention), not a
`(set-info :status …)`, so the flat parser reports `expected=unknown`. Reproduce
the selection with the `--expect-comment` flag (which accepts the comment as ground
truth; default behavior is unchanged):

```sh
python3 scripts/curate-public-slice.py QF_UFFF - --expect-comment
# QF_UFFF (..., expect_comment=True, ...): 8 files
```

## Corpus reality

The cvc5 suite has exactly **8** files declaring `(set-logic QF_UFFF)` — all in
`cli/regress0/ff/` — and all 8 are clean under the standing filter (plain
`assert`+`check-sat`, no `push`/`pop`/`get-value`). This is the full division, not
a curation artifact. The bitwuzla suite has no finite-field files.
