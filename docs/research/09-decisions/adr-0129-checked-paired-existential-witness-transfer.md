# ADR-0129: Checked paired-existential witness transfer

Status: accepted
Date: 2026-07-12

## Context

After ADR-0128, `nested9_true-unreach-call` is the smallest unsupported row in
the public cvc5 quantified-BV slice. Its two assertions have the shape

```text
P and exists v. S(v)
not (P and exists w. W(w))
```

where `P` is byte-identical ground context. The bodies differ in one signed
bound: `S` contains `v + 3 <=s k`, while `W` contains `w + 1 <=s k`; both also
contain `v <=s 3`. Thus every witness for `S` is a witness for `W`, provided the
modular additions do not wrap through the signed maximum.

The reference solvers use broader mechanisms to find useful terms. cvc5's BV
CEGQI instantiator queries model values, solves literals through its BV inverter,
and may replace inequalities by boundary equalities; its own comments identify
candidate selection as heuristic. Z3's QSAT engine alternates existential and
universal kernels and uses model-based projection to construct blocking
formulas. Those mechanisms guide search, but neither search trace is accepted
as evidence for an Axeyum verdict.

## Decision

**Certify UNSAT for one source-bound pair of Bool/BV existential assertions
when the positive body's complete witness tuple implies every conjunct of the
negated existential body under exactly identical ground premises.**

The certificate names the exact positive and negative source assertions, the
unique existential leaf in each, and one justification for every target-body
conjunct that is not alpha-identical to an available premise or source-body
conjunct. The checker requires:

- two distinct named assertions that both belong to the original query;
- a positive conjunction with exactly one `exists+` leaf and a negative
  assertion whose direct child is a conjunction with exactly one `exists+`
  leaf;
- byte-identical sorted ground-premise sets on both sides;
- nonempty prefixes with equal lengths and pairwise-equal Bool/BV sorts, at
  most 128 distinct binders in total, and no reused binder IDs;
- at most 4,096 distinct nodes across both complete source assertions, with
  only Bool/BV sorts;
- quantifier-free Bool bodies and premises with no function application;
- no cross-prefix binder leakage and no bound binder in a ground premise;
- deterministic alpha-alignment of each binder pair to one fresh symbol; and
- exactly one independently checked obligation for every unmatched target
  conjunct, with no duplicates or omissions.

An obligation is discharged in one of two ways:

1. A source-selected `QF_BV` implication proof. The certificate names only
   exact shared premises or source-body conjuncts. Replay re-instantiates those
   terms, appends the negated target conjunct, regenerates the CNF, and rechecks
   the carried DRAT/LRAT proof.
2. The exact signed-add monotonicity lemma. For one common-width variable and
   upper term, replay must match source conjuncts `x + s <=s k` and `x <=s b`
   and target conjunct `x + w <=s k`, decode all constants as signed values,
   and prove `0 <= w <= s` and `b <= MAX_SIGNED - s`. From `x <=s b`, both
   additions are non-wrapping; hence `x + w <=s x + s <=s k`.

Untrusted search examines at most 256 ordered assertion pairs and 256 selected
proof subsets under the shared deadline. It alpha-aligns the prefixes, first
tries the exact word-level lemma, then asks the ordinary proof-producing
`QF_BV` route for a sufficient implication subset. Solver and evidence dispatch
return UNSAT only after the public checker accepts the generated certificate.
The evidence has an empty trust ledger. Lean reconstruction is a separate
future boundary.

## Evidence

`nested9_true-unreach-call` moves from unsupported to checked UNSAT. Five
optimized solve samples are 0.075, 0.073, 0.081, 0.076, and 0.069 ms (median
0.075 ms); evidence-production samples are 0.039, 0.039, 0.055, 0.038, and
0.037 ms (median 0.039 ms).

The fresh 54-row public cvc5 quantified-BV measurement is 32 SAT / 17 UNSAT /
0 unknown / 5 unsupported, with 49 expected-status agreements and no
disagreement, error, or model-replay failure. Five PAR-2 samples are 2.065130,
2.065493, 2.065744, 2.065791, and 2.066172 seconds (median 2.065744 seconds).
The dominance audit certifies and checks all 49 decisions; 40 are dominant
candidates and Lean checks 8/17 UNSAT rows. The target taxonomy is
`bv-paired-existential-transfer-unsat` with an empty trust ledger.

Eight focused tests cover the public row, assertion-order independence,
source/reason/proof mutation,
alpha-identity and generic `QF_BV` transfer, malformed contexts/prefixes/sorts,
both hard caps, explicit signed-overflow neighbors, and 64 generated safe
transfers plus 64 genuine wraparound non-transfer controls checked directly
against static Z3. The cumulative quantified-BV direct-Z3 campaigns cover
1,720 cases and controls without disagreement.

The generated width-10 negative initially exposed two independent linear-depth
builders: exact finite-domain expansion left-folded 1,024 instances, and AC
canonicalization flattened the repaired tree then rebuilt it left-associated.
Both now use deterministic pairwise balanced folds. A regression checks that
maximum admitted expansion and its canonical form remain logarithmic-depth;
the normal Rust test stack completes the full differential sweep.

## Alternatives

- **Trust cvc5-style inversion or Z3-style projection.** Rejected: both are
  useful untrusted candidate generators, not source-bound proof artifacts.
- **Treat signed addition as mathematical integer addition.** Rejected: the
  implication is false across modular signed overflow. The checker proves the
  exact no-wrap margin and the differential controls cross that boundary.
- **Reuse one existential witness after normalization without alpha replay.**
  Rejected: prefix correspondence, sort equality, body substitution, and every
  consequence must be reconstructed from original source IDs.
- **Bit-blast the complete target theorem.** Rejected as the primary target
  route: an irrelevant multiplication made that proof materially more
  expensive. The exact word-level lemma is smaller and easier to audit; generic
  source-subset proofs remain available for other admitted conjuncts.
- **Admit arbitrary polarity contexts, functions, arrays, or arithmetic.**
  Deferred: each requires a separate source theorem and evidence contract.
- **General BV QSAT/QE.** Deferred: this pair needs witness transfer, not a
  complete alternating decision procedure.

## Consequences

One positive existential witness can now refute a paired negated existential
under exact shared ground context, including the checked signed-offset class and
generic source-bound `QF_BV` consequences. Different premises, unequal prefixes,
non-conjunctive polarity, nested quantifiers, functions, arrays, arithmetic,
general existential normalization, proof serialization, Lean reconstruction,
and general QSAT remain unsupported by this route.
