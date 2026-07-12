# ADR-0102: Closed-universal counterexamples to Lean

Status: accepted
Date: 2026-07-11

## Context

ADR-0100 gives `ARI176e1` and `issue5279-nqe` independently checkable UNSAT
certificates: one concrete value per binder of a closed universal, with the
untouched quantifier-free body evaluating to `false`. Their solver evidence has
zero trust holes, but the generic quantified Alethe route still declines. That
route can reconstruct `forall_inst` only when its ground tail is an EUF
refutation; these rows instead need integer normalization and a computational
Bool `ite`.

Several existing structural Lean routes recheck a certificate and then declare
a theorem-specific `refuter : P -> False` axiom. The current dominance audit
counts the resulting module as kernel-checked, but applying that pattern here
would not close the proof-parity gap: the certificate theorem would remain an
opaque assumption. This increment requires a proof whose only query-specific
axiom is the original asserted universal.

## Decision

Add a certificate-specific Lean reconstruction boundary for the ADR-0100
fragment whose body is an integer equality or disequality over:

1. `Int` and `Bool` universal binders;
2. integer constants, `+`, `-`, unary negation, and multiplication admitted by
   the existing bounded integer ring normalizer; and
3. integer `ite` controlled by a bound Bool value.

The public reconstruction entry point first reruns
`check_closed_universal_counterexample` against the untouched assertion. It then:

1. translates the original universal into nested Lean dependent products over
   the existing `IntPrelude` carrier `Z` and computational `Bool`;
2. introduces that universal as the input hypothesis;
3. applies the certificate's typed witnesses with ordinary `forall`
   elimination;
4. independently rebuilds the ground integer expressions and checks their
   normal forms against evaluator values; and
5. closes `False` with a kernel-derived equality proof or a literal
   disequality proved from the integer order axioms.

Because the integer prelude encodes literals as repeated signed units, proof
construction also enforces a 4,096-unit budget over source literals, witnesses,
evaluated operands, and expanded ground products. Oversized but logically valid
certificates decline before ring normalization.

The generic `prove_unsat_to_lean_module` router may rediscover a certificate
under explicit two-second and deterministic resource limits, but it delegates
acceptance to the same checker and proof builder. Search is not trusted.

The first disequality slice supports distinct nonnegative literal results. A
negative-result equality counterexample declines until signed literal order
normalization is added; it must not fall back to an opaque refuter axiom.

## Evidence

- `ARI176e1` reconstructs `forall U V, not (3*U = 22 + (-5)*V)` by applying
  `U=9, V=1` and proving both sides normalize to `27`.
- `issue5279-nqe` reconstructs `forall a b, a = ite b 0 1` by applying
  `a=2, b=false`; `Bool.rec` iota-reduces the ITE to `1`, and integer order
  proves `2 != 1`.
- Focused tests cover both real corpus rows through the certificate API and the
  generic router, plus a tampered ARI witness rejected before reconstruction.
- Acceptance requires the quantified-LIA dominance audit to report Lean UNSAT
  2/7 and dominant candidates 4/9, with all nine decisions still
  certified/rechecked, zero trust holes, no mismatches, and no audit errors or
  timeouts.

## Alternatives

- **Add a checked-certificate refuter axiom.** Rejected: the kernel would check
  only the application of an opaque theorem, not the quantified arithmetic
  argument. This would inflate the Lean metric without reducing proof trust.
- **Extend the generic EUF quantifier tail.** Deferred: composing
  `forall_inst`, Boolean structure, `lia_generic`, and integer Lean
  reconstruction is the broader reusable target. The certificate boundary is
  smaller and already supplies exact witnesses.
- **Credit certificate checking as Lean checking.** Rejected: executable
  evidence replay and kernel proof reconstruction are distinct assurance
  layers in the Pareto audit.
- **Handle all ADR-0100 scalar sorts immediately.** Rejected: Real/BV and
  arbitrary Boolean formulas require different proof preludes. Unsupported
  forms continue to decline.

## Consequences

- Two certified quantified-LIA UNSAT rows gain genuine kernel reconstruction,
  moving proof coverage without changing solver verdicts.
- The trusted base is unchanged: the logic prelude, integer ring/order axioms,
  and kernel were already trusted. No theorem-specific refuter axiom is added.
- The other five quantified-LIA UNSAT certificates still need proof-specific or
  composed Alethe reconstruction; they remain honestly uncredited.
- Resource rejection is separate from certificate validity: a checked theorem
  may remain certified while its unary Lean reconstruction honestly declines.
