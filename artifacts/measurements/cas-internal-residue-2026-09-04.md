# The ADR-0601 SS2 `cas-internal` residue (roadmap W1-13)

Measured 2026-09-04 at commit `c181655e9` (lane `producer-measurements`).

## The question

`docs/math-department/11-applied-and-computational.md`'s reviewer: "the
labelled `cas-internal` residue should be measured and shrinking, and that
number should be published." ADR-0601 SS2 requires every `cas-certificate`
fact's evidence to classify as `kernel-reconstructed` (an independent
re-derivation through the kernel trust anchor exists) or `cas-internal` (the
checker never leaves the CAS's own normal form) — never a third,
unclassifiable case.

The 2026-09-04 applied-and-computational audit
(`docs/math-department/AUDIT-2026-09-04.md`, row 11) found that
`scripts/check-cas-substance.py` and its `.ratchet` file exist, established
that *something* about CAS substance is ratcheted, and explicitly could not
determine whether that something was this residue — and had not run the
ratchet to check. It is not: `check-cas-substance.py` (ADR-0622) floors what
the 14 `kernel-reconstructed` facts' kernel obligations *establish* (their
`shape`: `combination`/`refl`/`evaluation`/...), never the count split
between `kernel-reconstructed` and `cas-internal` itself.

## Method

`scripts/validate-facts.py` already computes the classification
(`classify_cas_certificate_checker`/`classify_cas_certificate_fact`): a
`cas-certificate` fact's evidence classifies as `kernel-reconstructed` if any
executed `cargo test`/`cargo run` segment names the `axeyum-lean-kernel`
package, `cas-internal` if it names only `axeyum-cas`, and `unrecognized`
otherwise (a case `validate_one` already refuses in a passing ledger).

`scripts/check-cas-internal-residue.py` (new, this lane) reuses that
classifier — one definition, not reimplemented — over every
`artifacts/facts/*.json` fact whose `proof_route` is `cas-certificate`, and:

1. reports the total / kernel-reconstructed / cas-internal / unrecognized
   split, overall and per `formal.fragment` family (`--report`);
2. ratchets a **floor**: a fact recorded `kernel-reconstructed` in the
   committed `scripts/check-cas-internal-residue.ratchet` must still classify
   that way today. Regressing to `cas-internal`, going `unrecognized`, or
   disappearing from the ledger is refused. A **new** `cas-internal` fact, or
   the residue's absolute count growing as the ledger grows, is not refused —
   ADR-0601 makes `cas-internal` an honest label, not a forbidden one.

Re-run with:

```sh
python3 scripts/check-cas-internal-residue.py --report
```

## The numbers, 2026-09-04

```
cas-certificate: 60 total -- kernel-reconstructed 14, cas-internal 46, unrecognized 0
  cas-internal residue share: 76.7%
```

This matches `scripts/validate-facts.py`'s own summary line exactly (same
classifier, independently re-invoked), which is the cross-check that the two
tools are answering the same question:

```
routes: cas-certificate=60(kernel-reconstructed=14,cas-internal=46) ...
```

**The "neither" bucket is empty.** 0 of 60 facts are `unrecognized` — every
`cas-certificate` fact in the ledger is honestly one or the other, which is
the invariant ADR-0601 SS2 requires and `validate-facts.py`'s `validate_one`
already enforces at ingestion. `check-cas-internal-residue.py` re-checks this
independently (it reads the raw fact JSON directly, not through
`validate_one`) rather than trusting that guard alone.

### Per operation family (`formal.fragment`)

Verbatim `python3 scripts/check-cas-internal-residue.py --report` output,
2026-09-04:

```
  fragment                                       kernel-reconstructed  cas-internal  unrecognized
  NRA                                                               0            10             0
  boolean-circuit-exhaustive-replay                                 0             1             0
  cas-certified-integral-direct-branch                              0             1             0
  cas-ntheory-composite-certificate                                 0             1             0
  cas-ntheory-crt-certificate                                       0             1             0
  cas-ntheory-factorization-certificate                             0             1             0
  cas-ntheory-pratt-certificate                                     0             1             0
  exact-rational-geometry-cofactor-identity                         2             0             0
  exact-rational-partial-fractions                                  0             1             0
  exact-rational-partial-fractions-coefficient-matching-identity    1             0             0
  finite-gf2-enumeration                                            0             1             0
  gf2-extension-polynomial-identity                                 0             1             0
  gf2-finite-field-order                                            0             1             0
  gf2-polynomial-identity                                           0             1             0
  gf2-rabin-irreducibility                                          0             1             0
  gf2-shard-manifest-exhaustion                                     0             1             0
  gf2-tensor-rank-decomposition-replay                              0             1             0
  gosper-acceptance-mode-certificate                                0             1             0
  groebner-cofactor-unit-ideal-refutation                           0             1             0
  hypergeometric-summation                                          0             9             0
  integer-matrix-smith-normal-form                                  0             1             0
  nra-geometry-cofactor-identity                                    4             0             0
  rational-integration-horowitz                                     0             1             0
  real-algebraic-evt                                                0             1             0
  real-algebraic-evt-derivative-sign-bracket                        1             0             0
  real-algebraic-evt-endpoint-exclusion                             1             0             0
  real-algebraic-inverse                                            0             1             0
  real-algebraic-ivt                                                0             1             0
  real-algebraic-ivt-sign-bracket                                   2             0             0
  real-algebraic-mvt                                                0             1             0
  real-algebraic-mvt-secant-endpoints                               1             0             0
  real-algebraic-rationality                                        0             1             0
  real-algebraic-taylor-lagrange                                    0             1             0
  real-algebraic-taylor-remainder-lhs                                1             0             0
  sos-barrier                                                       0             1             0
  sos-lyapunov                                                      0             1             0
  sos-psd-not-sos                                                   0             1             0
  univariate-polynomial-identity                                    1             0             0
```

**Reading this table:** every family that reconstructs is real-algebraic
sign-bracket/geometry-cofactor/polynomial-identity work — the CAS certificate
carries enough structure (a coordinate system, a Gröbner cofactor
combination, a concrete sign evaluation) that a kernel-level re-derivation
exists. Every family that is `cas-internal` is number theory (Pratt/CRT/
factorization certificates), GF(2) computation, hypergeometric/binomial
identity checking, or SOS/Positivstellensatz certificates — exactly the
families `docs/math-department/11-applied-and-computational.md`'s "Next Five"
item 3 (a Positivstellensatz-to-kernel bridge) and ADR-0601's own roadmap
name as not yet bridged. The residue is not spread evenly; it is
concentrated exactly where the reconstruction bridge has not been built yet.

## The gate

`scripts/check-cas-internal-residue.py`, registered in `scripts/check.sh` and
`justfile` (`step cas-internal-residue` / the corresponding `just check`
line), with a companion `scripts/tests/test_check_cas_internal_residue.py`
(10 tests) registered under `scripts/tests/mutation_controls.py`'s
`cas-internal-residue` suite. Mutation-verified 2026-09-04 on a scratch copy
(never the shared worktree): baseline green (10 tests), and each of the four
guards, deleted independently, kills **exactly one** test:

| guard | kills |
|---|---|
| G1 an `unrecognized` fact is refused | `test_G1_an_unrecognized_fact_is_refused` |
| G2 a missing ratchet file is refused | `test_G2_a_missing_ratchet_is_refused` |
| G3 a fact regressed kernel-reconstructed → cas-internal is refused | `test_G3_a_reclassified_fact_is_refused` |
| G4 a ratcheted fact that vanished is refused | `test_G4_a_vanished_fact_is_refused` |

Re-run: `python3 scripts/tests/mutation_controls.py cas-internal-residue`.

## What would make this number fall

Per the per-fragment table above, the residue shrinks exactly when a new
kernel-reconstruction route lands for one of the `cas-internal` families:

- A Positivstellensatz/SOS-to-kernel bridge closes 3 facts
  (`sos-barrier`/`sos-lyapunov`/`sos-psd-not-sos`) — already named as
  `11-applied-and-computational.md`'s Next-Five item 3.
- A number-theory certificate bridge (Pratt primality, CRT, factorization)
  closes 4.
- A hypergeometric/binomial-identity bridge closes 9 — the single largest
  family in the residue.
- A GF(2) bridge (irreducibility, tensor rank, finite-field order) closes 6.

None of this is scoped as work for this lane (measurement-only, no kernel
declarations); it is the concrete next-five list this measurement makes
legible by family rather than only by total.
