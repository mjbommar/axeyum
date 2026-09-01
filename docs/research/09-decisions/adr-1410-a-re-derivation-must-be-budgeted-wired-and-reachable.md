# ADR-1410: a re-derivation must be budgeted, wired, and reachable

Date: 2026-09-01
Status: Accepted
Lane: `cas-certificate-repair`

Index-summary: ADR-1400 says a certificate must record every distinction its acceptance depends on, preferring re-derivation to a recorded field. Repairing four CAS certificates against that rule produced four findings the rule does not cover, each measured by a mutation control rather than argued. (1) A re-derivation must be BUDGETED and exhausting the budget must be a refusal, or it silently degrades back into trusting the producer -- `axeyum-gf2-check-shard` accepted a fabricated exhaustion with the entire body `summary.exhausted += 1`. (2) Testing the predicate is not testing the WIRING: mutating the Smith/Hermite shape check out of the entry points killed zero tests until the three checks were extracted into a named `admit_*` gate a fixture could hand a forged pair. (3) A guard on an unreachable state is a guard no fixture can kill -- refuse at the OPTIONS, not at the consequence; this fired twice, and both times the honest move was to delete the guard and add one that discriminates. (4) A boolean "did the check pass" conflates DECLINE with REFUTATION, and the caller's next move differs: Gosper admitted a reconstruction its own zero-test had decided WRONG, on the weaker reduced identity. Separately measured and repaired: `equal` returned `Certified { equal: true }` for `ln(x^2) = 2*ln(x)` at an exactly-negative `x`, because an `f64` sign test read `-10^-16` as `+3.44e-16`.
Index-status: Accepted

## Context

ADR-1400 states the rule: **a certificate must record every distinction its
acceptance depends on, or re-derive it** — re-derivation preferred, because a
recorded field can be forged and a re-derivation cannot, with
recording-plus-a-committed-control as the fallback.

Applying it to four CAS certificates surfaced four failure modes the rule as
stated does not reach. Each is recorded here with the mutation control that
established it, because in every case the argument for the guard was persuasive
and the measurement disagreed.

## Decision

### 1. A re-derivation must be budgeted, and running out of budget is a refusal

`ShardStatus::Exhausted` is a negative theorem: every sparse candidate the
policy admits at that degree is reducible. Nothing in the manifest witnesses it
and no field could, because the claim is about the *absence* of a witness. The
checker's whole acceptance body was `summary.exhausted += 1`.

The repair re-runs the producer's own deterministic enumeration under the
manifest's own declared policy and requires the identical verdict *and* the
identical candidate count. That is ADR-1400's preferred shape and it works.

What ADR-1400 does not say is that re-derivation **costs real work**, so it
needs a ceiling — and that the ceiling is where the repair can quietly undo
itself. If exhausting the budget admitted the row, the checker would be back to
accepting exhaustion on the producer's word, with a re-derivation in the diff
to prove it did not.

So: **a budget for a re-derivation must fail closed, and the summary must report
how much re-derivation actually ran.** `rederived_candidates` is in the PASS
line for exactly this: a run that re-derived nothing cannot be mistaken for one
that did.

### 2. Testing the predicate is not testing the wiring

`hermite_normal_form` certified `U * A = H` and `det(U) = ±1` and nothing else.
Both hold for `(I, A)` for **any** `A`, so the factorization was verified and
the normal form never was. For `smith_normal_form` the missing check is the
invariant-factor divisibility chain, which is the entire content of the Smith
form.

The first repair added `certifies_hermite_shape` / `certifies_smith_shape`, ten
adversarial assertions each, and positive controls. Every mutation of the
predicate's internals was killed. Then:

```
MUTANT|N1_hermite_shape_unchecked|status=0|running 11 tests|killed=NONE
MUTANT|N2_smith_shape_unchecked  |status=0|running 11 tests|killed=NONE
```

Mutating the shape check **out of the shipped entry points** killed nothing.
The fixtures exercised the predicate; nothing showed the entry point calls it.
This is the "registering a checker's tests is not registering the checker"
shape, one level down.

The fix is structural, not another assertion: the three checks became one named
gate per form (`admit_hermite`, `admit_smith`) that a fixture can hand a forged
pair. `admit_hermite(&A, &I, &A)` must return `None` while
`admit_hermite(&A, &U, &H)` from the real producer returns `Some`. After that,
N1 and N2 each kill exactly one test.

**So: when a certificate gains a new check, the fixture must exercise the
ADMISSION, not the predicate.** If the admission is three inline `if`s in a
function that also computes its own inputs, there is nothing a fixture can hand
it, and that absence is the finding.

### 3. A guard on an unreachable state is a guard no fixture can kill

This fired twice, in two unrelated modules, and both times the guard read as
diligence.

*gf2 shard.* A pre-check refused a row claiming more candidates than the
re-derivation budget had left. It survived being turned off. Every input it
rejected is already rejected downstream — by the budgeted search stopping at its
ceiling, or by the candidate-count binding — so it only ever changed the error
message.

*Telescoping.* The first draft refused a verification in which the pointwise
layer ran zero times, "whatever the options say". No fixture could reach it:
the edge-vanishing check forces the window to contain the support, and the ratio
layer then confirms over that same window, so zero pointwise confirmations with
every other layer green does not occur. It was replaced by refusing
`min_pointwise_samples == 0` at the **options**, which any committed
certificate can exercise in one line.

**So: refuse at the input, not at the consequence.** A check on a state the
design cannot reach is the checker-that-cannot-fail defect wearing the clothes
of defence in depth. When a guard survives its mutation, the two honest
outcomes are to delete it or to find the fixture — never to keep it because the
reasoning sounds right.

### 4. A boolean check conflates a decline with a refutation

`gosper::certifies_telescoping` returned `bool`, mapping `ZeroTest::Unknown` and
`ZeroTest::Certified { equal: false }` onto the same `false`. One is the checker
declining; the other is the checker **refuting** the reconstruction in hand.

The caller's next move differs, and it was wrong. A candidate the full zero-test
had decided WRONG fell through to `if reduced_certifies` and was returned on the
weaker reduced polynomial identity — the certificate that cannot see the
problem, preferred over the one that can.

Measured while writing the fixture, and it inverts the intuition: an opaque head
is **not** a decline. `Gamma(k+1) - Gamma(k) = k` comes back decidably FALSE, as
do Si, Ci, Ai, erf, LambertW, BesselJ and sin, because `equal_core` treats an
unplaced head as an independent atom. `Refuted` is the common outcome here, not
a corner case.

**So: a check whose outcomes drive different caller behaviour must be
three-valued, and the acceptance policy over those outcomes must be a total
function that a table-driven test can walk exhaustively.**

### 5. A serialized demand is required on parse, never defaulted

`min_pointwise_samples` is written into every telescoping certificate file and
**required** when parsing. A default would let a file be re-admitted under a
floor it never declared, which is ADR-1400's recorded-distinction defect arriving
through backward compatibility. The eight committed artifacts were regenerated
rather than grandfathered.

## Consequences

Landed with mutation controls; every guard below is killed by at least one named
fixture, and every fixture named here was verified to fail without its fix.

| repair | file | mutants killed |
| --- | --- | --- |
| exhaustion re-derivation | `gf2_shard.rs` | 7 of 8; the 8th was finding 3 and was removed |
| Gosper acceptance mode | `gosper.rs` | 4 of 4 |
| pointwise floor | `telescoping_check.rs`, `telescoping_json.rs` | 3 of 3 |
| normal-form shape | `normalforms.rs` | 8 of 8, after finding 2 |

### An exact certificate rested on a floating-point sign test

Found while verifying an unrelated item and repaired in the same lane, because
it is a wrong `Certified`, which is the class this whole architecture exists to
prevent.

`expand_log_over_primes` gated the `ln` distribution laws on
`evalf(e, &[]).is_some_and(|v| v > 0.0)`, and that function is part of `equal`'s
canonicalization. Measured on this tree before the fix:

```
x = (sqrt(2)*sqrt(2) - 2) - 1/10^16      exact value  -10^-16
evalf(x)                       = +3.440892098500626e-16
equal(ln(x^2), 2*ln(x))        = Certified { equal: true }
```

`sqrt(2)*sqrt(2)` evaluates to `2.0000000000000004` and `simplify_radicals` does
not collapse it, so the CAS never sees a cancelled zero. `ln(x^2) = 2*ln(x)` is
false for negative `x`: the left side is `ln(10^-32)`, a real number, and the
right side is not real.

Replaced by `is_certainly_positive`, an exact structural predicate that declines
rather than guesses. A decline costs completeness — `equal` falls back to
`ZeroTest::Unknown`, a first-class result — while a guess cost soundness. It is
also strictly better on one axis: `exp(t)` is positive for every real `t`, which
the numeric test could not see because `evalf` returns `None` for a free
variable. The full crate sweep is unchanged at 929 lib tests, so nothing
depended on the numeric answer.

The rule to carry, which is narrower than "no floating point": **the standard to
aim at is the SOS subtree, where there is no floating point at all — exact
rational arithmetic, overflow is a decline rather than a verdict, and decimals
are a hard parse error.** A certified result may not depend on an inexact
comparison anywhere in its derivation, including inside a canonicalization it
does not appear to call.

### Not repaired, and what was actually found

Three further items were checked. Two hold with a correction to the mechanism,
one is confirmed as described:

- **`ratint.rs`'s independent verifiers.** The substance holds — `verify_horowitz`
  and `verify_log_terms` exist, are thoroughly tested, and are called from
  `#[cfg(test)]` code only, while the shipped path calls `horowitz` and
  `log_terms` directly. The stated mechanism does not: there is no
  `#[expect(dead_code)]` anywhere in `crates/axeyum-cas/src/`. The shipped path
  is not uncertified — `prove_derivative` certifies the whole answer downstream,
  which is arguably stronger than either rung verifier — so this is a question
  of defence in depth rather than a hole.
- **`series.rs` discards the truncation order.** Confirmed.
  `series(expr, var, order) -> Option<CasExpr>` returns a bare expression, while
  the sibling `taylor.rs` carries a `TaylorCertificate` with
  `verify_taylor_certificate`. A truncated series without its order is a value
  whose meaning is not recoverable from the value.
- **`prove_derivative`'s half-angle fallback.** Not verified. Reported as
  **did not run**.
