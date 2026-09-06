# Lane: complex-polyderiv — uniform continuity closes under products, and ℂ gets a transport and a power rule

<!-- plan-section: lane-status -->

**Closure of `Complex.UniformlyContinuousOn` under `+` and `·`,
`Complex.hasDerivative_congr`, `Complex.hasDerivative_pow`, and the
Cauchy–Riemann disc-membership bridge — nine declarations, all axiom-free**
(`PARTIAL`, complex-polyderiv, 2026-09-06, ADR-1656).

## What this slice is

ADR-1642 put the ℂ derivative on the real shelf's UNIFORM footing, with a closed
disc replacing the interval; ADR-1646 landed `Complex.BoundedOn` and
`Complex.UniformlyContinuousOn`; `complex/leibniz.rs` landed the product rule.
That rule takes four hypotheses it does not derive, and `leibniz.rs`'s own
module documentation named the obstruction between it and a polynomial's
derivative exactly: an induction over the degree applies the product rule at
every step and must **rebuild** all four for the accumulated partial
polynomial. Two of the four (`bounded_on_add`, `bounded_on_mul`) were already
closed. This lane closed the other two, then went as far up the ladder as they
reach.

## Partition check

Run before proving anything, and it came back clean. None of `Complex`,
`uniformlyContinuous`, `UniformlyContinuous`, `polyEval`, `hasDerivative`,
`CauchyRiemann`, `Holomorphic` or `holomorphic` occurs in
`artifacts/structural-index/held-out-exclusion-manifest.json`,
`artifacts/autogenesis/nursery-v2-extension.json`, or
`corpus/glaurung-proof-populations/`. Coverage was confirmed positively with a
control term of the same kind (`Nat`), which hits all three sources — so the
empty result is a real negative and not a grep that never pointed at its
subject. **No target of this lane is in a blind evaluation population.**

## What landed

Nine declarations across three new files, all under `crates/axeyum-lean-kernel/src/complex/`.

`uc_closure.rs`:

| name | what it says |
| --- | --- |
| `Complex.uniformlyContinuous_add` | uniform continuity is closed under pointwise `+` on a disc |
| `Complex.uniformlyContinuous_mul` | …and under pointwise `·`, given `BoundedOn` for both factors |

`polyderiv.rs`:

| name | what it says |
| --- | --- |
| `Complex.hasDerivative_congr` | transport a derivative along pointwise `Complex.Equiv` agreement **on the disc only** |
| `Complex.hasDerivative_pow` | the power rule at exponent `Nat.succ n`, gated on two `Nat → Nat` magnitude Skolems |

`cauchy_riemann.rs`:

| name | what it says |
| --- | --- |
| `Complex.abs_I` | `Complex.abs I ~ CReal.one` |
| `Complex.inDisc_ofReal_offset` | a point at real offset `u` from `c` is in the disc as soon as `\|u\| ≤ r` |
| `Complex.inDisc_I_offset` | the same on the vertical segment |
| `Complex.inDisc_of_two_sided` | …from the two ONE-SIDED bounds, the form interval hypotheses arrive in |
| `Complex.inDisc_I_of_two_sided` | the vertical twin |

## The three calls worth reading (ADR-1656)

1. **The accuracy budget is `CReal`'s verbatim; only the algebra is
   re-derived.** `Complex.UniformlyContinuousOn`'s bound is
   `CReal.le (Complex.abs …) (CReal.ofRat …)`, so nothing past the modulus is
   complex, and `natDivSucc_antitone` / `natDivSucc_scale` (through
   `fold_index0_first`) / `natDivSucc_add` / `natDivSucc_halve` are reused
   exactly rather than approximately. What ℂ buys is the algebra: the real
   shelf's private ~60-line `product_diff_identity` and its
   `add4_comm`/`neg_add` shuffle are each ONE `ring_law_proof` call here.

2. **The power induction still commutes the product, and
   `uniformlyContinuous_mul` does not change that.** `hasDerivative_mul` needs
   continuity of its FIRST factor; `pow z (succ j) ≡ mul (pow z j) z` puts the
   already-built `pow (·, j)` there, and that function's own continuity is
   exactly what is missing at an arbitrary `j`. Closure under products answers
   a different question. So the step uses `F := id` and transports across
   `mul_comm` — which is what `hasDerivative_congr` is for.

3. **The Cauchy–Riemann bridge is cheap and is NOT the obstruction.** Cost,
   measured: two rewriting steps and no estimate. `(c + ofReal u) − c ~ ofReal
   u` is a two-atom ring identity, `Complex.abs_ofReal` converts the modulus,
   `CReal.le_congr` carries the bound. The vertical segment costs one lemma
   more (`abs_I`). What CR is blocked on is **component extraction** — see
   below.

## What did NOT land, and the sized obstruction

- **`Complex.hasDerivative_polyEval` / `Complex.holomorphic_polyEval`.** With
  `hasDerivative_pow` in place the remaining work is a second induction over
  `Complex.polyEval`'s coefficient list. Both closures it needs are now
  available, but every application of `hasDerivative_mul` inside that induction
  needs its three magnitude Skolems supplied **at the accumulated degree**, so
  the slice needs a `Nat → Nat` built by recursion over the same list. That
  recursion, not the analysis, is what remains.

- **The Cauchy–Riemann equations themselves.** Blocked on component extraction:
  from `Complex.HasDerivativeOn F F' c r` produce
  `CReal.HasDerivativeOn (fun t => re (F (c + ofReal t))) … a b`. The real
  obstruction is that `re` has no HOMOMORPHISM law here — `complex.rs` has
  `re_congr` (a congruence for `Equiv`) but for `mul` there is no law to have,
  since `re (z·w) = re z · re w − im z · im w`. Controlling the imaginary parts
  is precisely the content of the CR equations, so the two directions
  (horizontal and vertical) must be computed separately and compared. That is a
  genuine slice, not a corollary.

## Files

- `crates/axeyum-lean-kernel/src/complex/uc_closure.rs` (new)
- `crates/axeyum-lean-kernel/src/complex/polyderiv.rs` (new)
- `crates/axeyum-lean-kernel/src/complex/cauchy_riemann.rs` (new)
- `crates/axeyum-lean-kernel/src/complex.rs` (module registration, `STEPS`)
- `crates/axeyum-lean-kernel/src/complex/complex_tests.rs` (every-declaration
  sweep, `EXPECTED_STEP_ORDER`)
- `docs/research/09-decisions/adr-1656-the-complex-polynomial-derivative-is-a-transport-and-the-cauchy-riemann-block-is-component-extraction.md`
