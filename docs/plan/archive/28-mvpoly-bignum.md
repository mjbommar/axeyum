# Lane: mvpoly-bignum (coefficient width in `MvPoly`, decline attribution, monomial order)

<!-- plan-section: lane-status -->

**Continuation lane — took the shared wall that `telescoping-scale` and
`geometry` both hit in `crates/axeyum-cas/src/mvpoly.rs` (2026-08-14).**

**(1) The multivariate GCD no longer runs in `i128`.** The failure was
*intermediate*, and the reproduction is the whole argument: on Apéry's degree-8
shift quotient the inputs' largest coefficient is **120**, the answer's is **6**,
and the pseudo-remainder sequence between them passes through **4187 bits** —
against the 127 an `i128` numerator holds. So the binding bound was on the
scratch space, not on the question or the answer. `MvPoly::gcd` now converts to
an unbounded-integer ring (`src/mvpoly/big.rs`), runs the same recursive
primitive PRS there with the integer content divided out at **every** step
(4187 bits becomes 76), and converts only the answer back. `MvPoly` itself keeps
its `Copy` `i128` rationals and its checked contract; 163 call sites across two
crates are untouched, and the Gröbner path — which never calls `gcd` — is
unaffected. Chosen over a subresultant PRS because that only makes the growth
polynomial: a large enough input still overflows, and the decline would still be
a fact about `i128` rather than about mathematics.

**(2) Apéry verifies.** `∑_k C(n,k)²·C(n+k,k)²` was the acceptance test; the
search returns **Apéry's own recurrence** — `(n+1)³`, `−(2n+3)(17n²+51n+39)`,
`(n+2)³`, coefficient for coefficient — in 97 ms, and the independent checker
accepts it. Committed as an artifact (`apery-numbers-recurrence.json`,
re-checked from the file by a sweep that never calls the search) and as
`F:apery-numbers-recurrence`; the `cas-certificate` route is now 15 facts,
`validate-facts.py` 0 errors. The fact claims the **recurrence only** — not the
irrationality of `ζ(3)`, which needs the second solution and a growth estimate.

Cost, measured as a real A/B (a `git archive HEAD` snapshot built clean, both
binaries pinned to cores 0–7, best of seven): **1.10–1.26× slower** on the seven
identities that already worked, checker times unchanged, and one identity that
declined now verifies. Reproducible via
`cargo run -p axeyum-cas --release --example telescoping_search_cost`, whose
second table reports peak GCD coefficient width per identity against the 127-bit
line — including what the *old* sequence computed, so "could not have finished"
is a measurement rather than an inference.

**(3) A decline says which kind.** `CofactorOutcome::Declined(DeclineReason)`
splits `ReductionSteps` / `PairIterations` / `BasisSize` / `PolyTerms` from
`Overflow`, with `is_ceiling()` drawing the line that decides whether raising a
budget could help. Every `?` on exact arithmetic in `groebner_cert.rs` goes
through `Budget::arith`, so the attribution is exhaustive rather than a guess.
It propagates to `ProofOutcome::Declined(GeometryDecline)` (which also separates
`UnverifiedWitness` — a refusal, not a resource limit) and into the solver, where
`cas_poly.rs` had been reporting the fixed string "hit a deterministic step
ceiling" for overflows too. Two controls, one per side: a starved budget must
decline as `ReductionSteps`, and reducing `x²` modulo `x − 10³⁰` must decline as
`Overflow` with every budget barely touched.

**(4) Degree-reverse-lex is available and measured, and it moves the geometry
frontier.** `MonomialOrder::{Lex, DegRevLex}` on `groebner_cert::Limits`. On the
corpus that already certifies, `grevlex` is **1.3–2.2× faster** with identical
verdicts and identical cofactor term counts. On the frontier it is not a
constant factor: `rhombus-diagonals-perpendicular` with `{abd-not-collinear}`
**declined after 287.8 s under `lex` and is IN IDEAL in 23.6 s under `grevlex`**,
34 cofactor terms, same ceilings. A frontier theorem is reachable.

And the decline it used to give is now legible: **`ceiling: ReductionSteps`,
not an overflow.** The geometry lane suspected `i128` and recorded that as
unestablished; it is now established, and it is not `i128` — so widening
`MvPoly`'s arithmetic would not have moved that theorem at all.

Defaults stay `Lex` in `geometry_limits()` and `ideal_limits()`, deliberately.
`certify` returns the certificate for the **smallest condition subset that
succeeds**, so a faster order can change *which* non-degeneracy conditions a
certificate uses — and those conditions are hypotheses in the facts'
`formal.statement`. Regenerating six committed certificates under a new order is
a change to what six facts claim, not a re-render, and it belongs to the lane
that curates the geometry corpus. `euler-line` was re-attempted under both
orders and **remains out of reach**: 1200 s each, no verdict on even the empty
condition subset. `grevlex` is a large lever, not a general solvent.

Gates: `cargo test -p axeyum-cas` 598 lib + 38 integration + 147 doc, all green;
the 19 telescoping tamper controls and both geometry non-degeneracy
counterexamples still **reject**; the seven pre-existing certificate artifacts
are byte-identical after the GCD change; `check-fact-evidence-replay.sh`
14/14 on `cas-certificate` (15/15 with Apéry); clippy clean on
`axeyum-cas` and `axeyum-solver` with `-D warnings`.

Full write-up:
[`docs/mathematics-2026-08/diary-mvpoly-bignum.md`](../../mathematics-2026-08/diary-mvpoly-bignum.md).

**Next for whoever picks this up, in order of payoff:** (a) switch
`geometry_limits()` to `grevlex`, regenerate the six certificates, **check
whether any certificate now uses a smaller condition set** (that is a change to
what the fact claims, and the point of doing it deliberately), and promote
`rhombus-diagonals-perpendicular` off the frontier with a fact of its own —
the measurement says it is reachable; (b) the Gröbner path's `MvPoly` arithmetic
is *not* the bottleneck on the rhombus (measured: `ReductionSteps`), so widen it
only when a run actually reports `Overflow` — which is now readable rather than
inferred; (c) `leading_integer_zeros` still declines when the leading recurrence
coefficient mentions more than the shift variable, which a Saalschütz-type
identity will hit.

<!-- plan-section: landed-changes -->

| 2026-08-14 | `mvpoly-bignum` | `MvPoly::gcd` moved into an unbounded-integer ring with per-step content removal (Apéry's shift quotient: 4187-bit peak against a 127-bit type, now 76); Apéry's recurrence found and verified, with an artifact and a fact; `CofactorOutcome::Declined` split into ceiling-versus-overflow and propagated to geometry and the solver; degree-reverse-lex added to `groebner.rs`, measured at 1.3–2.2× on the geometry corpus, and shown to reach `rhombus-diagonals-perpendicular` in 23.6 s where `lex` declines after 287.8 s | `crates/axeyum-cas/src/mvpoly/big.rs`, `crates/axeyum-cas/src/mvpoly.rs`, `crates/axeyum-cas/src/groebner.rs`, `crates/axeyum-cas/src/groebner_cert.rs`, `crates/axeyum-cas/src/geometry_certify.rs`, `crates/axeyum-cas/src/lib.rs`, `crates/axeyum-solver/src/cas_poly.rs`, `crates/axeyum-cas/tests/telescoping_identities.rs`, `crates/axeyum-cas/examples/telescoping_search_cost.rs`, `crates/axeyum-cas/examples/geometry_probe.rs`, `crates/axeyum-cas/examples/emit_telescoping_certificates.rs`, `artifacts/cas-certificates/apery-numbers-recurrence.json`, `artifacts/facts/F-apery-numbers-recurrence.json` |
