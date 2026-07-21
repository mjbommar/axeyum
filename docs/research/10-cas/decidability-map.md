# Decidability map — the certified core vs. the computed frontier

Status: design note (2026-07-20)
Last updated: 2026-07-20

The load-bearing document. It fixes, per CAS capability, **(1)** whether the
underlying decision problem is decidable, **(2)** whether the standard algorithm
is complete, and **(3)** the **certificate route** — which axeyum procedure
discharges the equality/correctness obligation and what the checkable witness is.
This table *is* the proof-carrying contract: a capability may ship a `certified`
result only if this map gives it a witness route.

Trust tags (per-answer, first-class output; mirrors the
[capability matrix](../08-planning/capability-matrix.md) assurance levels and the
[trust ledger](../08-planning/trust-ledger.md)):
- **`certified`** — a checkable witness is attached (re-checkable independently).
- **`decidable-uncertified`** — a complete algorithm produced it, but no witness
  is emitted (yet). Sound, but the user must trust the implementation.
- **`heuristic`** — may fail to find a true answer; **never asserts a false one**.
  This is the honest label for the undecidable frontier.

## The pivot: zero-testing

Almost every CAS correctness obligation reduces to **zero-testing** — deciding
`a − b ≡ 0`. axeyum can certify a transform exactly when it can lower the
obligation `transform(e) − e ≡ 0` (or the appropriate structural equality) into a
theory with a decidable zero-test:

| Domain of the obligation | Zero-test | axeyum route | Witness |
|---|---|---|---|
| Polynomials / rational functions over ℚ | **decidable** | `poly.rs` canonical form; QF_NRA identity | normal form / RCF refutation of `≠` |
| Algebraic numbers | **decidable** | `real_algebraic.rs` (defining poly + interval) | sign/compare certificate |
| Finite fields 𝔽ₚ, modular / BV | **decidable** | QF_BV bit-blast + DRAT | DRAT/Alethe/Lean UNSAT proof |
| Linear real/integer | **decidable** | QF_LRA (Farkas) / QF_LIA | Farkas / Lean-kernel certificate |
| RCF (real-closed field) inequalities | **decidable** (Tarski) | QF_NRA CAD/SOS | SOS/Positivstellensatz cert (partial) |
| General elementary (sin/exp/abs constants) | **undecidable** (Richardson) | — | none — `heuristic` |

## Per-capability contract

| Capability | Decidable? | Complete? | Trust ceiling | Certificate route (axeyum) |
|---|---|---|---|---|
| Differentiation of **rational functions** | Yes | Yes | **certified** | compute `d/dx` on terms; check `result − Dp ≡ 0` via `poly.rs::rat_derivative` exact match **and** QF_NRA identity |
| Differentiation with elementary heads (sin/exp/log…) | Yes (mechanical) | Yes | **decidable-uncertified** → `certified` on the *rule table* | rule application is denotation-preserving by a manifested rule; the *identity to the derivative operator* is trusted per-rule (Lean-liftable later) |
| Polynomial arithmetic (+,×,÷, rem) | Yes | Yes | **certified** | exact `poly.rs`; re-multiply/So check |
| Polynomial **GCD** (subresultant) | Yes | Yes | **certified** | cofactors + Bézout: `g·q₁=a, g·q₂=b`, checked exactly |
| Square-free decomposition | Yes | Yes | **certified** | `p = ∏ fᵢⁱ`, re-multiply + `gcd(fᵢ,fᵢ′)=1` |
| Factorization over 𝔽ₚ / ℤ / ℚ | Yes | Yes | **certified** | re-multiply factors ≡ input (trivial check); irreducibility is the harder claim |
| Canonical form / **zero-testing** of rational functions | Yes | Yes | **certified** | `poly.rs` normal form is the certificate; or QF_NRA |
| **Simplify** (general elementary) | **No** (Richardson) | No | **heuristic** | certify only the sub-steps that lower to a decidable domain; label the rest |
| Exact linear algebra (solve, det, rank) | Yes | Yes | **certified** | Bareiss; witness = residual `A·x−b≡0` / cofactor matrices |
| Integer matrix normal forms (Hermite/Smith) | Yes | Yes | **certified** | unimodular transform matrices `U,V`, checked `U·A·V = S` |
| Linear / polynomial equation solving | Yes | Yes | **certified** | substitute solution back; residual zero-test |
| Transcendental equation solving | **No** | No | **heuristic** | certify a *found* root by substitution + zero-test; never completeness |
| Integration (rational functions) | Yes | Yes | **certified** | **differentiate the answer, zero-test against integrand** (the clean self-certifying case) |
| Integration (elementary, computable constants) | Conditional (Risch) | complete over computable constant field | **certified** when returned; **heuristic** on fallthrough | differentiate-and-check the antiderivative; "provably non-elementary" needs the Risch structure theorem (later) |
| Integration (general / definite / Meijer-G) | Heuristic | No | **heuristic** | differentiate-and-check when an antiderivative is claimed; else labeled |
| Limits (exp-log via Gruntz) | Yes on class | complete on class | **decidable-uncertified** | value computed; certification route open |
| Series to finite order | Yes | Yes | **certified** | truncation identity checkable to the order |
| Summation: Gosper (indefinite) | Yes | Yes | **certified** | telescoping certificate `t(n+1)−t(n)=aₙ`, zero-tested |
| Summation: Zeilberger (definite, holonomic) | Yes on holonomic | complete on holonomic | **certified** | recurrence + certificate function, checkable identity |
| Primality | Yes | Yes | **certified** | ECPP/Pratt certificate, or deterministic AKS |
| Integer factorization | Yes | Yes | **certified** | re-multiply factors (trivial); primality certs on factors |
| Bounded / modular number theory | Yes | Yes | **certified** | QF_BV/QF_LIA + DRAT/Lean (already in-tree) |
| Diophantine (general) | **No** (MRDP) | No | **heuristic** | bounded instances only, via QF_LIA |
| Branch-cut identities (multivalued) | convention-dependent | No | **heuristic** unless assumptions pin the branch | certify only under an explicit assumption/domain (needs the assumptions engine) |

## Design consequences

1. **The certified core is large and exactly axeyum's home turf**: everything
   that lowers to polynomials, rational functions, algebraic numbers, finite
   fields, linear arithmetic, or RCF. Differentiation-of-rationals, GCD, factor,
   exact linear algebra, rational-function integration (self-certifying by
   differentiate-and-check), Gosper/Zeilberger, primality — all `certified`.
2. **Integration has a beautiful asymmetry**: *finding* an antiderivative is hard
   and often heuristic, but *checking* one is just differentiation + zero-test —
   which is `certified` whenever the integrand/answer are rational (or elementary
   with a decidable constant field). So even heuristic integration can return a
   **certified** answer when it happens to succeed. This is the flagship
   demonstration of the proof-carrying thesis.
3. **The frontier is honestly labeled, never hidden**: general `simplify`,
   transcendental solving, general Diophantine, branch cuts → `heuristic`, with
   the sub-steps that *do* lower to a decidable domain individually certified.
4. **The assumptions engine is a prerequisite** for certifying domain-sensitive
   rewrites (`sqrt(x²)→|x|`, branch cuts). It is a mid-phase dependency, not a
   day-one one.

See [build-plan.md](build-plan.md) for the sequencing this implies.
