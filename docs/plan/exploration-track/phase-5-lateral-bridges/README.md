# Phase 5 — widening the graph with lateral bridges from the CAS

Verdict from review: **the funnel diagnosis is correct and quantifiable; the
direction is sound; three corrections to the framing.**

## The funnel, quantified

Of the 14 `TrustId` reductions, **nine** (BitBlast, Tseitin, SatRefutation,
ArrayElim, Ackermann, IntBlast, DatatypeElim, Fpa2Bv, TermLevelEnum) are eager
elimination toward SAT/enumeration. Only Farkas, LraDpll, XorGaussian, Sos, and
Diophantine are lateral, and **each is narrow**: `Sos` is **degree-2 only**
(ADR-0039); XorGaussian's certified sub-case is the no-branching Gaussian level;
Diophantine is integer-Farkas-shaped. Dispatch is fixed feature-routing, and
`recommended_portfolio` in `strategy.rs` returns fixed one- or two-element lists.

**An agentic search over today's graph would mostly re-derive that hand ordering.**
The branch's central claim holds.

## Three corrections

1. **The CAS is a disconnected component, not an under-used node.**
   `crates/axeyum-cas/Cargo.toml` depends only on `axeyum-ir` + num crates, and
   **no crate in the workspace depends on `axeyum-cas`**. The solver never calls
   it. ADR-0301 deliberately points the dependency the *other* way (CAS lowers to
   the solver to certify itself). So the first lateral bridge is also an
   integration keystone — where certificate types and checkers live is an
   ADR-level decision under CLAUDE.md's minimal-crate rule, and it is task zero.
2. **Most CAS "certificates" are not yet artifacts.** The discipline is excellent
   (`ZeroTest::Certified { witness: MultiPoly }`, `Certainty` tags, honest
   `None`/`Unknown` on i128 overflow), but with few exceptions the witness is an
   in-memory normal form re-derived by the same code, not a serialized certificate
   an *independent* checker replays. Critically, `groebner.rs` computes bases and
   decides ideal membership but **discards the cofactors** — `reduce()` (line 321)
   keeps no quotients — so the single most valuable lateral certificate
   (Nullstellensatz cofactors) does not exist yet. **Bridge work is mostly
   certificate-formalization work, not new mathematics.**
3. **Some proposed bridges have no traffic.** `axeyum-ir::Op` has no
   factorial/binomial/transcendental heads, so a WZ bridge — however beautifully
   checkable — has nothing to fire on from the solver side. It is a CAS-surface
   capability until a front-end recognizer exists. Widening must be measured
   against corpora (the `progress_frontier` ratchet) or it is decoration.

## The proposed lateral bridge set

Certificate class: **A** = one small algebraic identity (re-multiply/compare);
**B** = recomputation with an already-trusted kernel; **C** = no practical
independent certificate.

| # | Bridge | Certificate | Crosses back? | Class | Size |
|---|---|---|---|---|---|
| B1 | NIA/NRA equational UNSAT → **Gröbner/Nullstellensatz** | cofactors `qᵢ` with `1 = Σ qᵢ·gᵢ`; check = re-multiply via `MvPoly` | yes — new `TrustId::Nullstellensatz` + `recheck()`; Lean route = ring normalization (the `linear_combination` model) | **A** | M |
| B2 | Integer linear systems → **Hermite/Smith normal forms** | `U, V, S` with `U·A·V = S`, `det U,V = ±1`; infeasibility from Smith divisors; feasibility = explicit solution | yes — composes with `DiophantineCertificate` + the ADR-0042 Lean int prelude | **A** | M |
| B3 | NRA nonnegativity degree ≥ 4 → **SOS Gram + exact rounding** | exact rational weighted-square decomposition; extends `SosCertificate::verify` (already trusts nothing from the producer) | yes — same `TrustId::Sos`, wider sub-case | **A** | L |
| B4 | Univariate real roots → **Sturm / RootOf** | Sturm chain + endpoint sign counts; check = recompute | partially — solver already has Sturm internally; gain is a shared serialized artifact | **B** | S |
| B5 | Modular constraints → **𝔽ₚ polynomial algebra** | root value checked by evaluation; factors by re-multiply. **Unsat via irreducibility is uncertified — do not ship that direction** | sat yes, unsat no | A/C | S |
| B6 | Combinatorial identities → **Gosper/Zeilberger/WZ** | rational function `R(n,k)` + base cases; one telescoping identity | not yet — no solver traffic; ship as serialized CAS-surface evidence | **A** | S / L |
| B7 | Rigorous numerics → **interval arithmetic** | the interval evaluation itself | supporting role for B3 rounding | **B** | S |
| B8 | Counting → generating functions | truncation only; real cert needs holonomic machinery not present | no | C | defer |
| B9 | Graph → spectral | `Av=λv` checkable but combinatorial conclusions lack a small cert | no | C | defer |
| B10 | Group/permutation | needs Schreier–Sims straight-line programs; the module is 245 lines | no | C | defer |

**Recommended first three: B1, B2, and B3-lite** (B3 restricted initially to
diagonally-dominant / LDLᵀ-decomposable Gram matrices — no SDP needed, pure exact
rational, still strictly widens degree-2). All three are class-A certificates
checkable by exact arithmetic already in-tree; B1 and B2 open genuinely new UNSAT
classes rather than re-deriving the funnel; each registers cleanly in the trust
ledger with a `recheck()` in the ADR-0010/0013/0014 mold.

**B6 (WZ) is the best demonstration artifact and nearly free to serialize** —
`prove_wz_sum` (`lib.rs:6204`) and `certifies_wz_sum` (`:5626`) already implement
discovery and checking — but it widens the CAS's certified surface, not the
solver's search space. Keep it in the plan, honestly labeled.

## CAS capability inventory (what exists, what is certified)

`crates/axeyum-cas` is ~47k lines, pure Rust, WASM-safe, leaf crate. Results carry
`Certainty::{Certified, DecidableUncertified, Heuristic}` and
`ZeroTest::{Certified{equal, witness: MultiPoly}, Unknown}` (`lib.rs:2004-2028`).
Governing docs: `docs/research/10-cas/{vision,decidability-map,substrate-map,
gap-analysis,next-wave-roadmap}.md` and ADR-0301.

Highlights: `integrate` → `CertifiedIntegral` (`lib.rs:13410`) certified by
differentiate-and-check; WZ certificates as above; `groebner.rs` Buchberger
(**lex only**, no cofactors); `mvpoly.rs` sparse ℚ-multivariate; `sturm.rs` /
`algebraic.rs` (RootOf = minimal poly + isolating interval); `gfp.rs` Berlekamp
factorization (irreducibility **uncertified**); `normalforms.rs` Hermite (:450)
and Smith (:479) **returning transform matrices** — already in certificate shape;
`interval_arith.rs` rational-endpoint enclosures; `permutation.rs` **245 lines,
too thin for group reasoning**; no Pratt/ECPP primality certificates despite the
decidability-map naming them.

Solver side: `SosCertificate::verify` (`nra_real_root.rs:6335`, degree-2, exact
rational, "never trusts the producer's matrix"), `simplex.rs`/`alethe_lra.rs`
(Farkas + Alethe), `lia_gcd.rs`, `nia_square.rs`, `DiophantineCertificate` with a
Lean discretely-ordered-ring prelude (ADR-0042).

## Prior art

- **SC-Square** — the community that *is* this bridge (SMT-RAT, cvc5+CoCoALib,
  Maple+SAT) but with a **weak certificate story**. That gap is exactly axeyum's
  identity. <https://www.sc-square.org/>, <https://arxiv.org/abs/2209.04359>,
  Kremer et al. *Proving UNSAT in SMT: The Case of QF_NRA*
  <https://arxiv.org/pdf/2108.05320>
- **PAC proofs — the strongest template.** Kaufmann–Fleury–Biere's Practical
  Algebraic Calculus: Gröbner-based multiplier verification emitting certificates
  checked by Pacheck and the Isabelle-verified Pastèque. Untrusted algebraic
  search + small trusted checker, over circuits — directly adjacent to axeyum's
  bit-blast core. <https://link.springer.com/article/10.1007/s10703-022-00391-x>,
  <https://github.com/d-kfmnn/pacheck>
- **Lean `polyrith`/`linear_combination` — the direct precedent**: untrusted
  Gröbner cofactor search returning a certificate Lean re-checks by ring
  normalization. **Cautionary datum: the Sage backend was shut down and polyrith
  deprecated** — design bridges so the search half is replaceable without
  invalidating checked certificates.
- **SOS with exact rational rounding** — Peyrl–Parrilo; Monniaux–Corbineau on the
  degenerate-case failures <https://arxiv.org/abs/1105.4421>; Coq Micromega
  `psatz`; Harrison TPHOLs 2007. **cvc5 has no SOS route** (its NRA proofs are
  incremental linearization).
- **WZ replay** — Harrison's HOL Light work; the Coq ζ(3) effort checking
  *unverified Maple* certificates a posteriori.
- **CAD is a trap** — Davenport–Heintz doubly-exponential lower bound; **no
  production CAD is verified**; the verified work is univariate/QE-shaped only
  (BKR in Isabelle, verified virtual substitution).
- **Sturm as certificate** — Li–Paulson "untrusted certificates": a Sturm chain is
  checked by *recomputation*, not by a one-multiply identity.
  <https://arxiv.org/abs/1506.08238>

## CLAUDE.md compliance per bridge

Every bridge lands as: (i) semantics — the exact source-fragment recognizer;
(ii) the certificate struct + independent `recheck()` beside the other
`*Certificate` types in `axeyum-solver`; (iii) `TrustId` registration + regenerated
golden trust ledger; (iv) soundness-negative tests (mutated cofactors, transforms,
Gram entries must be rejected); (v) degenerate-argument fuzz seed-classes — zero
polynomial, empty generator set, zero matrix, `p=2` fields, non-monic leading
terms, identity permutation — **before** anything becomes public.

## Tasks

| id | title | size |
|---|---|---|
| [T5.1](T5.1-adr-bridge-boundary.md) | **ADR: bridge boundary and dependency direction** | S |
| [T5.2](T5.2-cofactor-division.md) | `reduce_with_quotients` in `groebner.rs` | M |
| [T5.3](T5.3-ideal-membership-certificate.md) | Generator-representation tracking + membership certificate | M |
| [T5.4](T5.4-nullstellensatz-trustid.md) | `NullstellensatzCertificate` + `recheck()` + `TrustId` | M |
| [T5.5](T5.5-nia-nra-frontier-ratchet.md) | Corpus + frontier ratchet for newly decided slices | S |
| [T5.6](T5.6-smith-hermite-certificates.md) | Smith/Hermite integer certificates | M |
| [T5.7](T5.7-sos-degree-lift.md) | SOS degree-lift phase 1 (LDLᵀ / diagonally dominant, no SDP) | L |
| [T5.8](T5.8-wz-evidence-artifact.md) | WZ evidence artifact + minimized independent checker | S–M |
| [T5.9](T5.9-sturm-shared-artifact.md) | Sturm/RootOf shared artifact | S |
| [T5.10](T5.10-deferred-bridges.md) | Deferred: recognizers, holonomic counting, 𝔽ₚ irreducibility certs | L |

## Risks

- **Gröbner blowup, aggravated by local choices** — `groebner.rs` is lex-only (the
  worst order computationally; fine for the certificate, since the *check* is
  order-independent) on i128 rationals, so coefficient swell hits the
  overflow-`None` path early. Nullstellensatz degrees are doubly exponential in the
  worst case. Mitigation: honest budgets, grevlex + BigInt as follow-up, and the
  bridge fires only on the decline path.
- **CAD is a trap** — do not build a CAD bridge. Take SOS for unsat and Sturm
  recomputation for models; that is also where the verified-checker prior art is.
- **SOS rounding failure modes** — floating SDP → exact rational fails precisely on
  non-strictly-feasible instances, and there is no pure-Rust SDP. Hence LDLᵀ first.
- **Bridges with no traffic** — WZ, generating-function, spectral, permutation
  certify things the solver cannot express. Each must show a measured frontier
  delta or be labeled CAS-surface capability.
- **The CAS `equal` is a large trusted surface** — `canonicalize_for_equality`
  (Γ-recurrence, Γ-reflection, Euler rewrite, prime-basis logs, `lib.rs:~2050`) is
  a stack of hand-proved folds. Fine for the CAS's own tags; it erodes "small
  trusted checker" if imported wholesale. Bridge checkers must be **minimized**
  re-implementations.
- **Uncertifiable directions dressed as certified** — 𝔽ₚ/ℚ irreducibility,
  factor-list completeness, primality. Only the re-multiply direction is class-A
  today; use the ledger's sub-case discipline.
- **Integration hygiene** — a careless `axeyum-solver → axeyum-cas` dependency
  drags 47k lines of search into the solver's audit surface. T5.1 exists to
  prevent this.
