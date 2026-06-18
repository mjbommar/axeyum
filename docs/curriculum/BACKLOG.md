# Curriculum Build Backlog (next 10–20 items)

Prioritized by **yield × readiness**, drawn from the curriculum gaps, the
foundational-book drawable fragments ([source-tocs.md](foundational-books/source-tocs.md)),
and the engine findings from the [Spivak benchmark](foundational-books/spivak.md).
Tags: **✅** decidable/ready · **◐** fixed-instance only · **⚙** engine work ·
**✦** Lean-horizon scaffolding. Size: S(mall)/M/L.

## Tier A — high-yield, decidable, ready now

1. **CRT solvability + witness** (`Family::NumberTheory`). `x≡a (mod m) ∧ x≡b
   (mod n)`, `gcd(m,n)=1` → SAT with the CRT witness. ✅ S · BV/LIA · *Stein Ch.2*.
2. **Quadratic residue / Legendre symbol** (`Family::NumberTheory`). `∃x. x²≡r
   (mod p)` at fixed small prime `p`, exhaustive over `x∈[0,p)` → SAT (QR) /
   UNSAT (non-residue). ✅ S · BV/enumeration · *Stein Ch.4*.
3. **Sum of two squares** (`Family::NumberTheory`). `n = a²+b²` for a representable
   `n`, SAT-by-witness (and a UNSAT case for `n≡3 mod 4`). ✅ S · BV · *Stein Ch.5.7*.
4. **Factor theorem** (`Family::Polynomial`). `(x−r) | p(x) ⇔ p(r)=0` at fixed
   coefficients; verify a claimed root and that the quotient multiplies back.
   ✅ S · BV · *Shoup Ch.18*.
5. **Finite field 𝔽ₚ inverses** (`Family::Algebra`). For prime `p`, *every* nonzero
   element is invertible (exhaustive over 𝔽ₚ), contrasted with composite `n`
   (some element has no inverse). Upgrades the ℤ/2ʷ field story to real 𝔽ₚ.
   ✅ M · BV/enumeration · *Shoup Ch.19*.
6. **Linear algebra over ℚ** (new `tests/linear_algebra_rational.rs`, solver/LRA).
   `Ax=b` solvability + the rational solution as witness; matrix inverse via
   `Ax=b` at fixed size; Farkas-refuted inconsistent system. ✅ M · LRA ·
   *VMLS Part II, Shoup Ch.15*.
7. **Proofs node demo** (closes the `proofs` curriculum gap). Pigeonhole
   `PHP(n+1,n)` → emit a DRAT/LRAT (and Alethe) refutation and **re-check it
   in-tree** — the "show your work / trusted small checking" lesson, on a
   proof-complexity landmark. ✅ M · proof track.
8. **Rationals node** (`tests`, solver/LRA). Exact-ℚ field & order facts
   (density: `a<b ⇒ a<(a+b)/2<b`; trichotomy) with Farkas certificates → covers
   the `rationals` node. ✅ S · LRA · *the ordered-field shadow of Spivak Ch.1*.

## Tier B — gap-filling / fixed-instance

9. **Fermat / Euler at fixed modulus** (`Family::Predicate`). `∀a∈(Z/pZ)*.
   a^(p−1)=1` as a finite-domain quantified check at small fixed `p`. ◐ M ·
   finite-domain quantifiers · *Stein Ch.2, Shoup Ch.2*.
10. **Polynomial division-with-remainder** (`Family::Polynomial`). `p = q·d + r`,
    `deg r < deg d`, at fixed coefficients over BV. ◐ S · *Shoup Ch.18*.
11. **RSA round-trip** (`Family::NumberTheory`). `(mᵉ)ᵈ ≡ m (mod n)` at fixed small
    keys (modular exponentiation by squaring, unrolled). ◐ M · *Stein Ch.3*.
12. **3×3 matrix identities** (`Family::LinearAlgebra`). `det(AB)=detA·detB`,
    associativity at 3×3 — over 𝔽₂ where still exhaustive; record where it exceeds
    the budget. ◐ M.
13. **SAT/CNF + bit-blasting demo** (example/lesson). "Watch a formula become
    Tseitin CNF, then DPLL/CDCL decide it" on a tiny instance, with the DIMACS and
    proof shown — closes the `sat-and-cnf` / `bit-blasting` concept gaps. ◐ M.

## Tier C — engine work surfaced by the benchmarks

14. **`prove` LRA→NRA dispatch** (⚙, `produce_evidence`). Route nonlinear real
    goals to NRA instead of rejecting them as `Unsupported`. Unblocks proving the
    Spivak NRA inequalities through the front door. ⚙ S/M.
15. **NRA honors its timeout** (⚙, `check_with_nra` refinement loop). The
    `am_gm`/`square_nonneg` cases run past the configured deadline; tighten the
    spatial branch-and-bound to bail to `unknown` promptly. ⚙ M.
16. **NRA sum-of-squares / positivstellensatz** (⚙, P2.5). Prove the foundational
    SOS inequalities (`a²+b² ≥ 2ab`, AM–GM₂, Cauchy–Schwarz) that linearization
    cannot — an SOS or CAD/nlsat path. Promotes the `#[ignore]`d Spivak frontier
    tests. ⚙ L · *the headline NRA gap*.

## Tier D — Lean-horizon scaffolding (sequence later)

17. **Decidable-geometry (RCF) node**. Coordinate-geometry facts over ℝ
    (Pythagoras, midpoint, collinearity) — mostly the NRA frontier today; freeze
    as targets that promote when Tier-C #16 lands. ◐/frontier.
18. **Peano-induction reconstruction targets** (✦). Freeze a small set of `∀n`
    theorems (`n+0=n`, commutativity of `+`, Bernoulli ∀n) as `.smt2`/Lean stubs
    documenting the P3.6/P3.7 goal — *targets, not benchmarks*.
19. **"Fill the proof step" tutor** (✦, example). An Alethe proof with a hole, the
    student fills the step, `check_alethe` grades it — interactive proof pedagogy
    on the now-compiling proof stack.

## Sequencing note

Tier A items #1–8 are all decidable and independent — build them in any order;
each flips a curriculum node or deepens a covered one and grows the BV/LIA/LRA
corpus. **#7 (proofs via pigeonhole) and #6 (LA over ℚ) are the highest-yield
gap-closers.** Tier C #14 is the cheapest engine win (unblocks the Spivak NRA
suite); #16 is the deep, high-value one (the SOS frontier). The
`covered_nodes_have_a_family_realized` invariant test keeps the
graph/code/docs in sync as each lands.
