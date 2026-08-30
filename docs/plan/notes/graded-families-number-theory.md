# Notes: graded-families-number-theory

Detail moved out of [`../status/graded-families-number-theory.md`](../status/graded-families-number-theory.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

New file: `crates/axeyum-lean-kernel/src/nat_prelude/fermat_witness.rs`.
Landed across commits `127b4f716` (declarations), `8e002a641` (row-3 test),
`2740d11cb` (fact ledger), `37f869b08` (ADR-0825).

1. `Nat.mod_eq_iff_mod_eq : forall d a b, 0 < d -> Iff (ModEq d a b) (Eq (modulo a d) (modulo b d))`
   — bridges the existential balanced-witness `ModEq` to the EXECUTABLE
   `Nat.mod` comparison, built from two already-landed theorems:
   `mod_eq_iff_div_mod_remainder_eq` (`modular.rs`) instantiated with
   `div_mod_exec` (`division.rs`) supplying the `divMod` witness at both `a`
   and `b`. No new induction. `div_mod_exec` needs the divisor syntactically
   `succ`-shaped (`Nat.divMod`'s own `r < divisor` bound is false at
   `divisor = 0`), so this is built at `n := succ (pred d)` and transported
   back to `d`, exactly `fermat.rs`'s own `pos_implies_succ_pred` pattern.
2. `Nat.not_prime_of_pow_mod_ne : forall p a, Not (Eq (modulo (pow a p) p) (modulo a p)) -> Not (Prime p)`
   — ADR-0603 row 1, general constructive form, true for every `p, a` with
   no restriction and no decidability principle beyond what already exists:
   direct contrapositive of the already-landed `Nat.pow_prime_modeq_self`
   (Fermat's little theorem), composed through step 1's bridge.
3. Row 2: none, argued from shape (matches ADR-0825/ADR-0716) — a single
   modus-tollens step on an unconditional theorem has no comparison or
   search to extract a boundary from.
4. Row 3: the SAME row-1 declaration, instantiated at DISCRIMINATING
   numerals and kernel-checked both ways
   (`not_prime_of_pow_mod_ne_certifies_four_composite_and_is_rejected_at_five_prime`,
   `nat_prelude_tests.rs`): composite `p=4, a=3` (`3^4 mod 4 = 1 != 3 mod 4
   = 3`) admits `Not (Prime 4)` as a throwaway theorem; the IDENTICAL
   construction at the real prime `p=5, a=3` (`3^5 mod 5 = 3 = 3 mod 5`) is
   attempted and the trusted gate genuinely REFUSES it (`Eq.refl` cannot
   certify a `beq` reduction to `true` as `false`) -- the non-vacuity
   control, verified as a real `Err`, not asserted.

**Axiom footprint, read from the kernel** (`theorem_axiom_footprint`, fresh
`--release` build): both declarations `footprint=[]`, against the whole Nat
prelude's 727 theorems, all axiom-free, 0 trusted declarations in the
environment.

**Bug found and fixed while writing the row-3 test**: `NatOps::eq`/`::refl`
hardcode the `Nat` carrier (the same "dev helper hardcodes a carrier"
hazard `CLAUDE.md` documents for `NatOps::congr`/`IntDev::irefl`) --
comparing two `Bool`-typed `beq` results needs `bool_eq`/`bool_refl`, and
using the `Nat` forms produced an opaque `TypeMismatch { expected: AxNat,
got: Bool }` traced via `d.explain(&e)`.

`cargo test -p axeyum-lean-kernel --lib nat_prelude::`: 225 passed, 0
failed (was 224 before this lane's first declaration, 223 before the
coverage-list fix).

Facts: `F:nat-mod-eq-iff-mod-eq`, `F:nat-not-prime-of-pow-mod-ne`.
`depends_on` populated by `scripts/check-fact-depends-derived.py --fix`,
not hand-listed. `python3 scripts/validate-facts.py`: 0 errors, 2276 facts
(was 2274).

## Holdout isolation

Before and after (identical -- this lane never touches
`artifacts/autogenesis/`, confirmed via `git status --porcelain --
artifacts/autogenesis/` being empty throughout):

    python3 scripts/check-autogenesis-holdout-isolation.py
    AUTOGENESIS_HOLDOUT_ISOLATION|held_out=116|files_scanned=1110|settled=0|references=0|verdict=PASS

## Why only one family

Step 0 found the two most obvious number-theory targets both already
claimed or actively contested this session (see the survey above):
Euler's theorem is genuinely blocked on three hard pieces per a sibling
lane's own verified handoff (not the "one theorem away" ADR-0716 claimed),
and the Euclid-Euler even-perfect-number theorem is under active
multi-lane construction in a 3,702-line file with commits landing
throughout this session. Rather than duplicate either or dispatch a second
family into unfamiliar, contested territory under time pressure, this lane
landed one complete, well-graded family with both rows kernel-checked and
axiom-free, and recorded the reasoning in ADR-0825 (including the general
finding: a decidable-subject row 1 that is directly executable at concrete
instances IS row 3, needing no separate `axeyum-cas` producer/verifier
pair). A Mathlib reader would correctly note this family does not touch
Euler's theorem, the Euclid-Euler characterization, or quadratic
reciprocity -- all three remain open, all three are honestly recorded as
open (two as actively in-progress by other lanes) rather than claimed.

## Next steps for a successor lane

1. Euler's theorem: pick up `docs/plan/status/374-euler-theorem.md`'s three
   named remaining pieces (Nat/Int index bridge, `euler_unit_coprime`'s IFF
   converse, final assembly) -- verify each in-tree first, per the standing
   "a handoff's blocked-on-X is a claim about one route" rule.
2. Euclid-Euler perfect numbers: check `nat_prelude/perfect.rs`'s latest
   state before touching it; `declare_perfect_all` is the wiring point once
   the final assembly lands.
3. Quadratic reciprocity: row 1 is genuinely absent under any spelling
   tried (`reciproc`, `legendre`, `jacobi`, `quadratic_res`); the Legendre
   symbol criterion (`Int.euler_criterion_pm_one`,
   `Int.is_quadratic_residue*`) is landed and could seed row 3.
