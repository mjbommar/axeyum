# ADR-0985: Gauss's lemma's `a := 2` closed form lands axiom-free; the connecting theorem to `a^m mod p` stays open

Status: accepted
Date: 2026-08-31
Index-summary: `Nat.gaussCountBleClosedFormDisj` (the general `countRange`
closed-form invariant, by induction on `n` with `half` held fixed) and
`Nat.gaussNegCountTwoClosedForm` (`gaussNegCount (succ (mul 2 m)) 2 m = sub m
(div m 2)`, the classical `a := 2` closed form at the odd-prime shape `p =
2m+1`) land axiom-free in `nat_prelude/gauss_lemma.rs`, executing the route
ADR-0970 sized and left open. The connecting theorem to `a^m mod p` (Gauss's
lemma's actual content) is still not reached.
Index-status: accepted

## Context

ADR-0970 landed the counting primitive (`Nat.leastResidue`,
`Nat.gaussSignNeg`, `Nat.gaussNegCount`), the `a := 2` mod-bypass theorem, and
seven concrete `gaussNegCount` instances confirming the classical `p mod 8`
pattern numerically (the ADR's own summary said eight; the real count in the
landed module is seven — six at `a := 2` for `p ∈ {7,11,13,17,19,23}` plus one
at `a := 3, p := 7`). It fully routed, lemma-by-lemma, the general symbolic
closed form and the specialization to `pp := 2m+1`, but declined to execute
the ~150-250 line construction in the same session, judging it more likely to
consume the session in `TypeMismatch` debugging without a REPL than to land
cleanly.

This session verified every lemma name and signature the routed proof depends
on directly against the tree (`Nat.lt_or_eq_of_le`, `Nat.mul_le_mul_left`,
`Nat.le_add_right`, `Nat.le_trans`, `Nat.lt_succ_of_le`,
`Nat.ble_eq_false_of_lt`, `Nat.ble_eq_true_of_le`, `Nat.le_of_lt_succ`,
`Nat.add_le_add_left`, `Nat.le_succ`, `Nat.le_succ_succ`,
`Nat.lt_of_lt_of_le`, `Nat.lt_of_le_of_lt`, `Nat.add_comm`,
`Nat.add_right_comm`, `Nat.div_mod_exec`, `Nat.div_mod_unique`,
`Nat.zero_le`, `Nat.le_refl`, `Nat.sub_eq_zero_of_le`,
`Nat.add_sub_cancel_left`, `Nat.countRange_congr_lt`), confirmed the route was
faithful to the actual `Nat.divMod`/`Nat.countRange`/`Nat.add`/`Nat.mul`
definitions (in particular that `add x 1`, `add x 0`, and `mul x (succ y)`
are all `refl`-provable regardless of `x`'s shape, since these operators
recurse on their RIGHT argument — several of ADR-0970's "propositional via
`add_zero`" steps turned out to be pure defeq once checked), and then executed
it.

## What landed

`crates/axeyum-lean-kernel/src/nat_prelude/gauss_lemma.rs` (extended, no new
module):

- **`Nat.gaussCountBleClosedFormDisj : ∀ half n, Disj(half, n)`** where
  `Disj(half, n) := Or (And (Eq (countRange f n) 0) (Le n t)) (And (Le t n)
  (Eq (add (countRange f n) t) n))`, `f j := Nat.ble (Nat.succ half) (Nat.mul
  2 (Nat.succ j))`, `t := Nat.div half 2`. By induction on `n` with `half`
  (and `t`, and a once-computed `lt_half_mul2_succt : Lt half (mul 2 (succ
  t))`) held fixed as outer parameters — exactly ADR-0970's routed proof,
  with one structural simplification: `NatOps::induct` (`ops.rs`) builds the
  `Nat.rec` application directly from `motive`/`base`/`step` closures, so the
  proof never hand-assembles a raw `Nat.rec` term.
- **`Nat.gaussNegCountTwoClosedForm : ∀ m, Eq (gaussNegCount (succ (mul 2 m))
  2 m) (sub m (div m 2))`** — the classical closed form at the odd-prime
  shape `p := 2m+1`. Establishes `div (succ (mul 2 m)) 2 = m` via a direct
  `divMod 2 pp m 1` witness (`pp` is literally `add (mul 2 m) 1` up to
  defeq, and `Lt 1 2 = Le 2 2` by `le_refl`) plus `div_mod_unique`; bridges
  `gaussNegCount pp 2 m` to the general closed form's `countRange` via
  `gauss_residue_two_eq_double_of_lt` (ADR-0970) lifted through
  `countRange_congr_lt`; reads the value off
  `gaussCountBleClosedFormDisj` specialized at `half := m, n := m`.

Both new declarations are private local helpers plus the two `Declaration::
Theorem`s: `closed_form_pred`, `mul2succ`, `count_range_of`,
`congr_bool_to_nat`/`congr_nat_to_bool`/`bool_trans` (local `Bool`-carrier
congruence/transitivity twins of `NatOps::congr`/`NatOps::trans`, which are
hardcoded to a `Nat`-typed carrier — the same shape `bitwise.rs`,
`xor_algebra.rs`, and `subset_product.rs` each carry privately),
`or_elim2`/`and_intro2` (thin wrappers around `Or.rec`/`And.intro`, mirroring
`ops.rs`'s `cases_lt_bound`/`cases_lt_or_ge`), `ClosedFormCtx` (the shared
`half`/`t`/`lt_half_mul2_succt` scaffolding threaded through the base case
and all three step branches), and `disj_to_sub_eq` (extracts `Eq cf (sub x
t)` from the disjunction generically, reused for the `half := n := m`
specialization).

**Axiom footprint, read from the kernel**
(`theorem_axiom_footprint`): `Nat.gaussCountBleClosedFormDisj` and
`Nat.gaussNegCountTwoClosedForm` both carry footprint `0`.

**Agreement with the seven ADR-0970 instances, recomputed independently**: at
`a := 2`, `sub m (div m 2)` equals the landed value for all six instances —
`(p,m,expected)` = `(7,3,2)`, `(11,5,3)`, `(13,6,3)`, `(17,8,4)`, `(19,9,5)`,
`(23,11,6)`, each satisfying `expected = m - m/2` (`⌈m/2⌉`). One of the seven
(`a := 3, p := 7`) is outside this closed form's scope (`a := 2` only) and is
not compared. A new test,
`gauss_neg_count_two_closed_form_matches_the_landed_seven_two_instance`,
instantiates the closed-form theorem itself at `m := 3` and confirms the
kernel's own reduction agrees with `gauss_neg_count_seven_two`'s value (`2`),
independently of the symbolic admission.

**Verification run this session**: `cargo test -p axeyum-lean-kernel --lib
gauss_lemma::` (3 passed), `cargo test -p axeyum-lean-kernel --lib
nat_prelude::` (243 passed, 0 failed — nonzero count confirmed, up from 242
before this session), `cargo clippy -p axeyum-lean-kernel --lib -- -D
warnings` (clean), `python3 scripts/check-autogenesis-holdout-isolation.py`
(PASS, `held_out=146`, 0 files under `artifacts/autogenesis/` touched this
session).

## Bugs found and fixed while executing the routed proof

Three direction/argument bugs surfaced only once the kernel type-checked the
assembled term (a throwaway `#[cfg(test)]` probe rendering both sides of each
`TypeMismatch` via `Kernel::render_lean` found each in one run, per this
repository's standing debugging idiom):

1. `or_inl`'s first argument was the bare `Eq` component instead of the full
   `And` type the produced proof actually has.
2. A `Le`-transport in branch A2 used `heq : Eq j t` directly where the
   transport's direction needed `Eq t j` (`d.symm` first).
3. A `congr` call meant to lift `Eq j t` through `mul2succ` was instead
   applied to the already-`succ`-shifted `Eq (succ j) (succ t)`, doubling the
   `succ` in the conclusion; fixed by applying `mul2succ` directly to `heq`.

None of these represent an unsound proof reaching the environment — the
kernel rejected each before `add_declaration` admitted anything malformed.

## What remains — the connecting theorem

Unchanged from ADR-0970's sizing: `gaussNegCount p 2 m`'s value alone does
not establish the second supplementary law. That needs the least-residue
map's injectivity on `{1,…,m}`, a pairing lemma, and a product-cancellation
argument over `Int.prodRange` (built for Wilson's theorem). This session did
not attempt it — the closed form was the full scope of the routed work.

## Verification

- `cargo test -p axeyum-lean-kernel --lib gauss_lemma::` — 3 passed, 0
  failed.
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` — 243 passed, 0
  failed (nonzero count confirmed).
- `cargo clippy -p axeyum-lean-kernel --lib -- -D warnings` — clean.
- `cargo run --release -p axeyum-lean-kernel --example theorem_axiom_footprint
  -- gaussCountBleClosedFormDisj` / `-- gaussNegCountTwoClosedForm` (run
  separately — this tool keeps only the first name argument) — both
  footprint `0`.
- `python3 scripts/check-autogenesis-holdout-isolation.py` — PASS
  (`artifacts/autogenesis/` untouched this session).
- No fact-ledger entries added this session (see
  `docs/plan/status/gauss-lemma-closed-form.md` for the naming-collision
  note against `F:nat-gauss-lemma`, an unrelated divisibility-cancellation
  theorem also called "Gauss's lemma").
