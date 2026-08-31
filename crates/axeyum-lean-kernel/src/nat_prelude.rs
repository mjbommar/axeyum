//! The **natural-number prelude**: arithmetic over the logic prelude's
//! *inductive* `Nat`, together with the `Eq`-combinator and induction machinery
//! a development needs to use it.
//!
//! Unlike [`build_arith_prelude`](crate::build_arith_prelude) (an axiomatized
//! linear ordered field, for Farkas/LRA reconstruction) and
//! [`build_int_prelude`](crate::build_int_prelude) (an axiomatized discretely
//! ordered ring, for integer-cut reconstruction), **this prelude declares no
//! axioms at all**. [`build_logic_prelude`] admits `Nat` as a real inductive
//! with a real, ι-computing `Nat.rec`, so `add`/`mul`/`pow` are *definitions* by
//! structural recursion and every algebraic law below is a *theorem* the kernel
//! type-checks at admission through
//! [`Kernel::add_declaration`](crate::Kernel::add_declaration).
//! `nat_prelude_tests::the_nat_prelude_declares_no_axioms` enforces that claim
//! mechanically by walking the resulting environment.
//!
//! ## What is declared (all under the `Nat` namespace)
//!
//! **Recursive arithmetic definitions** — each by `Nat.rec` on its **second**
//! argument, so the defining equations hold *definitionally* (β/δ/ι) and need
//! no equation lemmas:
//!
//! | name      | zero case            | successor case                       |
//! |-----------|----------------------|--------------------------------------|
//! | `Nat.add` | `add x zero ≡ x`     | `add x (succ j) ≡ succ (add x j)`    |
//! | `Nat.mul` | `mul x zero ≡ zero`  | `mul x (succ j) ≡ add (mul x j) x`   |
//! | `Nat.pow` | `pow x zero ≡ 1`     | `pow x (succ j) ≡ mul (pow x j) x`   |
//!
//! **Truncated subtraction**: `Nat.pred` computes predecessor with
//! `pred zero ≡ zero`; `Nat.sub` recurses on its second argument. Checked
//! theorems include successor cancellation, self-subtraction, and restoration
//! under explicit order evidence.
//!
//! **Finite ranges**: `Nat.sumRange f n` recursively sums `f 0` through
//! `f (n-1)`. Its empty and successor equations are checked theorems backed by
//! definitional reduction.
//!
//! **Defining-equation theorems** (`add_zero`, `add_succ`, `mul_zero`,
//! `mul_succ`, `pow_zero`, `pow_succ`, `pred_zero`, `pred_succ`, `sub_zero`,
//! `sub_succ`) — each proved by `Eq.refl`; they exist so callers can rewrite by
//! name without knowing the recursion scheme.
//!
//! **Computational equality**: `Nat.beq` structurally compares two naturals and
//! ι-reduces to `Bool.true` exactly when they are equal. Its soundness,
//! completeness, and `Iff` specification are checked theorems, giving later
//! algorithms a constructive branch condition without classical choice.
//!
//! **Additive theorems**: `zero_add`, `succ_add`, `add_comm`, `add_assoc`,
//! `add_right_comm`, successor injectivity, and left/right cancellation.
//!
//! **Multiplicative theorems**: `zero_mul`, `succ_mul`, `mul_comm`,
//! `left_distrib`, `right_distrib`, `mul_assoc`, `one_mul`, `mul_one`,
//! `mul_eq_zero` (no zero divisors).
//!
//! **Order** (`Nat.le`): an *indexed* `Prop`-valued inductive relation with the
//! same shape as Lean's own `Nat.le` — `Nat.le.refl : Le n n` and
//! `Nat.le.step : Le n m → Le n (succ m)` — admitted through the same trusted
//! inductive gate, so its recursor `Nat.le.rec` (induction on the *derivation*)
//! is kernel-generated. `Nat.lt n m := Nat.le (Nat.succ n) m`. Theorems:
//! `zero_le`, `le_succ_succ`, `le_of_succ_le_succ`, `le_trans`, `le_total`, and
//! `le_add_right`, addition/multiplication monotonicity, order-conditioned
//! `sub_add_cancel`, and bounded `mul_sub_left_distrib`. The reducible checked
//! definition `lt_well_founded` lets generic `WellFounded.fix` programs perform
//! strong recursion over this order.
//!
//! **Divisibility**: `Nat.dvd a n := Exists (fun q => n = a * q)`, together
//! with checked reflexivity, zero, transitivity, multiplication, addition, and
//! all-Nat additive-cancellation laws. `dvd_mod_iff` connects those laws to the
//! executable remainder for every positive divisor without requiring the
//! common divisor itself to be positive.
//!
//! **Division and congruence**: `Nat.divMod` carries quotient and remainder
//! witnesses and proves existence, uniqueness, and floor-order laws. One shared
//! structurally recursive state computes total `Nat.div` and `Nat.mod`; its
//! projections use Lean's dividend-first argument order and zero-divisor values.
//! `div_mod_exec` proves those projections satisfy the relational specification
//! for every positive divisor, so its uniqueness, floor, congruence, and
//! divisibility laws apply to computation.
//! `Nat.gcd` then follows Lean's first-argument Euclidean recursion through the
//! generic checked `WellFounded.fix`; its recursive remainder is justified by
//! the checked `mod_lt` theorem, and `gcd_zero_left` / `gcd_succ` expose its
//! unfolding equations. `gcd_dvd`, `dvd_gcd`, and `dvd_gcd_iff` prove its full
//! common-divisor characterization over all naturals.
//! `Nat.bezout m n g := ∃ mp mn np nn, g + m*mn + n*nn = m*mp + n*np`
//! encodes signed coefficients as balanced natural parts. `gcd_bezout` proves
//! that relation for the executable gcd by the same checked Euclidean descent,
//! without importing the separate assumption-bearing integer prelude.
//! `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v` avoids signed subtraction;
//! reflexivity, symmetry, transitivity, and pairwise additive and multiplicative
//! closure are checked theorems.
//!
//! ## What is **not** here
//!
//! No `min` or decidability of order, no multiplicative divisibility
//! cancellation, Gauss lemma, or `n ≠ succ n`-style
//! discrimination.
//! Adding those is ordinary work on top of this prelude, not a kernel question:
//! the order fragment is deliberately minimal (see [`NatPrelude::le`]).
//!
//! ## Building proofs on top
//!
//! [`NatOps`] is the reusable proof-construction layer: `Eq` combinators
//! (`symm`, `trans`, `congr`, `chain`, `transport`, `eq_motive`), a `Nat.rec`
//! [`induct`](NatOps::induct) helper for `Prop`-valued motives, and the
//! [`define_binary`](NatOps::define_binary) /
//! [`theorem`](NatOps::theorem) declaration plumbing. Implement its two required
//! methods on your own development struct (so your own operators stay ordinary
//! methods and every closure keeps taking `&mut YourDev`), or use the ready-made
//! [`NatDev`] over a borrowed kernel.

// Proof scripts are long, straight-line term constructions with short
// mathematical names; splitting them would obscure the derivation they mirror.
// `type_complexity`: the higher-order declaration helpers take
// `&dyn Fn(&mut Self, …) -> …` builders; a type alias mentioning `Self` is not
// expressible, and naming them per-implementor would hide the signature.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::PreludeKey;
use crate::PreludeValue;
use crate::build_logic_prelude;
use crate::name::NameId;

mod add_basics;
mod add_choose_div;
mod add_desc_factorial_asc_factorial;
mod add_factorial_le;
mod add_factorial_lt;
mod add_pos;
mod algebra;
mod and_or_distrib;
mod asc_factorial;
mod asc_factorial_div;
mod base_induction;
mod bezout;
mod binary;
mod binary_rec;
mod binomial;
mod bit_decode;
mod bit_extra;
mod bit_order;
mod bits;
mod bitwise;
mod ble;
mod cantor;
mod cardinality;
mod catalan;
mod choose;
mod choose_factorial_add;
mod clog;
mod coprime_lemmas;
mod coprime_mul_add_mul_ne_mul;
mod count_range_permute;
mod count_range_reversal;
mod crt;
mod defs;
mod desc_factorial;
mod diagonal;
mod dist;
mod dist_more2;
mod div_mod_lemmas;
mod divisibility;
mod division;
mod draw11_mirrors;
mod dvd_add_iff_left;
mod dvd_mul_split;
mod euler;
mod even_add_family;
mod even_div;
mod factorization;
mod fermat;
mod fermat_number;
mod fermat_number_mirrors;
mod fermat_witness;
mod fibonacci;
mod finite;
mod finite_set;
mod gauss_lemma;
mod gcd;
mod gcd_dvd_mirrors;
mod gcd_mul_right;
mod gcd_mul_right_mirrors;
mod group;
mod helpers;
mod irrational;
mod land;
mod land_div_two;
mod land_low_bit;
mod land_self;
mod lcm;
mod lcm_gcd_lemmas;
mod ldiff;
mod least_number;
mod log;
mod log2;
mod log_clog_order;
mod lor;
mod min_fac;
mod mod_mul_lemmas;
mod modeq_add_cancel;
mod modeq_add_le_of_lt;
mod modeq_cancel_div_gcd;
mod modular;
mod mul_order_lemmas;
mod multichoose;
mod no_confusion;
mod nth;
mod nth_root;
mod ops;
mod order;
mod order_extra;
mod order_more;
mod parity;
mod parity_div;
mod perfect;
mod permutation;
mod pow_add_prime;
mod powsq;
mod prime_char;
mod prime_dvd_mirrors;
mod primes;
mod rec_agreement;
mod rectangle;
mod rel_prime;
mod relation;
mod restrict_pair;
mod size_extra;
mod sqrt;
mod squarefree;
mod subset_product;
mod testbit_bitwise;
mod totient;
mod totient_dvd_chain;
mod totient_gcd_mul;
mod totient_lemmas;
mod totient_mul;
mod totient_mul_coprime;
mod totient_multiplicative;
mod totient_prime_pow;
pub(crate) mod transposition;
mod vandermonde;
mod xor;
mod xor_algebra;
mod xor_order;
mod xor_parity;
mod xor_trichotomy;

pub use ops::{NatDev, NatOps, NatState};

use add_basics::declare_add_basics;
use add_choose_div::declare_add_choose;
use add_desc_factorial_asc_factorial::declare_add_desc_factorial_eq_asc_factorial;
use add_factorial_le::{
    declare_add_factorial_le_factorial_add, declare_add_factorial_succ_le_factorial_add_succ,
};
use add_factorial_lt::{
    declare_add_factorial_lt_factorial_add, declare_add_factorial_succ_lt_factorial_add_succ,
};
use add_pos::declare_add_pos;
use algebra::{
    declare_add_no_zero_summands, declare_additive_theorems, declare_finite_sum_theorems,
    declare_mul_no_zero_divisors, declare_multiplicative_theorems, declare_subtraction_theorems,
    declare_zero_or_succ,
};
use and_or_distrib::declare_and_or_distrib_all;
use asc_factorial::declare_asc_factorial_all;
use asc_factorial_div::declare_asc_factorial_eq_div;
use base_induction::declare_base_induction;
use bezout::{declare_euclid_lemma, declare_gcd_bezout, declare_prime_dvd_choose};
use binary::{declare_binary_all, declare_size_all, declare_zero_of_test_bit};
use binary_rec::declare_binary_rec_all;
use binomial::{
    declare_binomial_theorem, declare_combinatorial_identities, declare_succ_mul_choose_eq,
    declare_succ_sub_of_le,
};
use bit_decode::declare_bit_decode_all;
use bit_extra::declare_bit_extra_all;
use bit_order::declare_bit_order_all;
use bits::declare_bit_all;
use bitwise::{
    declare_bitwise_all, declare_bitwise_bit, declare_bitwise_comm, declare_bitwise_swap,
};
use ble::declare_boolean_le;
use cantor::declare_cantor_all;
use cardinality::declare_nat_pigeonhole;
use catalan::declare_catalan_all;
use choose::declare_choose_all;
use choose_factorial_add::declare_add_choose_mul_factorial_mul_factorial;
use clog::declare_clog_all;
use coprime_lemmas::declare_coprime_lemmas;
use coprime_mul_add_mul_ne_mul::declare_coprime_mul_add_mul_ne_mul;
use count_range_permute::{
    declare_count_range_congr_lt, declare_count_range_permute, declare_count_range_point_change,
    declare_count_range_product,
};
use count_range_reversal::declare_count_range_reversal_even;
use crt::declare_crt;
use defs::{
    declare_arithmetic, declare_boolean_equality, declare_defining_equations,
    declare_executable_division, declare_finite_ranges, declare_subtraction,
};
use desc_factorial::declare_desc_factorial_all;
use diagonal::declare_diagonal;
use dist::{declare_dist_all, declare_dist_more_all};
use dist_more2::declare_dist_more2_all;
use div_mod_lemmas::{
    declare_add_div_mod_shift_family, declare_add_div_of_dvd_add_add_one, declare_div_mod_block,
};
use divisibility::declare_factorial_order;
use divisibility::{declare_div_dvd_div_left, declare_divisibility};
use division::declare_euclidean_division;
use draw11_mirrors::declare_draw11_mirrors_all;
use dvd_add_iff_left::declare_dvd_add_iff_left;
use dvd_mul_split::declare_dvd_mul_split;
use euler::declare_mod_eq_cancel;
use even_add_family::declare_even_add_family_all;
use even_div::declare_even_div;
use factorization::{declare_exists_prime_factorization, declare_prod_range};
use fermat::declare_fermat;
use fermat_number::declare_fermat_number_all;
use fermat_number_mirrors::{declare_fermat_number_easy_all, declare_fermat_number_mirrors_all};
use fermat_witness::declare_fermat_witness_all;
use fibonacci::declare_fib_all;
use finite::{
    declare_fin, declare_injective_surjective, declare_pigeonhole, declare_restrict_injective,
    declare_restrict_maps_into, declare_succ_pred_of_pos,
};
use finite_set::declare_finite_set_all;
use gauss_lemma::declare_gauss_lemma_all;
use gcd::{declare_executable_gcd, declare_gcd_semantics, declare_modeq_gcd_eq};
use gcd_dvd_mirrors::declare_gcd_dvd_mirrors;
use gcd_mul_right::declare_gcd_mul_right;
use gcd_mul_right_mirrors::declare_gcd_mul_right_mirrors;
use group::declare_group_all;
use irrational::{declare_even_of_even_sq, declare_no_rational_sqrt_two};
use land::declare_land_all;
use land_div_two::declare_land_div_two_all;
use land_low_bit::declare_land_low_bit_all;
use land_self::declare_land_self_all;
use lcm::{
    declare_coprime_lcm_eq_mul, declare_dvd_antisymm, declare_gauss_lemma, declare_lcm,
    declare_lcm_comm, declare_lcm_dvd, declare_mod_lcm,
};
use lcm_gcd_lemmas::declare_lcm_gcd_lemmas;
use ldiff::declare_ldiff_all;
use least_number::declare_least_number_all;
use log::declare_log_all;
use log_clog_order::declare_log_clog_order_all;
use log2::declare_log2_all;
use lor::declare_lor_all;
use min_fac::{declare_min_fac_all, declare_min_fac_minimal_all};
use mod_mul_lemmas::declare_mod_mul_family;
use modeq_add_cancel::declare_mod_eq_add_cancel;
use modeq_add_le_of_lt::declare_mod_eq_add_le_of_lt;
use modeq_cancel_div_gcd::declare_modeq_cancel_div_gcd;
use modular::declare_modular_congruence;
use mul_order_lemmas::{
    declare_div_lt_of_lt_mul, declare_lt_of_mul_lt_mul, declare_mul_lt_mul_iff,
};
use multichoose::declare_multichoose_all;
use no_confusion::declare_no_confusion;
use nth::declare_nth_all;
use nth_root::declare_nth_root_all;
use order::declare_order;
use order_extra::declare_order_extra;
use order_more::declare_order_more;
use parity::declare_parity_all;
use parity_div::declare_even_add_one;
use parity_div::declare_parity_div_all;
use perfect::declare_perfect_all;
use perfect::declare_sum_divisors_two_pow;
use perfect::declare_sum_divisors_two_pow_eq_geom_sum;
use permutation::declare_permutation_all;
use pow_add_prime::declare_pow_add_prime_all;
use powsq::declare_powsq_all;
use prime_char::{
    declare_prime_mul_eq_prime_sq_iff, declare_prime_not_coprime_iff_dvd,
    declare_prime_not_prime_pow_all,
};
use prime_dvd_mirrors::declare_prime_dvd_mirrors_all;
use primes::{
    declare_coprime_add_self_left, declare_coprime_add_self_right, declare_coprime_odd_of_left,
    declare_coprime_odd_of_right, declare_coprime_of_dvd, declare_coprime_of_dvd_both,
    declare_coprime_of_forall_prime_dvd, declare_coprime_of_lt_prime, declare_coprime_one_iff,
    declare_coprime_or_dvd_of_prime, declare_coprime_primes, declare_coprime_self_add_left,
    declare_coprime_self_add_right, declare_coprime_symmetric, declare_coprime_two_left,
    declare_coprime_two_right, declare_dvd_lcm_of_dvd, declare_dvd_of_forall_prime_mul_dvd,
    declare_dvd_of_lcm_dvd, declare_euclid, declare_five_le_of_ne_two_of_ne_three,
    declare_not_coprime_zero_zero, declare_not_prime_of_dvd_of_ne,
    declare_prime_dvd_iff_not_coprime, declare_prime_dvd_mul_of_dvd_ne,
    declare_prime_dvd_of_dvd_pow, declare_prime_even_iff, declare_prime_not_dvd_mul,
    declare_prime_odd_of_ne_two, declare_prime_pred_pos, declare_primes, declare_succ_pred_prime,
};
use rec_agreement::{
    declare_land_assoc_all, declare_land_comm, declare_land_fuel_irrelevance_all,
    declare_land_le_left_all, declare_land_le_right_all, declare_land_zero_propagation_all,
    declare_ldiff_fuel_irrelevance_all, declare_lor_assoc_all,
    declare_lor_aux_ne_zero_of_right_ne_zero_all, declare_lor_comm,
    declare_lor_fuel_irrelevance_all, declare_rec_agreement_all,
};
use rectangle::declare_rectangle;
use rel_prime::{declare_coprime_iff_is_rel_prime, declare_is_rel_prime};
use relation::{
    declare_bijective_of_injective_on, declare_bijective_on, declare_comp,
    declare_eq_equivalence_on, declare_injective_on_comp, declare_mod_eq_equivalence_on,
    declare_relation_properties,
};
use restrict_pair::{
    declare_restrict_pair_injective, declare_restrict_pair_maps_into, declare_setwise_fixed,
};
use size_extra::declare_size_extra_all;
use sqrt::declare_sqrt_all;
use squarefree::declare_squarefree_all;
use subset_product::{declare_pigeonhole_p_all, declare_prod_range_if_all};
use testbit_bitwise::declare_testbit_bitwise_all;
use totient::declare_totient_all;
use totient_dvd_chain::declare_totient_dvd_chain_all;
use totient_gcd_mul::declare_totient_gcd_mul_all;
use totient_lemmas::{
    declare_odd_totient_iff, declare_odd_totient_iff_eq_one, declare_totient_coprime_totient_iff,
    declare_totient_even, declare_totient_lemmas_all,
};
use totient_mul::declare_totient_mul_all;
use totient_mul_coprime::{declare_coprime_mul_iff, declare_gcd_mod_left_eq_gcd};
use totient_multiplicative::{declare_coprime_mul_of_coprime, declare_gcd_comm};
use totient_prime_pow::declare_totient_prime_pow_all;
use transposition::{
    declare_conjugate_injective, declare_conjugate_maps_into, declare_transposition,
    declare_transposition_injective, declare_transposition_involutive,
    declare_transposition_maps_into,
};
use vandermonde::declare_vandermonde_all;
use xor::declare_xor_all;
use xor_algebra::declare_xor_algebra_all;
use xor_order::declare_xor_order_all;
use xor_parity::declare_xor_parity_all;
use xor_trichotomy::declare_xor_trichotomy_all;

/// The interned names produced by [`build_nat_prelude`]: the inductive `Nat`
/// and its constructors/recursor (re-exported from the [`LogicPrelude`] for
/// convenience), the arithmetic definitions, and every theorem name.
///
/// Handles belong to the kernel they were built in; do not mix them across
/// kernels. All fields are public so callers can build `Const` terms
/// (`k.const_(nat.add, vec![])`) directly.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatPrelude {
    /// The embedded logical prelude (`False`, `Not`, `Eq`, `Exists`, `Nat`, …).
    pub logic: LogicPrelude,

    // --- the inductive Nat (from the logic prelude) --------------------------
    /// `Nat : Type` — the inductive unary naturals.
    pub nat: NameId,
    /// `Nat.zero : Nat`.
    pub zero: NameId,
    /// `Nat.succ : Nat → Nat`.
    pub succ: NameId,
    /// `Nat.rec` — the generated, ι-computing recursor.
    pub rec: NameId,

    // --- definitions ---------------------------------------------------------
    /// `Nat.add : Nat → Nat → Nat`, by recursion on the second argument.
    pub add: NameId,
    /// `Nat.mul : Nat → Nat → Nat`, by recursion on the second argument.
    pub mul: NameId,
    /// `Nat.pow : Nat → Nat → Nat`, by recursion on the exponent.
    pub pow: NameId,
    /// Computational equality `Nat.beq : Nat → Nat → Bool`.
    pub beq: NameId,
    /// `Nat.beq_refl : ∀ n, Nat.beq n n = Bool.true`.
    pub beq_refl: NameId,
    /// `Nat.eq_of_beq_eq_true : ∀ a b, Nat.beq a b = true → a = b`.
    pub eq_of_beq_eq_true: NameId,
    /// `Nat.beq_eq_true_of_eq : ∀ a b, a = b → Nat.beq a b = true`.
    pub beq_eq_true_of_eq: NameId,
    /// `Nat.beq_eq_true_iff : ∀ a b, Nat.beq a b = true ↔ a = b`.
    pub beq_eq_true_iff: NameId,
    /// Shared executable division state `divModState d n : Bool → Nat`;
    /// `true` selects the quotient and `false` the remainder.
    pub div_mod_state: NameId,
    /// Total executable quotient `Nat.div dividend divisor`.
    pub div: NameId,
    /// Total executable remainder `Nat.mod dividend divisor`.
    pub mod_: NameId,
    /// Executable Euclidean greatest-common-divisor algorithm, recursing on its
    /// first argument through checked well-founded recursion.
    pub gcd: NameId,
    /// `Nat.sumRange : (Nat → Nat) → Nat → Nat`.
    pub sum_range: NameId,
    /// `Nat.factorial : Nat → Nat`, by structural recursion on its argument:
    /// `factorial zero ≡ 1` and `factorial (succ n) ≡ factorial n * succ n`
    /// hold **definitionally** (β/δ/ι), exactly as for [`pow`](Self::pow), so a
    /// proof can step through them without an explicit rewrite.
    ///
    /// The first half of Euclid's theorem (`F:nat-exists-prime-gt`): the number
    /// that every `d` with `1 ≤ d ≤ n` divides. See
    /// [`dvd_factorial_of_le`](Self::dvd_factorial_of_le).
    pub factorial: NameId,
    /// `Nat.descFactorial : Nat → Nat → Nat`, by structural recursion on its
    /// **second** argument via [`NatOps::define_binary`]:
    /// `descFactorial n zero ≡ 1` and
    /// `descFactorial n (succ k) ≡ (n - k) * descFactorial n k` hold
    /// **definitionally** (β/δ/ι), mirroring Mathlib's `Nat.descFactorial`.
    /// `n * (n-1) * … * (n-k+1)`, `k` factors of truncated `Nat.sub`. See
    /// [`desc_factorial_of_lt`](Self::desc_factorial_of_lt) for the
    /// truncation boundary.
    pub desc_factorial: NameId,
    /// `descFactorial_zero : ∀ n, n.descFactorial 0 = 1`.
    pub desc_factorial_zero: NameId,
    /// `descFactorial_succ : ∀ n k, n.descFactorial (succ k) = (n - k) * n.descFactorial k`.
    pub desc_factorial_succ: NameId,
    /// `descFactorial_one : ∀ n, n.descFactorial 1 = n`.
    pub desc_factorial_one: NameId,
    /// `descFactorial_of_lt : ∀ n k, n < k → n.descFactorial k = 0` — once
    /// `k` exceeds `n`, truncated `Nat.sub` forces a zero factor.
    pub desc_factorial_of_lt: NameId,
    /// `descFactorial_succ_eq_succ_mul : ∀ n k, (succ n).descFactorial (succ k)
    /// = succ n * n.descFactorial k` — the "front-peel" identity: peel the
    /// LARGEST factor (`succ n`) off the front of the product, leaving
    /// exactly `n.descFactorial k` (the same `k` factors, one row down).
    /// Proved by induction on `k` with `n` held fixed. The tool this bridge
    /// needs: [`Self::desc_factorial_succ`] (`desc_factorial.rs`'s own
    /// recursion) peels the SMALLEST factor off the BACK instead, so it
    /// cannot supply this directly.
    pub desc_factorial_succ_eq_succ_mul: NameId,
    /// `descFactorial_eq_factorial_mul_choose : ∀ n k, n.descFactorial k =
    /// k! * n.choose k` — the falling-factorial / binomial-coefficient
    /// bridge, closing `F:ml430-nat-factorial-dvd-descfactorial-bbf6124f`'s
    /// prerequisite. Proved by induction on `n`, `k` generalized inside the
    /// motive, chaining [`Self::desc_factorial_succ_eq_succ_mul`], the outer
    /// induction hypothesis, `mul_left_comm`, [`Self::succ_mul_choose_eq`],
    /// `mul_assoc`, and [`Self::factorial_succ`].
    pub desc_factorial_eq_factorial_mul_choose: NameId,
    /// `Nat.add_choose_mul_factorial_mul_factorial : ∀ i j, (i+j).choose j *
    /// i! * j! = (i+j)!`. See `nat_prelude::choose_factorial_add`.
    pub add_choose_mul_factorial_mul_factorial: NameId,
    /// `Nat.add_choose : ∀ i j, (i+j).choose j = (i+j)! / (i! * j!)`.
    /// Division-normal form of
    /// [`Self::add_choose_mul_factorial_mul_factorial`]. Closes
    /// `F:ml430-nat-add-choose-eb49fa11`. See `nat_prelude::add_choose_div`.
    pub add_choose: NameId,
    /// `factorial_dvd_descFactorial : ∀ n k, k! ∣ n.descFactorial k`.
    /// Closes `F:ml430-nat-factorial-dvd-descfactorial-bbf6124f`. Immediate
    /// from [`Self::desc_factorial_eq_factorial_mul_choose`] plus `dvd_mul`.
    pub factorial_dvd_desc_factorial: NameId,
    /// `descFactorial_self : ∀ n, n.descFactorial n = n.factorial`. Closes
    /// `F:ml430-nat-descfactorial-self-899fc0e0`. Immediate from
    /// [`Self::desc_factorial_eq_factorial_mul_choose`] at `k := n` plus
    /// [`Self::choose_self`] (`choose n n = 1`) and `mul_one`.
    pub desc_factorial_self: NameId,
    /// `descFactorial_le : ∀ n {k m}, k ≤ m → k.descFactorial n ≤
    /// m.descFactorial n` — monotone in the base for fixed exponent `n`.
    /// Closes `F:ml430-nat-descfactorial-le-2b8cc09a`. Route: rewrite both
    /// sides via [`Self::desc_factorial_eq_factorial_mul_choose`] to
    /// `n! * choose k n ≤ n! * choose m n`, closed by [`Self::choose_le_choose`]
    /// plus [`Self::mul_le_mul_left`].
    pub desc_factorial_le: NameId,
    /// `self_le_factorial : ∀ n, n ≤ n.factorial`. Closes
    /// `F:ml430-nat-self-le-factorial-cfdffc69`. Direct induction on `n`
    /// using [`Self::one_le_factorial`] (`1 ≤ n!`) to bound the step, not the
    /// `descFactorial`/`choose` bridge above.
    pub self_le_factorial: NameId,
    /// `Nat.ascFactorial : Nat → Nat → Nat`, by structural recursion on its
    /// **second** argument via [`NatOps::define_binary`], mirroring
    /// [`Self::desc_factorial`] but climbing with `Nat.add` instead of
    /// descending with truncated `Nat.sub`: `ascFactorial n zero ≡ 1` and
    /// `ascFactorial n (succ k) ≡ (n + k) * ascFactorial n k` hold
    /// **definitionally** (β/δ/ι), mirroring Mathlib's `Nat.ascFactorial`.
    /// `n * (n+1) * … * (n+k-1)`, `k` factors.
    pub asc_factorial: NameId,
    /// `ascFactorial_zero : ∀ n, n.ascFactorial 0 = 1`.
    pub asc_factorial_zero: NameId,
    /// `ascFactorial_succ : ∀ n k, n.ascFactorial (succ k) = (n + k) * n.ascFactorial k`.
    pub asc_factorial_succ: NameId,
    /// `ascFactorial_one : ∀ n, n.ascFactorial 1 = n`.
    pub asc_factorial_one: NameId,
    /// `zero_ascFactorial_succ : ∀ k, (0:Nat).ascFactorial (succ k) = 0` —
    /// the ascending analogue of `descFactorial_of_lt`'s boundary: the
    /// leading factor is `0` itself once there is at least one factor.
    pub zero_asc_factorial_succ: NameId,
    /// `ascFactorial_succ_eq_factorial_mul_choose : ∀ m k, (succ m).ascFactorial k
    /// = k! * (m + k).choose k` — the subtraction-free rising-factorial /
    /// binomial-coefficient bridge (reindexed by `n := succ m` so no
    /// `Nat.sub` — hence no truncation guard on `n ≥ 1` — is ever needed).
    /// Proved by induction on `k`, `m` held fixed. Same chain shape as
    /// [`Self::desc_factorial_eq_factorial_mul_choose`] plus two extra
    /// `succ_add`/`add_succ` index-alignment rewrites (the descending
    /// bridge's `n`/`k` shift in lockstep already; here `m+k`'s addend must
    /// be nudged to line up with `succ_mul_choose_eq`'s own shape).
    pub asc_factorial_succ_eq_factorial_mul_choose: NameId,
    /// `factorial_dvd_ascFactorial : ∀ n k, k! ∣ n.ascFactorial k`. Closes
    /// `F:ml430-nat-factorial-dvd-ascfactorial-44a4e641`. Case-splits `n`:
    /// `n = 0` via [`Self::zero_asc_factorial_succ`] + `dvd_zero` (`k = 0`
    /// needs only `dvd_refl`); `n = succ m` via
    /// [`Self::asc_factorial_succ_eq_factorial_mul_choose`] + `dvd_mul`.
    pub factorial_dvd_asc_factorial: NameId,
    /// `Nat.add_descFactorial_eq_ascFactorial : ∀ n k, (n+k).descFactorial k
    /// = (n+1).ascFactorial k`. Closes
    /// `F:ml430-nat-add-descfactorial-eq-ascfactorial-5faac784`. Two lemma
    /// applications chained through the shared RHS `k! * choose (n+k) k`
    /// (no induction). See `nat_prelude::add_desc_factorial_asc_factorial`.
    pub add_desc_factorial_eq_asc_factorial: NameId,
    /// `Nat.ascFactorial_eq_div : ∀ n k, (n+1).ascFactorial k = (n+k)! /
    /// n!`. Closes `F:ml430-nat-ascfactorial-eq-div-87d768e8`. See
    /// `nat_prelude::asc_factorial_div`.
    pub asc_factorial_eq_div: NameId,
    /// `Nat.multichoose n k` — the number of size-`k` multisets from an
    /// `n`-element type, defined directly as `choose (pred (add n k)) k`
    /// (i.e. `(n + k - 1).choose k`) rather than by a fresh recursion. See
    /// `nat_prelude/multichoose.rs`.
    pub multichoose: NameId,
    /// `multichoose_zero_right : ∀ n, n.multichoose 0 = 1`.
    pub multichoose_zero_right: NameId,
    /// `multichoose_one : ∀ k, Nat.multichoose 1 k = 1`.
    pub multichoose_one: NameId,
    /// `multichoose_one_right : ∀ n, n.multichoose 1 = n`.
    pub multichoose_one_right: NameId,
    /// `Nat.pred : Nat → Nat`, with `pred zero = zero`.
    pub pred: NameId,
    /// `Nat.sub : Nat → Nat → Nat`, truncated at zero and recursive in the
    /// second argument.
    pub sub: NameId,

    /// `Nat.noConfusionType : Sort u -> Nat -> Nat -> Sort u` — generated
    /// constructor disjointness/injectivity machinery (mirrors what Lean's
    /// elaborator synthesizes for every inductive).
    pub no_confusion_type: NameId,
    /// `Nat.noConfusion : Π (P:Sort u) (n1 n2:Nat), n1 = n2 -> noConfusionType P n1 n2`.
    pub no_confusion: NameId,
    /// `Nat.succ_ne_zero : ∀ n, Not (Eq Nat (succ n) zero)`, proved via `noConfusion`.
    pub succ_ne_zero: NameId,
    /// `Nat.not_lt_zero : ∀ n, Not (Lt n zero)`, proved via `noConfusion` (not a
    /// bespoke discriminator, unlike `not_succ_le_zero` above).
    pub not_lt_zero: NameId,
    /// `Nat.succ_pred_of_pos : ∀ n, Lt zero n → Eq n (succ (pred n))`, by
    /// induction on `n` (base case impossible via `not_lt_zero`; successor
    /// case is `refl`, since `pred (succ m)` reduces to `m` definitionally).
    /// The single declared home for a proof that used to be rebuilt privately
    /// in `finite.rs`, `fermat.rs`, and `totient.rs`.
    pub succ_pred_of_pos: NameId,

    // --- executable division equations -------------------------------------
    /// `div_zero : ∀ n, div n zero = zero`.
    pub div_zero: NameId,
    /// `mod_zero : ∀ n, mod n zero = n`.
    pub mod_zero: NameId,
    /// `zero_div : ∀ d, div zero d = zero`.
    pub zero_div: NameId,
    /// `zero_mod : ∀ d, mod zero d = zero`.
    pub zero_mod: NameId,
    /// Successor equation for executable quotient.
    pub div_succ: NameId,
    /// Successor equation for executable remainder.
    pub mod_succ: NameId,

    // --- defining equations (each proved by `Eq.refl`) -----------------------
    /// `add_zero : ∀ (n : Nat), Eq Nat (add n zero) n`.
    pub add_zero: NameId,
    /// `add_succ : ∀ (n m : Nat), Eq Nat (add n (succ m)) (succ (add n m))`.
    pub add_succ: NameId,
    /// `mul_zero : ∀ (n : Nat), Eq Nat (mul n zero) zero`.
    pub mul_zero: NameId,
    /// `mul_succ : ∀ (n m : Nat), Eq Nat (mul n (succ m)) (add (mul n m) n)`.
    pub mul_succ: NameId,
    /// `pow_zero : ∀ (n : Nat), Eq Nat (pow n zero) (succ zero)`.
    pub pow_zero: NameId,
    /// `pow_add : ∀ (a m n : Nat), Eq Nat (pow a (add m n)) (mul (pow a m) (pow a n))`.
    ///
    /// The exponent law. Closes fact `F:nat-pow-add`, whose `depends_on`
    /// (`F:nat-mul-assoc`, `F:nat-mul-comm`) were already settled — the ledger
    /// picked this goal, which is the self-extension loop working as designed.
    pub pow_add: NameId,
    /// `pow_succ : ∀ (n m : Nat), Eq Nat (pow n (succ m)) (mul (pow n m) n)`.
    pub pow_succ: NameId,
    /// `pred_zero : pred zero = zero`.
    pub pred_zero: NameId,
    /// `pred_succ : ∀ n, pred (succ n) = n`.
    pub pred_succ: NameId,
    /// `sub_zero : ∀ n, sub n zero = n`.
    pub sub_zero: NameId,
    /// `sub_succ : ∀ n m, sub n (succ m) = pred (sub n m)`.
    pub sub_succ: NameId,
    /// `succ_sub_succ : ∀ n m, sub (succ n) (succ m) = sub n m`.
    pub succ_sub_succ: NameId,
    /// `sub_self : ∀ n, sub n n = zero`.
    pub sub_self: NameId,
    /// `add_sub_cancel_left : ∀ m n, sub (add m n) m = n`.
    pub add_sub_cancel_left: NameId,
    /// `sumRange_zero : ∀ f, sumRange f zero = zero`.
    pub sum_range_zero: NameId,
    /// `sumRange_succ : ∀ f n, sumRange f (succ n) = sumRange f n + f n`.
    pub sum_range_succ: NameId,
    /// `sumRange_congr : (∀ i, f i = g i) → sumRange f n = sumRange g n`.
    pub sum_range_congr: NameId,
    /// `mul_sumRange : ∀ a f n, a * sumRange f n = sumRange (fun i => a * f i) n`.
    pub mul_sum_range: NameId,
    /// `mul_sumRange_pow : ∀ a n, a * sumRange (a^·) n = sumRange (a^(·+1)) n`.
    pub mul_sum_range_pow: NameId,
    /// `factorial_zero : factorial zero = succ zero`.
    pub factorial_zero: NameId,
    /// `factorial_succ : ∀ n, factorial (succ n) = factorial n * succ n`.
    pub factorial_succ: NameId,

    // --- additive theorems ---------------------------------------------------
    /// `zero_add : ∀ (n : Nat), Eq Nat (add zero n) n`.
    pub zero_add: NameId,
    /// `succ_add : ∀ (n m : Nat), Eq Nat (add (succ n) m) (succ (add n m))`.
    pub succ_add: NameId,
    /// `add_comm : ∀ (n m : Nat), Eq Nat (add n m) (add m n)`.
    pub add_comm: NameId,
    /// `add_assoc : ∀ (a b c : Nat), Eq Nat (add (add a b) c) (add a (add b c))`.
    pub add_assoc: NameId,
    /// `add_right_comm : ∀ (a b c : Nat), Eq Nat (add (add a b) c) (add (add a c) b)`.
    pub add_right_comm: NameId,
    /// `succ_injective : ∀ n m, succ n = succ m → n = m`.
    pub succ_injective: NameId,
    /// `add_right_cancel : ∀ n m k, n + k = m + k → n = m`.
    pub add_right_cancel: NameId,
    /// `add_left_cancel : ∀ a b c, a + b = a + c → b = c`.
    pub add_left_cancel: NameId,
    /// `add_add_add_comm : ∀ a b c d, add (add a b) (add c d) = add (add a c)
    /// (add b d)`. `F:ml430-nat-add-add-add-comm-74d2c151`.
    pub add_add_add_comm: NameId,
    /// `add_eq : ∀ x y, add x y = add x y` — this prelude has no separate `+`
    /// notation distinct from `Nat.add`, so Mathlib's `Nat.add_eq` (which
    /// bridges `Nat.add x y` and `x + y`) closes here by `Eq.refl` on the one
    /// function we have. `F:ml430-nat-add-eq-ab0eab69`.
    pub add_eq: NameId,
    /// `add_eq_left : ∀ a b, add a b = a ↔ b = 0`. `F:ml430-nat-add-eq-left-8e12789f`.
    pub add_eq_left: NameId,
    /// `add_eq_right : ∀ a b, add a b = b ↔ a = 0`. `F:ml430-nat-add-eq-right-9067eb1a`.
    pub add_eq_right: NameId,
    /// `add_eq_zero_iff : ∀ m n, add m n = 0 ↔ m = 0 ∧ n = 0` — the `Iff` form
    /// Mathlib states (`Nat.add_eq_zero_iff`); [`Self::add_eq_zero`] is the
    /// weaker mp-only arrow already declared for a different consumer, so this
    /// is a distinct name rather than a replacement.
    /// `F:ml430-nat-add-eq-64233539` (formal statement is the `Iff`).
    pub add_eq_zero_iff: NameId,
    /// `add_eq_one_iff : ∀ m n, add m n = 1 ↔ (m=0∧n=1) ∨ (m=1∧n=0)`.
    /// `F:ml430-nat-add-eq-one-iff-f8463abc`.
    pub add_eq_one_iff: NameId,
    /// `add_eq_two_iff : ∀ m n, add m n = 2 ↔ (m=0∧n=2)∨(m=1∧n=1)∨(m=2∧n=0)`.
    /// `F:ml430-nat-add-eq-two-iff-25385c65`.
    pub add_eq_two_iff: NameId,
    /// `add_eq_three_iff : ∀ m n, add m n = 3 ↔
    /// (m=0∧n=3)∨(m=1∧n=2)∨(m=2∧n=1)∨(m=3∧n=0)`.
    /// `F:ml430-nat-add-eq-three-iff-799a0a8f`.
    pub add_eq_three_iff: NameId,

    // --- multiplicative theorems --------------------------------------------
    /// `zero_mul : ∀ (n : Nat), Eq Nat (mul zero n) zero`.
    pub zero_mul: NameId,
    /// `succ_mul : ∀ (n m : Nat), Eq Nat (mul (succ n) m) (add (mul n m) m)`.
    pub succ_mul: NameId,
    /// `mul_comm : ∀ (n m : Nat), Eq Nat (mul n m) (mul m n)`.
    pub mul_comm: NameId,
    /// `left_distrib : ∀ (a b c : Nat), Eq Nat (mul a (add b c)) (add (mul a b) (mul a c))`.
    pub left_distrib: NameId,
    /// `right_distrib : ∀ (a b c : Nat), Eq Nat (mul (add a b) c) (add (mul a c) (mul b c))`.
    pub right_distrib: NameId,
    /// `mul_assoc : ∀ (a b c : Nat), Eq Nat (mul (mul a b) c) (mul a (mul b c))`.
    pub mul_assoc: NameId,
    /// `one_mul : ∀ (a : Nat), Eq Nat (mul (succ zero) a) a`.
    pub one_mul: NameId,
    /// `mul_one : ∀ (a : Nat), Eq Nat (mul a (succ zero)) a`.
    pub mul_one: NameId,

    // --- the order relation --------------------------------------------------
    /// `Nat.le : Nat → Nat → Prop` — an indexed inductive relation with the
    /// shape of Lean's own `Nat.le` (the first argument is a *parameter*, the
    /// second an *index*).
    ///
    /// This fragment is deliberately minimal: it carries reflexivity/step
    /// (the constructors), `zero_le`, successor monotonicity/inversion,
    /// transitivity, and `le_add_right` — enough to *state and derive* bounds,
    /// but **not** a complete order library. There is no antisymmetry, `min`,
    /// or decidability. The constructor shape matches Lean's,
    /// so those are extensions rather than redesigns.
    pub le: NameId,
    /// `Nat.lt n m := Nat.le (Nat.succ n) m`.
    pub lt: NameId,
    /// `Nat.inClosedInterval lower upper value := Le lower value ∧ Le value upper`.
    pub in_closed_interval: NameId,
    /// `Nat.le.refl : ∀ (n : Nat), Le n n`.
    pub le_refl: NameId,
    /// `Nat.le.step : ∀ (n m : Nat), Le n m → Le n (succ m)`.
    pub le_step: NameId,
    /// `Nat.le.rec` — the generated recursor (induction on the derivation).
    pub le_rec: NameId,
    /// `zero_le : ∀ (n : Nat), Le zero n`.
    pub zero_le: NameId,
    /// `le_succ_succ : ∀ (n m : Nat), Le n m → Le (succ n) (succ m)`.
    pub le_succ_succ: NameId,
    /// `le_of_succ_le_succ : ∀ (n m : Nat), Le (succ n) (succ m) → Le n m`.
    pub le_of_succ_le_succ: NameId,
    /// `le_trans : ∀ (a b c : Nat), Le a b → Le b c → Le a c`.
    pub le_trans: NameId,
    /// `Nat.monotone_of_le_succ : ∀ f, (∀ n, Le (f n) (f (succ n))) →
    /// ∀ a b, Le a b → Le (f a) (f b)`.
    pub monotone_of_le_succ: NameId,
    /// `lt_or_eq_of_le : ∀ a b, Le a b → Or (Lt a b) (Eq Nat a b)`.
    pub lt_or_eq_of_le: NameId,
    /// `lt_of_lt_of_le : ∀ a b c, Lt a b → Le b c → Lt a c`.
    pub lt_of_lt_of_le: NameId,
    /// `lt_of_le_of_lt : ∀ a b c, Le a b → Lt b c → Lt a c`.
    pub lt_of_le_of_lt: NameId,
    /// `lt_irrefl : ∀ a, Not (Lt a a)`.
    pub lt_irrefl: NameId,
    /// Reducible `lt_well_founded : WellFounded Nat.lt`.
    pub lt_well_founded: NameId,
    /// `le_total : ∀ a b, Or (Le a b) (Le b a)`.
    pub le_total: NameId,
    /// `not_succ_le_zero : ∀ n, Not (Le (succ n) zero)`.
    pub not_succ_le_zero: NameId,
    /// `le_antisymm : ∀ a b, Le a b → Le b a → Eq a b`.
    pub le_antisymm: NameId,
    /// `le_intro : ∀ a b k, a+k=b → Le a b`.
    pub le_intro: NameId,
    /// `le_dest : ∀ a b, Le a b → Exists (fun k => a+k=b)`.
    pub le_dest: NameId,
    /// `le_add_right : ∀ (n k : Nat), Le n (add n k)`.
    pub le_add_right: NameId,
    /// `add_le_add_left : ∀ c a b, Le a b → Le (c+a) (c+b)`.
    pub add_le_add_left: NameId,
    /// `add_lt_add_left : ∀ c a b, Lt a b → Lt (c+a) (c+b)`.
    pub add_lt_add_left: NameId,
    /// `add_le_add_right : ∀ c a b, Le a b → Le (a+c) (b+c)`.
    pub add_le_add_right: NameId,
    /// `le_of_add_le_add_left : ∀ c a b, Le (c+a) (c+b) → Le a b`.
    pub le_of_add_le_add_left: NameId,
    /// `le_of_add_le_add_right : ∀ c a b, Le (a+c) (b+c) → Le a b`.
    pub le_of_add_le_add_right: NameId,
    /// `mul_le_mul_left : ∀ c a b, Le a b → Le (c*a) (c*b)`.
    pub mul_le_mul_left: NameId,
    /// `mul_succ_add_lt_of_le_of_lt : ∀ n m i j, Le i m → Lt j (succ n) →
    /// Lt (add (mul (succ n) i) j) (mul (succ n) (succ m))` — the "flatten a
    /// row-major (block, offset) index" bound: a block index `i` capped at
    /// `m` and an in-block offset `j` capped below the block width `succ n`
    /// together stay strictly below the total count `(succ n)*(succ m)`.
    /// Needed by `CReal.riemannSum_cauchy`'s roadmap step 3 (out of scope
    /// here) to place a global fine index — `CReal.samplePoint_reblock`'s
    /// own `Nat.add (Nat.mul (Nat.succ n) i) j` — inside the `Nat.succ
    /// m_prime` bound `riemannSum_sample_in_bounds`/
    /// `subdivisionPoint_in_bounds` need, `Nat.succ m_prime` being `(Nat.succ
    /// n)*(Nat.succ m)` definitionally (`crate::creal::integral`'s private
    /// `succ_mul_succ`).
    pub mul_succ_add_lt_of_le_of_lt: NameId,
    /// `le_of_mul_le_mul_left_succ : ∀ c a b, Le ((succ c)*a) ((succ c)*b) → Le a b`.
    pub le_of_mul_le_mul_left_succ: NameId,
    /// `le_of_mul_le_mul_left : ∀ c a b, Le one c → Le (c*a) (c*b) → Le a b`.
    pub le_of_mul_le_mul_left: NameId,
    /// `mul_left_cancel_of_pos : ∀ c a b, Le one c → Eq (c*a) (c*b) → Eq a b`.
    pub mul_left_cancel_of_pos: NameId,
    /// `sub_add_cancel : ∀ m n, Le m n → add (sub n m) m = n`.
    pub sub_add_cancel: NameId,
    /// `sub_eq_zero_of_le : ∀ a b, Le a b → sub a b = zero`.
    pub sub_eq_zero_of_le: NameId,
    /// `sub_le_iff_le_add : ∀ x y z, Iff (Le (sub x y) z) (Le x (add z y))`.
    pub sub_le_iff_le_add: NameId,
    /// `mul_sub_left_distrib : ∀ b q a, Le a q → b*(q-a) = b*q-b*a`.
    pub mul_sub_left_distrib: NameId,
    /// Unconditional truncated distributivity `b*(q-a) = b*q-b*a`.
    pub mul_sub_left_distrib_total: NameId,

    // --- additional order/pred/sub lemmas (imported-corpus bridge names) ----
    // These are the exact Lean-core flat names a reconstructed corpus proof's
    // type closure resolves against; several are thin wrappers restating an
    // existing prelude fact (a constructor, or a differently-named theorem)
    // under its Lean-core name, proved independently from our own
    // definitions rather than aliased.
    /// `Nat.le_refl : ∀ (n : Nat), Le n n` — the flat top-level name matching
    /// [`le_refl`](Self::le_refl) (`Nat.le.refl`, the constructor).
    pub le_refl_thm: NameId,
    /// `Nat.le_succ : ∀ (n : Nat), Le n (succ n)`.
    pub le_succ: NameId,
    /// `Nat.succ_le_succ : ∀ (n m : Nat), Le n m → Le (succ n) (succ m)` — the
    /// Lean-core name matching [`le_succ_succ`](Self::le_succ_succ).
    pub succ_le_succ: NameId,
    /// `Nat.le_of_lt_succ : ∀ (n m : Nat), Lt n (succ m) → Le n m`.
    pub le_of_lt_succ: NameId,
    /// `Nat.lt_succ_self : ∀ (n : Nat), Lt n (succ n)`.
    pub lt_succ_self: NameId,
    /// `Nat.lt_succ_of_le : ∀ (n m : Nat), Le n m → Lt n (succ m)`.
    pub lt_succ_of_le: NameId,
    /// `Nat.lt_add_one : ∀ (n : Nat), Lt n (add n (succ zero))`.
    pub lt_add_one: NameId,
    /// `Nat.not_succ_le_self : ∀ (n : Nat), Not (Le (succ n) n)` — the
    /// Lean-core name matching [`lt_irrefl`](Self::lt_irrefl) unfolded at
    /// `Lt n n`.
    pub not_succ_le_self: NameId,
    /// `Nat.le_succ_of_le : ∀ (n m : Nat), Le n m → Le n (succ m)` — the
    /// Lean-core name matching the [`le_step`](Self::le_step) constructor.
    pub le_succ_of_le: NameId,
    /// `Nat.zero_lt_succ : ∀ (n : Nat), Lt zero (succ n)`.
    pub zero_lt_succ: NameId,
    /// `Nat.pred_le : ∀ (n : Nat), Le (pred n) n`.
    pub pred_le: NameId,
    /// `Nat.pred_le_pred : ∀ (n m : Nat), Le n m → Le (pred n) (pred m)`.
    pub pred_le_pred: NameId,
    /// `Nat.sub_le : ∀ (n m : Nat), Le (sub n m) n`.
    pub sub_le: NameId,
    /// `Nat.sub_lt : ∀ (n m : Nat), Lt zero n → Lt zero m → Lt (sub n m) n`.
    pub sub_lt: NameId,
    /// `Nat.succ_sub_succ_eq_sub : ∀ (n m : Nat), sub (succ n) (succ m) = sub n m`
    /// — the Lean-core name matching [`succ_sub_succ`](Self::succ_sub_succ).
    pub succ_sub_succ_eq_sub: NameId,

    // --- five more order/beq bridge lemmas (order_more.rs) ------------------
    /// `Nat.lt_of_not_le : ∀ (a b : Nat), Not (Le a b) → Lt b a` — the
    /// constructive trichotomy route (via the internal `le_or_gt` double
    /// induction, not excluded middle): `Nat.le` is decidable, so refuting
    /// `Le a b` picks out the other side of `Or (Le a b) (Lt b a)`.
    pub lt_of_not_le: NameId,
    /// `Nat.lt_or_ge : ∀ (a b : Nat), Or (Lt a b) (Le b a)` — `a ≥ b` unfolds
    /// to `Le b a` (this kernel has no separate `Nat.ge`).
    pub lt_or_ge: NameId,
    /// `Nat.le_of_lt_add_one : ∀ (a b : Nat), Lt a (add b (succ zero)) → Le a b`
    /// — `add b (succ zero)` is definitionally `succ b`, so this is
    /// [`le_of_lt_succ`](Self::le_of_lt_succ) restated at the `+1` spelling.
    pub le_of_lt_add_one: NameId,
    /// `Nat.zero_lt_of_ne_zero : ∀ (n : Nat), Not (Eq Nat n zero) → Lt zero n`.
    pub zero_lt_of_ne_zero: NameId,
    /// `Nat.ne_of_beq_eq_false : ∀ (a b : Nat), beq a b = Bool.false → Not (Eq Nat a b)`
    /// — bridges the boolean and propositional worlds via
    /// [`beq_eq_true_of_eq`](Self::beq_eq_true_of_eq) and the existing
    /// `Bool.false ≠ Bool.true` discriminator (`NatOps::false_true_elim`), so
    /// no new `Bool.noConfusion` machinery was needed for this one.
    pub ne_of_beq_eq_false: NameId,
    /// `Nat.add_pos_right : ∀ {b : Nat} (a : Nat), Lt zero b → Lt zero (add a b)`
    /// — Mathlib's `Int.add_pos_right`'s `Nat` sibling. A case split on `b`:
    /// at `zero` the hypothesis is impossible ([`not_lt_zero`](Self::not_lt_zero));
    /// at `succ k`, `add a (succ k)` is definitionally `succ (add a k)`, so
    /// the conclusion is [`NatOps::zero_lt_succ`](super::ops::NatOps::zero_lt_succ),
    /// independent of the hypothesis.
    pub add_pos_right: NameId,

    // --- boolean `≤`, bridging `Nat.ble` to `Nat.le` -------------------------
    /// `Nat.ble : Nat → Nat → Bool` — the executable analogue of [`beq`](Self::beq):
    /// `ble zero _ ≡ true`, `ble (succ _) zero ≡ false`,
    /// `ble (succ x) (succ y) ≡ ble x y`, all definitionally.
    pub ble: NameId,
    /// `Nat.ble_self_eq_true : ∀ (n : Nat), ble n n = true`.
    pub ble_self_eq_true: NameId,
    /// `Nat.ble_succ_eq_true : ∀ (n m : Nat), ble n m = true → ble n (succ m) = true`.
    pub ble_succ_eq_true: NameId,
    /// `Nat.ble_eq_true_of_le : ∀ (n m : Nat), Le n m → ble n m = true`.
    pub ble_eq_true_of_le: NameId,
    /// `Nat.le_of_ble_eq_true : ∀ (n m : Nat), ble n m = true → Le n m`.
    pub le_of_ble_eq_true: NameId,
    /// `Nat.not_le_of_not_ble_eq_true :
    ///   ∀ (n m : Nat), Not (ble n m = true) → Not (Le n m)`.
    pub not_le_of_not_ble_eq_true: NameId,

    // --- Euclidean division -------------------------------------------------
    /// `Nat.divMod d n q r := n = d*q+r ∧ r<d`.
    pub div_mod: NameId,
    /// `Nat.div_mod_exists : ∀ d n, Le one d → ∃ q r, divMod d n q r`.
    pub div_mod_exists: NameId,
    /// `Nat.div_mod_unique : divMod d n q₁ r₁ → divMod d n q₂ r₂ → q₁=q₂ ∧ r₁=r₂`.
    pub div_mod_unique: NameId,
    /// `Nat.div_mod_bounds : divMod d n q r → d*q ≤ n ∧ n < d*(succ q)`.
    pub div_mod_bounds: NameId,
    /// `Nat.div_mod_mul_le_iff : divMod d n q r → (d*s ≤ n ↔ s ≤ q)`.
    pub div_mod_mul_le_iff: NameId,
    /// `Nat.div_mod_lt_mul_iff : divMod d n q r → (n < d*s ↔ q < s)`.
    pub div_mod_lt_mul_iff: NameId,
    /// `Nat.div_mod_add_multiple :
    ///   divMod d n q r → divMod d (n+d*k) (q+k) r`.
    pub div_mod_add_multiple: NameId,

    // --- ml430 add/div/mod shift family (`div_mod_lemmas.rs`) ---------------
    /// `Nat.add_div_left : ∀ x {z}, 0 < z → (z+x)/z = x/z+1`.
    pub add_div_left: NameId,
    /// `Nat.add_div_right : ∀ x {z}, 0 < z → (x+z)/z = x/z+1`.
    pub add_div_right: NameId,
    /// `Nat.add_mod_left : ∀ x z, (x+z)%x = z%x`.
    pub add_mod_left: NameId,
    /// `Nat.add_mod_right : ∀ x z, (x+z)%z = x%z`.
    pub add_mod_right: NameId,
    /// `Nat.add_mul_div_left : ∀ x z {y}, 0 < y → (x+y*z)/y = x/y+z`.
    pub add_mul_div_left: NameId,
    /// `Nat.add_mul_div_right : ∀ x y {z}, 0 < z → (x+y*z)/z = x/z+y`.
    pub add_mul_div_right: NameId,
    /// `Nat.add_mul_mod_self_left : ∀ x y z, (x+y*z)%y = x%y`.
    pub add_mul_mod_self_left: NameId,
    /// `Nat.add_mul_mod_self_right : ∀ x y z, (x+y*z)%z = x%z`.
    pub add_mul_mod_self_right: NameId,
    /// `Nat.add_div_of_dvd_add_add_one :
    ///   ∀ {c a b}, c ∣ (a+b+1) → (a+b)/c = a/c + b/c`.
    pub add_div_of_dvd_add_add_one: NameId,
    /// `Nat.base_induction : {P : Nat -> Prop} {n : Nat} (b : Nat),
    ///   1 < b -> (∀ m, m < b -> P m) ->
    ///   (∀ m k, k < b -> 0 < m -> P m -> P (b*m+k)) -> P n`.
    pub base_induction: NameId,
    /// `Nat.mod_mul : ∀ {a b x}, x % (a*b) = x%a + a*(x/a % b)`. Closes
    /// `F:ml430-nat-mod-mul-beaccbad`.
    pub mod_mul: NameId,
    /// `Nat.mod_mul_left_mod : ∀ a b c, a % (b*c) % c = a % c`. Closes
    /// `F:ml430-nat-mod-mul-left-mod-9b785abc`.
    pub mod_mul_left_mod: NameId,
    /// `Nat.mod_mul_right_mod : ∀ a b c, a % (b*c) % b = a % b`. Closes
    /// `F:ml430-nat-mod-mul-right-mod-a481eff8`.
    pub mod_mul_right_mod: NameId,
    /// `Nat.mod_mul_left_div_self : ∀ m n k, m % (k*n) / n = m/n % k`. Closes
    /// `F:ml430-nat-mod-mul-left-div-self-0aca6c6e`.
    pub mod_mul_left_div_self: NameId,
    /// `Nat.mod_mul_right_div_self : ∀ m n k, m % (n*k) / n = m/n % k`. Closes
    /// `F:ml430-nat-mod-mul-right-div-self-900e0b01`.
    pub mod_mul_right_div_self: NameId,

    // --- divisibility -------------------------------------------------------
    /// `Nat.dvd : Nat → Nat → Prop`, where `dvd a n := ∃ q, n = a * q`.
    pub dvd: NameId,
    /// `Nat.div_mod_remainder_eq_zero_iff_dvd : divMod d n q r → (r=0 ↔ dvd d n)`.
    pub div_mod_remainder_eq_zero_iff_dvd: NameId,
    /// `Nat.div_mod_exact_exists : Le one d → dvd d n → ∃ q, divMod d n q zero`.
    pub div_mod_exact_exists: NameId,
    /// `Nat.mod_self : ∀ n, mod n n = zero`.
    pub mod_self: NameId,
    /// Executable quotient and remainder satisfy `divMod` at every successor divisor.
    pub div_mod_exec: NameId,
    /// `Nat.mod_lt : ∀ x y, 0 < y → mod x y < y`.
    pub mod_lt: NameId,
    /// `Nat.gcd_zero_left : ∀ n, gcd zero n = n`.
    pub gcd_zero_left: NameId,
    /// `Nat.gcd_succ : ∀ k n, gcd (succ k) n = gcd (mod n (succ k)) (succ k)`.
    pub gcd_succ: NameId,
    /// `Nat.gcd_dvd : ∀ m n, gcd m n | m ∧ gcd m n | n`.
    pub gcd_dvd: NameId,
    /// `Nat.gcd_dvd_left : ∀ m n, gcd m n | m`.
    pub gcd_dvd_left: NameId,
    /// `Nat.gcd_dvd_right : ∀ m n, gcd m n | n`.
    pub gcd_dvd_right: NameId,
    /// `Nat.dvd_gcd : k | m → k | n → k | gcd m n`.
    pub dvd_gcd: NameId,
    /// `Nat.dvd_gcd_iff : k | gcd m n ↔ k | m ∧ k | n`.
    pub dvd_gcd_iff: NameId,
    /// `Nat.gcd_mul_right : ∀ a b c, gcd (a*c) (b*c) = gcd a b * c` — the
    /// Euclidean algorithm's descent commutes with scaling both arguments by
    /// a common factor. Built by well-founded induction on the first
    /// argument mirroring `gcd`'s own recursion (`gcd_mul_right.rs`), using
    /// the scaling lemma `(n*c) % (m*c) = (n%m)*c` as the bridge between the
    /// unscaled and scaled Euclidean steps.
    pub gcd_mul_right: NameId,
    /// `Nat.dvd_gcd_mul_iff_dvd_mul : ∀ k n m, k ∣ gcd k n * m ↔ k ∣ n * m` —
    /// `F:ml430-nat-dvd-gcd-mul-iff-dvd-mul-0afe640a`
    /// (`gcd_mul_right_mirrors.rs`).
    pub dvd_gcd_mul_iff_dvd_mul: NameId,
    /// `Nat.dvd_gcd_mul_gcd_iff_dvd_mul : ∀ k n m, k ∣ (gcd k n) * (gcd k m)
    /// ↔ k ∣ n * m` — `F:ml430-nat-dvd-gcd-mul-gcd-iff-dvd-mul-07fec722`
    /// (`gcd_mul_right_mirrors.rs`).
    pub dvd_gcd_mul_gcd_iff_dvd_mul: NameId,
    /// `Nat.dvd_mul_gcd_iff_dvd_mul : ∀ k n m, k ∣ n * gcd k m ↔ k ∣ n * m` —
    /// `F:ml430-nat-dvd-mul-gcd-iff-dvd-mul-f9517e6b`
    /// (`gcd_mul_right_mirrors.rs`).
    pub dvd_mul_gcd_iff_dvd_mul: NameId,
    /// `Nat.ModEq.cancel_left_div_gcd : ∀ m a b c, 0 < m → c*a ≡ c*b [MOD m]
    /// → a ≡ b [MOD m / gcd m c]` — `F:ml430-nat-modeq-cancel-left-div-gcd-57ef8287`
    /// (`modeq_cancel_div_gcd.rs`).
    pub mod_eq_cancel_left_div_gcd: NameId,
    /// `Nat.ModEq.cancel_right_div_gcd : ∀ m a b c, 0 < m → a*c ≡ b*c [MOD m]
    /// → a ≡ b [MOD m / gcd m c]` — `F:ml430-nat-modeq-cancel-right-div-gcd-22a4f40d`
    /// (`modeq_cancel_div_gcd.rs`).
    pub mod_eq_cancel_right_div_gcd: NameId,
    /// `Nat.ModEq.cancel_left_div_gcd' : ∀ m a b c d, 0 < m → c ≡ d [MOD m] →
    /// c*a ≡ d*b [MOD m] → a ≡ b [MOD m / gcd m c]` —
    /// `F:ml430-nat-modeq-cancel-left-div-gcd-cfca1225`
    /// (`modeq_cancel_div_gcd.rs`). Rust name carries `_general` since
    /// identifiers cannot carry `'`.
    pub mod_eq_cancel_left_div_gcd_general: NameId,
    /// `Nat.lcm a b := div (mul a b) (gcd a b)` — the least common multiple.
    /// `lcm 0 0 = 0` matches Mathlib's convention: at that one degenerate point
    /// `gcd a b = 0` too, and `div _ 0 = 0`, so `lcm 0 0` computes to `0` and
    /// `gcd_mul_lcm` still holds there as `0 * 0 = 0 * 0`.
    pub lcm: NameId,
    /// `Nat.lcm_zero_left : ∀ b, lcm zero b = zero` — `zero_mul`/`zero_div`
    /// collapse the numerator without ever needing `gcd zero b`'s value.
    pub lcm_zero_left: NameId,
    /// `Nat.dvd_lcm_left : ∀ a b, dvd a (lcm a b)`.
    pub dvd_lcm_left: NameId,
    /// `Nat.dvd_lcm_right : ∀ a b, dvd b (lcm a b)`.
    pub dvd_lcm_right: NameId,
    /// `Nat.gcd_mul_lcm : ∀ a b, gcd a b * lcm a b = a * b` — the headline
    /// identity, unconditional (including at `a = b = 0`).
    pub gcd_mul_lcm: NameId,
    /// `Nat.gauss_lemma : ∀ x y z, gcd x y = 1 → x ∣ y*z → x ∣ z` — a
    /// coprime divisor of a product divides the other factor. Built from
    /// `gcd_bezout` by induction on `x`: `x = 0` forces `y = 1` via
    /// `gcd_zero_left`, and `x = succ k` scales the Bézout identity by `z`
    /// and cancels through `dvd_add_right_cancel_of_pos`, exactly the `g = 1`
    /// branch of `euclid_lemma` with the primality side condition dropped.
    pub gauss_lemma: NameId,
    /// `Nat.lcm_dvd : ∀ a b c, dvd a c → dvd b c → dvd (lcm a b) c` — the
    /// "least" half of the least common multiple's universal property.
    pub lcm_dvd: NameId,
    /// `Nat.dvd_antisymm : ∀ a b, dvd a b → dvd b a → Eq a b` — antisymmetry
    /// of divisibility. Conceptually belongs beside `dvd_gcd`/`dvd_gcd_iff`
    /// in `nat_prelude/divisibility.rs`; it lands in `nat_prelude/lcm.rs`
    /// instead (flagged for promotion) because it needs `le_of_dvd`
    /// (declared in `primes.rs`, after `lcm.rs` runs) and another lane held
    /// `divisibility.rs` when this was built. Double induction (`a` then
    /// `b`, both inner IHs unused — a case split, not real recursion):
    /// `a = 0` forces `b = 0` from `dvd 0 b` alone via `zero_mul`; at
    /// `a = succ k`, `b = 0` forces `a = 0` symmetrically from `dvd 0 a`
    /// (no absurdity lemma needed — it *is* the goal at that branch), and
    /// `b = succ j` closes via `le_of_dvd` in both directions plus
    /// `le_antisymm`.
    pub dvd_antisymm: NameId,
    /// `Nat.dvd_lcm_of_dvd_left : ∀ a b c, dvd a b → dvd a (lcm b c)` —
    /// `dvd_trans` through `dvd_lcm_left`.
    pub dvd_lcm_of_dvd_left: NameId,
    /// `Nat.dvd_lcm_of_dvd_right : ∀ a b c, dvd a b → dvd a (lcm c b)` —
    /// `dvd_trans` through `dvd_lcm_right`.
    pub dvd_lcm_of_dvd_right: NameId,
    /// `Nat.dvd_of_lcm_left_dvd : ∀ a b c, dvd (lcm a b) c → dvd b c` —
    /// `dvd_trans` through `dvd_lcm_right` (`b ∣ lcm a b`) composed with the
    /// hypothesis.
    pub dvd_of_lcm_left_dvd: NameId,
    /// `Nat.dvd_of_lcm_right_dvd : ∀ a b c, dvd (lcm a b) c → dvd a c` —
    /// `dvd_trans` through `dvd_lcm_left` (`a ∣ lcm a b`) composed with the
    /// hypothesis.
    pub dvd_of_lcm_right_dvd: NameId,

    // --- Catalan numbers (`catalan.rs`) --------------------------------------
    /// `Nat.catalan n := choose (n+n) n − choose (n+n) (n+1)` — the closed
    /// form. `Nat.sub` is TOTAL, so the definition needs no `≤` side
    /// condition; the recursive convolution form was priced and NOT built
    /// (it is course-of-values, so a curried accumulator does not reach it).
    pub catalan: NameId,
    /// `Nat.catalan_mul_succ : ∀ n, succ n · catalan n = choose (n+n) n` —
    /// the multiplicative identity tying `catalan` to `choose`, stated so no
    /// division is needed. Proved from two instances of
    /// `Nat.succ_mul_choose_eq` on the odd row `2n−1`, tied together by
    /// `Nat.choose_symm`; the truncated subtraction is handled by the
    /// UNCONDITIONAL `Nat.mul_sub_left_distrib_total`, so no `≤` proof is
    /// required anywhere.
    pub catalan_mul_succ: NameId,
    /// `Nat.lcm_comm : ∀ a b, lcm a b = lcm b a`. Direct from `dvd_antisymm`
    /// fed the two `lcm_dvd` applications (each built from
    /// `dvd_lcm_left`/`dvd_lcm_right` with the endpoints swapped).
    pub lcm_comm: NameId,
    /// `Nat.gcd_comm : ∀ a b, gcd a b = gcd b a`. Direct from `dvd_antisymm`,
    /// the identical shape to [`lcm_comm`](Self::lcm_comm): each of
    /// `gcd a b`/`gcd b a` divides the other via `dvd_gcd`, fed the matching
    /// `gcd_dvd_left`/`gcd_dvd_right` witnesses with the endpoints swapped.
    /// Filed in `totient_multiplicative.rs` rather than beside `lcm_comm`
    /// here — see that file's module doc for why.
    pub gcd_comm: NameId,
    /// `Nat.coprime_mul_of_coprime : ∀ x m n, Eq (gcd x m) one → Eq (gcd x n)
    /// one → Eq (gcd x (mul m n)) one` (Mathlib's `Nat.Coprime.mul_right`) —
    /// the coprimality-combine step `docs/plan/status/301-totient-
    /// multiplicative.md` flagged as one of the two weakest steps toward
    /// `totient(m*n) = totient(m)*totient(n)`. Route (b) from that doc:
    /// `coprime_of_forall_prime_dvd(x, mul m n, hyp)`, where `hyp` takes a
    /// prime `k` dividing both `x` and `mul m n` and derives `dvd k one` —
    /// `euclid_lemma` splits `dvd k (mul m n)` into `dvd k m ∨ dvd k n`, and
    /// each side combines with `dvd k x` via `dvd_gcd` into `dvd k (gcd x
    /// m)`/`dvd k (gcd x n)`, transported along the corresponding hypothesis
    /// to `dvd k one`. No Bézout-coefficient algebra (route (a) in that doc)
    /// was needed.
    pub coprime_mul_of_coprime: NameId,
    /// `Nat.gcd_mod_left_eq_gcd : ∀ x m, Eq (gcd (mod x m) m) (gcd x m)` --
    /// `docs/plan/status/301-totient-multiplicative.md`'s "Step 1"
    /// (mod-gcd invariance) toward `totient_mul_of_coprime`. Case split on
    /// `m`: `m = 0` closes by `mod_zero` plus congruence; `m = succ k`
    /// chains `gcd_succ` (`gcd m x = gcd (mod x m) m`) with `gcd_comm`
    /// (bridging `gcd m x` to `gcd x m`) via `symm`/`trans`. Filed in
    /// `totient_mul_coprime.rs` (see that module's doc).
    pub gcd_mod_left_eq_gcd: NameId,
    /// `Nat.coprime_mul_iff : ∀ x m n, Iff (Eq (gcd x (mul m n)) one) (And
    /// (Eq (gcd x m) one) (Eq (gcd x n) one))` -- `301`'s "Step 3" pointwise
    /// predicate identity (the `mod`-substituted form composes this with
    /// [`gcd_mod_left_eq_gcd`](Self::gcd_mod_left_eq_gcd) at the call site).
    /// No `Coprime m n` hypothesis needed: `mp` shrinks via
    /// `coprime_mul_right_right`/`coprime_mul_left_right`, `mpr` is
    /// `coprime_mul_of_coprime`. Filed in `totient_mul_coprime.rs`.
    pub coprime_mul_iff: NameId,
    /// `Nat.coprime_lcm_eq_mul : ∀ a b, gcd a b = 1 → lcm a b = a * b`. From
    /// the unconditional `gcd_mul_lcm`, substituting the coprimality
    /// hypothesis and cancelling the leading `1` with `one_mul`.
    pub coprime_lcm_eq_mul: NameId,
    /// `Nat.gcd_dvd_mul : ∀ m n, gcd m n ∣ m * n`. `gcd_dvd_left` composed
    /// with `dvd_mul_right_of_dvd`, no induction. Closes ledger fact
    /// `F:ml430-nat-gcd-dvd-mul`.
    pub gcd_dvd_mul: NameId,
    /// `Nat.gcd_le_mul : ∀ m n, 0 < m → 0 < n → gcd m n ≤ m * n`.
    /// `gcd_dvd_mul` plus `one_le_mul` (from the two positivity hypotheses)
    /// feeding `le_of_dvd`. Closes ledger fact `F:ml430-nat-gcd-le-mul`.
    pub gcd_le_mul: NameId,
    /// `Nat.eq_zero_of_lcm_eq_zero : ∀ m n, lcm m n = 0 → m = 0 ∨ n = 0`.
    /// `gcd_mul_lcm` transported along the hypothesis collapses `m * n` to
    /// `0`, and `mul_eq_zero` finishes. Closes ledger fact
    /// `F:ml430-nat-eq-zero-of-lcm-eq-zero`.
    pub eq_zero_of_lcm_eq_zero: NameId,
    /// `Nat.lcm_assoc : ∀ m n k, (lcm m n).lcm k = lcm m (lcm n k)`. Pure
    /// mutual-divisibility argument: both sides divide each other via
    /// `dvd_lcm_left`/`dvd_lcm_right`/`dvd_trans`/`lcm_dvd`, and
    /// `dvd_antisymm` closes it — no induction. Closes ledger fact
    /// `F:ml430-nat-lcm-assoc`.
    pub lcm_assoc: NameId,
    /// `Nat.lcm_div : ∀ m n k, dvd k m → dvd k n → lcm (m/k) (n/k) = lcm m n / k`.
    /// Induction on `k`: at `k = 0`, `div _ 0 = 0` on every term collapses
    /// both sides to `0` regardless of the hypotheses. At `k = succ k'`,
    /// write `m = k*m1`, `n = k*n1` (`dvd_elim` on the two hypotheses) and
    /// show `k * lcm m1 n1 = lcm m n` by mutual divisibility (the same
    /// `dvd_antisymm`-via-`lcm_dvd` technique as `lcm_assoc`, scaled by `k`
    /// through two small local cancellation helpers), then divide out `k`.
    /// Closes ledger fact `F:ml430-nat-lcm-div`.
    pub lcm_div: NameId,
    /// Balanced natural Bézout certificates:
    /// `bezout m n g := ∃ mp mn np nn, g + m*mn + n*nn = m*mp + n*np`.
    pub bezout: NameId,
    /// `Nat.gcd_bezout : ∀ m n, bezout m n (gcd m n)`.
    pub gcd_bezout: NameId,
    /// `Nat.modEq d a b := ∃ u v, a + d*u = b + d*v`.
    pub mod_eq: NameId,
    /// `Nat.mod_eq_refl : ∀ d a, modEq d a a`.
    pub mod_eq_refl: NameId,
    /// `Nat.mod_eq_symm : ∀ d a b, modEq d a b → modEq d b a`.
    pub mod_eq_symm: NameId,
    /// `Nat.mod_eq_trans : ∀ d a b c, modEq d a b → modEq d b c → modEq d a c`.
    pub mod_eq_trans: NameId,
    /// `Nat.mod_eq_add_left : ∀ d a b c, modEq d a b → modEq d (c+a) (c+b)`.
    pub mod_eq_add_left: NameId,
    /// `Nat.mod_eq_add_right : ∀ d a b c, modEq d a b → modEq d (a+c) (b+c)`.
    pub mod_eq_add_right: NameId,
    /// `Nat.mod_eq_add : modEq d a b → modEq d c e → modEq d (a+c) (b+e)`.
    pub mod_eq_add: NameId,
    /// `Nat.mod_eq_mul_left : ∀ d a b c, modEq d a b → modEq d (c*a) (c*b)`.
    pub mod_eq_mul_left: NameId,
    /// `Nat.mod_eq_mul_right : ∀ d a b c, modEq d a b → modEq d (a*c) (b*c)`.
    pub mod_eq_mul_right: NameId,
    /// `Nat.mod_eq_mul : modEq d a b → modEq d c e → modEq d (a*c) (b*e)`.
    pub mod_eq_mul: NameId,
    /// `Nat.div_mod_same_remainder_mod_eq :
    ///   divMod d a qa r → divMod d b qb r → modEq d a b`.
    pub div_mod_same_remainder_mod_eq: NameId,
    /// `Nat.div_mod_remainder_eq_of_mod_eq :
    ///   modEq d a b → divMod d a qa ra → divMod d b qb rb → ra = rb`.
    pub div_mod_remainder_eq_of_mod_eq: NameId,
    /// `Nat.mod_eq_iff_div_mod_remainder_eq :
    ///   divMod d a qa ra → divMod d b qb rb → (modEq d a b ↔ ra = rb)`.
    pub mod_eq_iff_div_mod_remainder_eq: NameId,
    /// `Nat.mod_eq_zero_of_dvd : dvd d n → modEq d n zero`.
    pub mod_eq_zero_of_dvd: NameId,
    /// `Nat.dvd_of_mod_eq_zero_of_pos :
    ///   Le one d → modEq d n zero → dvd d n`.
    pub dvd_of_mod_eq_zero_of_pos: NameId,
    /// `Nat.mod_eq_zero_iff_dvd : modEq d n zero ↔ dvd d n`.
    pub mod_eq_zero_iff_dvd: NameId,
    /// `Nat.mod_eq_cancel : ∀ n c a b, gcd c n = 1 → modEq n (c*a) (c*b) →
    /// modEq n a b`. Multiplicative cancellation modulo `n`: the engine
    /// behind Euler's theorem (`euler.rs`).
    pub mod_eq_cancel: NameId,
    /// `Nat.ModEq.gcd_eq : ∀ m a b, modEq m a b → gcd a m = gcd b m`. Closes
    /// ledger fact `F:ml430-nat-modeq-gcd-eq`.
    pub mod_eq_gcd_eq: NameId,
    /// `Nat.mod_eq_add_left_cancel : ∀ n a b c d, modEq n a b →
    /// modEq n (a+c) (b+d) → modEq n c d`. Closes
    /// `F:ml430-nat-modeq-add-left-cancel` (`modeq_add_cancel.rs`).
    pub mod_eq_add_left_cancel: NameId,
    /// `Nat.mod_eq_add_right_cancel : ∀ n a b c d, modEq n c d →
    /// modEq n (a+c) (b+d) → modEq n a b`. Closes
    /// `F:ml430-nat-modeq-add-right-cancel` (`modeq_add_cancel.rs`).
    pub mod_eq_add_right_cancel: NameId,
    /// `Nat.mod_eq_add_iff_left : ∀ n a b c d, modEq n a b →
    /// (modEq n (a+c) (b+d) ↔ modEq n c d)`. Closes
    /// `F:ml430-nat-modeq-add-iff-left` (`modeq_add_cancel.rs`).
    pub mod_eq_add_iff_left: NameId,
    /// `Nat.mod_eq_add_iff_right : ∀ n a b c d, modEq n c d →
    /// (modEq n (a+c) (b+d) ↔ modEq n a b)`. Closes
    /// `F:ml430-nat-modeq-add-iff-right` (`modeq_add_cancel.rs`).
    pub mod_eq_add_iff_right: NameId,
    /// `Nat.mod_eq_cancel_left : ∀ m a b c, gcd m c = 1 →
    /// modEq m (c*a) (c*b) → modEq m a b`. Same content as `mod_eq_cancel`
    /// with the coprimality hypothesis's `gcd` argument order flipped via
    /// `gcd_comm`. Closes `F:ml430-nat-modeq-cancel-left-of-coprime`
    /// (`modeq_add_cancel.rs`).
    pub mod_eq_cancel_left: NameId,
    /// `Nat.mod_eq_add_le_of_lt : ∀ m a b, modEq m a b → a < b → a + m ≤ b`.
    /// Closes `F:ml430-nat-modeq-add-le-of-lt-c774015b` (`modeq_add_le_of_lt.rs`).
    pub mod_eq_add_le_of_lt: NameId,
    /// `Nat.valuationAt a n e := dvd (a^e) n ∧ Not (dvd (a^(e+1)) n)`.
    pub valuation_at: NameId,
    /// `Nat.dvd_mul : ∀ a q, dvd a (a * q)`.
    pub dvd_mul: NameId,
    /// `Nat.dvd_refl : ∀ a, dvd a a`.
    pub dvd_refl: NameId,
    /// `Nat.dvd_zero : ∀ a, dvd a zero`.
    pub dvd_zero: NameId,
    /// `Nat.dvd_trans : ∀ a b c, dvd a b → dvd b c → dvd a c`.
    pub dvd_trans: NameId,
    /// `Nat.dvd_mul_right_of_dvd : dvd a b → dvd a (b*c)`.
    pub dvd_mul_right_of_dvd: NameId,
    /// `Nat.dvd_add_iff_right : dvd k m → (dvd k n ↔ dvd k (m+n))`.
    pub dvd_add_iff_right: NameId,
    /// Positive-divisor executable remainder preserves divisibility.
    pub dvd_mod_iff: NameId,
    /// `Nat.dvd_add : ∀ a m n, dvd a m → dvd a n → dvd a (m + n)`.
    pub dvd_add: NameId,
    /// `Nat.dvd_add_right_cancel_of_pos : ∀ a m n, Le one a → dvd a m → dvd a (m+n) → dvd a n`.
    pub dvd_add_right_cancel_of_pos: NameId,
    /// `Nat.euclid_lemma : ∀ p a b, prime p → p ∣ a*b → p ∣ a ∨ p ∣ b`.
    ///
    /// Primality is spelled out inline as `2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`
    /// rather than through a `Prime` predicate, because that is the shape the
    /// ledger's `F:nat-euclid-lemma` states and a fact is only closed by the
    /// statement it actually makes.
    pub euclid_lemma: NameId,
    // --- `prime_dvd_mirrors.rs`: the small consequences of `prime_condition`'s
    // own clause, plus the `Coprime <-> not dvd` bridge -------------------
    /// `Nat.prime_one_lt : ∀ p, prime_condition p → Lt one p`.
    pub prime_one_lt: NameId,
    /// `Nat.prime_one_le : ∀ p, prime_condition p → Le one p`.
    pub prime_one_le: NameId,
    /// `Nat.prime_pos : ∀ p, prime_condition p → Lt zero p`.
    pub prime_pos: NameId,
    /// `Nat.prime_ne_one : ∀ p, prime_condition p → Not (Eq p one)`.
    pub prime_ne_one: NameId,
    /// `Nat.prime_ne_zero : ∀ p, prime_condition p → Not (Eq p zero)`.
    pub prime_ne_zero: NameId,
    /// `Nat.prime_not_dvd_one : ∀ p, prime_condition p → Not (dvd p one)`.
    pub prime_not_dvd_one: NameId,
    /// `Nat.prime_eq_one_or_self_of_dvd : ∀ p m, prime_condition p → dvd m p
    /// → Or (Eq m one) (Eq m p)` — the divisor clause of `prime_condition`
    /// applied at `m`, named.
    pub prime_eq_one_or_self_of_dvd: NameId,
    /// `Nat.prime_dvd_iff_eq : ∀ p a, prime_condition p → Not (Eq a one) →
    /// Iff (dvd a p) (Eq p a)`.
    pub prime_dvd_iff_eq: NameId,
    /// `Nat.prime_dvd_mul_iff : ∀ p m n, prime_condition p → Iff (dvd p (mul
    /// m n)) (Or (dvd p m) (dvd p n))` — `euclid_lemma` plus
    /// `dvd_mul_right_of_dvd`/`dvd_mul_left_of_dvd`.
    pub prime_dvd_mul_iff: NameId,
    /// `Nat.prime_coprime_iff_not_dvd : ∀ p n, prime_condition p → Iff (Eq
    /// (gcd p n) one) (Not (dvd p n))`.
    pub prime_coprime_iff_not_dvd: NameId,
    /// `Nat.prime_eq_two_or_odd : ∀ p, prime_condition p → Or (Eq p two)
    /// (Odd p)`.
    pub prime_eq_two_or_odd: NameId,
    /// `Nat.prime_eq_two_or_mod_two_eq_one : ∀ p, prime_condition p → Or (Eq
    /// p two) (Eq (mod p two) one)`.
    pub prime_eq_two_or_mod_two_eq_one: NameId,
    /// `Nat.prime_mod_two_eq_one_iff_ne_two : ∀ p, prime_condition p → Iff
    /// (Eq (mod p two) one) (Not (Eq p two))`.
    pub prime_mod_two_eq_one_iff_ne_two: NameId,
    /// `Nat.prime_coprime_pow_of_not_dvd : ∀ p m a, prime_condition p → Not
    /// (dvd p a) → Eq (gcd a (pow p m)) one` — induction on `m` via
    /// `coprime_mul_of_coprime`.
    pub prime_coprime_pow_of_not_dvd: NameId,
    /// `Nat.prime_dvd_choose : ∀ p k, prime p → 0 < k → k < p → p ∣ choose p
    /// k` — a live lane's blocker on the way to Fermat's little theorem.
    /// Primality is spelled inline, matching `euclid_lemma`'s own convention.
    /// From `euclid_lemma` plus `succ_mul_choose_eq`: the absorption identity
    /// gives `k * choose p k = p * choose (p-1) (k-1)`, so `p ∣ k * choose p
    /// k`; `euclid_lemma` splits that into `p ∣ k ∨ p ∣ choose p k`, and
    /// `0 < k < p` rules out the first disjunct (`le_of_dvd` would force
    /// `p ≤ k`).
    pub prime_dvd_choose: NameId,
    /// `Nat.one_le_factorial : ∀ n, Le one (factorial n)`.
    pub one_le_factorial: NameId,
    /// `Nat.exists_prime_gt : ∀ n, ∃ p, n < p ∧ (2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p)`.
    ///
    /// Euclid's theorem. Closes ledger fact `F:nat-exists-prime-gt`, whose two
    /// dependencies (`F:nat-dvd-add`, `F:nat-exists-prime-dvd`) are settled.
    pub exists_prime_gt: NameId,
    /// `Nat.not_dvd_one_of_two_le : ∀ a, Le two a → Not (dvd a one)`.
    pub not_dvd_one_of_two_le: NameId,
    /// `Nat.eq_one_of_dvd_one : ∀ d, dvd d one → Eq d one` — the closing step
    /// for coprimality after dividing by a gcd.
    pub eq_one_of_dvd_one: NameId,
    /// `Nat.coprime_of_bezout_one : ∀ a b, bezout a b 1 → Eq (gcd a b) 1` — a
    /// Bézout identity with coefficient `1` *is* coprimality.
    pub coprime_of_bezout_one: NameId,
    /// `Nat.bezout_of_scaled : ∀ g a b, 1 ≤ g → bezout (g*a) (g*b) g →
    /// bezout a b 1` — divide a Bézout identity through by its coefficient.
    pub bezout_of_scaled: NameId,
    /// `Nat.gcd_cofactors_coprime : ∀ g a b, 1 ≤ g → gcd (g*a) (g*b) = g →
    /// gcd a b = 1` — the cofactors of a gcd are coprime.
    pub gcd_cofactors_coprime: NameId,
    /// `Nat.div_mul_cancel_of_dvd : ∀ g n, 1 ≤ g → dvd g n → g * (n / g) = n` —
    /// exact division recovers its dividend.
    pub div_mul_cancel_of_dvd: NameId,
    /// `Nat.div_dvd_div_left : ∀ n m k, dvd m k → dvd n m → dvd (k/m) (k/n)`.
    /// Closes ledger fact `F:ml430-nat-div-dvd-div-left`.
    pub div_dvd_div_left: NameId,
    /// `Nat.one_le_right_of_mul : ∀ g q, 1 ≤ g * q → 1 ≤ q`.
    pub one_le_right_of_mul: NameId,
    /// `Nat.one_le_left_of_mul : ∀ g q, 1 ≤ g * q → 1 ≤ g`.
    pub one_le_left_of_mul: NameId,
    /// `Nat.one_le_of_dvd_pos : ∀ g n, 1 ≤ n → dvd g n → 1 ≤ g` — a divisor of a
    /// positive number is positive.
    pub one_le_of_dvd_pos: NameId,
    /// `Nat.one_le_mul : ∀ a b, 1 ≤ a → 1 ≤ b → 1 ≤ a * b`.
    pub one_le_mul: NameId,
    /// `Nat.mul_eq_zero : ∀ a b, a * b = 0 → a = 0 ∨ b = 0` — `ℕ` has no zero
    /// divisors. Proved by a constructor case-split on both factors (not
    /// induction): `a = 0` or `b = 0` are immediate, and `a = succ x`,
    /// `b = succ y` makes the product `succ_mul` + `add_succ` away from a bare
    /// successor, which `succ_ne_zero` refutes against the hypothesis.
    pub mul_eq_zero: NameId,
    /// `Nat.add_eq_zero : ∀ a b, a + b = 0 → a = 0 ∧ b = 0`. `Nat.add`
    /// recurses on its RIGHT argument, so this is a single `cases_zero_succ`
    /// on `b` (not a nested double case-split like `mul_eq_zero`): at
    /// `b = 0`, `add a 0` is defeq to `a`, so the hypothesis itself already
    /// has the shape `a = 0`; at `b = succ y`, `add a (succ y)` is defeq to
    /// `succ (add a y)`, which `succ_ne_zero` refutes against the hypothesis.
    /// Built for `nat-assoc-dichotomy`'s `land_aux_assoc_of_fuel` attempt
    /// (`docs/plan/status/247-nat-bitwise-assoc.md`'s item 1): the per-bit
    /// successor row is `2 * rec + bit`, and deciding whether that compound
    /// value is zero needs `2 * rec = 0 ∧ bit = 0` from `add_eq_zero`, then
    /// `rec = 0` from the existing `mul_eq_zero` (eliminating the `2 = 0`
    /// disjunct via `succ_ne_zero`, no new `mul`-side lemma needed).
    pub add_eq_zero: NameId,
    /// `Nat.zero_or_succ : ∀ n, n = 0 ∨ ∃ p, n = succ p` — every `Nat` is
    /// either `0` or a successor, stated as an equational dichotomy (rather
    /// than [`super::ops::cases_zero_succ`]'s raw elimination) so it can be
    /// applied via `d.lemma` at an ARBITRARY compound term (not just a bound
    /// variable in the caller's own goal): the caller gets back a genuine
    /// `Or`-typed FACT naming that term, usable with `or_elim` without the
    /// caller's motive ever needing to fold the term's internal structure
    /// into a `Nat.rec` motive. Built for `nat-assoc-dichotomy`'s
    /// `land_aux_assoc_of_fuel` attempt (`docs/plan/status/247-nat-bitwise-assoc.md`
    /// item 2): the successor row's nested value `X := landAux fuel a b` is a
    /// compound arithmetic expression appearing in an ARGUMENT position, and
    /// deciding whether it is zero needs exactly this — a proof that `X = 0`
    /// or `X = succ p` for SOME `p` — without disturbing `X`'s own formula
    /// (`2 * rec + bit`), which a direct `Nat.rec` elimination on `X` inside
    /// the goal's own motive would discard.
    pub zero_or_succ: NameId,
    /// `Nat.dvd_factorial_of_le : ∀ d n, Le 1 d → Le d n → dvd d (factorial n)`.
    ///
    /// Every positive number at most `n` divides `n!`. This is the first of the
    /// two ingredients Euclid's theorem (`F:nat-exists-prime-gt`) needs — the
    /// number divisible by everything in range — and it is what makes
    /// `1 + n!` have no divisor in `[2, n]`. The other ingredient, "every
    /// `m ≥ 2` has a prime divisor", is
    /// [`exists_prime_dvd`](Self::exists_prime_dvd).
    pub dvd_factorial_of_le: NameId,
    /// `Nat.factorial_dvd_factorial : ∀ m n, Le m n → dvd (factorial m) (factorial n)`.
    ///
    /// Induction on `n` with the order hypothesis inside the motive, mirroring
    /// [`dvd_factorial_of_le`](Self::dvd_factorial_of_le)'s `at_succ` case
    /// verbatim (it never used the divisor-positivity fact). The `n = 0` base
    /// case differs: without a fixed `1 ≤ m` to contradict `m ≤ 0`, it
    /// case-splits on `m` itself (`m = 0` via [`dvd_refl`](Self::dvd_refl),
    /// `m = succ _` refuted by [`not_succ_le_zero`](Self::not_succ_le_zero)).
    pub factorial_dvd_factorial: NameId,
    /// `Nat.factorial_le : ∀ m n, Le m n → Le (factorial m) (factorial n)`, via
    /// [`factorial_dvd_factorial`](Self::factorial_dvd_factorial) and
    /// [`le_of_dvd`](Self::le_of_dvd) against the positivity of `factorial n`
    /// ([`one_le_factorial`](Self::one_le_factorial)).
    pub factorial_le: NameId,
    /// `Nat.factorial_lt_of_lt : ∀ m n, Lt zero n → Lt n m → Lt (factorial n) (factorial m)`.
    ///
    /// `n! < (succ n)! ≤ m!`: the first step needs `factorial n * n ≥ 1`
    /// ([`one_le_mul`](Self::one_le_mul) against `0 < n`) to make the
    /// `mul_succ` expansion of `(succ n)!` strictly exceed `factorial n`
    /// ([`add_lt_add_left`](Self::add_lt_add_left)), the second is
    /// [`factorial_le`](Self::factorial_le) at `succ n ≤ m`, and
    /// [`lt_of_lt_of_le`](Self::lt_of_lt_of_le) chains them.
    pub factorial_lt_of_lt: NameId,
    /// `Nat.factorial_ne_zero : ∀ n, Not (Eq (factorial n) zero)`, via
    /// [`one_le_factorial`](Self::one_le_factorial) transported along a
    /// hypothetical `factorial n = zero` into `Le 1 zero`, refuted by
    /// [`not_succ_le_zero`](Self::not_succ_le_zero).
    pub factorial_ne_zero: NameId,
    /// `Nat.add_factorial_le_factorial_add : ∀ i n, Le 1 n → Le (i + n!)
    /// ((i+n)!)`. Closes
    /// `F:ml430-nat-add-factorial-le-factorial-add-b0400cf6`. See
    /// `nat_prelude::add_factorial_le`.
    pub add_factorial_le_factorial_add: NameId,
    /// `Nat.add_factorial_succ_le_factorial_add_succ : ∀ i n, Le (i +
    /// (succ n)!) ((i + succ n)!)`. Closes
    /// `F:ml430-nat-add-factorial-succ-le-factorial-add-succ-e8145feb`.
    /// Corollary of [`Self::add_factorial_le_factorial_add`].
    pub add_factorial_succ_le_factorial_add_succ: NameId,
    /// `Nat.add_factorial_lt_factorial_add : ∀ i n, Le 2 i → Le 1 n → Lt (i +
    /// n!) ((i+n)!)`. Closes
    /// `F:ml430-nat-add-factorial-lt-factorial-add-7501a8c8`. See
    /// `nat_prelude::add_factorial_lt`.
    pub add_factorial_lt_factorial_add: NameId,
    /// `Nat.add_factorial_succ_lt_factorial_add_succ : ∀ i n, Le 2 i → Lt (i
    /// + (n+1)!) ((i+n+1)!)`. Closes
    /// `F:ml430-nat-add-factorial-succ-lt-factorial-add-succ-ec0fa8d3`.
    /// Corollary of [`Self::add_factorial_lt_factorial_add`].
    pub add_factorial_succ_lt_factorial_add_succ: NameId,
    /// `Nat.not_dvd_one_add_mul_of_two_le : ∀ a t, Le two a → Not (dvd a (one+a*t))`.
    pub not_dvd_one_add_mul_of_two_le: NameId,
    /// `Nat.valuation_at_two_mul_sq : ∀ a u, Le two a → Not (dvd a u) → valuationAt a ((a*a)*u) two`.
    pub valuation_at_two_mul_sq: NameId,
    /// `Nat.le_of_dvd : ∀ a n, Le 1 n → dvd a n → Le a n`.
    ///
    /// A divisor of a **positive** number is bounded by it. The positivity
    /// hypothesis is load-bearing: `2 ∣ 0` and `2 ≤ 0` is false.
    pub le_of_dvd: NameId,
    /// `Nat.two_le_succ_or_eq_one : ∀ j, Or (Le two (succ j)) (Eq (succ j) one)`.
    ///
    /// The only successor below `2` is `1` — the dichotomy the least-divisor
    /// search needs before it may offer `succ j` as a candidate divisor.
    pub two_le_succ_or_eq_one: NameId,
    /// `Nat.least_divisor_search : ∀ k m, Or (∃ x, Le two x ∧ (dvd x m ∧ ∀ e, Le two e → Lt e x → Not (dvd e m))) (∀ c, Le two c → Le c k → Not (dvd c m))`.
    ///
    /// Bounded search for the **least** divisor `≥ 2` of `m`, by ordinary
    /// `Nat.rec` on the bound `k`. Constructive: each step decides `succ j ∣ m`
    /// by reducing `beq (mod m (succ j)) 0`, with the two branches separated by
    /// [`div_mod_remainder_eq_zero_iff_dvd`](Self::div_mod_remainder_eq_zero_iff_dvd).
    pub least_divisor_search: NameId,
    /// `Nat.exists_prime_dvd : ∀ m, Le two m → ∃ p, (Le two p ∧ ∀ d, dvd d p → Or (Eq d one) (Eq d p)) ∧ dvd p m`.
    ///
    /// Every `m ≥ 2` has a prime divisor — the second of the two ingredients
    /// Euclid's theorem (`F:nat-exists-prime-gt`) needs, the first being
    /// [`dvd_factorial_of_le`](Self::dvd_factorial_of_le). Primality is spelled
    /// inline because the prelude has no `Prime` predicate. The prime is the
    /// least divisor `≥ 2` supplied by
    /// [`least_divisor_search`](Self::least_divisor_search); minimality is
    /// exactly what makes it prime.
    pub exists_prime_dvd: NameId,
    /// `Nat.coprime_of_lt_prime : ∀ p a, (Le two p ∧ ∀ d, dvd d p → Or (Eq d one) (Eq d p)) → Lt zero a → Lt a p → Eq (gcd a p) one`.
    ///
    /// Every nonzero residue below a prime is invertible modulo it — the fact
    /// that makes ℤ/p a field, proved here as: `gcd a p` divides `p`, so
    /// primality forces it to be `1` or `p`; it also divides `a`, and `a < p`
    /// rules out `p` (`le_of_dvd` would force `p ≤ a`, contradicting `a < p`
    /// via `lt_of_le_of_lt`/`lt_irrefl`), so it is `1`.
    pub coprime_of_lt_prime: NameId,
    /// `Nat.coprime_of_dvd_left : ∀ a1 a2 b, dvd a1 a2 → Eq (gcd a2 b) one →
    /// Eq (gcd a1 b) one`.
    ///
    /// Coprimality descends along a left divisor. `gcd a1 b` divides `a1`
    /// (`gcd_dvd_left`), which divides `a2` (`dvd_trans` with the
    /// hypothesis), and it divides `b` (`gcd_dvd_right`); `dvd_gcd` combines
    /// those two into `gcd a1 b ∣ gcd a2 b`, which is `1` by hypothesis, so
    /// `gcd a1 b ∣ 1` and `eq_one_of_dvd_one` closes it. Mirrors
    /// `Nat.Coprime.of_dvd_left`; `Coprime` has no separate name here,
    /// matching `coprime_of_lt_prime`'s convention.
    pub coprime_of_dvd_left: NameId,
    /// `Nat.coprime_of_dvd_right : ∀ a b1 b2, dvd b1 b2 → Eq (gcd a b2) one →
    /// Eq (gcd a b1) one` — the right-hand mirror of
    /// [`coprime_of_dvd_left`](Self::coprime_of_dvd_left), same route with
    /// `a` fixed and the divisor chain run on the second argument of `gcd`.
    pub coprime_of_dvd_right: NameId,
    /// `Nat.prime_dvd_iff_not_coprime : ∀ p n, (Le two p ∧ ∀ d, dvd d p → Or
    /// (Eq d one) (Eq d p)) → Iff (dvd p n) (Not (Eq (gcd p n) one))`.
    ///
    /// Forward: `dvd p n` plus `dvd p p` (`dvd_refl`) give `dvd p (gcd p n)`
    /// (`dvd_gcd`); if `gcd p n = 1` that transports to `dvd p 1`, forcing
    /// `p ≤ 1` (`le_of_dvd`) against the primality hypothesis's `2 ≤ p` —
    /// contradiction via `le_trans`/`lt_of_le_of_lt`/`lt_irrefl`, so
    /// `gcd p n ≠ 1`.
    /// Reverse: `gcd p n` divides `p` (`gcd_dvd_left`), so primality's
    /// divisor clause forces `gcd p n = 1 ∨ gcd p n = p`; the hypothesis
    /// rules out `= 1` (`absurd`), leaving `gcd p n = p`, and `dvd p n`
    /// follows from `gcd_dvd_right` transported along that equation. Mirrors
    /// `Nat.Prime.dvd_iff_not_coprime`; `Prime` is spelled inline as
    /// `prime_condition`, matching this file's own convention.
    pub prime_dvd_iff_not_coprime: NameId,
    /// `Nat.coprime_add_self_right : ∀ m n, Iff (Eq (gcd m (add n m)) one)
    /// (Eq (gcd m n) one)`.
    ///
    /// `gcd m (n+m) = gcd m n` (interned as the shared value both `Eq`s
    /// substitute against, so the `Iff` follows by `d.chain` once that one
    /// equation is in hand), proved by antisymmetry of divisibility
    /// (`dvd_antisymm`): `g1 := gcd m (n+m)` divides `m` and `n+m`
    /// (`gcd_dvd_left`/`_right`); `dvd_add_iff_right` (after `add_comm` to
    /// match its `m+n` order) cancels the shared `m` factor to give
    /// `g1 ∣ n`, so `dvd_gcd` gives `g1 ∣ gcd m n`. Conversely
    /// `g2 := gcd m n` divides `m` and `n`, so `dvd_add` gives
    /// `g2 ∣ (n+m)` directly (no reordering needed, since that is the
    /// lemma's own argument order), and `dvd_gcd` gives `g2 ∣ g1`.
    pub coprime_add_self_right: NameId,
    /// `Nat.Coprime.of_dvd : ∀ a1 a2 b1 b2, dvd a1 a2 → dvd b1 b2 →
    /// Eq (gcd a2 b2) one → Eq (gcd a1 b1) one` — a two-step composition of
    /// `coprime_of_dvd_right` (shrink `b2` to `b1`) then `coprime_of_dvd_left`
    /// (shrink `a2` to `a1`).
    pub coprime_of_dvd: NameId,
    /// `Nat.Coprime.coprime_dvd_left : ∀ m k n, dvd m k → Coprime k n →
    /// Coprime m n` — [`coprime_of_dvd_left`](Self::coprime_of_dvd_left)
    /// under the Mathlib v4.30 name (`Init.Data.Nat.Coprime`), same
    /// statement verbatim once `Coprime` unfolds to `gcd _ _ = one`. Closes
    /// ledger fact `F:ml430-nat-coprime-coprime-dvd-left-2ce391d2`.
    pub coprime_dvd_left: NameId,
    /// `Nat.Coprime.coprime_dvd_right : ∀ n m k, dvd n m → Coprime k m →
    /// Coprime k n` — [`coprime_of_dvd_right`](Self::coprime_of_dvd_right)
    /// under the Mathlib v4.30 name, same statement verbatim. Closes ledger
    /// fact `F:ml430-nat-coprime-coprime-dvd-right-4a2670ae`.
    pub coprime_dvd_right: NameId,
    /// `Nat.Coprime.coprime_mul_left : ∀ k m n, Coprime (mul k m) n →
    /// Coprime m n`. `m ∣ (k*m)` (`dvd_mul` transported along `mul_comm`)
    /// feeds [`coprime_of_dvd_left`](Self::coprime_of_dvd_left). Closes
    /// ledger fact `F:ml430-nat-coprime-coprime-mul-left-fb5bd11a`.
    pub coprime_mul_left: NameId,
    /// `Nat.Coprime.coprime_mul_right : ∀ m k n, Coprime (mul m k) n →
    /// Coprime m n`. `m ∣ (m*k)` is `dvd_mul` directly, no `mul_comm` needed,
    /// feeding [`coprime_of_dvd_left`](Self::coprime_of_dvd_left). Closes
    /// ledger fact `F:ml430-nat-coprime-coprime-mul-right-70e4e946`.
    pub coprime_mul_right: NameId,
    /// `Nat.Coprime.coprime_mul_left_right : ∀ m k n, Coprime m (mul k n) →
    /// Coprime m n`. `n ∣ (k*n)` (`dvd_mul` transported along `mul_comm`)
    /// feeds [`coprime_of_dvd_right`](Self::coprime_of_dvd_right). Closes
    /// ledger fact `F:ml430-nat-coprime-coprime-mul-left-right-910d7d8f`.
    pub coprime_mul_left_right: NameId,
    /// `Nat.Coprime.coprime_mul_right_right : ∀ m n k, Coprime m (mul n k) →
    /// Coprime m n`. `n ∣ (n*k)` is `dvd_mul` directly, feeding
    /// [`coprime_of_dvd_right`](Self::coprime_of_dvd_right). Closes ledger
    /// fact `F:ml430-nat-coprime-coprime-mul-right-right-9599ecd3`.
    pub coprime_mul_right_right: NameId,
    /// `Nat.Coprime.dvd_of_dvd_mul_left : ∀ k m n, Coprime k m →
    /// dvd k (mul m n) → dvd k n` — [`gauss_lemma`](Self::gauss_lemma)
    /// verbatim, argument names aside. Closes ledger fact
    /// `F:ml430-nat-coprime-dvd-of-dvd-mul-left-b0608cb9`.
    pub dvd_of_dvd_mul_left: NameId,
    /// `Nat.Coprime.dvd_of_dvd_mul_right : ∀ k n m, Coprime k n →
    /// dvd k (mul m n) → dvd k m` — [`gauss_lemma`](Self::gauss_lemma) at
    /// `(k, n, m)`, with the hypothesis `dvd k (mul m n)` transported along
    /// `mul_comm m n` to the `dvd k (mul n m)` shape `gauss_lemma` expects.
    /// Closes ledger fact `F:ml430-nat-coprime-dvd-of-dvd-mul-right-efc3a4ec`.
    pub dvd_of_dvd_mul_right: NameId,
    /// `Nat.Coprime.coprime_div_right : ∀ m n a, Coprime m n → dvd a n →
    /// Coprime m (div n a)`. Cases on `a`: at `a = 0`, `dvd 0 n` forces
    /// `n = 0` (`zero_mul`), and `div _ 0 = 0` (`div_zero`) collapses both
    /// `n` and `div n a` to the same value transported from the hypothesis.
    /// At `a = succ a'`, the witness `q` from `dvd a n` (`n = a*q`) gives
    /// `div n a = q` (`div_mul_cancel_of_dvd` at the positive `a`, the same
    /// "exact factor divided back out" route `lcm_gcd_lemmas.rs`'s private
    /// `div_eq_of_mul_eq` uses), and `Coprime m n` transported along
    /// `n = a*q` is `Coprime m (a*q)`, which
    /// [`coprime_of_dvd_right`](Self::coprime_of_dvd_right) shrinks to
    /// `Coprime m q` via `q ∣ (a*q)` (`dvd_mul` transported along
    /// `mul_comm`). Closes ledger fact
    /// `F:ml430-nat-coprime-coprime-div-right-7a8ce438`.
    pub coprime_div_right: NameId,
    /// `Nat.Coprime.coprime_div_left : ∀ m n a, Coprime m n → dvd a m →
    /// Coprime (div m a) n`. Mirror image of
    /// [`coprime_div_right`](Self::coprime_div_right): cases on `a`, at
    /// `a = 0`, `dvd 0 m` forces `m = 0` (`zero_mul`), and `div _ 0 = 0`
    /// (`div_zero`) collapses both `m` and `div m a` to the same value
    /// transported from the hypothesis. At `a = succ a'`, the witness `q`
    /// from `dvd a m` (`m = a*q`) gives `div m a = q`
    /// (`div_mul_cancel_of_dvd` at the positive `a`, via the same private
    /// `div_eq_of_mul_eq` helper), and `Coprime m n` transported along
    /// `m = a*q` is `Coprime (a*q) n`, which
    /// [`coprime_of_dvd_left`](Self::coprime_of_dvd_left) shrinks to
    /// `Coprime q n` via `q ∣ (a*q)` (`dvd_mul` transported along
    /// `mul_comm`). Closes ledger fact
    /// `F:ml430-nat-coprime-coprime-div-left-6f7082bd`.
    pub coprime_div_left: NameId,
    /// `Nat.coprime_of_dvd' : ∀ m n, (∀ k, prime_condition k → dvd k m →
    /// dvd k n → dvd k one) → gcd m n = one`. Closes ledger fact
    /// `F:ml430-nat-coprime-of-dvd`.
    pub coprime_of_forall_prime_dvd: NameId,
    /// `Nat.dvd_of_forall_prime_mul_dvd : ∀ a b, (∀ k, prime_condition k →
    /// dvd k a → dvd (mul k a) b) → dvd a b`. Closes ledger fact
    /// `F:ml430-nat-dvd-of-forall-prime-mul-dvd`.
    pub dvd_of_forall_prime_mul_dvd: NameId,
    /// `Nat.IsRelPrime m n := ∀ d, d ∣ m → d ∣ n → d = 1` — a `Definition`,
    /// Mathlib's `IsUnit d` specialized to `Nat`'s only unit `1`. See
    /// `rel_prime.rs`'s module doc for why this predicate, unlike `Coprime`,
    /// needs a name of its own.
    pub is_rel_prime: NameId,
    /// `Nat.coprime_iff_isRelPrime : ∀ m n, Iff (Eq (gcd m n) one)
    /// (IsRelPrime m n)`. Closes ledger fact
    /// `F:ml430-nat-coprime-iff-isrelprime-0c08eb25`.
    pub coprime_iff_is_rel_prime: NameId,
    /// `Nat.minFacAux fuel n candidate : Nat` — fuel-recursive linear divisor
    /// search, see `min_fac.rs`'s module doc for why this is NOT Mathlib's
    /// `minFacAux` (theirs is well-founded, skips even candidates, and exits
    /// early at `sqrt n`) even though the two agree pointwise.
    pub min_fac_aux: NameId,
    /// `Nat.minFac n : Nat` — the least prime factor of `n`, with `minFac 0 =
    /// 2` and `minFac 1 = 1` as boundary conventions (matching Mathlib's).
    pub min_fac: NameId,
    /// `Nat.minFacAuxMinimal : ∀ fuel n candidate, Le 2 candidate → Eq (add
    /// candidate fuel) n → (∀ e, 2 ≤ e → e < candidate → ¬ e∣n) →
    /// ∀ e, 2 ≤ e → e < minFacAux fuel n candidate → ¬ e∣n` — the
    /// fuel-generalized minimality invariant carried by the linear search:
    /// nothing below the value the search returns divides `n`, for a search
    /// started at any `candidate ≥ 2` already known to be minimal below
    /// itself. See `min_fac.rs`'s module doc for the induction.
    pub min_fac_aux_minimal: NameId,
    /// `Nat.min_fac_minimal_of_two_le : ∀ n, Le 2 n → ∀ e, Le 2 e → Lt e
    /// (minFac n) → Not (dvd e n)` — [`min_fac_aux_minimal`](Self::min_fac_aux_minimal)
    /// specialized to `minFac`'s own search (`candidate := 2`,
    /// `fuel := sub n 2`), for `n ≥ 2` (the boundary values `minFac 0 = 2`
    /// and `minFac 1 = 1` are not a search result — see `min_fac.rs`).
    pub min_fac_minimal_of_two_le: NameId,
    /// `Nat.coprime_of_lt_min_fac : ∀ n m, Not (Eq m zero) → Lt m (minFac n)
    /// → Eq (gcd n m) one` — a NEW local fact about THIS repository's
    /// `minFac`, not a flip of `F:ml430-nat-coprime-of-lt-minfac`: that
    /// mirror stays open because this `minFac` is fuel-recursive, not
    /// Mathlib's well-founded `minFacAux` (see `min_fac.rs`'s module doc).
    /// Case split on `n`: `n = 0` forces `m = 1` (the only value `< minFac 0
    /// = 2` other than `0`), `n = 1` is vacuous (`minFac 1 = 1`, nothing is
    /// `< 1` other than `0`, excluded by hypothesis), and `n ≥ 2` uses
    /// [`min_fac_minimal_of_two_le`](Self::min_fac_minimal_of_two_le): if
    /// `gcd n m ≠ 1` then (since `m ≠ 0` forces `gcd n m ≠ 0`, hence `gcd n m
    /// ≥ 2` by `lt_or_eq_of_le`) `gcd n m` is a divisor of `n` that is `≥ 2`
    /// and `≤ m < minFac n` (via `le_of_dvd` on `gcd n m ∣ m`), contradicting
    /// minimality.
    pub coprime_of_lt_min_fac: NameId,
    /// `Nat.coprime_self_add_right : ∀ m n, Iff (Eq (gcd m (add m n)) one)
    /// (Eq (gcd m n) one)` — [`coprime_add_self_right`](Self::coprime_add_self_right)
    /// with `m`/`n`'s sum reordered via `add_comm`: the only difference is
    /// which side of `add` carries `m`.
    pub coprime_self_add_right: NameId,
    /// `Nat.Coprime.symmetric : ∀ a b, Eq (gcd a b) one → Eq (gcd b a) one` —
    /// `gcd a b` and `gcd b a` divide each other (`gcd_dvd_left`/
    /// `gcd_dvd_right` both orderings plus `dvd_gcd`), so `dvd_antisymm`
    /// gives `gcd a b = gcd b a` and the hypothesis transports along it.
    pub coprime_symmetric: NameId,
    /// `Nat.Coprime.mul_add_mul_ne_mul : ∀ m n a b, Coprime m n → a ≠ 0 → b ≠
    /// 0 → a*m + b*n ≠ m*n`. Closes
    /// `F:ml430-nat-coprime-mul-add-mul-ne-mul-51b56f70`. See
    /// `nat_prelude::coprime_mul_add_mul_ne_mul`.
    pub coprime_mul_add_mul_ne_mul: NameId,
    /// `Nat.not_coprime_zero_zero : Not (Eq (gcd zero zero) one)`. `gcd 0 0 =
    /// 0` (`gcd_zero_left`), so `gcd 0 0 = 1` would give `0 = 1`, refuted by
    /// `succ_ne_zero`.
    pub not_coprime_zero_zero: NameId,
    /// `Nat.coprime_one_left_iff : ∀ n, Iff (Eq (gcd one n) one) True`. `gcd 1
    /// n` divides `1` (`gcd_dvd_left`), so `eq_one_of_dvd_one` closes it
    /// unconditionally.
    pub coprime_one_left_iff: NameId,
    /// `Nat.coprime_one_right_iff : ∀ n, Iff (Eq (gcd n one) one) True` —
    /// the right-hand mirror of
    /// [`coprime_one_left_iff`](Self::coprime_one_left_iff) via
    /// `gcd_dvd_right`.
    pub coprime_one_right_iff: NameId,
    /// `Nat.coprime_add_self_left : ∀ m n, Iff (Eq (gcd (add m n) n) one) (Eq
    /// (gcd m n) one)` — [`coprime_add_self_right`](Self::coprime_add_self_right)
    /// instantiated at `(n, m)`, with both sides of the `Iff` swapped through
    /// [`coprime_symmetric`](Self::coprime_symmetric).
    pub coprime_add_self_left: NameId,
    /// `Nat.coprime_self_add_left : ∀ m n, Iff (Eq (gcd (add m n) m) one) (Eq
    /// (gcd n m) one)` — [`coprime_add_self_left`](Self::coprime_add_self_left)
    /// with `m`/`n`'s sum reordered via `add_comm`, the same
    /// congruence-transport shape
    /// [`coprime_self_add_right`](Self::coprime_self_add_right) uses.
    pub coprime_self_add_left: NameId,
    /// `Nat.coprime_or_dvd_of_prime : ∀ p, prime_condition p → ∀ i, Or
    /// (Eq (gcd p i) one) (dvd p i)` — decides `beq (gcd p i) one`
    /// (`Bool.rec`, fully constructive): the `true` branch gives `Coprime p i`
    /// directly (`eq_of_beq_eq_true`), the `false` branch gives
    /// `Not (Coprime p i)` (`ne_of_beq_eq_false`), which
    /// `prime_dvd_iff_not_coprime` converts to `dvd p i`.
    pub coprime_or_dvd_of_prime: NameId,
    /// `Nat.coprime_two_left : ∀ n, Iff (Eq (gcd two n) one) (Odd n)`.
    ///
    /// `2` is prime (`prime_two`, a private helper rebuilding
    /// `prime_condition(2)` the way `irrational.rs`'s private
    /// `two_divisor_dichotomy` / `perfect.rs`'s private `divisors_of_two`
    /// already bound a divisor of `2` to `1` or `2`), so
    /// [`coprime_or_dvd_of_prime`](Self::coprime_or_dvd_of_prime) splits into
    /// `gcd 2 n = 1 ∨ dvd 2 n`, and
    /// [`prime_dvd_iff_not_coprime`](Self::prime_dvd_iff_not_coprime) relates
    /// `dvd 2 n` to `Not (gcd 2 n = 1)`. A private bridge (`even_of_dvd_two`/
    /// `dvd_two_of_even`, via the `2 * k = k + k` identity rebuilt the same
    /// way) connects `dvd 2 n` and `Even n`, and
    /// [`even_or_odd_exists`](Self::even_or_odd_exists)/
    /// [`even_not_odd`](Self::even_not_odd) rule out the even case in each
    /// direction.
    pub coprime_two_left: NameId,
    /// `Nat.coprime_two_right : ∀ n, Iff (Eq (gcd n two) one) (Odd n)` —
    /// [`coprime_two_left`](Self::coprime_two_left) composed with
    /// [`coprime_symmetric`](Self::coprime_symmetric) on both sides of the
    /// `Iff` to swap `gcd`'s argument order.
    pub coprime_two_right: NameId,
    /// `Nat.Coprime.odd_of_left : ∀ n, Eq (gcd two n) one → Odd n` — the `mp`
    /// direction of [`coprime_two_left`](Self::coprime_two_left) alone.
    pub coprime_odd_of_left: NameId,
    /// `Nat.Coprime.odd_of_right : ∀ n, Eq (gcd n two) one → Odd n` — the
    /// `mp` direction of [`coprime_two_right`](Self::coprime_two_right)
    /// alone.
    pub coprime_odd_of_right: NameId,
    /// `Nat.prime_odd_of_ne_two : ∀ p, prime_condition p → Not (Eq p two) →
    /// Odd p` — [`coprime_or_dvd_of_prime`](Self::coprime_or_dvd_of_prime)
    /// applied at `(p, two)` splits into `gcd p two = 1 ∨ dvd p two`: the
    /// first branch gives `Odd p` via
    /// [`coprime_symmetric`](Self::coprime_symmetric) +
    /// [`coprime_odd_of_left`](Self::coprime_odd_of_left); the second
    /// branch applies `2`'s own primality (`prime_two`) to `p` as a
    /// divisor, giving `p = 1 ∨ p = 2` — `p = 1` contradicts `p`'s lower
    /// bound `2 ≤ p`, `p = 2` contradicts the hypothesis directly.
    pub prime_odd_of_ne_two: NameId,
    /// `Nat.prime_even_iff : ∀ p, prime_condition p → Iff (Even p) (Eq p
    /// two)` — same case split as
    /// [`prime_odd_of_ne_two`](Self::prime_odd_of_ne_two) for `mp` (the
    /// `gcd p two = 1` branch now contradicts `Even p` via
    /// [`even_not_odd`](Self::even_not_odd) instead of closing the goal);
    /// `mpr` transports the private `even_of_dvd_two two dvd_refl` witness
    /// along the hypothesised `p = 2`.
    pub prime_even_iff: NameId,
    /// `Nat.prime_not_dvd_mul : ∀ p m n, prime_condition p → Not (dvd p m) →
    /// Not (dvd p n) → Not (dvd p (mul m n))` — the contrapositive of
    /// `euclid_lemma` (`bezout.rs`): assuming `dvd p (m*n)`, `euclid_lemma`
    /// splits into `dvd p m ∨ dvd p n`, and each branch contradicts one of
    /// the two hypotheses directly.
    pub prime_not_dvd_mul: NameId,
    /// `Nat.prime_dvd_of_dvd_pow : ∀ p m n, prime_condition p → dvd p (pow m
    /// n) → dvd p m` — induction on `n`. `n = 0`: `pow m 0 = 1`
    /// (`pow_zero`), and a prime cannot divide `1` (the same
    /// `le_of_dvd`/`le_trans`/`le_of_succ_le_succ`/`not_succ_le_zero`
    /// refutation `prime_dvd_iff_not_coprime`'s `mp` branch already uses
    /// against `p ≤ 1`), so the hypothesis is vacuous. `n = succ j`:
    /// `pow m (succ j) = mul (pow m j) m` (`pow_succ`), and `euclid_lemma`
    /// splits `dvd p (pow m j * m)` into `dvd p (pow m j) ∨ dvd p m` — the
    /// first branch applies the induction hypothesis, the second **is**
    /// the goal.
    pub prime_dvd_of_dvd_pow: NameId,
    /// `Nat.coprime_primes : ∀ p q, prime_condition p → prime_condition q →
    /// Iff (Eq (gcd p q) one) (Not (Eq p q))` — `mp` transports `dvd p p`
    /// (`dvd_refl`) along a hypothesised `p = q` to `dvd p q`, then
    /// [`prime_dvd_iff_not_coprime`](Self::prime_dvd_iff_not_coprime)'s `mp`
    /// turns that into `Not (Coprime p q)`, contradicting the coprimality
    /// hypothesis. `mpr` splits
    /// [`coprime_or_dvd_of_prime`](Self::coprime_or_dvd_of_prime) applied at
    /// `(p, q)`: the coprime branch is the goal directly; the `dvd p q`
    /// branch applies `q`'s own primality clause to divisor `p`, giving
    /// `p = 1 ∨ p = q` — `p = 1` is refuted against `p`'s `2 ≤ p` lower
    /// bound, `p = q` contradicts the `p ≠ q` hypothesis.
    pub coprime_primes: NameId,
    /// `Nat.not_prime_of_dvd_of_ne : ∀ m n, dvd m n → Not (Eq m one) → Not
    /// (Eq m n) → Not (prime_condition n)` — a prime's divisor clause
    /// applied to `m` gives `m = 1 ∨ m = n`; either disjunct directly
    /// contradicts one of the two hypotheses.
    pub not_prime_of_dvd_of_ne: NameId,
    /// `Nat.Prime.five_le_of_ne_two_of_ne_three : ∀ p, prime_condition p →
    /// Not (Eq p two) → Not (Eq p three) → Le five p` — Mathlib's
    /// `Nat.Prime.five_le_of_ne_two_of_ne_three`. Split at `Nat.lt_or_ge p
    /// 5` ([`ops::cases_lt_or_ge`](super::ops::cases_lt_or_ge)): the `Le 5
    /// p` side is the hypothesis itself. The `Lt p 5` side is a genuine
    /// 5-way case split to concrete `p ∈ {0,1,2,3,4}`
    /// ([`ops::cases_lt_bound_absurd`](super::ops::cases_lt_bound_absurd), a
    /// second new finite-cases eliminator whose branches discharge a FIXED
    /// goal by contradiction rather than each proving a static fact): `p =
    /// 0` and `p = 1` both contradict the primality hypothesis's own lower
    /// bound `2 ≤ p`; `p = 2` and `p = 3` contradict the two `Not`
    /// hypotheses directly; `p = 4` is refuted by
    /// [`not_prime_of_dvd_of_ne`](Self::not_prime_of_dvd_of_ne) at `(2, 4)`
    /// (`dvd_mul 2 2` defeq `dvd 2 4`, plus `2 ≠ 1` and `2 ≠ 4` from
    /// `finite::ne_of_lt`), applied to the primality hypothesis transported
    /// to `p = 4`.
    pub five_le_of_ne_two_of_ne_three: NameId,
    /// `Nat.Prime.pred_pos : ∀ p, prime_condition p → Lt zero (pred p)` —
    /// `2 ≤ p` transports along `p = succ (pred p)`
    /// ([`pos_implies_succ_pred`], `finite.rs`) to `2 ≤ succ (pred p)`, then
    /// `le_of_succ_le_succ` strips one `succ`, leaving `1 ≤ pred p`, defeq
    /// to the goal.
    pub prime_pred_pos: NameId,
    /// `Nat.succ_pred_prime : ∀ p, prime_condition p → Eq (succ (pred p))
    /// p` — [`pos_implies_succ_pred`] (`finite.rs`) gives `p = succ (pred
    /// p)` from `p`'s positivity (itself from `2 ≤ p`); `Eq.symm` flips it.
    pub succ_pred_prime: NameId,
    /// `Nat.Prime.not_prime_pow : ∀ x n, Le two n → Not (prime_condition
    /// (pow x n))` — the shared argument in
    /// `prime_pow_ge2_contradiction` (`prime_char.rs`):
    /// `x` divides `x^n` (witness `x^(n-1)`), so the divisor clause forces
    /// `x = 1` (collapsing `x^n` to `1` via `one_pow`, contradicting the `2
    /// ≤ x^n` lower bound) or `x = x^n` (cancelling the shared factor `x`
    /// via `mul_left_cancel_of_pos` forces `x^(n-2) = 1`, hence `x ∣ 1`,
    /// refuted by `not_dvd_one_of_two_le`). `n` is cased into `0`, `1`,
    /// `succ (succ _)` first; the hypothesis is absurd in the first two.
    /// Closes `F:ml430-nat-prime-not-prime-pow-d6480abf`.
    pub prime_not_prime_pow_two_le: NameId,
    /// `Nat.Prime.not_prime_pow' : ∀ x n, Not (Eq n one) → Not
    /// (prime_condition (pow x n))` — the same case split as
    /// [`prime_not_prime_pow_two_le`](Self::prime_not_prime_pow_two_le),
    /// with an `n = 0` case added (`pow x 0 = 1` directly contradicts the
    /// lower bound) and the `n = 1` case discharged by the `Not (Eq n one)`
    /// hypothesis itself rather than by an absurd bound. Closes
    /// `F:ml430-nat-prime-not-prime-pow-5f14afc6`.
    pub prime_not_prime_pow_ne_one: NameId,
    /// `Nat.Prime.eq_one_of_pow : ∀ x n, prime_condition (pow x n) → Eq n
    /// one` — the same three-way case split on `n` read the other way:
    /// `n = 0` and `n = succ (succ _)` both contradict the primality
    /// hypothesis directly (the latter via
    /// `prime_pow_ge2_contradiction` (`prime_char.rs`)),
    /// leaving `n = 1` as the only reachable case, which **is** the goal.
    /// Closes `F:ml430-nat-prime-eq-one-of-pow-846d2949`.
    pub prime_eq_one_of_pow: NameId,
    /// `Nat.Prime.not_coprime_iff_dvd : ∀ m n, Iff (Not (Eq (gcd m n) one))
    /// (∃ p, prime_condition p ∧ (dvd p m ∧ dvd p n))` — `mpr` builds `p ∣
    /// gcd m n` (`dvd_gcd`) and transports a hypothesised `gcd m n = one`
    /// into `p ∣ one`, refuted by `not_dvd_one_of_two_le`. `mp` trichotomizes
    /// `g := gcd m n` (`lt_or_ge` twice, matching
    /// `coprime_of_forall_prime_dvd`'s own split): `g = 0` forces `m = n =
    /// 0` (`gcd_dvd_left`/`_right` transported, then `dvd_elim` against
    /// `zero_mul`), and `2` (this file's own `prime_two`, built from
    /// `ops::two_divisor_dichotomy`) divides both trivially (`dvd_zero`);
    /// `g = 1` contradicts the hypothesis directly; `2 ≤ g` supplies a prime
    /// `pw ∣ g` (`exists_prime_dvd`), and `dvd_trans` through
    /// `gcd_dvd_left`/`_right` gives `pw ∣ m` and `pw ∣ n`. Closes
    /// `F:ml430-nat-prime-not-coprime-iff-dvd-c83110ca`.
    pub prime_not_coprime_iff_dvd: NameId,
    /// `Nat.Prime.mul_eq_prime_sq_iff : ∀ x y p, prime_condition p → Not (Eq
    /// x one) → Not (Eq y one) → Iff (Eq (mul x y) (pow p two)) (And (Eq x
    /// p) (Eq y p))` — `mpr` substitutes `x = p`/`y = p` into `p * p = p^2`
    /// (`pow_succ`/`pow_zero`/`one_mul` chained, as `divisibility.rs`'s
    /// `valuation_at_two_mul_sq` already does). `mp` uses `x*y = p^2 = p*p`
    /// to get `dvd p (mul x y)`, splits via `euclid_lemma` into `dvd p x ∨
    /// dvd p y`, and both branches route through this file's own
    /// `prime_sq_factor_case` (`prime_char.rs`): the divisor witness `k`
    /// (`a = p*k`) substitutes into `a*b = p*p` to give `k*b = p`
    /// (`mul_assoc` + `mul_left_cancel_of_pos`), and `k`'s own primality
    /// clause (`prime_eq_one_or_self_of_dvd`) forces `k = 1` (giving `a = p`
    /// and, via `k*b=p`, `b = p`) or `k = p` (giving `b = 1` via the same
    /// cancellation, contradicting the `Not (Eq b one)` hypothesis). The
    /// `dvd p y` branch calls the same helper with `x`/`y` swapped
    /// (`mul_comm` rebuilds the equation) and swaps the resulting `And`
    /// back. Closes `F:ml430-nat-prime-mul-eq-prime-sq-iff-d3fd2e31`.
    pub prime_mul_eq_prime_sq_iff: NameId,
    /// `Nat.Prime.dvd_mul_of_dvd_ne : ∀ p1 p2 n, Not (Eq p1 p2) →
    /// prime_condition p1 → prime_condition p2 → dvd p1 n → dvd p2 n → dvd
    /// (mul p1 p2) n` — [`coprime_primes`](Self::coprime_primes)'s `mpr`
    /// turns `p1 ≠ p2` (with both primality hypotheses) into `Coprime p1
    /// p2`, then `coprime_mul_dvd` (`crt.rs`) combines the two divisibility
    /// hypotheses.
    pub prime_dvd_mul_of_dvd_ne: NameId,

    // --- binomial coefficients (`choose.rs`) --------------------------------
    /// `Nat.choose : Nat → Nat → Nat`, by structural recursion on both
    /// arguments: `choose n 0 ≡ 1`, `choose 0 (succ k) ≡ 0`,
    /// `choose (succ n) (succ k) ≡ choose n k + choose n (succ k)`.
    pub choose: NameId,
    /// `Nat.choose_zero_right : ∀ n, choose n 0 = 1`.
    pub choose_zero_right: NameId,
    /// `Nat.choose_succ_succ : ∀ n k, choose (succ n) (succ k) = choose n k + choose n (succ k)`
    /// — Pascal's rule.
    pub choose_succ_succ: NameId,
    /// `Nat.zero_choose_succ : ∀ k, choose 0 (succ k) = 0`.
    pub zero_choose_succ: NameId,
    /// `Nat.choose_succ_self_eq_zero : ∀ n, choose n (succ n) = 0`.
    pub choose_succ_self_eq_zero: NameId,
    /// `Nat.choose_self : ∀ n, choose n n = 1`.
    pub choose_self: NameId,
    /// `Nat.choose_symm : ∀ n k, Le k n → choose n k = choose n (sub n k)`.
    pub choose_symm: NameId,
    /// `Nat.choose_one_right : ∀ n, choose n 1 = n`. By induction on `n`: the
    /// base case is `zero_choose_succ` at `k := 0` (`succ 0 ≡ 1`), and the
    /// successor case expands `choose (succ n) 1` via Pascal's rule into
    /// `choose n 0 + choose n 1`, closed by `choose_zero_right` and the
    /// induction hypothesis.
    pub choose_one_right: NameId,
    /// `Nat.choose_eq_zero_of_lt : ∀ n k, Lt n k → choose n k = 0`. By
    /// induction on `n` with an inner case split on `k`: `n = 0` needs `k`'s
    /// shape (`lt_irrefl`/`zero_choose_succ`); `n = succ m` strips one `succ`
    /// off both sides of the hypothesis (`le_of_succ_le_succ`) to reach two
    /// instances of the outer induction hypothesis, combined via Pascal's
    /// rule.
    pub choose_eq_zero_of_lt: NameId,
    /// `Nat.choose_ne_zero : ∀ n k, Le k n → choose n k ≠ 0` — via the
    /// private helper `choose::choose_pos_all`, `0 < choose n k`, and
    /// `lt_irrefl` after transporting along a hypothetical `choose n k = 0`.
    pub choose_ne_zero: NameId,
    /// `Nat.choose_le_succ : ∀ a c, choose a c ≤ choose (succ a) c`. By
    /// induction on `c`: `c = 0` has both sides defeq `1`
    /// (`le_refl`); `c = succ c'` expands the successor side via Pascal's
    /// rule into `choose a c' + choose a c`, which dominates `choose a c` by
    /// `le_add_right` plus `add_comm`.
    pub choose_le_succ: NameId,
    /// `Nat.choose_symm_of_eq_add : ∀ n a b, n = a + b → choose n a = choose n b`
    /// — `choose_symm` restated at the additive witness: `a ≤ a+b`
    /// (`le_add_right`) supplies `choose_symm`'s hypothesis, and
    /// `add_sub_cancel_left` rewrites its `n - a` conclusion to `b`.
    pub choose_symm_of_eq_add: NameId,
    /// `Nat.choose_le_add : ∀ a b c, choose a c ≤ choose (a + b) c`. By
    /// induction on `b`: `b = 0` is defeq `choose a c ≤ choose a c`
    /// (`add a zero ≡ a`); `b = succ b'` chains the induction hypothesis with
    /// `choose_le_succ (a+b') c` via `le_trans` (`add a (succ b') ≡ succ (add
    /// a b')`).
    pub choose_le_add: NameId,
    /// `Nat.choose_symm_add : ∀ a b, choose (a+b) a = choose (a+b) b` —
    /// `choose_symm_of_eq_add` instantiated at `n := a+b` with its hypothesis
    /// closed by `refl`.
    pub choose_symm_add: NameId,
    /// `Nat.choose_le_choose : ∀ a b c, Le a b → Le (choose a c) (choose b c)`.
    /// Route: `d0 := sub b a`; `sub_add_cancel(a, b, h) : Eq (add d0 a) b`;
    /// `add_comm(d0, a)` flips it to `Eq (add a d0) b`; `choose_le_add(a, d0,
    /// c) : Le (choose a c) (choose (add a d0) c)` transports along that
    /// equation to `Le (choose a c) (choose b c)`.
    pub choose_le_choose: NameId,
    /// `Nat.choose_mono : ∀ c a a', Le a a' → Le (choose a c) (choose a' c)`
    /// — the core unfolding of Mathlib's `Nat.choose_mono : ∀ b, Monotone
    /// (fun a => a.choose b)`. `choose_le_choose` with its arguments
    /// permuted so the fixed column comes first; no new induction.
    pub choose_mono: NameId,

    // --- binomial theorem (`binomial.rs`) -----------------------------------
    /// `Nat.sumRange_add : ∀ f g n, sumRange (fun i => f i + g i) n = sumRange f n + sumRange g n`.
    pub sum_range_add: NameId,
    /// `Nat.sumRange_shiftFront : ∀ f n, sumRange f (succ n) = f 0 + sumRange (fun k => f (succ k)) n`
    /// — peeling the FRONT term off a finite sum, the reindexing counterpart to
    /// the defining (back-peeling) `sum_range_succ`.
    pub sum_range_shift_front: NameId,
    /// `Nat.sumRange_congr_lt : ∀ f g n, (∀ i, Lt i n → f i = g i) → sumRange f n = sumRange g n`
    /// — the BOUNDED pointwise congruence: unlike `sum_range_congr`, the
    /// hypothesis only needs to hold below the sum's own bound.
    pub sum_range_congr_lt: NameId,
    /// `Nat.add_pow_zero : ∀ a b, (a+b)^0 = sumRange (fun k => choose 0 k * a^k * b^(0-k)) 1`
    /// — the `n=0` sanity instance of `add_pow`, checked directly (no
    /// induction) before the general theorem.
    pub add_pow_zero: NameId,
    /// `Nat.add_pow_one : ∀ a b, (a+b)^1 = sumRange (fun k => choose 1 k * a^k * b^(1-k)) 2`
    /// — the `n=1` sanity instance.
    pub add_pow_one: NameId,
    /// `Nat.add_pow : ∀ a b n, (a+b)^n = sumRange (fun k => choose n k * a^k * b^(n-k)) (succ n)`
    /// — the binomial theorem, by induction on `n`.
    pub add_pow: NameId,

    // --- row sum, term bound (`binomial.rs`) --------------------------------
    /// `Nat.one_pow : ∀ m, pow 1 m = 1`. Collapses every `1^k`/`1^(n-k)`
    /// factor of `add_pow`'s summand when specialized at `a = b = 1`.
    pub one_pow: NameId,
    /// `Nat.le_sumRange_of_lt : ∀ f n k, Lt k n → Le (f k) (sumRange f n)` —
    /// a term inside a finite sum's range is at most the sum.
    pub le_sum_range_of_lt: NameId,
    /// `Nat.sum_choose_row : ∀ n, sumRange (fun k => choose n k) (succ n) = pow 2 n`
    /// — the row sum, via `add_pow` at `a = b = 1`.
    pub sum_choose_row: NameId,
    /// `Nat.choose_le_two_pow : ∀ n k, Le k n → Le (choose n k) (pow 2 n)` —
    /// a binomial coefficient is at most `2^n`, an immediate consequence of
    /// [`sum_choose_row`](Self::sum_choose_row) and
    /// [`le_sum_range_of_lt`](Self::le_sum_range_of_lt).
    pub choose_le_two_pow: NameId,

    // --- Vandermonde's convolution prep (`binomial.rs`) ---------------------
    /// `Nat.succ_sub_of_le : ∀ m i, Le i m → sub (succ m) i = succ (sub m i)`
    /// — gives the truncated difference a successor shape once its subtrahend
    /// is known to be at most the minuend. `Nat.sub` recurses on its SECOND
    /// argument, so `sub (succ m) i` does not reduce for a bound `i` the way
    /// `sub m (succ i)` does; this is the lemma that supplies the missing
    /// successor shape Vandermonde's convolution needs to drive Pascal's rule
    /// on the `n`-side index. See the doc comment on
    /// `declare_combinatorial_identities` in `binomial.rs` for the stall this
    /// unblocks. Proved via `le_dest` + `add_sub_cancel_left`, mirroring
    /// `super::choose::sub_succ_of_lt`'s use of `le_dest`/`exists_rec`.
    pub succ_sub_of_le: NameId,
    /// `Nat.succ_mul_choose_eq : ∀ n k, succ k * choose (succ n)(succ k) =
    /// succ n * choose n k` — multiplying a row of Pascal's triangle by its
    /// column index reindexes it one row up. The absorption identity behind
    /// [`prime_dvd_choose`](Self::prime_dvd_choose). Induction on `n`,
    /// generalized over `k`; the successor step splits on `k` too (Pascal
    /// needs a `succ` shape there as well).
    pub succ_mul_choose_eq: NameId,

    // --- Fermat's little theorem (`fermat.rs`) ------------------------------
    /// `Nat.modEq_pow : ∀ d a b k, modEq d a b → modEq d (pow a k) (pow b k)`.
    pub mod_eq_pow: NameId,
    /// `Nat.dvd_sum_range_of_forall_lt :
    ///   ∀ d f n, (∀ k, Lt k n → dvd d (f k)) → dvd d (sumRange f n)`.
    pub dvd_sum_range_of_forall_lt: NameId,
    /// `Nat.add_pow_modeq_prime : prime p → (a+b)^p ≡ a^p + b^p [p]` — the
    /// Frobenius endomorphism / "freshman's dream" over ℕ.
    pub add_pow_modeq_prime: NameId,
    /// `Nat.pow_prime_modeq_self : prime p → a^p ≡ a [p]` — Fermat's little
    /// theorem.
    pub pow_prime_modeq_self: NameId,
    /// `Nat.mod_eq_iff_mod_eq : ∀ d a b, Iff (ModEq d a b) (Eq (modulo a d)
    /// (modulo b d))` — bridges the existential balanced-witness congruence
    /// to the executable `Nat.mod` comparison (`fermat_witness.rs`).
    pub mod_eq_iff_mod_eq: NameId,
    /// `Nat.not_prime_of_pow_mod_ne : ∀ p a, Not (Eq (modulo (pow a p) p)
    /// (modulo a p)) → Not (Prime p)` — the contrapositive of
    /// `pow_prime_modeq_self`, a computable Fermat compositeness certificate
    /// (`fermat_witness.rs`).
    pub not_prime_of_pow_mod_ne: NameId,

    // --- Euler's totient (`totient.rs`) -------------------------------------
    /// `Nat.countRange p n := |{k < n : p k = true}|` — the count of a
    /// decidable (`Bool`-valued) predicate over `[0,n)`, by structural
    /// recursion on `n`. Nothing in this prelude could count a decidable
    /// subset before this.
    pub count_range: NameId,
    /// `Nat.countRange_zero : ∀ p, countRange p 0 = 0`.
    pub count_range_zero: NameId,
    /// `Nat.countRange_succ : ∀ p n, countRange p (succ n) =
    /// countRange p n + (if p n then 1 else 0)`.
    pub count_range_succ: NameId,
    /// `Nat.countRange_le : ∀ p n, countRange p n ≤ n`.
    pub count_range_le: NameId,
    /// `Nat.countRange_congr : ∀ f g n, (∀ i, Eq Bool (f i) (g i)) →
    /// countRange f n = countRange g n` — two predicates that agree
    /// pointwise (everywhere, not just below `n`) count the same subset of
    /// `[0,n)`. Mirrors `sumRange_congr` (`algebra.rs`), the unconditional
    /// congruence law for `sumRange`.
    pub count_range_congr: NameId,
    /// `Nat.countRange_split : ∀ f m j, countRange f (add m j) =
    /// add (countRange f m) (countRange (fun k => f (add m k)) j)` — the
    /// `countRange` analogue of `sumRange_split` (`rectangle.rs`), by
    /// induction on `j` alone (`f`, `m` held fixed).
    pub count_range_split: NameId,
    /// `Nat.countRange_congr_lt : ∀ f g n, (∀ i, Lt i n → Eq Bool (f i) (g i))
    /// → Eq Nat (countRange f n) (countRange g n)` — the BOUNDED pointwise
    /// congruence (`count_range_permute.rs`), the form
    /// [`count_range_congr`](Self::count_range_congr)'s own doc comment says to
    /// add when a proof needs it.
    pub count_range_congr_lt: NameId,
    /// `Nat.countRange_point_change : ∀ a b i0 n, Lt i0 n →
    /// (∀ k, Lt k i0 → Eq Bool (a k) (b k)) →
    /// (∀ k, Lt i0 k → Lt k n → Eq Bool (a k) (b k)) →
    /// Eq Nat (add (countRange a n) (sel (b i0)))
    ///        (add (countRange b n) (sel (a i0)))` — two predicates agreeing on
    /// `[0,n)` except possibly at the single index `i0` have counts that differ
    /// exactly as their values at `i0` do (`count_range_permute.rs`). Stated
    /// additively; `Nat.sub` is truncated. This is what lets `countRange` skip
    /// the adjacent-transposition apparatus `Int.prodRange_permute` needed.
    pub count_range_point_change: NameId,
    /// `Nat.countRange_permute : ∀ f σ n, InjectiveOn σ n → MapsInto σ n →
    /// Eq Nat (countRange f n) (countRange (fun k => f (σ k)) n)` — counting
    /// over `[0,n)` is invariant under any injective self-map of `[0,n)`
    /// (`count_range_permute.rs`), the exact `countRange` mirror of
    /// `Int.prodRange_permute`. The primitive under `Nat.totient_mul_of_coprime`:
    /// the CRT map `x ↦ (x mod m) * n + (x mod n)` is such a self-map of
    /// `[0, m*n)` exactly when `m` and `n` are coprime.
    pub count_range_permute: NameId,
    /// `Nat.countRange_product : ∀ P R S n m,
    /// (∀ a b, Lt b n → Eq Bool (R a) true → Eq Bool (P (add (mul n a) b)) (S b)) →
    /// (∀ a b, Lt b n → Eq Bool (R a) false → Eq Bool (P (add (mul n a) b)) false) →
    /// Eq Nat (countRange P (mul n m)) (mul (countRange S n) (countRange R m))`
    /// — counting over `[0, n*m)` a predicate that factors through the block
    /// decomposition `y = n*a + b` multiplies the two factors' counts
    /// (`count_range_permute.rs`). **Coprimality-INDEPENDENT**, unlike the
    /// totient identity it will serve; keeping the two apart is the lesson of
    /// `301`'s false `count_range_row_major` claim. No `Lt 0 n` needed: at
    /// `n = 0` both sides are `zero` and both hypotheses are vacuous.
    pub count_range_product: NameId,
    /// `Nat.div_mod_block : ∀ n a b, Lt b n →
    /// And (Eq (div (add (mul n a) b) n) a) (Eq (mod (add (mul n a) b) n) b)`
    /// — the block decomposition read back (`div_mod_lemmas.rs`). Both halves
    /// at once, because they come from one `Nat.div_mod_unique`. This is the
    /// bridge [`count_range_product`](Self::count_range_product)'s consumer
    /// needs: that lemma's per-block hypotheses live at the index
    /// `add (mul n a) b`, and a predicate written in `div y n` / `mod y n`
    /// reduces there only once these two equations are in hand.
    pub div_mod_block: NameId,
    /// `Nat.crtSelfMap_mapsInto : ∀ mp np, MapsInto (fun x => add (mul
    /// (succ np) (mod x (succ mp))) (mod x (succ np))) (mul (succ np) (succ
    /// mp))` (`totient_mul.rs`) — the CRT residue-pairing self-map of
    /// `[0, n*m)` stays in range. **No hypothesis**: positivity is syntactic
    /// in the successor form, and coprimality is genuinely not needed (it
    /// holds at all 26 non-coprime pairs with `1 ≤ m,n ≤ 9`). One lemma of
    /// content, `Nat.mul_succ_add_lt_of_le_of_lt`.
    pub crt_self_map_maps_into: NameId,
    /// `Nat.crtSelfMap_injectiveOn : ∀ mp np, Eq (gcd (succ mp) (succ np)) 1
    /// → InjectiveOn (the same map) (mul (succ np) (succ mp))`
    /// (`totient_mul.rs`) — and this is the ONLY obligation under
    /// [`totient_mul_of_coprime`](Self::totient_mul_of_coprime) that the
    /// coprimality hypothesis pays for. Sharp: injective at every coprime
    /// pair and at **none** of the 26 non-coprime ones (smallest collision
    /// `m = n = 2`, where the map sends both `0` and `2` to `0`). Route:
    /// [`div_mod_block`](Self::div_mod_block) twice, then
    /// `mod_eq_iff_div_mod_remainder_eq` in reverse, then
    /// [`crt_unique`](Self::crt_unique) — the Nat-native one — then the same
    /// iff forward at the product modulus. No Bezout witness and no CRT
    /// existence over the naturals is used.
    pub crt_self_map_injective_on: NameId,
    /// `Nat.totient_mul_of_coprime : ∀ m n, Eq (gcd m n) 1 → Eq (totient (mul
    /// m n)) (mul (totient m) (totient n))` (`totient_mul.rs`) — Euler's
    /// totient is multiplicative on coprime arguments. The identity is FALSE
    /// without the hypothesis, at 26 of 26 non-coprime pairs with
    /// `1 ≤ m,n ≤ 9` (smallest counterexample `m = n = 2`: `totient 4 = 2`
    /// against `1 * 1`), which is what `docs/plan/status/301`'s traced plan
    /// got wrong. Assembled from
    /// [`count_range_congr`](Self::count_range_congr) (pointwise,
    /// unconditional), [`count_range_permute`](Self::count_range_permute)
    /// (the one coprimality-dependent step) and
    /// [`count_range_product`](Self::count_range_product) (Fubini, also
    /// unconditional).
    pub totient_mul_of_coprime: NameId,

    // --- `totient_prime_pow.rs`: the totient at a prime power ---------------
    /// `Nat.countRange_const_true : ∀ n, Eq Nat (countRange (fun _ => true) n) n`
    /// — counting a predicate that is `true` everywhere over `[0,n)` gives
    /// `n`. The trivial `countRange` companion that did not exist; a three-line
    /// induction over
    /// [`count_range_succ_of_true`](Self::count_range_succ_of_true), whose
    /// `f k = true` hypothesis is `Eq.refl true` for a constant predicate.
    /// Collapses the block-count factor
    /// [`count_range_product`](Self::count_range_product) leaves behind.
    pub count_range_const_true: NameId,
    /// `Nat.coprime_mul_iff_of_dvd : ∀ k m e, Dvd e m →
    /// Iff (Eq (gcd k (mul m e)) 1) (Eq (gcd k m) 1)` — when `e ∣ m`,
    /// multiplying the modulus by `e` does not change which residues are
    /// coprime to it. Forward is
    /// [`coprime_mul_iff`](Self::coprime_mul_iff)'s `mp` projected left (that
    /// direction is unconditional); backward is its `mpr` with
    /// [`coprime_of_dvd_right`](Self::coprime_of_dvd_right) supplying
    /// `gcd k e = 1`, and that is the ONLY place `e ∣ m` is spent.
    /// Load-bearing: the `Iff` fails at 165 non-dividing pairs with
    /// `1 ≤ m,e ≤ 15` (`scripts/tests/check-totient-prime-power-numerics.py`,
    /// check `3N`).
    pub coprime_mul_iff_of_dvd: NameId,
    /// `Nat.totient_mul_of_dvd : ∀ m e, Dvd e m →
    /// Eq Nat (totient (mul m e)) (mul (totient m) e)` — the non-coprime
    /// counting law (`totient_prime_pow.rs`). **No primality, no positivity,
    /// no factorization**; the hypothesis is `e ∣ m` and nothing more, and it
    /// is genuinely load-bearing (the identity fails at 493 non-dividing pairs
    /// with `1 ≤ m,e ≤ 25`, smallest `(1,2)`: `φ(2) = 1` against
    /// `φ(1)·2 = 2`). Proved by
    /// [`coprime_mul_iff_of_dvd`](Self::coprime_mul_iff_of_dvd) under
    /// [`count_range_congr`](Self::count_range_congr), then
    /// [`count_range_product`](Self::count_range_product) at block width `m`
    /// and block count `e`, then
    /// [`count_range_const_true`](Self::count_range_const_true). Nothing here
    /// runs an induction: `countRange_product` already did.
    pub totient_mul_of_dvd: NameId,
    /// `Nat.totient_pow_succ_of_prime : ∀ q j, Prime q →
    /// Eq Nat (totient (pow q (succ j))) (mul (sub q 1) (pow q j))` — the
    /// prime-power induction in the multiplicative form, which keeps
    /// `Nat.sub`'s truncation out of the inductive step. The step is
    /// [`totient_mul_of_dvd`](Self::totient_mul_of_dvd) at
    /// `m := pow q (succ j)`, `e := q`, whose `Dvd q (pow q (succ j))`
    /// obligation is [`dvd_mul_left`](Self::dvd_mul_left) because
    /// `pow q (succ j)` is DEFINITIONALLY `mul (pow q j) q`.
    /// **Primality is used in the base case only**, through
    /// [`totient_prime`](Self::totient_prime).
    pub totient_pow_succ_of_prime: NameId,
    /// `Nat.totient_prime_pow : ∀ q j, Prime q →
    /// Eq Nat (totient (pow q (succ j))) (sub (pow q (succ j)) (pow q j))`
    /// — Euler's totient at a prime power, `φ(p^k) = p^k − p^(k−1)`,
    /// stated at `succ j` rather than with a `Lt 0 k` hypothesis so `pow`'s
    /// ι-equation fires syntactically. The subtractive form of
    /// [`totient_pow_succ_of_prime`](Self::totient_pow_succ_of_prime), via
    /// [`add_sub_cancel_left`](Self::add_sub_cancel_left) (the right-handed
    /// `add_sub_cancel` does not exist here, hence an `add_comm` first).
    /// FALSE at composite bases — 42 composite `(c,k)` pairs, smallest
    /// `c = 4, k = 1` where `φ(4) = 2` and not `3`.
    pub totient_prime_pow: NameId,
    /// `Nat.totient_dvd_totient_mul_prime : ∀ x q, Prime q →
    /// Dvd (totient x) (totient (mul x q))` — **the prime step**:
    /// multiplying by a prime multiplies the totient by `q` or by `q - 1`, and
    /// either way the old totient divides the new one. One case split on
    /// [`coprime_or_dvd_of_prime`](Self::coprime_or_dvd_of_prime), whose two
    /// branches have the IDENTICAL shape and differ only in which product
    /// lemma supplies the rewrite —
    /// [`totient_mul_of_coprime`](Self::totient_mul_of_coprime) or
    /// [`totient_mul_of_dvd`](Self::totient_mul_of_dvd).
    ///
    /// This is the rung that makes `F:ml430-nat-totient-dvd-of-dvd-9622e44a`
    /// and `F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7` reachable
    /// WITHOUT unique factorisation (ADR-0668): the consumer supplies primes
    /// one at a time from [`exists_prime_dvd`](Self::exists_prime_dvd), ANY
    /// choice works, and no factor multiset is ever named.
    pub totient_dvd_totient_mul_prime: NameId,
    /// `Nat.totient_dvd_totient_mul : ∀ k a, Dvd (totient a) (totient (mul a
    /// k))` — the fully general (no hypothesis) form of Target 1
    /// (`F:ml430-nat-totient-dvd-of-dvd-9622e44a`), by well-founded induction
    /// on the cofactor `k` (`totient_dvd_chain.rs`). Chains
    /// [`totient_dvd_totient_mul_prime`](Self::totient_dvd_totient_mul_prime)
    /// along a factorisation of `k` supplied one prime at a time by
    /// [`exists_prime_dvd`](Self::exists_prime_dvd); no factor multiset is
    /// ever named (ADR-0668).
    pub totient_dvd_totient_mul: NameId,
    /// `Nat.totient_dvd_of_dvd : ∀ a b, Dvd a b → Dvd (totient a) (totient
    /// b)` — `F:ml430-nat-totient-dvd-of-dvd-9622e44a`. One `exists_rec`
    /// unpacking `a ∣ b` into `b = a*k` plus
    /// [`totient_dvd_totient_mul`](Self::totient_dvd_totient_mul) at
    /// `(k, a)` (`totient_dvd_chain.rs`).
    pub totient_dvd_of_dvd: NameId,
    /// `Nat.totient_mul_cofactor_bound : ∀ k a, Le one (totient a) → Le two
    /// k → Or (Le (mul two (totient a)) (totient (mul a k))) (And (Eq k two)
    /// (Eq (totient (mul a k)) (totient a)))` — the multiplier-tracking bound
    /// Target 3 (`F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7`) is
    /// built from (`totient_dvd_chain.rs`, ADR-0668): for a cofactor `k ≥ 2`,
    /// either `φ(a·k) ≥ 2·φ(a)` outright, or `k = 2` and `φ(a·k) = φ(a)`
    /// exactly. The second disjunct is reachable only via a single prime
    /// step at `q = 2` in the COPRIME branch (`a` odd), never at depth ≥ 2.
    pub totient_mul_cofactor_bound: NameId,
    /// `Nat.eq_or_eq_of_totient_eq_totient : ∀ a b, Dvd a b → Eq (totient a)
    /// (totient b) → Or (Eq a b) (Eq (mul two a) b)` —
    /// `F:ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7`. Unpacks `a ∣ b`
    /// into `b = a*k`; `k = 0` is refuted by `totient(a) ≥ 1`; `k = 1` gives
    /// `a = b` directly; `k ≥ 2` uses
    /// [`totient_mul_cofactor_bound`](Self::totient_mul_cofactor_bound) —
    /// its first disjunct is refuted by the totient-equality hypothesis
    /// (`2·φ(a) ≤ φ(a) < 2·φ(a)` when `φ(a) ≥ 1`), leaving only `k = 2`.
    pub eq_or_eq_of_totient_eq_totient: NameId,
    /// `Nat.totient_gcd_mul_aux : ∀ d a b, Eq (gcd a b) d → Eq (mul (totient
    /// d) (totient (mul a b))) (mul (mul (totient a) (totient b)) d)` —
    /// `totient_gcd_mul.rs`. The measure-generalized form of the last
    /// `ml430` totient mirror (ADR-0668): strong induction on the gcd
    /// value, peeling one prime at a time via
    /// [`coprime_or_dvd_of_prime`](Self::coprime_or_dvd_of_prime) applied
    /// independently to each of the two reduced cofactors (no factor
    /// multiset, no Euclid's lemma — narrower than ADR-0668's own sketch).
    pub totient_gcd_mul_aux: NameId,
    /// `Nat.totient_gcd_mul_totient_mul : ∀ a b, Eq (mul (totient (gcd a b))
    /// (totient (mul a b))) (mul (mul (totient a) (totient b)) (gcd a b))`
    /// — `F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7`, the non-coprime
    /// generalization of [`totient_mul_of_coprime`](Self::totient_mul_of_coprime)
    /// (which this collapses to at `gcd a b = 1`). One application of
    /// [`totient_gcd_mul_aux`](Self::totient_gcd_mul_aux) at `val := gcd a
    /// b`, discharged by `Eq.refl` (`totient_gcd_mul.rs`).
    pub totient_gcd_mul_totient_mul: NameId,
    /// `Nat.countRange_reversal_even : ∀ L h, (∀ j, Lt j L → Eq Bool (h (sub
    /// (pred L) j)) (h j)) → (∀ j, Lt j L → Eq Bool (h j) true → Not (Eq Nat
    /// j (sub (pred L) j))) → Even (countRange h L)` — a general,
    /// `totient`-INDEPENDENT evenness lemma (`count_range_reversal.rs`): a
    /// `Bool`-valued predicate over `[0,L)` invariant under the reflection
    /// `j <-> pred L - j` with no fixed point where it is `true` counts an
    /// EVEN number of `true`s. By well-founded induction on `L`
    /// (`lt_well_founded`/`WellFounded.fix`), peeling both range-ends
    /// together via `countRange_split` plus `countRange`'s own succ
    /// equation. The `Nat.totient_even` piece this was built for chains
    /// `gcd (n-k) n = gcd k n` through `coprime_add_self_right`/
    /// `coprime_self_add_right`/`coprime_symmetric` to supply this lemma's
    /// two hypotheses, but nothing here mentions `gcd`/`totient`.
    pub count_range_reversal_even: NameId,
    /// `Nat.totient_even : ∀ n, Lt two n → Even (totient n)` — Euler's
    /// totient is even above `2` (`F:ml430-nat-totient-even-28e0415f`).
    /// Peels index `0` off `[0,n)` (`countRange_split(f,1,n-1)`, `f 0 =
    /// false` since `n > 1`), then applies
    /// [`count_range_reversal_even`](Self::count_range_reversal_even) to the
    /// shifted predicate `h(k) := f(1+k)` at `L := n-1`: the reflection
    /// invariance chains `gcd(n-k,n) = gcd(k,n)` through
    /// `coprime_self_add_right`/`coprime_symmetric` (no new gcd fact), and
    /// the no-fixed-point hypothesis derives `2 < n` contradicts a fixed
    /// point directly (`gcd k n = 1` at a fixed point forces `n = 2k` and
    /// `k | gcd k n = 1`, so `k = 1`, `n = 2`). See `totient_lemmas.rs`'s
    /// module doc for the full route (`docs/plan/status/295-totient-even.md`,
    /// `299-totient-even-exec.md`).
    pub totient_even: NameId,
    /// `Nat.odd_totient_iff_eq_one : ∀ n, Iff (Odd (totient n)) (Eq (totient
    /// n) one)` (`F:ml430-nat-odd-totient-iff-eq-one-d0491d84`) — both
    /// unblocked by [`totient_even`](Self::totient_even): `mp`'s hard case
    /// (`2 < n`) refutes `Odd (totient n)` against `Even (totient n)`
    /// (`totient_even` + `odd_not_even`); the `n ≤ 2` cases and `mpr` are
    /// cheap `def_eq`/existential-witness closures, the same shape
    /// `totient_eq_one_iff` already uses.
    pub odd_totient_iff_eq_one: NameId,
    /// `Nat.odd_totient_iff : ∀ n, Iff (Odd (totient n)) (Or (Eq n one) (Eq n
    /// two))` (`F:ml430-nat-odd-totient-iff-b6a6596f`) —
    /// [`odd_totient_iff_eq_one`](Self::odd_totient_iff_eq_one) composed with
    /// [`NatPrelude::totient_eq_one_iff`] by direct `mp`/`mpr` function
    /// composition (no general `iff_trans` helper).
    pub odd_totient_iff: NameId,
    /// `Nat.totient_coprime_totient_iff : ∀ m n, Iff (Eq (gcd (totient m)
    /// (totient n)) one) (Or (Or (Eq m one) (Eq m two)) (Or (Eq n one) (Eq n
    /// two)))` (`F:ml430-nat-totient-coprime-totient-iff-3932cf83`). `mpr` is
    /// unconditional composition: whichever disjunct holds forces one side's
    /// totient to `one` ([`totient_eq_one_iff`](Self::totient_eq_one_iff)),
    /// and `gcd 1 x = 1` / `gcd x 1 = 1` regardless of the other argument
    /// (`coprime_one_left_iff`/`coprime_one_right_iff`). `mp`'s hard case is
    /// `2 < m` and `2 < n` both holding: two even naturals
    /// ([`totient_even`](Self::totient_even)) cannot be coprime, since each
    /// is divisible by `2` (`succ_mul`/`one_mul` turn the `Even` witness
    /// `k+k` into `mul two k`) and `dvd_gcd` then forces `2 | 1`, refuted by
    /// peeling one `succ` to `not_succ_le_zero` (the same ending
    /// `totient_le_one_contradiction_above_two` uses). The `m = 0` / `n = 0`
    /// sub-cases route through `gcd_zero_left` (this prelude has no named
    /// `gcd_zero_right`, so the `n = 0` sub-case bridges via `gcd_comm` first).
    pub totient_coprime_totient_iff: NameId,
    /// `Nat.beq_eq_false_of_ne : ∀ a b, Not (Eq Nat a b) → beq a b = false` —
    /// the converse of `ne_of_beq_eq_false`, closing the boolean/propositional
    /// bridge from the other side. Proved by deciding `beq a b` itself
    /// (`Bool.rec` into `Or (Eq Bool _ true) (Eq Bool _ false)`, fully
    /// constructive) and refuting the `true` branch via `eq_of_beq_eq_true`.
    pub beq_eq_false_of_ne: NameId,
    /// `Nat.totient n := countRange (fun k => beq (gcd k n) 1) n` — Euler's
    /// totient, the count of residues in `[0,n)` coprime to `n`. `k = 0` is
    /// never counted for `n > 1` (`gcd 0 n = n ≠ 1`), so this matches the
    /// textbook `[1,n]` convention (`n` itself is out of range but was never
    /// coprime to itself for `n > 1` either).
    pub totient: NameId,
    /// `Nat.countRange_eq_pred_of_only_zero_false : ∀ f n, (∀ k, 0 < k → k <
    /// succ n → f k = true) → f 0 = false → countRange f (succ n) = n` — the
    /// counting lemma `totient_prime` rests on: a predicate false at exactly
    /// one endpoint and true everywhere else in the range counts one short of
    /// the range's length.
    pub count_range_eq_pred_of_only_zero_false: NameId,
    /// `Nat.totient_prime : Prime p → totient p = sub p 1` — the bridge that
    /// makes Euler's theorem generalize Fermat's: every prime's totient is
    /// `p - 1`.
    pub totient_prime: NameId,

    // --- `totient_lemmas.rs`: the `ml430` totient mirrors -------------------
    /// `Nat.coprime_succ_self : ∀ m, Eq (gcd m (succ m)) one` — consecutive
    /// naturals are coprime. Falls out of `coprime_add_self_right(m, one)`
    /// (`Iff (gcd m (add one m) = one) (gcd m one = one)`) plus
    /// `coprime_one_right_iff` (`gcd m one = one` unconditionally), then
    /// `add one m = succ m` via `succ_add`/`zero_add`. The general
    /// `∀ m, coprime m (succ m)` fact this prelude had not yet named, and the
    /// key witness `totient_eq_zero` needs: the top index `n - 1` of the
    /// range `[0, n)` is always coprime to `n = succ (n - 1)`.
    pub coprime_succ_self: NameId,
    /// `Nat.totient_eq_zero : ∀ n, Iff (Eq (totient n) 0) (Eq n 0)` —
    /// `F:ml430-nat-totient-eq-zero`. Case-split on `n`: `n = 0` is
    /// `count_range_zero` on both sides; `n = succ k` reduces `totient
    /// (succ k)` to `succ (countRange f k)` for `f := totient's own
    /// predicate at succ k` (defeq unfold of `countRange`'s `Nat.rec`, plus
    /// `coprime_succ_self k` promoting `beq (gcd k (succ k)) 1` to `true`
    /// through `bool_select_nat`), which is never `0` (`succ_ne_zero`) —
    /// matching `succ k`'s own never-`0`ness, so both sides of the `Iff` are
    /// simply `False` and it closes by `ex_falso` in each direction. No
    /// existence/counting machinery beyond the top-index witness is needed,
    /// unlike `totient_eq_one_iff`/`totient_even`/the rest of this family
    /// (see `totient_lemmas.rs`'s module doc for what those still need).
    pub totient_eq_zero: NameId,
    /// `Nat.countRange_succ_of_true : ∀ f k, Eq Bool (f k) true →
    /// Eq Nat (countRange f (succ k)) (succ (countRange f k))` — promoting a
    /// single witness through `countRange`'s defining equation (itself
    /// proved by `Eq.refl`, so this is one `bool_congr_nat` step plus the
    /// same `add x 1 ≡ succ x` reduction `totient_eq_zero` already leans on).
    pub count_range_succ_of_true: NameId,
    /// `Nat.countRange_le_of_le : ∀ f m n, Le m n → Le (countRange f m)
    /// (countRange f n)` — cardinality monotonicity in the RANGE BOUND
    /// (distinct from `countRange_le_of_subset`'s monotonicity in the
    /// PREDICATE). Via `le_dest` (`m + k = n` for some `k`) plus
    /// `countRange_split` and `le_add_right`.
    pub count_range_le_of_le: NameId,
    /// `Nat.countRange_ge_two_of_two_witnesses : ∀ f n i j, Lt i j → Lt j n →
    /// Eq Bool (f i) true → Eq Bool (f j) true → Le 2 (countRange f n)` — the
    /// general "two distinct witnesses ⇒ count ≥ 2" lemma
    /// `totient_lemmas.rs`'s module doc names as the missing piece for
    /// `totient_eq_one_iff`'s forward direction and
    /// `dvd_two_of_totient_le_one`. Built from `count_range_succ_of_true` at
    /// each witness plus `count_range_le_of_le` to carry the resulting `≥ 1`
    /// bound up to the next witness and the `≥ 2` bound up to `n`.
    pub count_range_ge_two_of_two_witnesses: NameId,
    /// `Nat.dvd_two_of_totient_le_one : ∀ a, Lt zero a → Le (totient a) one →
    /// dvd a two` (`F:ml430-nat-dvd-two-of-totient-le-one`). `trichotomy` at
    /// `c = 2` on `a`: `a < 2` combined with `0 < a` forces `a = 1` (`dvd 1 2`
    /// trivially, witness `2`); `a = 2` is `dvd 2 2` (`dvd_refl`); `2 < a`
    /// contradicts `totient a ≤ 1` via `countRange_ge_two_of_two_witnesses`
    /// at the two witnesses `1` and `pred a` (see
    /// `totient_le_one_contradiction_above_two` in `totient_lemmas.rs`,
    /// shared with `totient_eq_one_iff`'s forward direction).
    pub dvd_two_of_totient_le_one: NameId,
    /// `Nat.totient_eq_one_iff : ∀ n, Iff (Eq (totient n) one) (Or (Eq n one)
    /// (Eq n two))` (`F:ml430-nat-totient-eq-one-iff`). Reverse direction:
    /// `totient one = one` and `totient two = one` both hold by pure
    /// reduction (`countRange` over `[0,1)`/`[0,2)`, like
    /// `totient_computes_on_small_numerals`). Forward direction shares
    /// `dvd_two_of_totient_le_one`'s `trichotomy` shape at `c = 2`: `n < 2`
    /// splits again (`lt_or_eq_of_le`) into `n = 0` (contradicts `totient n =
    /// 1` since `totient 0 = 0`) or `n = 1`; `n = 2` is immediate; `2 < n`
    /// uses the same shared contradiction as `dvd_two_of_totient_le_one`.
    pub totient_eq_one_iff: NameId,

    // --- `Fin`, and the pigeonhole notions (`finite.rs`) --------------------
    /// `Nat.Fin : Nat → Type 0` — the canonical finite index type
    /// `{0, …, n-1}`, the subtype form `⟨val : Nat, isLt : val < n⟩` declared
    /// as a one-parameter, one-constructor inductive family (the same
    /// data-field-plus-dependent-`Prop`-field shape `CReal` carries, with `n`
    /// as a genuine shared parameter — see `finite.rs`'s module doc).
    pub fin: NameId,
    /// `Nat.Fin.mk : Π (n val : Nat), Lt val n → Fin n`.
    pub fin_mk: NameId,
    /// `Nat.Fin.rec` — the kernel-generated recursor `Fin.val`/`Fin.isLt`
    /// project through.
    pub fin_rec: NameId,
    /// `Nat.Fin.val : Π (n : Nat), Fin n → Nat` — the underlying index.
    pub fin_val: NameId,
    /// `Nat.Fin.isLt : Π (n : Nat) (x : Fin n), Lt (val n x) n`.
    pub fin_is_lt: NameId,
    /// `Nat.Fin.val_mk : ∀ n val (h : Lt val n), Eq Nat (val n (mk n val h)) val`
    /// — `Fin.mk`'s defining equation for its data field, closed by `Eq.refl`
    /// (the recursor ι-reduces on the literal constructor).
    pub fin_val_mk: NameId,
    /// `Nat.injectiveOn f n := ∀ i j, i < n → j < n → f i = f j → i = j` —
    /// injectivity restricted to `{0, …, n-1}`, stated directly over a plain
    /// `Nat → Nat` function (no `Fin` needed: `finite.rs`'s module doc).
    pub injective_on: NameId,
    /// `Nat.surjectiveOn f n := ∀ k, k < n → ∃ i, i < n ∧ f i = k`.
    pub surjective_on: NameId,
    /// `Nat.mapsInto f n := ∀ i, i < n → f i < n` — `f` is a self-map of
    /// `{0, …, n-1}`. The pigeonhole principle needs this hypothesis
    /// explicitly: an injective function into a *larger* codomain need not be
    /// surjective onto a smaller one.
    pub maps_into: NameId,
    /// `Nat.injective_on_imp_surjective_on : ∀ f n, InjectiveOn f n →
    /// MapsInto f n → SurjectiveOn f n` — the finite pigeonhole principle.
    pub injective_on_imp_surjective_on: NameId,
    /// `Nat.restrict_injective : ∀ σ i0 n, InjectiveOn σ (succ n) → Lt i0 n →
    /// InjectiveOn (fun k => point_override σ i0 (σ n) k) n` — restricting an
    /// injective self-map of `{0,…,n}` to `{0,…,n-1}` by overriding the
    /// value at interior index `i0` with `σ n`, one of the two pieces
    /// `Int.prodRange_permute` needs (`finite.rs`'s module doc,
    /// `point_override`).
    pub restrict_injective: NameId,
    /// `Nat.restrict_maps_into : ∀ σ i0 n, InjectiveOn σ (succ n) →
    /// MapsInto σ (succ n) → Lt i0 n → Eq Nat (σ i0) n →
    /// MapsInto (fun k => point_override σ i0 (σ n) k) n` — the companion
    /// closure lemma to [`Self::restrict_injective`].
    pub restrict_maps_into: NameId,
    /// `Nat.transposition : Nat → Nat → Nat → Nat` — `transposition i j k`
    /// swaps `i` and `j` and fixes everything else, built from four nested
    /// `Nat.ble` cuts in the style of `point_override`/`point_swap`
    /// (`transposition.rs`'s module doc). The reusable object
    /// `Int.prodRange_swap` does not give: it takes its swapped function by
    /// hypothesis rather than constructing one.
    pub transposition: NameId,
    /// `Nat.transposition_involutive : ∀ i j, Lt i j → ∀ k,
    /// Eq Nat (transposition i j (transposition i j k)) k`.
    pub transposition_involutive: NameId,
    /// `Nat.transposition_injective : ∀ i j n, Lt i j →
    /// InjectiveOn (fun k => transposition i j k) n` — any involution is
    /// injective, applying [`Self::transposition_involutive`].
    pub transposition_injective: NameId,
    /// `Nat.transposition_maps_into : ∀ i j n, Lt i j → Lt j n →
    /// MapsInto (fun k => transposition i j k) n`.
    pub transposition_maps_into: NameId,
    /// `Nat.conjugate_injective : ∀ t σ n, (∀ x, Eq Nat (t (t x)) x) →
    /// MapsInto t n → InjectiveOn σ n →
    /// InjectiveOn (fun k => t (σ (t k))) n` — conjugating an injective
    /// self-map by any involutive self-map preserves injectivity, generic
    /// over `t` (not specialized to [`Self::transposition`]).
    pub conjugate_injective: NameId,
    /// `Nat.conjugate_maps_into : ∀ t σ n, MapsInto t n → MapsInto σ n →
    /// MapsInto (fun k => t (σ (t k))) n` — the companion closure lemma to
    /// [`Self::conjugate_injective`], needing no involution law.
    pub conjugate_maps_into: NameId,

    // --- `Nat.restrict_pair_*` (`restrict_pair.rs`) — the `N → N-2` step ----
    /// `Nat.setwise_fixed σ i j := And (Eq Nat (σ i) i) (Eq Nat (σ j) j)` —
    /// the POINTWISE form of "σ fixes `{i,j}` setwise" (`restrict_pair.rs`'s
    /// module doc explains why the pointwise form, not the disjunctive
    /// "swaps or fixes" one, is what the interior-collapse application has).
    pub setwise_fixed: NameId,
    /// `Nat.add_sub_cancel_of_le : ∀ i k, Le i k → add i (sub k i) = k` — the
    /// round trip the OTHER way from `sub_add_cancel`: `i` plus its
    /// complement-to-`k` restores `k`, for `i ≤ k`. Immediate from
    /// `sub_add_cancel` plus `add_comm`, but stated on its own because this is
    /// exactly the diagonal pairing `(i, k−i)` over `{(i,j) : i+j=k, i ≤ k}`
    /// — the fact `Nat.sumRange_diagonal`'s antidiagonal index `i` never
    /// appears un-paired with the fact that it, plus its `sub`-computed
    /// partner, IS `k`.
    pub add_sub_cancel_of_le: NameId,
    /// `Nat.sumRange_diagonal : ∀ F n,
    ///   sumRange (fun k => sumRange (fun i => F i (sub k i)) (succ k)) n
    ///     = sumRange (fun i => sumRange (fun j => F i j) (sub n i)) n`
    /// — the Cauchy-product diagonal reindexing: summing `F i j` over the
    /// triangle `{(i,j) : i+j < n}` by ANTIDIAGONAL `k = i+j` (outer bound
    /// `n`, inner index `i` ranging `0..=k` with its partner `k−i`) equals
    /// summing it by ROW `i` (outer bound `n`, inner `j` ranging `0..(n−i)`).
    /// `Nat.sub` appears in both sides' index arithmetic — the diagonal's
    /// partner `k−i` for `i ≤ k`, and the row's remaining budget `n−i` for
    /// `i < n` — but every equation the PROOF uses about it goes through
    /// `succ_sub_of_le`/`sub_self` (the additive round-trip), never through
    /// induction on `sub`'s own recursion. Proved by induction on `n`; see
    /// `nat_prelude/diagonal.rs`'s module doc for why a computationally
    /// subtraction-free statement is not available here (`Exists`'s witness
    /// is not exposed by `Exists.rec`, so `le_dest` cannot supply a VALUE, only
    /// further propositions).
    pub sum_range_diagonal: NameId,

    // --- `rectangle = triangle + corner` (`rectangle.rs`) -------------------
    /// `Nat.sumRange_split : ∀ f m j,
    ///   sumRange f (add m j) = add (sumRange f m) (sumRange (fun k => f (add m k)) j)`
    /// — splitting a finite sum at an arbitrary point, quantified over the
    /// split point `m` and the tail length `j` directly (bound `:= m+j`)
    /// rather than over `m ≤ n`, so the proof (induction on `j`, `f`/`m` held
    /// fixed) never touches `Nat.sub` — the same shape
    /// `Rat.prob_complement`'s private `sum_range_split` uses. ℝ
    /// (`CRealPrelude::sum_range_split`) and ℂ (`ComplexPrelude::sum_range_split`)
    /// already had this; ℕ did not.
    pub sum_range_split: NameId,
    /// `Nat.sumRange_rect_eq_diag_add_corner : ∀ F n,
    ///   sumRange (fun i => sumRange (fun j => F i j) n) n
    ///     = add (sumRange (fun k => sumRange (fun i => F i (sub k i)) (succ k)) n)
    ///           (sumRange (fun i => sumRange (fun k => F i (add (sub n i) k)) i) n)`
    /// — `rectangle = triangle + corner`: the RECTANGLE sum `Σ_{i<n} Σ_{j<n}
    /// F i j` equals the antidiagonal TRIANGLE (`sumRange_diagonal`'s own
    /// LHS, the sum over `{(i,j) : i+j<n}`) plus the CORNER (the sum over
    /// `{(i,j) : i<n, j<n, i+j≥n}`, row `i`'s width-`i` suffix reindexed from
    /// `n−i`). This is the correct replacement for the FALSE naive finite
    /// Cauchy identity `(Σ a)·(Σ b) = Σ_{k<n} Σ_{i≤k} a i · b(k−i)` — false at
    /// `n=2` already, where the rectangle's `a1 b1` term is outside the
    /// triangle. Proved by splitting every row via `sumRange_split` at
    /// `n=(n−i)+i` (pointwise for `i<n`, lifted via `sumRange_congr_lt`),
    /// regrouping via `sumRange_add`, then replacing the row-major half by
    /// the triangle via [`Self::sum_range_diagonal`].
    pub sum_range_rect_eq_diag_add_corner: NameId,

    // --- Vandermonde's convolution (`vandermonde.rs`) -----------------------
    /// `Nat.choose_add_convolution : ∀ m n k, choose (add m n) k = sumRange
    /// (fun i => choose m i * choose n (sub k i)) (succ k)` — Vandermonde's
    /// convolution: binomial coefficients as a convolution algebra. By
    /// induction on `m` (not `n`, and not `m+n`); see `vandermonde.rs`'s
    /// module doc for why that avoids the successor-shape obstruction an
    /// induction on `n` runs into.
    pub choose_add_convolution: NameId,
    /// `Nat.sum_choose_sq : ∀ n, sumRange (fun i => choose n i * choose n i)
    /// (succ n) = choose (add n n) n` — the `m = n = k = n` instance of
    /// [`Self::choose_add_convolution`], via `choose_symm` collapsing
    /// `choose n (sub n i)` to `choose n i` for `i ≤ n`.
    pub sum_choose_sq: NameId,

    /// `Nat.restrict_pair_injective : ∀ σ i j n,
    /// InjectiveOn σ (succ (succ n)) → Lt i j → Lt j (succ (succ n)) →
    /// setwise_fixed σ i j →
    /// InjectiveOn (fun k => compact_pair i j (σ (expand_pair i j k))) n` —
    /// a bijection of `[0, succ (succ n))` fixing `{i,j}` setwise restricts
    /// to an injective self-map of the complement, reindexed to `[0,n)`.
    pub restrict_pair_injective: NameId,
    /// `Nat.restrict_pair_maps_into : ∀ σ i j n,
    /// InjectiveOn σ (succ (succ n)) → MapsInto σ (succ (succ n)) →
    /// Lt i j → Lt j (succ (succ n)) → setwise_fixed σ i j →
    /// MapsInto (fun k => compact_pair i j (σ (expand_pair i j k))) n` — the
    /// companion closure lemma to [`Self::restrict_pair_injective`].
    pub restrict_pair_maps_into: NameId,

    // --- Binary representation (`binary.rs`) ---------------------------------
    /// `Nat.testBitAux : Nat → Nat → Nat`, recursion on the FIRST argument
    /// (the bit index — structural, the fuel route), carrying the second
    /// argument (the number) through unchanged: `testBitAux 0 n ≡ mod n 2`,
    /// `testBitAux (succ i) n ≡ testBitAux i (div n 2)`. Not the public name;
    /// [`Self::test_bit`] flips the argument order to Lean's convention.
    pub test_bit_aux: NameId,
    /// `Nat.testBit n i := testBitAux i n` — the `i`-th binary digit of `n`,
    /// `0` or `1`.
    pub test_bit: NameId,
    /// `Nat.testBit_zero : ∀ n, testBit n 0 = mod n 2` (refl).
    pub test_bit_zero: NameId,
    /// `Nat.testBit_succ : ∀ n i, testBit n (succ i) = testBit (div n 2) i`
    /// (refl — the defining recursion, exposed by name).
    pub test_bit_succ: NameId,
    /// `Nat.testBit_le_one : ∀ n i, Le (testBit n i) 1` — every bit is `0` or
    /// `1`.
    pub test_bit_le_one: NameId,
    /// `Nat.test_bit_of_zero : ∀ i, Eq (testBit 0 i) zero` — every bit of
    /// `0` is `0`. Induction on `i`: base is `testBit_zero` plus `zero_mod`;
    /// step is `testBit_succ` plus `zero_div` (`div zero 2 = zero`, so the
    /// recursive call is at the SAME `0`) applied to the induction
    /// hypothesis.
    pub test_bit_of_zero: NameId,
    /// `Nat.mod_two_mul_split : ∀ n m, Lt 0 m →
    /// add (mul 2 (mod (div n 2) m)) (mod n 2) = mod n (mul m 2)` — peeling
    /// the low bit of `n` before dividing by `m`, the reusable arithmetic
    /// fact `sum_testBit_lt`'s step needs (a general fact, not specific to
    /// `testBit`).
    pub mod_two_mul_split: NameId,
    /// `Nat.sum_testBit_lt : ∀ k n,
    /// sumRange (fun i => mul (testBit n i) (pow 2 i)) k = mod n (pow 2 k)` —
    /// the partial-sum form: the low `k` bits of `n`, read back as a number,
    /// equal `n mod 2^k`.
    pub sum_test_bit_lt: NameId,
    /// `Nat.sizeAux : Nat → Nat → Nat`, `sizeAux fuel n`: recursion on the
    /// FIRST argument (`fuel`, structural — the same fuel route `testBitAux`
    /// uses), with a zero-check Boolean guard on the SECOND argument so the
    /// answer stops changing once `n` hits `0`:
    /// `sizeAux 0 n ≡ 0`; `sizeAux (succ f) n ≡`
    /// `if beq n 0 then 0 else succ (sizeAux f (n / 2))`. Not the public name;
    /// [`Self::size`] supplies fuel `n` itself, which
    /// [`Self::size_aux_lt_pow`] proves is always enough.
    pub size_aux: NameId,
    /// `Nat.size n := sizeAux n n` — the number of binary digits of `n`
    /// (`size 0 = 0`, `size 1 = 1`, `size 13 = 4`, `size 16 = 5`).
    pub size: NameId,
    /// `Nat.size_zero : size 0 = 0` (refl).
    pub size_zero: NameId,
    /// `Nat.size_aux_lt_pow : ∀ fuel n, Le n fuel → Lt n (pow 2 (sizeAux fuel n))`
    /// — for any fuel at least as large as `n`, `sizeAux fuel n` reports enough
    /// bits to bound `n`. This is the fuel-sufficiency fact
    /// [`Self::size`] relies on (specializing at `fuel := n` via `le_refl`
    /// both proves [`Self::lt_pow_size`] and witnesses that `n` itself is
    /// always enough fuel), proved by induction on `fuel` generalized over
    /// `n`, matching [`Self::test_bit_le_one`]/[`Self::sum_test_bit_lt`]'s
    /// shape.
    pub size_aux_lt_pow: NameId,
    /// `Nat.lt_pow_size : ∀ n, Lt n (pow 2 (size n))` — a natural number is
    /// strictly bounded by 2 raised to its own bit count. The
    /// `fuel := n` instance of [`Self::size_aux_lt_pow`].
    pub lt_pow_size: NameId,
    /// `Nat.size_one : Eq (size 1) 1` — `refl`. See `nat_prelude::size_extra`.
    pub size_one: NameId,
    /// `Nat.size_eq_zero : ∀ n, Iff (Eq (size n) 0) (Eq n 0)`. See
    /// `nat_prelude::size_extra`.
    pub size_eq_zero: NameId,
    /// `Nat.mod_eq_self_of_lt : ∀ n m, Lt n m → mod n m = n` — a general
    /// division fact (not specific to binary representation), needed as glue
    /// for [`Self::sum_test_bit_eq`]. Proved by comparing the executable
    /// `divMod` witness against the hand-built witness `(quotient := 0,
    /// remainder := n)` via `div_mod_unique`.
    pub mod_eq_self_of_lt: NameId,
    /// `Nat.sum_testBit_eq : ∀ n,
    /// sumRange (fun i => mul (testBit n i) (pow 2 i)) (size n) = n` — a
    /// natural number IS the sum of its own bits. [`Self::sum_test_bit_lt`]
    /// at `k := size n`, closed by [`Self::lt_pow_size`] and
    /// [`Self::mod_eq_self_of_lt`].
    pub sum_test_bit_eq: NameId,
    /// `Nat.sumRange_const_zero : ∀ k, sumRange (fun _ => zero) k = zero` —
    /// a reusable arithmetic fact (not specific to `testBit`), by induction
    /// on `k`: `sumRange_zero` closes the base; the step
    /// `sumRange g (succ j) = sumRange g j + g j` collapses via the
    /// induction hypothesis to `add zero zero`, which is `refl` (`add_zero`
    /// at `n := zero`).
    pub sum_range_const_zero: NameId,
    /// `Nat.zero_of_testBit_eq_zero : ∀ n, (∀ i, testBit n i = zero) → n =
    /// zero` — the Nat-valued analogue of Mathlib's
    /// `Nat.zero_of_testBit_eq_false` (`(∀ i, n.testBit i = false) → n =
    /// 0`), NOT a proof of that Bool-typed statement: our `testBit` returns
    /// `{0,1} : Nat`, a genuinely different codomain (see `binary.rs`'s
    /// module doc and `docs/plan/status/235-nat-bitwise-facts.md`), so this
    /// is registered as its own local fact rather than used to flip the
    /// pinned `ml430` mirror. Proved via [`Self::sum_test_bit_eq`]: the
    /// hypothesis makes every summand `mul (testBit n i) (pow 2 i)`
    /// collapse to `zero` (via [`Self::zero_mul`]), so
    /// [`Self::sum_range_congr`] plus [`Self::sum_range_const_zero`] gives
    /// `sumRange … (size n) = zero`, which `sum_testBit_eq` identifies with
    /// `n` itself.
    pub zero_of_test_bit_eq_zero: NameId,

    // --- Fibonacci numbers (`fibonacci.rs`) ----------------------------------
    /// `Nat.fibAux : Nat -> Nat -> Nat -> Nat`, `fibAux i a b`: recursion on
    /// the FIRST argument `i` (the fuel/step-count — structural), threading
    /// TWO ordinary curried `Nat` parameters `a b` through as the accumulator
    /// pair (there is no tuple type in this kernel; two curried parameters
    /// serve the same purpose without one — see `fibonacci.rs`'s module doc
    /// for why the `And`-pairing trick used to prove properties TOGETHER by
    /// ordinary `Nat.rec` does not by itself give a way to DEFINE a
    /// `Nat`-valued function). `fibAux 0 a b ≡ a`; `fibAux (succ i) a b ≡
    /// fibAux i b (add a b)`. Not the public name; [`Self::fib`] supplies the
    /// seed `(0, 1)`.
    pub fib_aux: NameId,
    /// `Nat.fib n := fibAux n 0 1` — the Fibonacci numbers. `fib 0 ≡ 0`,
    /// `fib 1 ≡ 1` by pure `δ`/`ι` reduction (no theorem needed);
    /// `fib (n+2) = fib (n+1) + fib n` is [`Self::fib_add_two`], which is
    /// NOT a bare `δ`/`ι` fact (see its own doc).
    pub fib: NameId,
    /// `Nat.fib_add_two : ∀ n, fib (succ (succ n)) = add (fib (succ n)) (fib n)`
    /// — the defining recurrence, stated over `fib` rather than `fibAux`.
    /// Proved from a STRONGER internal fact generalized over the accumulator
    /// seed (`∀ i a b, fibAux (succ (succ i)) a b = add (fibAux (succ i) a b)
    /// (fibAux i a b)`, built by `fibonacci.rs`'s private
    /// `fib_aux_add_two_gen` and specialized at `a=0, b=1` — the general
    /// statement's induction step closes by defeq alone (the induction
    /// hypothesis applied at the shifted seed `(b, a+b)` already has the
    /// exact type the goal unfolds to); only the base case needs an actual
    /// rewrite, `add_comm`.
    pub fib_add_two: NameId,
    /// `Nat.fib_le_succ : ∀ n, Le (fib n) (fib (succ n))` — the Fibonacci
    /// sequence is non-decreasing. By induction on `n`; the base case is
    /// `zero_le`, and the step needs no induction hypothesis at all —
    /// `fib_add_two` plus `le_add_right` gives it unconditionally.
    pub fib_le_succ: NameId,
    /// `Nat.fib_mono : ∀ a b, Le a b → Le (fib a) (fib b)` — composed from
    /// `fib_le_succ` by induction on the `Le a b` derivation.
    pub fib_mono: NameId,
    /// `Nat.fib_pos_of_pos : ∀ n, Lt zero n → Lt zero (fib n)` — every `fib`
    /// value past the zeroth is positive. From the unconditional `∀ i, Lt
    /// zero (fib (succ i))` (induction on `i`, base `le_refl`, step
    /// `fib_le_succ` chained through `lt_of_lt_of_le`), transported along
    /// `pos_implies_succ_pred` (`finite.rs`) to discharge the hypothesis.
    pub fib_pos_of_pos: NameId,
    /// `Nat.sum_fib : ∀ n, sumRange fib n = sub (fib (succ n)) one` —
    /// `Σ_{i<n} fib i = fib(n+1) - 1`. Proved from the SUBTRACTION-FREE
    /// internal fact `∀ n, add (sumRange fib n) 1 = fib (succ n)`
    /// (`sum_fib_add_one_gen`, straight induction using `add_right_comm` and
    /// `fib_add_two`), converted to the truncated-subtraction form by
    /// `add_comm` + `add_sub_cancel_left` — `Nat.sub` never drives an
    /// induction step here, only the final one-line conversion.
    pub sum_fib: NameId,
    /// `Nat.fib_add : ∀ m n, fib (succ (add m n)) =
    /// add (mul (fib m) (fib n)) (mul (fib (succ m)) (fib (succ n)))` — the
    /// Fibonacci addition formula, `succ`-shaped so `Nat.sub` never appears.
    /// Proved by pairing `stmt_at n` with `stmt_at (succ n)` and inducting
    /// ordinarily on `n` — the device `fibonacci.rs`'s own module doc names
    /// for PROVING a proposition about two indices at once, as opposed to
    /// DEFINING a function, which is why it was ruled out for `fib` itself.
    /// The successor step folds two `fib_add_two` applications together
    /// through `left_distrib` and a private four-term commutative regroup
    /// (`add_regroup_four`; this prelude has no `add_add_add_comm`).
    pub fib_add: NameId,
    /// `Nat.coprime_fib_succ : ∀ n, gcd (fib n) (fib (succ n)) = 1` —
    /// consecutive Fibonacci numbers are coprime. Induction on `n`; the step
    /// never computes the new `gcd` equation, it shows the new gcd divides
    /// `1` (via `gcd_dvd`, `fib_add_two`, `dvd_add_iff_right`, `dvd_gcd` and
    /// the induction hypothesis) and closes with `eq_one_of_dvd_one`.
    pub coprime_fib_succ: NameId,
    /// `Nat.fib_add_two_strictmono : ∀ a b, Lt a b → Lt (fib (succ (succ a)))
    /// (fib (succ (succ b)))` — the shifted-by-two Fibonacci sequence is
    /// strictly increasing everywhere (Mathlib's `StrictMono (fun n => fib
    /// (n+2))`, instantiated concretely rather than through an abstract
    /// `StrictMono` combinator, matching `fib_mono`'s own style). Induction
    /// on `b`, mirroring `perfect.rs`'s `pow_lt_pow_of_lt` exactly (base:
    /// `Lt a zero` is impossible via `not_lt_zero`; step: split `Le a b'`
    /// into `Lt a b'` or `Eq a b'` via `lt_or_eq_of_le`) but with NO base
    /// hypothesis to thread, because the adjacent step here
    /// (`fib_add_two_lt_succ`, private) holds unconditionally for every `n`
    /// — unlike `pow`'s, which needs the base `> 1`.
    pub fib_add_two_strictmono: NameId,
    /// `Nat.fib_strictmonoOn : ∀ a b, Le 2 a → Le 2 b → Lt a b → Lt (fib a)
    /// (fib b)` — Mathlib's `StrictMonoOn Nat.fib (Set.Ici 2)`, unwound to
    /// two explicit lower-bound hypotheses. Peels two `succ`s off both `a`
    /// and `b` (`Le 2 x` gives `Lt 0 x`, `pos_implies_succ_pred` applied
    /// twice — the second application needs `Le 2 x` transported along the
    /// first `x = succ x1` and stripped by `le_of_succ_le_succ` to get
    /// `Lt 0 x1`) to land on `fib_add_two_strictmono`'s shifted form, then
    /// transports the conclusion back along the two recovered equalities.
    pub fib_strictmonoon: NameId,
    /// `Nat.fib_lt_fib : ∀ m n, Le 2 m → Iff (Lt (fib m) (fib n)) (Lt m n)` —
    /// Mathlib's `Nat.fib_lt_fib_iff` (`2 ≤ m → (fib m < fib n ↔ m < n)`).
    /// Reverse direction is `fib_strictmonoOn` at `(m, n)`, needing `Le 2 n`
    /// derived from `Le 2 m` and `Lt m n` (weakened to `Le m n`) by
    /// transitivity. Forward direction is the contrapositive: case on
    /// `lt_or_ge m n` (private `or_elim`/`absurd`, mirroring
    /// `irrational.rs`'s copies); the `Le n m` branch feeds `fib_mono` to get
    /// `Le (fib n) (fib m)`, which contradicts the hypothesis `Lt (fib m)
    /// (fib n)` via `lt_of_lt_of_le` + `lt_irrefl`.
    pub fib_lt_fib: NameId,
    /// `Nat.le_fib_self : ∀ n, Le 5 n → Le n (fib n)` — Mathlib's
    /// `Nat.le_fib_self` (`5 ≤ n → n ≤ fib n`). Proved from an unexposed,
    /// index-shifted helper `∀ k, Le (5+k) (fib (5+k))` (pair-induction on
    /// `k`, mirroring `fib_add`'s own `stmt_at k / stmt_at (succ k)` device:
    /// the step sums the two induction-hypothesis inequalities via
    /// `add_le_add_left`/`add_le_add_right` + `le_trans`, then absorbs the
    /// `+1` slack the sum carries — `(5+k)+(6+k) > 6+k` since `5+k ≥ 1` —
    /// through `lt_add_one` + `add_le_add_left` + `lt_of_lt_of_le`, and
    /// converts `fib(5+k)+fib(6+k)` to `fib(7+k)` via `add_comm` and
    /// `fib_add_two` (reversed)), then instantiated at the hypothesis's own
    /// witness (`le_dest` gives `k` with `5+k=n`; `Exists.rec` transports the
    /// shifted fact along that equation to land on the goal at `n`).
    pub le_fib_self: NameId,
    /// `Nat.le_fib_add_one : ∀ n, Le n (add (fib n) 1)` — Mathlib's
    /// `Nat.le_fib_add_one` (`n ≤ fib n + 1`), unconditional (unlike
    /// [`le_fib_self`](Self::le_fib_self), whose `5 ≤ n` hypothesis this one
    /// has no room for: the bound is TIGHT — equality — at `n = 2, 3, 4`, so
    /// no bare induction from `n = 0` can close the step for small `n`; any
    /// slack margin needs `n` past the threshold where `le_fib_self` already
    /// applies). Split at `Nat.lt_or_ge n 5`
    /// ([`ops::cases_lt_or_ge`](super::ops::cases_lt_or_ge)): the `Le 5 n`
    /// side chains `le_fib_self` with `le_add_right (fib n) 1`; the `Lt n 5`
    /// side is a genuine 5-way case split down to concrete `n ∈ {0,1,2,3,4}`
    /// ([`ops::cases_lt_bound`](super::ops::cases_lt_bound)), each branch
    /// closed the same way [`le_fib_self`](Self::le_fib_self)'s own base
    /// case is — `Le i (add i k)` (`le_add_right`, or `zero_le` for `i = 0`)
    /// defeq to `Le i (add (fib i) 1)` by pure `δ`/`ι` unfolding of `fib` at
    /// the tiny literal `i`.
    pub le_fib_add_one: NameId,

    // --- relation properties bounded on `n` (`relation.rs`) -----------------
    /// `Nat.ReflexiveOn r n := ∀ i, i < n → r i i`, for `r : Nat → Nat → Prop`.
    pub reflexive_on: NameId,
    /// `Nat.SymmetricOn r n := ∀ i j, i < n → j < n → r i j → r j i`.
    pub symmetric_on: NameId,
    /// `Nat.TransitiveOn r n := ∀ i j k, i < n → j < n → k < n → r i j →
    /// r j k → r i k`.
    pub transitive_on: NameId,
    /// `Nat.EquivalenceOn r n := ReflexiveOn r n ∧ SymmetricOn r n ∧
    /// TransitiveOn r n` (right-nested `And`).
    pub equivalence_on: NameId,
    /// `Nat.eq_equivalence_on : ∀ n, EquivalenceOn (Eq Nat) n` — equality is
    /// an equivalence relation, the canonical worked instance.
    pub eq_equivalence_on: NameId,
    /// `Nat.modEq_equivalence_on : ∀ m n, EquivalenceOn (Nat.modEq m) n` —
    /// congruence mod `m` is an equivalence relation; connects this L0 node
    /// to the `modular-arithmetic` L2 node.
    pub mod_eq_equivalence_on: NameId,
    /// `Nat.BijectiveOn f n := InjectiveOn f n ∧ MapsInto f n ∧
    /// SurjectiveOn f n`.
    pub bijective_on: NameId,
    /// `Nat.bijective_of_injective_on : ∀ n f, InjectiveOn f n →
    /// MapsInto f n → BijectiveOn f n` — packaging over
    /// [`Self::injective_on_imp_surjective_on`] (`finite.rs`).
    pub bijective_of_injective_on: NameId,
    /// `Nat.comp f g := fun x => f (g x)`.
    pub comp: NameId,
    /// `Nat.injective_on_comp : ∀ n f g, MapsInto g n → InjectiveOn g n →
    /// InjectiveOn f n → InjectiveOn (comp f g) n`.
    pub injective_on_comp: NameId,

    // --- finite sets over a bounded universe (`finite_set.rs`) --------------
    // Curriculum node `sets` (Layer 0, docs/curriculum/00-foundations/sets.md).
    /// `Nat.setUnion p q := fun k => if p k then true else q k`.
    pub set_union: NameId,
    /// `Nat.setInter p q := fun k => if p k then q k else false`.
    pub set_inter: NameId,
    /// `Nat.setCompl p := fun k => if p k then false else true`.
    pub set_compl: NameId,
    /// `Nat.setDiff p q := fun k => if p k then (if q k then false else true) else false`
    /// — `p k ∧ ¬ q k`.
    pub set_diff: NameId,
    /// `Nat.Subset p q n := ∀ k, k < n → p k = true → q k = true` — a
    /// `Prop`-valued `Definition`, the same shape
    /// [`Self::injective_on`] already uses.
    pub subset: NameId,
    /// `Nat.countRange_union_add_inter : ∀ p q n,
    ///   countRange (setUnion p q) n + countRange (setInter p q) n =
    ///   countRange p n + countRange q n` — the two-set inclusion–exclusion
    /// law, stated additively (`Nat.sub` is truncated).
    pub count_range_union_add_inter: NameId,
    /// `Nat.countRange_le_of_subset : ∀ p q n,
    ///   Subset p q n → countRange p n ≤ countRange q n` — cardinality
    /// monotonicity.
    pub count_range_le_of_subset: NameId,
    /// `Nat.countRange_compl : ∀ p n,
    ///   countRange p n + countRange (setCompl p) n = n`.
    pub count_range_compl: NameId,

    // --- the two-bound pigeonhole (`cardinality.rs`) -------------------------
    // Curriculum node `cardinality` (Layer 0,
    // docs/curriculum/00-foundations/cardinality.md).
    /// `Nat.pigeonhole : ∀ n m f, Lt n m → (∀ i, i < m → f i < n) →
    /// InjectiveOn f m → False` — no injection from an `m`-set into a
    /// (strictly smaller) `n`-set. Not the same statement as
    /// [`Self::injective_on_imp_surjective_on`] (`finite.rs`), which is a
    /// SELF-map on one shared bound; this one crosses two bounds and is
    /// proved by reducing to that self-map lemma (see `cardinality.rs`'s
    /// module doc).
    pub pigeonhole: NameId,
    // --- pointwise Boolean-lattice laws for finite sets (`finite_set.rs`) --
    // The `sets` curriculum node's own claim: "the same Boolean laws as in
    // propositional logic, one level up". Every statement here is pointwise
    // (`∀ k, … p k … = … q k …`), not an equality of functions — this kernel
    // has no `funext`.
    /// `Nat.setUnion_comm : ∀ p q k, Eq Bool (setUnion p q k) (setUnion q p k)`.
    pub set_union_comm: NameId,
    /// `Nat.setInter_comm : ∀ p q k, Eq Bool (setInter p q k) (setInter q p k)`.
    pub set_inter_comm: NameId,
    /// `Nat.setUnion_assoc : ∀ p q r k,
    ///   Eq Bool (setUnion (setUnion p q) r k) (setUnion p (setUnion q r) k)`.
    pub set_union_assoc: NameId,
    /// `Nat.setInter_assoc : ∀ p q r k,
    ///   Eq Bool (setInter (setInter p q) r k) (setInter p (setInter q r) k)`.
    pub set_inter_assoc: NameId,
    /// `Nat.setUnion_idem : ∀ p k, Eq Bool (setUnion p p k) (p k)`.
    pub set_union_idem: NameId,
    /// `Nat.setInter_idem : ∀ p k, Eq Bool (setInter p p k) (p k)`.
    pub set_inter_idem: NameId,
    /// `Nat.setInter_union_distrib : ∀ p q r k,
    ///   Eq Bool (setInter p (setUnion q r) k)
    ///           (setUnion (setInter p q) (setInter p r) k)`.
    pub set_inter_union_distrib: NameId,
    /// `Nat.setUnion_inter_distrib : ∀ p q r k,
    ///   Eq Bool (setUnion p (setInter q r) k)
    ///           (setInter (setUnion p q) (setUnion p r) k)`.
    pub set_union_inter_distrib: NameId,
    /// `Nat.setUnion_absorb : ∀ p q k, Eq Bool (setUnion p (setInter p q) k) (p k)`.
    pub set_union_absorb: NameId,
    /// `Nat.setInter_absorb : ∀ p q k, Eq Bool (setInter p (setUnion p q) k) (p k)`.
    pub set_inter_absorb: NameId,
    /// `Nat.setCompl_union : ∀ p q k,
    ///   Eq Bool (setCompl (setUnion p q) k) (setInter (setCompl p) (setCompl q) k)`.
    pub set_compl_union: NameId,
    /// `Nat.setCompl_inter : ∀ p q k,
    ///   Eq Bool (setCompl (setInter p q) k) (setUnion (setCompl p) (setCompl q) k)`.
    pub set_compl_inter: NameId,
    /// `Nat.setCompl_involutive : ∀ p k, Eq Bool (setCompl (setCompl p) k) (p k)`.
    pub set_compl_involutive: NameId,
    // --- groups (`group.rs`) -------------------------------------------------
    // Curriculum node `groups` (Layer 2, docs/curriculum/02-structures/groups.md).
    /// `Nat.IsGroupOn (op : Nat → Nat → Nat) (e : Nat) (inv : Nat → Nat) (n :
    /// Nat) : Prop := closure ∧ (associativity ∧ (identity ∧ inverse))`, all
    /// bounded on `n`. The bundled-predicate shape `Rat.IsDistribution`
    /// already uses (this kernel has no typeclasses).
    pub is_group_on: NameId,
    /// `Nat.group_identity_unique : IsGroupOn op e inv n → ∀ e', e'<n →
    /// (∀ a, a<n → op a e' = a) → e' = e`.
    pub group_identity_unique: NameId,
    /// `Nat.group_inverse_unique : IsGroupOn op e inv n → ∀ a b c,
    /// a<n→b<n→c<n → op b a=e → op a c=e → b=c` — a left inverse of `a`
    /// equals a right inverse of `a`.
    pub group_inverse_unique: NameId,
    /// `Nat.group_left_cancel : IsGroupOn op e inv n → ∀ a b c,
    /// a<n→b<n→c<n → op a b=op a c → b=c`.
    pub group_left_cancel: NameId,
    /// `Nat.modAdd_isGroup : ∀ n, 0<n → IsGroupOn (fun a b => mod (add a b)
    /// n) 0 (fun a => mod (sub n a) n) n` — ℤ/n under addition, the worked
    /// instance.
    pub mod_add_is_group: NameId,
    /// `Nat.subset_refl : ∀ f n, Subset f f n` — reflexivity.
    pub subset_refl: NameId,
    /// `Nat.subset_trans : ∀ f g h n, Subset f g n → Subset g h n →
    /// Subset f h n` — transitivity.
    pub subset_trans: NameId,
    /// `Nat.subset_antisymm : ∀ f g n, Subset f g n → Subset g f n →
    /// ∀ k, k < n → Eq Bool (f k) (g k)` — antisymmetry, POINTWISE (this
    /// kernel has no `funext`).
    pub subset_antisymm: NameId,
    /// `Nat.setDiff_eq_inter_compl : ∀ f g k,
    ///   Eq Bool (setDiff f g k) (setInter f (setCompl g) k)` — `setDiff` is
    /// literally `setInter` composed with `setCompl`.
    pub set_diff_eq_inter_compl: NameId,
    /// `Nat.union_eq_right_of_subset : ∀ f g n, Subset f g n →
    ///   ∀ k, k < n → Eq Bool (setUnion f g k) (g k)` — the lattice–order
    /// bridge: union with a superset is the superset.
    pub union_eq_right_of_subset: NameId,
    /// `Nat.subset_union_left : ∀ f g n, Subset f (setUnion f g) n`.
    pub subset_union_left: NameId,
    /// `Nat.subset_inter_left : ∀ f g n, Subset (setInter f g) f n`.
    pub subset_inter_left: NameId,

    // --- the symmetric group's missing piece (`permutation.rs`) --------------
    // Curriculum node `groups` (Layer 2): the second worked instance of
    // `IsGroupOn`'s *representation problem* — `Nat.comp`/`Nat.id` are the
    // right operation/identity for permutations, and this is the explicit
    // inverse construction `IsGroupOn`'s bundled `inv : Nat → Nat` (function
    // case: `(Nat→Nat)→(Nat→Nat)`) actually needs, since `Exists.rec`
    // eliminates only into `Prop`.
    /// `Nat.permInverse (f : Nat → Nat) (n k : Nat) : Nat` — a bounded
    /// downward search: the least index found scanning `n-1, …, 0` with
    /// `f i = k`, `0` if none is found (never reached under
    /// [`Self::perm_inverse_left`]/[`Self::perm_inverse_right`]'s
    /// hypotheses).
    pub perm_inverse: NameId,
    /// `Nat.permInverse_right : ∀ f n, SurjectiveOn f n → ∀ k, k < n →
    /// f (permInverse f n k) = k` — `f ∘ permInverse f n` is the identity
    /// on `[0,n)`, a genuine right inverse.
    pub perm_inverse_right: NameId,
    /// `Nat.permInverse_left : ∀ f n, MapsInto f n → InjectiveOn f n →
    /// ∀ i, i < n → permInverse f n (f i) = i` — `permInverse f n ∘ f` is
    /// the identity on `[0,n)`, a genuine left inverse. Needs no
    /// `SurjectiveOn`: `i` is already its own existence witness.
    pub perm_inverse_left: NameId,
    /// `Nat.id : Nat → Nat := fun x => x` — the identity self-map,
    /// `IsGroupOnFn`'s `e`.
    pub id: NameId,
    /// `Nat.comp_assoc : ∀ f g h, comp (comp f g) h = comp f (comp g h)` —
    /// the associativity conjunct an `IsGroupOnFn` predicate over `Nat.comp`
    /// would need, proved by `Eq.refl` (both sides delta/beta-reduce to the
    /// same literal lambda — no `funext`).
    pub comp_assoc: NameId,
    /// `Nat.IsGroupOnFn (op : (Nat→Nat)→(Nat→Nat)→(Nat→Nat)) (e : Nat→Nat)
    /// (inv : (Nat→Nat)→(Nat→Nat)) (n : Nat) : Prop := closure ∧
    /// (associativity ∧ (identity ∧ inverse))` — `group.rs::IsGroupOn`
    /// generalised to function-valued elements, `BijectiveOn · n` standing
    /// in for `· < n` as carrier membership (representation option (a) from
    /// this slice's brief: a permutation is a `Nat → Nat`, not a `Nat`).
    pub is_group_on_fn: NameId,
    /// `Nat.bijective_on_comp : ∀ n a b, BijectiveOn a n → BijectiveOn b n →
    /// BijectiveOn (comp a b) n` — composition of self-maps preserves
    /// bijectivity on the same bound, `IsGroupOnFn`'s closure conjunct over
    /// `Nat.comp`. Injectivity is `Nat.injective_on_comp` applied directly;
    /// `MapsInto` composes with no case split; surjectivity destructures both
    /// witnesses via nested `Exists.rec`.
    pub bijective_on_comp: NameId,
    /// `Nat.bijective_on_perm_inverse : ∀ n f, BijectiveOn f n →
    /// BijectiveOn (permInverse f n) n` — the inverse of a bijection on
    /// `[0,n)` is itself one. Injectivity of `permInverse f n` follows
    /// because `f` is its own left inverse on `[0,n)` (`permInverse_right`);
    /// `MapsInto` is `permInverse`'s own unconditional bound
    /// (`permInverse f n k < n` for **any** `k`, given `0 < n`); surjectivity
    /// picks `f k` as the preimage of `k` (`permInverse_left`).
    pub bijective_on_perm_inverse: NameId,
    /// `Nat.EqOn (f g : Nat → Nat) (n : Nat) : Prop := ∀ i, i < n →
    /// Eq Nat (f i) (g i)` — bounded function equality, the fix for
    /// `IsGroupOnFn`'s `identity`/`inverse` conjuncts (see `permutation.rs`'s
    /// module doc, "The full `IsGroupOnFn` instance WAS REFUTED"): unbounded
    /// `Eq (Nat → Nat)` is unsatisfiable for `Nat.permInverse` outside
    /// `[0,n)`, and this kernel has no `funext` to state one differently.
    pub eq_on: NameId,
    /// `Nat.eqOn_refl : ∀ f n, EqOn f f n`.
    pub eq_on_refl: NameId,
    /// `Nat.eqOn_symm : ∀ f g n, EqOn f g n → EqOn g f n`.
    pub eq_on_symm: NameId,
    /// `Nat.eqOn_trans : ∀ f g h n, EqOn f g n → EqOn g h n → EqOn f h n`.
    pub eq_on_trans: NameId,
    /// `Nat.symmetric_group_isGroupOnFn : ∀ n, IsGroupOnFn Nat.comp Nat.id
    /// (fun f => Nat.permInverse f n) n` — the symmetric group on `[0,n)`,
    /// permutations under composition, the instance `IsGroupOnFn`'s original
    /// unbounded form refuted, landed once `identity`/`inverse` were
    /// rebuilt on `Nat.EqOn`.
    pub symmetric_group_is_group_on_fn: NameId,

    // --- factorization (`factorization.rs`) — FTA, existence half -----------
    /// `Nat.prodRange : (Nat → Nat) → Nat → Nat` — structural recursion on the
    /// `Nat` bound, mirroring [`Self::sum_range`]: `prodRange f zero ≡ one`
    /// and `prodRange f (succ n) ≡ mul (prodRange f n) (f n)`.
    pub prod_range: NameId,
    /// `Nat.prodRange_zero : ∀ f, Eq (prodRange f zero) one` — closes by
    /// `Eq.refl` since the equation is definitional.
    pub prod_range_zero: NameId,
    /// `Nat.prodRange_succ : ∀ f n, Eq (prodRange f (succ n))
    ///   (mul (prodRange f n) (f n))` — closes by `Eq.refl`.
    pub prod_range_succ: NameId,
    /// `Nat.exists_prime_factorization : ∀ n, Le two n → ∃ k f,
    ///   (∀ i, Lt i k → (Le two (f i) ∧ ∀ c, dvd c (f i) → Or (Eq c one)
    ///   (Eq c (f i)))) ∧ Eq (prodRange f k) n` — the existence half of the
    /// Fundamental Theorem of Arithmetic: every `n ≥ 2` is the product of `k`
    /// primes named by `f` on `[0,k)`. Primality is spelled inline, matching
    /// [`Self::exists_prime_dvd`]'s own convention (this prelude has no
    /// `Prime` predicate). Proved by well-founded induction on `Nat.lt`
    /// (`Self::lt_well_founded`, generic `WellFounded.fix`): `n`'s least
    /// prime divisor `p` (`Self::exists_prime_dvd`) either equals `n` (`n`
    /// itself is prime, `k := 1`) or is a proper divisor, in which case the
    /// cofactor `n / p` is `2 ≤ · < n` and the induction hypothesis supplies
    /// its factorization, extended by prepending `p`. There is no `List`,
    /// `Finset`, or product type in this kernel, so uniqueness (the multiset
    /// of prime factors) is not expressible here — only existence is stated.
    pub exists_prime_factorization: NameId,

    // --- Chinese Remainder Theorem, uniqueness half (`crt.rs`) --------------
    /// `Nat.coprime_mul_dvd : ∀ m n k, Eq (gcd m n) one → dvd m k → dvd n k →
    ///   dvd (mul m n) k` — coprime divisors of a common value combine into a
    /// divisor of their product. `lcm m n = m*n` under coprimality
    /// ([`Self::coprime_lcm_eq_mul`]) transported along [`Self::lcm_dvd`].
    pub coprime_mul_dvd: NameId,
    /// `Nat.crt_unique : ∀ m n x y, Eq (gcd m n) one → modEq m x y →
    ///   modEq n x y → modEq (mul m n) x y` — the Chinese Remainder Theorem's
    /// uniqueness half. Existence is declined for ℕ (see `crt.rs`'s module
    /// doc): the classical witness needs the signed Bézout coefficients
    /// `Nat.bezout`'s balanced form exists precisely to avoid resolving;
    /// `Int.crt_exists` (`int_prelude/crt.rs`) already proves it over ℤ,
    /// axiom-free.
    pub crt_unique: NameId,
    /// `Nat.mod_lcm : ∀ n m x y, modEq n x y → modEq m x y →
    ///   modEq (lcm n m) x y` — combining two congruences into their lcm's,
    /// **unconditionally** (no coprimality hypothesis, unlike
    /// [`crt_unique`](Self::crt_unique)): the divisibility combination step
    /// is [`lcm_dvd`](Self::lcm_dvd), which is already unconditional.
    /// Closes ledger fact `F:ml430-nat-mod-lcm`.
    pub mod_lcm: NameId,
    // --- exponentiation by squaring (`powsq.rs`) -----------------------------
    /// `Nat.powSqAux : Nat → Nat → Nat → Nat`, `powSqAux fuel b e`: structural
    /// `Nat.rec` on `fuel` (the only structural parameter — the true
    /// recursion is on `e/2`, not on `e`, so it needs fuel or well-founded
    /// recursion; see the module doc for why fuel was chosen). `powSqAux 0 b
    /// e ≡ 1`; `powSqAux (succ f) b e ≡ if beq e 0 then 1 else let h :=
    /// powSqAux f b (e/2) in if beq (e%2) 0 then h*h else h*h*b`. Not the
    /// public name; [`Self::pow_sq`] supplies `fuel := e`.
    pub pow_sq_aux: NameId,
    /// `Nat.powSq b e := powSqAux e b e` — exponentiation by squaring. `e`
    /// itself is always enough fuel ([`Self::pow_sq_eq_pow`]).
    pub pow_sq: NameId,
    /// `Nat.pow_half_split : ∀ b e, Eq (pow b e) (bool_select_nat (beq (mod e
    /// two) 0) (mul (pow b (div e two)) (pow b (div e two))) (mul (mul (pow b
    /// (div e two)) (pow b (div e two))) b))` — pure arithmetic about
    /// `Nat.pow`/`div`/`mod`, no fuel or induction hypothesis, true uniformly
    /// including at `e = 0`. The reusable core both
    /// [`Self::pow_sq_aux_eq_pow`]'s induction step and [`Self::pow_sq_succ`]
    /// consume.
    pub pow_half_split: NameId,
    /// `Nat.even_or_odd : ∀ n, Or (Eq n (add (div n 2) (div n 2)))
    /// (Eq n (succ (add (div n 2) (div n 2))))` — the decidable-parity split
    /// with a COMPUTED half `div n 2` (never an existential witness, since
    /// `Exists.rec` is `Prop`-only and cannot produce a term whose type
    /// mentions the extracted witness). Built from the same
    /// `div_mod_exec` + `Bool.rec` construction [`Self::pow_half_split`]
    /// already performs internally (its `e_eq_final` intermediate, in each
    /// branch, IS this fact) — extracted as its own reusable theorem because
    /// `creal/alternating.rs` needs exactly this to bridge an arbitrary `Nat`
    /// index to the even-indexed/odd-indexed partial sum it is closest to,
    /// and `nat_prelude/fibonacci.rs`'s module doc names the same gap for
    /// Cassini's identity.
    pub even_or_odd: NameId,
    /// `Nat.pow_sq_aux_eq_pow : ∀ fuel b e, Le e fuel → powSqAux fuel b e =
    /// pow b e` — sufficiency implies correctness, proved by induction on
    /// `fuel` (NOT the `sizeAux n n = sizeAux (succ n) n` fuel-vs-fuel shape
    /// a prior handover flagged as the wrong statement — see the module doc).
    /// Specializing at `fuel := e` via `le_refl` gives
    /// [`Self::pow_sq_eq_pow`].
    pub pow_sq_aux_eq_pow: NameId,
    /// `Nat.pow_sq_eq_pow : ∀ b e, powSq b e = pow b e` — `e` is always
    /// sufficient fuel for `powSq b e := powSqAux e b e`. The correctness
    /// theorem the handover asked for; [`Self::pow_sq_zero`] and
    /// [`Self::pow_sq_succ`] are read off it rather than proved directly
    /// against `powSqAux`'s raw unfolding.
    pub pow_sq_eq_pow: NameId,
    /// `Nat.pow_sq_zero : ∀ b, powSq b 0 = 1`.
    pub pow_sq_zero: NameId,
    /// `Nat.pow_sq_succ : ∀ b k, powSq b (succ k) = bool_select_nat (beq
    /// ((succ k) % 2) 0) (mul (powSq b ((succ k)/2)) (powSq b ((succ k)/2)))
    /// (mul (mul (powSq b ((succ k)/2)) (powSq b ((succ k)/2))) b)` — `powSq`'s
    /// own second defining equation, over `powSq` itself (not `powSqAux`).
    pub pow_sq_succ: NameId,

    // --- subset product (`subset_product.rs`) — product over a
    // predicate-defined subset of `[0,n)` -----------------------------------
    /// `Nat.prodRangeIf (p : Nat → Bool) (f : Nat → Nat) (n : Nat) : Nat :=
    /// prodRange (fun i => bool_select_nat (p i) (f i) 1) n` — the product
    /// over `i < n` of `f i` when `p i` holds and `1` (the multiplicative
    /// identity) otherwise, i.e. the product side of the `Nat.countRange`
    /// pattern (a fold over a `Bool`-valued predicate-defined subset of
    /// `[0,n)`). Defined in terms of the already-declared [`Self::prod_range`]
    /// rather than a fresh `Nat.rec`, so its defining equations are pure
    /// `Eq.refl` (delta into `prodRange`'s own iota reduction), exactly as
    /// `Nat.totient` is defined in terms of `Nat.countRange`.
    pub prod_range_if: NameId,
    /// `Nat.prodRangeIf_zero : ∀ p f, Eq Nat (prodRangeIf p f zero) 1` —
    /// closes by `Eq.refl`.
    pub prod_range_if_zero: NameId,
    /// `Nat.prodRangeIf_succ : ∀ p f n, Eq Nat (prodRangeIf p f (succ n))
    /// (mul (prodRangeIf p f n) (bool_select_nat (p n) (f n) 1))` — closes by
    /// `Eq.refl`.
    pub prod_range_if_succ: NameId,
    /// `Nat.prodRangeIf_congr_lt : ∀ p q f g n, (∀ i, Lt i n → Eq Bool (p i)
    /// (q i)) → (∀ i, Lt i n → Eq Nat (f i) (g i)) → Eq Nat (prodRangeIf p f
    /// n) (prodRangeIf q g n)` — `p` and `f` agreeing pointwise below `n`
    /// (against `q`/`g` respectively) gives equal products. Bounded (`Lt i
    /// n`), matching [`Self::sum_range_congr_lt`]'s convention rather than
    /// [`Self::count_range_congr`]'s unconditional one, since a predicate
    /// subset built from a partial operator (e.g. truncated subtraction)
    /// typically only agrees within the range.
    pub prod_range_if_congr_lt: NameId,
    /// `Nat.injectiveOnP p f n := ∀ i j, i<n → j<n → p i=true → p j=true →
    /// f i=f j → i=j` — [`Self::injective_on`] restricted to the `p`-subset
    /// of `[0,n)`.
    pub injective_on_p: NameId,
    /// `Nat.mapsIntoP p f n := ∀ i, i<n → p i=true → f i<n ∧ p (f i)=true`
    /// — a SELF-map of the `p`-subset, not merely into `[0,n)`.
    pub maps_into_p: NameId,
    /// `Nat.surjectiveOnP p f n := ∀ k, k<n → p k=true → ∃ i, i<n ∧
    /// p i=true ∧ f i=k`.
    pub surjective_on_p: NameId,
    /// `Nat.injective_on_p_imp_surjective_on_p : ∀ p f n, InjectiveOnP p f n
    /// → MapsIntoP p f n → SurjectiveOnP p f n` — the predicate-scoped
    /// pigeonhole, by reduction to [`Self::injective_on_imp_surjective_on`]
    /// (`finite.rs`) via the identity-outside-`S` extension of `f`
    /// (`subset_product.rs`'s module doc).
    pub injective_on_p_imp_surjective_on_p: NameId,
    /// `Nat.sumDivisors n := sumRange (fun d => bool_select_nat (beq (mod n
    /// d) 0) d 0) (succ n)` — the sum of every divisor of `n` in `[0,n]`,
    /// `n` itself included (`d = 0` never contributes: both `bool_select_nat`
    /// branches are `0` there).
    pub sum_divisors: NameId,
    /// `Nat.sumDivisors_one : Eq (sumDivisors (succ zero)) (succ zero)`.
    pub sum_divisors_one: NameId,
    /// `Nat.sumDivisors_prime : Prime p → Eq (sumDivisors p) (succ p)` — a
    /// prime's only divisors in `[0,p]` are `1` and `p`.
    pub sum_divisors_prime: NameId,
    /// `Nat.Perfect n := Eq (sumDivisors n) (mul 2 n)` — summing *all*
    /// divisors including `n` itself (the classical "proper divisors"
    /// phrasing needs `Nat.sub`, truncated here, and is avoided).
    pub perfect: NameId,
    /// `Nat.pow2_geom_sum : ∀ n, add (sumRange (fun i => pow 2 i) n) one =
    /// pow 2 n` — the finite geometric sum over powers of two, subtraction-
    /// free (`Σ_{i<n} 2^i = 2^n − 1` restated as `Σ_{i<n} 2^i + 1 = 2^n`).
    pub pow2_geom_sum: NameId,
    // --- Cantor's diagonal argument (`cantor.rs`) ----------------------------
    /// `Nat.cantor_diagonal : ∀ f : Nat → Nat → Bool,
    ///   ∃ g : Nat → Bool, ∀ n, Eq Bool (g n) (f n n) → False` — the pointwise,
    /// funext-free form of Cantor's diagonal argument: the witness `g := fun n
    /// => not (f n n)` disagrees with every row `f n` at that row's own index,
    /// so no `f : Nat → Nat → Bool` enumerates every `Nat → Bool` sequence.
    /// `Exists`'s witness type here is `Nat → Bool`, not `Nat`; see
    /// `cantor.rs`'s module doc for why that instantiation type-checks despite
    /// `Exists.rec` being restricted to `Prop` motives (`sum_range_diagonal`'s
    /// neighbouring finding, the opposite direction of the same restriction).
    pub cantor_diagonal: NameId,
    /// `Nat.cantor_diagonal_neg : ∀ f : Nat → Nat → Bool,
    ///   (∀ g : Nat → Bool, ∃ n, ∀ k, Eq Bool (f n k) (g k)) → False` — the
    /// negative form: no `f` enumerates every `Nat → Bool` sequence, where
    /// "enumerates" is stated pointwise (`∀ k, …`) rather than as a function
    /// equality, so this needs no `funext` either. Follows from
    /// [`Self::cantor_diagonal`] by nested `Exists.rec` elimination; see
    /// `cantor.rs`'s module doc.
    pub cantor_diagonal_neg: NameId,
    /// `Nat.cantor_no_fixed_point : ∀ F : Bool → Bool,
    ///   (∀ b, Eq Bool (F b) b → False) → (∃ d, Eq Bool (F d) d) → False` —
    /// the fixed-point corollary: a `Bool → Bool` function disagreeing with
    /// every input everywhere has no fixed point. Independent of
    /// [`Self::cantor_diagonal`]/[`Self::cantor_diagonal_neg`] (a single
    /// `Exists.rec`, no `Bool.rec` case split needed), but instantiating `F`
    /// at the diagonal's own `not` recovers "negation has no fixed point" —
    /// the seed of the halting argument's shape.
    pub cantor_no_fixed_point: NameId,
    /// `Nat.dvd_two_pow_mul_classify : ∀ k q, (2 ≤ q ∧ ∀ c, dvd c q → Eq c 1
    /// ∨ Eq c q) → ¬(dvd q 2) → ∀ d, dvd d (mul (pow 2 k) q) → (∃ i, Le i k
    /// ∧ Eq d (pow 2 i)) ∨ (∃ i, Le i k ∧ Eq d (mul (pow 2 i) q))` — every
    /// divisor of `2^k·q` (`q` prime) is either a power of `2` up to `2^k`
    /// or that power times `q`. The Euclid IX.36 divisor-classification
    /// blocker; see `perfect.rs`'s module doc for the proof route.
    pub dvd_two_pow_mul_classify: NameId,
    /// `Nat.dvd_two_pow_classify : ∀ k d, dvd d (pow 2 k) → ∃ i, Le i k ∧ Eq
    /// d (pow 2 i)` — every divisor of `2^k` is a power of `2` up to `2^k`
    /// (the `q`-free specialization [`Self::dvd_two_pow_mul_classify`]
    /// cannot be instantiated to give directly, since its cofactor carries a
    /// `2 ≤ q` primality hypothesis that blocks `q = 1`). This is the
    /// "divisors of `2^n` are exactly the powers of `2` up to `n`"
    /// classification `sumDivisors_two_pow`'s congruence step needs; see
    /// `perfect.rs`'s module doc for the proof route.
    pub dvd_two_pow_classify: NameId,
    /// `Nat.pow_two_ne_pow_two_mul_prime : ∀ i j q, (2 ≤ q ∧ ∀ c, dvd c q →
    /// Eq c 1 ∨ Eq c q) → ¬(dvd q 2) → ¬(Eq (pow 2 i) (mul (pow 2 j) q))` —
    /// the non-overlap fact between `2^k·q`'s two divisor families: no power
    /// of `2` equals `2^j` times an odd prime `q`. Needed to split
    /// `sumDivisors (2^k·q)` into its two families without double-counting
    /// (Euclid IX.36). Proved via [`Self::dvd_two_pow_classify`] rather than
    /// `euclid_lemma`: assume `Eq (pow 2 i) (mul (pow 2 j) q)`; `q` divides
    /// the right side unconditionally (`dvd_mul` + `mul_comm`), hence
    /// (transporting along the assumed equality) `q ∣ 2^i`; classify that
    /// divisor to get `q = 2^e` for some `e`. `e = 0` forces `q = 1`,
    /// contradicting `2 ≤ q`; `e = succ e'` forces `2 ∣ q` (`2^e ≡ 2^e' * 2`
    /// by iota), so `q`'s own divisor clause at `c = 2` gives `2 = 1` (absurd)
    /// or `2 = q` (giving `dvd q 2`, contradicting the odd-prime hypothesis
    /// directly). See `perfect.rs`'s module doc for why the constructed
    /// `dvd_two_pow_classify` route was chosen over `euclid_lemma`.
    pub pow_two_ne_pow_two_mul_prime: NameId,
    /// `Nat.pow_pos : ∀ b k, Lt zero b → Lt zero (pow b k)` — positivity of
    /// `pow` is preserved by a positive base, at any exponent. See
    /// `perfect.rs`'s module note for why this and `pow_lt_pow_succ` did not
    /// already exist (verified against the full theorem inventory).
    pub pow_pos: NameId,
    /// `Nat.pow_lt_pow_succ : ∀ b k, Lt (succ zero) b → Lt (pow b k) (pow b
    /// (succ k))` — strict monotonicity of `pow` in the exponent, one
    /// successor step at a time, for any base greater than `1`. The Euclid
    /// IX.36 blocker `perfect.rs`'s module doc names: `sumDivisors_two_pow`'s
    /// tail sub-induction needs `2^k < 2^(k+1)`, an instance at `b = 2`.
    pub pow_lt_pow_succ: NameId,
    /// `Nat.pow_lt_pow_of_lt : ∀ b i j, Lt (succ zero) b → Lt i j → Lt (pow b
    /// i) (pow b j)` — general strict monotonicity of `pow` in the exponent,
    /// across any gap, for any base greater than `1`. Built by induction on
    /// `j` (fixing `b`, `i`), composing [`Self::pow_lt_pow_succ`] one
    /// successor at a time with [`Self::lt_of_lt_of_le`]: the successor-step
    /// lemma already existed for exactly the reason this field's own history
    /// records (see `perfect.rs`'s module note by [`Self::pow_lt_pow_succ`]
    /// and [`Self::pow_pos`]), but nothing composed it across an arbitrary
    /// gap until Euclid IX.36's injectivity chain needed it.
    pub pow_lt_pow_of_lt: NameId,
    /// `Nat.pow_injective : ∀ b i j, Lt (succ zero) b → Eq (pow b i) (pow b
    /// j) → Eq i j` — `pow b` is injective in the exponent for any base
    /// greater than `1`. From [`Self::pow_lt_pow_of_lt`] plus trichotomy
    /// (`le_total` then `lt_or_eq_of_le` on each side): either strict
    /// direction contradicts the assumed equality via `lt_irrefl`, leaving
    /// only `Eq i j`.
    pub pow_injective: NameId,
    /// `Nat.pow_mul_prime_injective : ∀ i j q, Le (succ zero) q → Eq (mul
    /// (pow 2 i) q) (mul (pow 2 j) q) → Eq i j` — cancelling the shared
    /// positive cofactor `q` (via `mul_comm` + `mul_left_cancel_of_pos`,
    /// which cancels on the LEFT) reduces to `Eq (pow 2 i) (pow 2 j)`, then
    /// [`Self::pow_injective`] at `b = 2` (`Lt 1 2` from `le_refl 2`) finishes
    /// it. Needed to know the `2(k+1)` divisor-sum terms in Euclid IX.36's
    /// two-family case are pairwise distinct before they can be summed as a
    /// clean total.
    pub pow_mul_prime_injective: NameId,
    /// `Nat.dvd_two_pow_succ_iff_of_le : ∀ k d, Le d (pow 2 k) → Iff (dvd d
    /// (pow 2 k)) (dvd d (pow 2 (succ k)))` — the congruence step
    /// `sumDivisors_two_pow`'s tail sub-induction consumes: below the bound
    /// `2^k`, divisibility by `2^k` and by `2^(k+1)` agree. See
    /// `perfect.rs`'s module doc for the proof route.
    pub dvd_two_pow_succ_iff_of_le: NameId,
    /// `Nat.sumDivisors_two_pow_eq_geom_sum : ∀ k, Eq (sumDivisors (pow 2 k))
    /// (sumRange (fun i => pow 2 i) (succ k))` — the divisor sum of `2^k`
    /// equals the geometric sum of powers of `2` up to `k`; the bridge
    /// `Nat.sumDivisors_two_pow` composes with `pow2_geom_sum`. See
    /// `perfect.rs`'s module doc for the proof route.
    pub sum_divisors_two_pow_eq_geom_sum: NameId,
    /// `Nat.sumDivisors_two_pow : ∀ k, Eq (add (sumDivisors (pow 2 k)) one)
    /// (pow 2 (succ k))` — the divisor sum of `2^k`, subtraction-free
    /// (`Σd|2^k d = 2^(k+1) − 1` restated as `+1 =`).
    pub sum_divisors_two_pow: NameId,

    // --- the irrationality of `√2` (`irrational.rs`) ------------------------
    /// `Nat.even_of_even_sq : ∀ n, dvd 2 (mul n n) → dvd 2 n`. Via
    /// `gcd(2,n) ∈ {1,2}` plus `gauss_lemma`/`gcd_dvd_right`.
    pub even_of_even_sq: NameId,
    /// `Nat.no_rational_sqrt_two : ∀ p q, q ≠ 0 → p·p ≠ 2·(q·q)` — the
    /// content of "`√2` is irrational", stated purely over `Nat` (no real
    /// `sqrt`, no rational embedding). Infinite descent on `q` via
    /// `WellFounded.fix`.
    pub no_rational_sqrt_two: NameId,

    // --- parity (`parity.rs`) -------------------------------------------------
    /// `Nat.Even n := Exists (fun k => Eq n (add k k))` — an EXISTENTIAL
    /// witness, deliberately in the `k + k` form rather than `2 * k`:
    /// [`Self::even_or_odd`]'s own proof already produces exactly `n = half +
    /// half` (`half := div n 2`) as its even-branch intermediate, so
    /// [`Self::even_or_odd_exists`] below reuses that term verbatim as the
    /// witness equation instead of converting between `k+k` and `2*k` first.
    pub even: NameId,
    /// `Nat.Odd n := Exists (fun k => Eq n (succ (add k k)))` — `succ (k+k)`
    /// rather than `k+k+1`, for the same reason: [`Self::even_or_odd`]'s
    /// odd-branch intermediate is already exactly `n = succ (half + half)`.
    pub odd: NameId,
    /// `Nat.even_or_odd_exists : ∀ n, Or (Even n) (Odd n)` — [`Self::even_or_odd`]
    /// restated with an existential witness instead of the computed `div n
    /// 2`, derived from it directly (`Or.rec` over the same two branches,
    /// each closed by `Exists.intro` at witness `div n 2`) rather than
    /// re-run through `div_mod_exec` a second time.
    pub even_or_odd_exists: NameId,
    /// `Nat.add_self_ne_succ_add_self : ∀ k j, Not (Eq (add k k) (succ (add j
    /// j)))` — no doubled number equals the successor of a doubled number.
    /// The load-bearing step under [`Self::even_not_odd`]/[`Self::odd_not_even`],
    /// proved by induction on `k` with an inner case split on `j` (`k = 0` is
    /// immediate from `succ_ne_zero`; the successor case peels one `succ` off
    /// each side via `add_succ`/`succ_add` and closes with two rounds of
    /// `succ_injective` against the outer induction hypothesis). Registered
    /// as its own theorem, not a private helper, because both bridge lemmas
    /// need it applied at two *independently* existentially-bound witnesses.
    pub add_self_ne_succ_add_self: NameId,
    /// `Nat.even_not_odd : ∀ n, Even n → Not (Odd n)`. Both existentials are
    /// eliminated (`Exists.rec`, `Prop`-valued so this is legal even though
    /// the witnesses are never returned) down to `Eq (add k k) (succ (add j
    /// j))` for some `k, j`, refuted by [`Self::add_self_ne_succ_add_self`].
    pub even_not_odd: NameId,
    /// `Nat.odd_not_even : ∀ n, Odd n → Not (Even n)` — [`Self::even_not_odd`]
    /// with its two hypotheses supplied in the opposite order; no new
    /// construction.
    pub odd_not_even: NameId,
    /// `Nat.even_iff_odd_succ : ∀ n, Iff (Even n) (Odd (succ n))`. Both
    /// directions are direct `congrArg succ`/`succ_injective` on the
    /// existential witness — `parity_ne` is not needed here.
    pub even_iff_odd_succ: NameId,
    /// `Nat.even_iff_mod_two_eq_zero : ∀ n, Iff (Even n) (Eq (mod n 2) 0)` —
    /// the parity <-> low-bit bridge: `mp` eliminates the existential and
    /// rewrites through `mul_two_eq_add_self`/`div_mod_exec`/`div_mod_unique`;
    /// `mpr` reconstructs the witness from `div n 2`.
    pub even_iff_mod_two_eq_zero: NameId,
    /// `Nat.odd_iff_mod_two_eq_one : ∀ n, Iff (Odd n) (Eq (mod n 2) 1)` —
    /// [`Self::even_iff_mod_two_eq_zero`]'s `succ` twin.
    pub odd_iff_mod_two_eq_one: NameId,

    // --- `parity_div.rs`: the parity/division-by-two mirror cluster --------
    /// `Nat.div_two_mul_two_of_even : ∀ n, Even n → Eq (mul (div n 2) 2) n`.
    /// `F:ml430-nat-div-two-mul-two-of-even-9ccc5340`.
    pub div_two_mul_two_of_even: NameId,
    /// `Nat.div_two_mul_two_add_one_of_odd : ∀ n, Odd n → Eq
    /// (add (mul (div n 2) 2) 1) n`.
    /// `F:ml430-nat-div-two-mul-two-add-one-of-odd-9e3e8b82`.
    pub div_two_mul_two_add_one_of_odd: NameId,
    /// `Nat.add_one_lt_of_even : ∀ n m, Even n → Even m → Lt n m → Lt
    /// (add n 1) m`. `F:ml430-nat-add-one-lt-of-even-3464b374`.
    pub add_one_lt_of_even: NameId,
    /// `Nat.even_mul_of_even_left : ∀ m n, Even m → Even (mul m n)` — the
    /// load-bearing step under [`Self::odd_of_mul_left`]/
    /// [`Self::odd_of_mul_right`], via `right_distrib` on the `k+k` witness.
    pub even_mul_of_even_left: NameId,
    /// `Nat.odd_of_mul_left : ∀ m n, Odd (mul m n) → Odd m`.
    /// `F:ml430-nat-odd-of-mul-left-2c6c2553`.
    pub odd_of_mul_left: NameId,
    /// `Nat.odd_of_mul_right : ∀ m n, Odd (mul m n) → Odd n` — via
    /// [`Self::odd_of_mul_left`] and `mul_comm`.
    /// `F:ml430-nat-odd-of-mul-right-fe6d20ff`.
    pub odd_of_mul_right: NameId,
    /// `Nat.even_add_one : ∀ n, Iff (Even (add n 1)) (Not (Even n))`.
    /// `F:ml430-nat-even-add-one-15b5cb18`.
    pub even_add_one: NameId,
    /// `Nat.even_add : ∀ m n, Iff (Even (add m n)) (Iff (Even m) (Even n))`
    /// (`even_add_family.rs`). `F:ml430-nat-even-add-31386639`.
    pub even_add: NameId,
    /// `Nat.even_add' : ∀ m n, Iff (Even (add m n)) (Iff (Odd m) (Odd n))`
    /// (`even_add_family.rs`). `F:ml430-nat-even-add-39e3bc07`.
    pub even_add_prime: NameId,
    /// `Nat.even_div : ∀ m n, Iff (Even (div m n)) (Eq (div (mod m (mul 2
    /// n)) n) 0)` (`even_div.rs`). `F:ml430-nat-even-div-395c6b5e`.
    pub even_div: NameId,

    // --- the floor logarithm (`log.rs`) -------------------------------------
    /// `Nat.logAux : Nat → Nat → Nat → Nat` — `logAux b f n`, the floor base-`b`
    /// logarithm of `n` computed with **fuel** `f`, by structural recursion on
    /// `f`. `logAux b zero n ≡ 0` and `logAux b (succ f) n ≡ if 2 ≤ b then (if
    /// b ≤ n then succ (logAux b f (div n b)) else 0) else 0`, both
    /// definitionally. Mathlib's `Nat.log` recurses on `n / b`, which is not a
    /// constructor predecessor; fuel is how this prelude already expresses
    /// `Nat.div`/`Nat.mod`, and it keeps the construction axiom-free (a
    /// `WellFounded.fix` route would pull in `Quot.sound`/`propext`).
    pub log_aux: NameId,
    /// `Nat.log : Nat → Nat → Nat` — `log b n := logAux b n n`. The fuel is `n`
    /// itself, which always suffices: the guard forces `2 ≤ b ≤ n`, so each
    /// step replaces `n` by `div n b ≤ div n 2 < n`.
    pub log: NameId,
    /// `Nat.log_zero_right : ∀ b, Eq (log b 0) 0` — `refl`: the fuel is `0`, so
    /// `logAux` is already at its base case.
    pub log_zero_right: NameId,
    /// `Nat.log_zero_left : ∀ n, Eq (log 0 n) 0` — `ble 2 0` is `false`, so the
    /// outer cut collapses in both fuel cases (`Mathlib`: `Nat.log_zero_left`).
    pub log_zero_left: NameId,
    /// `Nat.log_one_left : ∀ n, Eq (log 1 n) 0` — `ble 2 1` reduces to `ble 1
    /// 0`, i.e. `false` (`Mathlib`: `Nat.log_one_left`).
    pub log_one_left: NameId,
    /// `Nat.log_one_right : ∀ b, Eq (log b 1) 0` — a three-way case analysis on
    /// `b`: `0` and `1` fail the `2 ≤ b` cut, and `succ (succ k)` passes it and
    /// then fails the `b ≤ 1` cut (`Mathlib`: `Nat.log_one_right`).
    pub log_one_right: NameId,
    /// `Nat.ble_eq_false_of_lt : ∀ b n, Lt n b → Eq Bool (ble b n) Bool.false`.
    /// A general [`ble`](Self::ble) fact with no `Nat.log` in it, declared in
    /// `log.rs` under its first consumer: `ble.rs` carries the two *positive*
    /// bridges ([`ble_eq_true_of_le`](Self::ble_eq_true_of_le),
    /// [`le_of_ble_eq_true`](Self::le_of_ble_eq_true)) and the negated-`Prop`
    /// form ([`not_le_of_not_ble_eq_true`](Self::not_le_of_not_ble_eq_true)),
    /// but nothing producing `Eq Bool _ Bool.false` — which is the shape a
    /// `Bool.rec` cut has to be rewritten with.
    pub ble_eq_false_of_lt: NameId,
    /// `Nat.log_of_lt : ∀ b n, Lt n b → Eq (log b n) 0` — below its own base a
    /// number has logarithm zero (`Mathlib`: `Nat.log_of_lt`). The outermost
    /// guard cut is the refuted one, so one `Eq.rec` over
    /// [`ble_eq_false_of_lt`](Self::ble_eq_false_of_lt) collapses the whole
    /// fuel step.
    pub log_of_lt: NameId,

    // --- the floor square root (`sqrt.rs`) ----------------------------------
    /// `Nat.sqrtAux : Nat → Nat → Nat` — `sqrtAux n f`, the floor square root
    /// of `n` computed by **fuel-bounded linear search**: `f` many
    /// structural-recursion steps, each incrementing an accumulator while
    /// `(accumulator + 1)² ≤ n` holds. `sqrtAux n zero ≡ 0` and `sqrtAux n
    /// (succ f) ≡ let c := sqrtAux n f in if (succ c) * (succ c) ≤ n then
    /// succ c else c`, both definitionally. Unlike
    /// [`log_aux`](Self::log_aux), `n` is a captured free variable, not
    /// threaded through `Nat.rec`'s motive — the motive here is the plain
    /// `fun _ => Nat` accumulator fold, because (unlike `log`'s `n / b`) the
    /// value being searched never changes across fuel steps.
    pub sqrt_aux: NameId,
    /// `Nat.sqrt : Nat → Nat` — `sqrt n := sqrtAux n n`. The fuel is `n`
    /// itself: the accumulator increments by at most `1` per step and the
    /// greatest `m` with `m * m ≤ n` is itself `≤ n`, so `n` steps always
    /// suffice.
    pub sqrt: NameId,
    /// `Nat.sqrt_zero : Eq (sqrt 0) 0` — `refl`: the fuel is `0`, so
    /// `sqrtAux` is already at its base case (`Mathlib`: `Nat.sqrt_zero`).
    pub sqrt_zero: NameId,
    /// `Nat.sqrt_one : Eq (sqrt 1) 1` — `refl`: fully concrete, one fuel step
    /// finds `1 * 1 ≤ 1` (`Mathlib`: `Nat.sqrt_one`).
    pub sqrt_one: NameId,
    // --- the ceiling logarithm (`clog.rs`) ----------------------------------
    /// `Nat.clogAux : Nat → Nat → Nat → Nat` — `clogAux b f n`, the ceiling
    /// base-`b` logarithm of `n` computed with **fuel** `f`, by structural
    /// recursion on `f`. `clogAux b zero n ≡ 0` and `clogAux b (succ f) n ≡
    /// if 2 ≤ b then (if 2 ≤ n then succ (clogAux b f (div (sub (add n b) 1)
    /// b)) else 0) else 0`, both definitionally. Same fuel device as
    /// [`log_aux`](Self::log_aux); the recursive call is at `(n + b - 1) /
    /// b`, not `n / b`.
    pub clog_aux: NameId,
    /// `Nat.clog : Nat → Nat → Nat` — `clog b n := clogAux b n n`.
    pub clog: NameId,
    /// `Nat.clog_zero_right : ∀ b, Eq (clog b 0) 0` — `refl`: the fuel is
    /// `0`, so `clogAux` is already at its base case.
    pub clog_zero_right: NameId,
    /// `Nat.clog_zero_left : ∀ n, Eq (clog 0 n) 0` — `ble 2 0` is `false`,
    /// so the outer cut collapses in every fuel case (`Mathlib`:
    /// `Nat.clog_zero_left`).
    pub clog_zero_left: NameId,
    /// `Nat.clog_one_left : ∀ n, Eq (clog 1 n) 0` — `ble 2 1` reduces to
    /// `ble 1 0`, i.e. `false` (`Mathlib`: `Nat.clog_one_left`).
    pub clog_one_left: NameId,
    /// `Nat.clog_one_right : ∀ b, Eq (clog b 1) 0` — a three-way case
    /// analysis on `b`: `0` and `1` fail the `2 ≤ b` cut, and `succ (succ
    /// k)` passes it and then fails the INNER cut `2 ≤ 1` (`Mathlib`:
    /// `Nat.clog_one_right`).
    pub clog_one_right: NameId,
    /// `Nat.logAux_le_fuel : ∀ b f n, Le (logAux b f n) f` — the fuel is
    /// always an upper bound on the fuel-recursive `logAux`, for every value
    /// `n`, not merely the one `log b n := logAux b n n` instantiates.
    ///
    /// The genuinely harder tier of `Nat.log`: induction on `f` with `n`
    /// **generalized inside the motive** (`∀ n, Le (logAux b f n) f`), because
    /// the recursive call is at `n / b`, a *different* `n` than the one the
    /// outer statement was stated at. Fixing `n` and inducting on `f` alone
    /// gives an induction hypothesis about `logAux b f n`, which does not
    /// apply at the recursive call's `logAux b f (n / b)`.
    ///
    /// [`log_le_self`](Self::log_le_self) is this lemma specialized at
    /// `f := n`.
    pub log_aux_le_fuel: NameId,
    /// `Nat.log_le_self : ∀ b n, Le (log b n) n` (`Mathlib`: `Nat.log_le_self`)
    /// — [`log_aux_le_fuel`](Self::log_aux_le_fuel) specialized at `f := n`,
    /// since `log b n := logAux b n n` definitionally.
    pub log_le_self: NameId,
    // --- `log`/`clog` order mirrors (`log_clog_order.rs`) -------------------
    /// `Nat.div_le_div_right : ∀ n m b, Le n m → Le (div n b) (div m b)` —
    /// general infrastructure, not itself an `ml430` mirror target, filed
    /// here under its first consumers ([`log_aux_mono`](Self::log_aux_mono),
    /// [`clog_aux_mono`](Self::clog_aux_mono)). At `b = 0` both sides are
    /// `0` (`div_zero`); at `b = succ bp`, `div_lt_of_lt_mul` applied to
    /// `n ≤ m < b*(succ (div m b))` (`div_mod_lt_mul_iff`'s backward
    /// direction fed `lt_succ_self`, via the canonical `div_mod_exec`
    /// witness) gives `div n b < succ (div m b)`, hence `≤` by
    /// `le_of_lt_succ`.
    pub div_le_div_right: NameId,
    /// `Nat.log_aux_mono : ∀ b f, ∀ g n m, Le f g → Le n m → Le (logAux b f n)
    /// (logAux b g m)` — fuel- and value-monotonicity proved TOGETHER by a
    /// single induction on `f` (with `g`, `n`, `m` generalized inside the
    /// motive, the same technique [`log_aux_le_fuel`](Self::log_aux_le_fuel)
    /// uses for `n`). The step case splits the outer fuel-comparison
    /// hypothesis on `g`'s shape (`g = 0` is refuted by `not_succ_le_zero`)
    /// and then reconciles `logAux`'s two guard cuts — `b ≤ n` OUTERMOST,
    /// `2 ≤ b` inner — against the corresponding `m` guards: the `2 ≤ b` cut
    /// is the SAME test on both sides (closed by the identity implication),
    /// the `b ≤ n`/`b ≤ m` cut needs `b ≤ n ≤ m` (`le_of_ble_eq_true` +
    /// `le_trans` + `ble_eq_true_of_le`), and the recursive quotients
    /// `n / b ≤ m / b` come from [`div_le_div_right`](Self::div_le_div_right).
    /// [`log_mono_right`](Self::log_mono_right) and
    /// [`log_monotone`](Self::log_monotone) both specialize this at
    /// `f := n, g := m` with the SAME hypothesis used for both the fuel and
    /// value comparison, since `log b n := logAux b n n` is diagonal.
    pub log_aux_mono: NameId,
    /// `Nat.log_mono_right : ∀ b n m, Le n m → Le (log b n) (log b m)`
    /// (`Mathlib`: `Nat.log_mono_right`) —
    /// [`log_aux_mono`](Self::log_aux_mono) at `f := n, g := m`.
    pub log_mono_right: NameId,
    /// `Nat.log_monotone : ∀ b, Monotone (log b)` (`Mathlib`:
    /// `Nat.log_monotone`) — `Monotone f` unfolds (Mathlib's own definition)
    /// to `∀ x y, x ≤ y → f x ≤ f y`, exactly
    /// [`log_mono_right`](Self::log_mono_right)'s core rendering with `b`
    /// fixed first (the same "core-rendered unfolding" already used for
    /// `Nat.choose_mono`).
    pub log_monotone: NameId,
    /// `Nat.clog_aux_mono` — [`log_aux_mono`](Self::log_aux_mono)'s
    /// counterpart for `clogAux`. Same double induction; the guard order is
    /// `clog.rs`'s opposite nesting (`2 ≤ b` OUTERMOST, same test both
    /// sides via the identity implication; `2 ≤ n`/`2 ≤ m` inner, related by
    /// `n ≤ m` the same Bool-bridge way), and the recursive argument
    /// monotonicity is `(n + b - 1) / b ≤ (m + b - 1) / b`, from
    /// `add_le_add_right` then [`div_le_div_right`](Self::div_le_div_right).
    pub clog_aux_mono: NameId,
    /// `Nat.clog_mono_right : ∀ b n m, Le n m → Le (clog b n) (clog b m)`
    /// (`Mathlib`: `Nat.clog_mono_right`) —
    /// [`clog_aux_mono`](Self::clog_aux_mono) at `f := n, g := m`.
    pub clog_mono_right: NameId,
    /// `Nat.clog_monotone : ∀ b, Monotone (clog b)` (`Mathlib`:
    /// `Nat.clog_monotone`) — the same `Monotone`-unfolds-to-pointwise
    /// rendering as [`log_monotone`](Self::log_monotone).
    pub clog_monotone: NameId,
    /// `Nat.clog_pos : ∀ b n, Lt 1 b → Lt 1 n → Lt 0 (clog b n)` (`Mathlib`:
    /// `Nat.clog_pos`) — case-split on `n` (`n = 0` is refuted by `Lt 1 0`
    /// via `not_succ_le_zero`); at `n = succ n'` the guard `2 ≤ b ∧ 2 ≤ n`
    /// holds by hypothesis, so `clog b n` reduces (two direct
    /// `bool_transport`s at the known-`true` evidence, no case split needed
    /// since the evidence is already in hand) to a `succ`, positive by
    /// `zero_lt_succ`.
    pub clog_pos: NameId,
    /// `Nat.log_aux_le_clog_aux : ∀ b f n, Le (logAux b f n) (clogAux b f
    /// n)` — the two aux FAMILIES compared at a SHARED fuel (both `log`/
    /// `clog` are diagonal at `f := n`, so one fuel counter suffices, unlike
    /// [`log_aux_mono`](Self::log_aux_mono)/
    /// [`clog_aux_mono`](Self::clog_aux_mono), which compare one family
    /// against itself at two DIFFERENT fuels). Induction on `f` (`n`
    /// generalized inside the motive); the step splits on THREE
    /// independent booleans — `2 ≤ b` (`logAux`'s inner cut, `clogAux`'s
    /// outer cut: the SAME test both families use), `b ≤ n` (`logAux`'s
    /// outer cut only) and `2 ≤ n` (`clogAux`'s inner cut only, derived from
    /// the first two via `le_trans` rather than split independently). The
    /// hard leaf (`2 ≤ b` and `b ≤ n` both true) needs one new small lemma,
    /// `Le n (sub (add n b) 1)` for `Le 1 b` (`n ≤ n+b-1`, via
    /// `add_le_add_left` then `pred_le_pred`, `sub x 1` being
    /// definitionally `pred x`), which gives `n / b ≤ (n+b-1) / b` via
    /// [`div_le_div_right`](Self::div_le_div_right); the recursive
    /// obligation is then `IH(n/b)` chained through
    /// `clog_aux_mono(predecessor, predecessor, n/b, (n+b-1)/b, le_refl,
    /// div_mono)` via `le_trans`, then `le_succ_succ`.
    pub log_aux_le_clog_aux: NameId,
    /// `Nat.log_le_clog : ∀ b n, Le (log b n) (clog b n)` (`Mathlib`:
    /// `Nat.log_le_clog`) —
    /// [`log_aux_le_clog_aux`](Self::log_aux_le_clog_aux) at the diagonal
    /// `f := n`, since both `log b n := logAux b n n` and
    /// `clog b n := clogAux b n n`.
    pub log_le_clog: NameId,
    /// `Nat.div_lt_self : ∀ n b, Lt 0 n → Lt 1 b → Lt (div n b) n`
    /// (`Mathlib`: `Nat.div_lt_self`) — general infrastructure for
    /// [`log_lt_self`](Self::log_lt_self), filed here under its first
    /// consumer. `mul_lt_mul_right(n, 1, b, pos_n)` (the `Iff` form,
    /// backward direction) fed `hb : Lt 1 b` gives `Lt (mul 1 n) (mul b
    /// n)`; rewriting `mul 1 n = n` via `one_mul` gives `Lt n (mul b n)`,
    /// then `div_lt_of_lt_mul(n, b, n, that)` gives `Lt (div n b) n`
    /// directly.
    pub div_lt_self: NameId,
    /// `Nat.log_aux_lt_of_pos : ∀ b f n, Le n f → Not (Eq n 0) → Lt (logAux
    /// b f n) n` — the genuinely hard tier for `log_lt_self`: STRUCTURAL
    /// induction on the fuel `f` (n generalized inside the motive, `Le n f`
    /// carried as an explicit hypothesis rather than needed well-founded
    /// recursion on `n` itself), because the recursive call's fuel
    /// (`predecessor`) and its argument (`n / b`) are validated together —
    /// `predecessor` is always sufficient fuel for `n / b` because
    /// [`div_lt_self`](Self::div_lt_self) plus `Le n (succ predecessor)`
    /// gives `Lt (n/b) (succ predecessor)`, hence `Le (n/b) predecessor` via
    /// `le_of_lt_succ`.
    ///
    /// The step case's hard leaf (both guards true) splits further on
    /// whether `n / b` is itself `0`: if so, `logAux b predecessor 0 = 0`
    /// unconditionally (a small nested induction on `predecessor` alone,
    /// using that `b ≤ 0` is provably `false` whenever `Lt 0 b`, collapsing
    /// BOTH of `logAux`'s guard levels via `bool_select_nat_same` — this
    /// does not need the outer `Le`/`Ne` hypotheses at all), giving `succ 0
    /// = 1 < n` directly from `2 ≤ b ≤ n`; otherwise the induction
    /// hypothesis applies at `n / b` (nonzero, sufficiently fueled),
    /// chained through `div_lt_self` and `lt_of_lt_of_le`/`le_of_lt_succ`.
    pub log_aux_lt_of_pos: NameId,
    /// `Nat.log_lt_self : ∀ b x, Not (Eq x 0) → Lt (log b x) x` (`Mathlib`:
    /// `Nat.log_lt_self`) —
    /// [`log_aux_lt_of_pos`](Self::log_aux_lt_of_pos) at the diagonal `f :=
    /// x`, via `le_refl`.
    pub log_lt_self: NameId,
    /// `Nat.div_le_div_left : ∀ n a b, Lt 0 a → Le a b → Le (div n b) (div n
    /// a)` — the MIRROR image of
    /// [`div_le_div_right`](Self::div_le_div_right): monotone DECREASING in
    /// the divisor rather than increasing in the dividend. Reconstructs `a`
    /// as `succ (pred a)` (`succ_pred_of_pos`, the `div_mod_reconstructed`
    /// pattern `base_induction.rs` uses) to get `div_mod_exec` in scope, then
    /// the same `div_mod_lt_mul_iff`/`lt_succ_self`/`div_lt_of_lt_mul` chain
    /// [`div_le_div_right`](Self::div_le_div_right) uses, with `a`'s role in
    /// the final product rewritten to `b` via `mul_le_mul_left` + `mul_comm`
    /// (`a ≤ b` gives `a * S ≤ b * S` after commuting to put the varying
    /// factor on the left).
    pub div_le_div_left: NameId,
    /// `Nat.log_aux_antitone_base : ∀ f n a b, Le a b → Lt 1 a → Lt 1 b → Le
    /// (logAux b f n) (logAux a f n)` — monotonicity in the BASE with the
    /// value held fixed, a materially different induction from
    /// [`log_aux_mono`](Self::log_aux_mono) (which fixes the base and varies
    /// fuel/value). Induction on the SHARED fuel `f` (both sides use the
    /// same `f`, since `log b n`/`log a n` share the same diagonal `n`); `n`,
    /// `a`, `b` generalized inside the motive. Because `1 < a`/`1 < b` are
    /// universal HYPOTHESES of the statement (not case-derived), each side's
    /// inner `2 ≤ base` cut is already known TRUE unconditionally — no case
    /// split on it, unlike `log_aux_mono`. Only `b ≤ n` is split: `false`
    /// collapses the `b`-side to `0` regardless of the `a`-side
    /// (`a ≤ n` need not even be decided); `true` gives `a ≤ b ≤ n` via
    /// `le_trans`, so the `a`-side's cut is also true. The recursive
    /// obligation compares `logAux b f' (n/b)` against `logAux a f' (n/a)` —
    /// DIFFERENT values at DIFFERENT bases — via `IH(n/b, a, b)` (bases at
    /// the SAME value `n/b`) chained through
    /// [`log_aux_mono`](Self::log_aux_mono) at the SAME base `a` (values
    /// `n/b ≤ n/a` from [`div_le_div_left`](Self::div_le_div_left)) and
    /// `le_trans`, then `le_succ_succ`.
    pub log_aux_antitone_base: NameId,
    /// `Nat.log_antitone_left : ∀ {n}, AntitoneOn (fun b => log b n) (Set.Ioi
    /// 1)` (`Mathlib`: `Nat.log_antitone_left`) — the core-rendered
    /// unfolding (`AntitoneOn f s := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≤ b → f
    /// b ≤ f a` and `x ∈ Set.Ioi c := c < x` are both Mathlib pointwise
    /// `def`s, the same "definitionally a pointwise implication" situation
    /// that already made `Monotone`/`log_monotone` an honest flip; no kernel
    /// `Set` type is needed) at
    /// [`log_aux_antitone_base`](Self::log_aux_antitone_base)'s diagonal `f
    /// := n`.
    pub log_antitone_left: NameId,
    /// `Nat.clog_aux_antitone_base : ∀ f n a b, Le a b → Lt 1 a → Lt 1 b →
    /// Le (clogAux b f n) (clogAux a f n)` — [`log_aux_antitone_base`](Self::log_aux_antitone_base)'s
    /// counterpart, with the two guard cuts' roles swapped: `clogAux`'s
    /// outer cut (`2 ≤ base`) is a pure base cut, individually known true
    /// from the statement's own `1 < a`/`1 < b` hypotheses (no case split);
    /// its inner cut (`2 ≤ n`) is the SAME expression on both sides (the
    /// value is fixed), so it needs exactly one case split. The recursive
    /// step compares two different CEILING quotients at different bases —
    /// not covered by [`div_le_div_left`](Self::div_le_div_left) directly,
    /// which is about a shared numerator — so each side's quotient is first
    /// rewritten to `(n-1)/base + 1` (a bridging identity between `(n +
    /// base) - 1` and `(n - 1) + base`, valid given `1 ≤ n`, plus
    /// `Nat.add_div_right`), turning the comparison into a floor comparison
    /// at the shared numerator `n - 1`.
    pub clog_aux_antitone_base: NameId,
    /// `Nat.clog_antitone_left : ∀ {n}, AntitoneOn (fun b => clog b n)
    /// (Set.Ioi 1)` (`Mathlib`: `Nat.clog_antitone_left`) — the
    /// core-rendered unfolding at
    /// [`clog_aux_antitone_base`](Self::clog_aux_antitone_base)'s diagonal
    /// `f := n`.
    pub clog_antitone_left: NameId,
    /// `Nat.log2 : Nat → Nat`, `log2 n := log 2 n` (Lean **core**,
    /// `Init/Data/Nat/Log2.lean` — Mathlib imports it unchanged). Lean
    /// core's own `log2` is a fuel-recursive `Nat.rec` with a non-dependent
    /// motive `fun _ => Nat → Nat`, fuel = the value itself, single guard
    /// `2 ≤ n` — exactly `logAux`'s own device specialized to the literal
    /// base `2` (the inner cut `2 ≤ 2` reduces to `Bool.true` by ι alone,
    /// leaving only the outer cut `2 ≤ n`), so this prelude declares it
    /// directly as `Nat.log 2` rather than re-deriving a second recursor.
    pub log2: NameId,
    /// `Nat.log2_eq_log_two : ∀ n, Eq (log2 n) (log 2 n)` (`Mathlib`:
    /// `Nat.log2_eq_log_two`) — `Eq.refl`, since `log2 n` delta-unfolds
    /// directly to `log 2 n` by construction.
    pub log2_eq_log_two: NameId,
    /// `Nat.bit : Bool → Nat → Nat`, `bit b n := add (mul 2 n) (cond b 1 0)`
    /// (`Mathlib`: `Nat.bit`, `cond b (2 * n + 1) (2 * n)`). Non-recursive —
    /// unlike `log`/`sqrt`/`clog` it needs no fuel device, since there is no
    /// recursive call to justify. This shape (rather than Mathlib's own
    /// `cond`-outermost form) normalizes to the same boundary values by
    /// delta+iota alone; see `nat_prelude::bits` for the derivation.
    pub bit: NameId,
    /// `Nat.bit_false : ∀ n, Eq (bit false n) (mul 2 n)` (`Mathlib`:
    /// `Nat.bit_false`) — `refl`: `cond false 1 0 ≡ 0` and `Nat.add`'s own
    /// zero case (`add x zero ≡ x`) collapses the sum.
    pub bit_false: NameId,
    /// `Nat.bit_true : ∀ n, Eq (bit true n) (add (mul 2 n) 1)` (`Mathlib`:
    /// `Nat.bit_true`) — `refl`: `cond true 1 0 ≡ 1` and both sides reduce to
    /// the same normal form `succ (mul 2 n)`.
    pub bit_true: NameId,
    /// `Nat.bit_true_pos : ∀ n, Lt 0 (bit true n)` — `bit true n` unfolds
    /// (delta+iota) to `succ (mul 2 n)`, so `zero_lt_succ` at `mul 2 n` is
    /// accepted directly by defeq.
    pub bit_true_pos: NameId,
    /// `Nat.bit_false_le_bit_true : ∀ n, Le (bit false n) (bit true n)` — both
    /// sides unfold to `mul 2 n` and `succ (mul 2 n)`, so `le_succ` at
    /// `mul 2 n` is accepted directly by defeq.
    pub bit_false_le_bit_true: NameId,
    /// `Nat.bit_false_zero : Eq (bit false 0) 0` — `refl`. See
    /// `nat_prelude::bit_extra`.
    pub bit_false_zero: NameId,
    /// `Nat.bit_le : ∀ (b : Bool) {m n}, Le m n → Le (bit b m) (bit b n)`.
    /// See `nat_prelude::bit_extra`.
    pub bit_le: NameId,
    /// `Nat.bit_ne_zero : ∀ (b : Bool) {n}, n ≠ 0 → bit b n ≠ 0`. See
    /// `nat_prelude::bit_extra`.
    pub bit_ne_zero: NameId,
    /// `Nat.bit_lt_bit : ∀ {m n} (a b : Bool), Lt m n → Lt (bit a m) (bit b
    /// n)`. See `nat_prelude::bit_extra`.
    pub bit_lt_bit: NameId,
    /// `Nat.bit_add_left : ∀ (b : Bool) (n m), bit b (n+m) = bit false n +
    /// bit b m`. See `nat_prelude::bit_extra`.
    pub bit_add_left: NameId,
    /// `Nat.bit_add_right : ∀ (b : Bool) (n m), bit b (n+m) = bit b n + bit
    /// false m`. See `nat_prelude::bit_extra`.
    pub bit_add_right: NameId,
    /// `Nat.landAux : Nat → Nat → Nat → Nat`, `landAux fuel m n`: structural
    /// recursion on the fuel (like `logAux`/`testBitAux`/`sizeAux`), carrying
    /// `m`/`n` through unchanged except for `div _ 2` at each step.
    /// `landAux 0 m n ≡ 0`; `landAux (succ f) m n ≡ if n = 0 then 0 else if
    /// m = 0 then 0 else 2 * landAux f (m/2) (n/2) + (m%2)*(n%2)`. Not the
    /// public name; [`Self::land`] supplies fuel `m` itself. See
    /// `nat_prelude::land` for the derivation and why the guard checks `n`
    /// before `m`.
    pub land_aux: NameId,
    /// `Nat.land m n := Nat.landAux m m n` — bitwise AND (`Mathlib`:
    /// `Nat.land`, via the general `Nat.bitwise`). Landed directly rather
    /// than through a general `Nat.bitwise`, because each bit's AND is a
    /// `Nat` product (`0` or `1`) and needs no `Bool`/`cond` combinator.
    pub land: NameId,
    /// `Nat.land_zero_left : ∀ n, Eq (land 0 n) 0` — `refl`: fuel is
    /// `m = 0`, so the outer `Nat.rec` is already exhausted. Not a mirror of
    /// a specific Mathlib name (this prelude's `land` is not Mathlib's).
    pub land_zero_left: NameId,
    /// `Nat.land_zero_right : ∀ m, Eq (land m 0) 0` — induction on `m` to
    /// expose the fuel's constructor; each case is `refl`, no induction
    /// hypothesis needed, because the outermost `n = 0` guard collapses the
    /// term regardless of `m`.
    pub land_zero_right: NameId,
    /// `Nat.land_one_one : Eq (land 1 1) 1` — concrete sanity check, one fuel
    /// step, both bits set.
    pub land_one_one: NameId,
    /// `Nat.land_three_five : Eq (land 3 5) 1` — concrete sanity check,
    /// `0b011 &&& 0b101 = 0b001`, exercising differing bit patterns that
    /// `land_one_one` alone cannot distinguish from a wrong-way step.
    pub land_three_five: NameId,
    /// `Nat.lorAux : Nat → Nat → Nat → Nat`, `lorAux fuel m n`: the same
    /// fuel-recursion device as `landAux`, but with the fuel-exhaustion base
    /// case returning `n` (not the constant `0`) and each per-step guard
    /// returning the OTHER operand — required because OR has no absorbing
    /// zero the way AND does. `lorAux 0 m n ≡ n`; `lorAux (succ f) m n ≡ if
    /// n = 0 then m else if m = 0 then n else 2 * lorAux f (m/2) (n/2) +
    /// max (m%2) (n%2)`. Not the public name; [`Self::lor`] supplies fuel
    /// `m` itself. See `nat_prelude::lor` for why fuel `= m` alone is still
    /// sound for OR and why the guard checks `n` before `m`.
    pub lor_aux: NameId,
    /// `Nat.lor m n := Nat.lorAux m m n` — bitwise OR (`Mathlib`: `Nat.lor`,
    /// via the general `Nat.bitwise`). Landed directly rather than through a
    /// general `Nat.bitwise`, and the per-bit step is `max` (via `Nat.ble` +
    /// `bool_select_nat`) rather than `land`'s product, because OR of two
    /// `{0, 1}` values is not their product.
    pub lor: NameId,
    /// `Nat.lor_zero_left : ∀ n, Eq (lor 0 n) n` — `refl`: fuel is `m = 0`,
    /// so the outer `Nat.rec` hits `lorAux`'s corrected `n`-returning base
    /// case directly. Not a mirror of a specific Mathlib name (this
    /// prelude's `lor` is not Mathlib's).
    pub lor_zero_left: NameId,
    /// `Nat.lor_zero_right : ∀ m, Eq (lor m 0) m` — induction on `m` to
    /// expose the fuel's constructor; each case is `refl`, no induction
    /// hypothesis needed, because the outermost `n = 0` guard collapses the
    /// term to `m` regardless of the fuel predecessor.
    pub lor_zero_right: NameId,
    /// `Nat.lor_three_five : Eq (lor 3 5) 7` — concrete sanity check,
    /// `0b011 ||| 0b101 = 0b111`, deliberately discriminating from
    /// `land_three_five`'s `3 &&& 5 = 1`.
    pub lor_three_five: NameId,
    /// `Nat.ldiffAux : Nat → Nat → Nat → Nat`, `ldiffAux fuel m n`: the same
    /// fuel-recursion device as `landAux`/`lorAux`, fuel-exhaustion base
    /// case `landAux`'s shape (constant `0`) because `m` — the fuel-sized
    /// operand — is also `ldiff`'s absorbing-zero operand. `ldiffAux 0 m n
    /// ≡ 0`; `ldiffAux (succ f) m n ≡ if n = 0 then m else if m = 0 then 0
    /// else 2 * ldiffAux f (m/2) (n/2) + (if (n%2) = 0 then (m%2) else 0)`.
    /// Not the public name; [`Self::ldiff`] supplies fuel `m` itself. See
    /// `nat_prelude::ldiff` for the full derivation.
    pub ldiff_aux: NameId,
    /// `Nat.ldiff m n := Nat.ldiffAux m m n` — bitwise "AND NOT" (`Mathlib`:
    /// `Nat.ldiff`, via the general `Nat.bitwise`). Landed directly rather
    /// than through `Nat.bitwise`, same as `land`/`lor`.
    pub ldiff: NameId,
    /// `Nat.ldiff_zero_left : ∀ n, Eq (ldiff 0 n) 0` — `refl`: fuel is
    /// `m = 0`, so the outer `Nat.rec` hits `ldiffAux`'s constant-`0` base
    /// case immediately, regardless of `n`. Not a specific Mathlib name
    /// (this prelude's `ldiff` is not Mathlib's).
    pub ldiff_zero_left: NameId,
    /// `Nat.ldiff_zero_right : ∀ m, Eq (ldiff m 0) m` — induction on `m` to
    /// expose the fuel's constructor; each case is `refl`, no induction
    /// hypothesis needed, because the outermost `n = 0` guard collapses the
    /// term to `m` (unchanged) regardless of the fuel predecessor.
    pub ldiff_zero_right: NameId,
    /// `Nat.ldiff_three_five : Eq (ldiff 3 5) 2` — concrete sanity check,
    /// `0b011 &~ 0b101 = 0b010`.
    pub ldiff_three_five: NameId,
    /// `Nat.ldiff_five_three : Eq (ldiff 5 3) 4` — the asymmetry check:
    /// `0b101 &~ 0b011 = 0b100`, deliberately differing from
    /// `ldiff_three_five`'s `2` since, unlike `land`/`lor`, `ldiff` is not
    /// commutative.
    pub ldiff_five_three: NameId,
    /// `Nat.bitwiseAux : (Bool → Bool → Bool) → Nat → Nat → Nat → Nat`,
    /// `bitwiseAux f fuel m n`: the general form `land`/`lor`/`ldiff` were
    /// each landed instead of. Not the public name; [`Self::bitwise`]
    /// supplies fuel `m` itself. See `nat_prelude::bitwise` for the full
    /// derivation, including what the general `f` costs over the three
    /// specializations.
    pub bitwise_aux: NameId,
    /// `Nat.bitwise f m n := Nat.bitwiseAux f m m n` — the general
    /// `Bool → Bool → Bool`-parameterized bitwise combinator (`Mathlib`:
    /// `Nat.bitwise`), of which `land`/`lor`/`ldiff` are (unrelated,
    /// independently-defined) specializations.
    pub bitwise: NameId,
    /// `Nat.bitwise_zero_left : ∀ f n, Eq (bitwise f 0 n) (if f false true
    /// then n else 0)` — `refl`, for every `f`: fuel is `m = 0`, so the
    /// outer `Nat.rec` hits `bitwiseAux`'s fuel-exhaustion row directly,
    /// which IS this RHS by construction.
    pub bitwise_zero_left: NameId,
    /// `Nat.bitwise_zero_right : ∀ f m, Eq (bitwise f m 0) (if f true false
    /// then m else 0)` — induction on `m`; every step is `refl` (the
    /// `n = 0` guard collapses immediately, exactly `land_zero_right`'s
    /// shape), but the base case needs one extra `Bool`-case-split lemma
    /// (`bool_select_same` in `bitwise.rs`) that `land`/`lor`/`ldiff`'s
    /// zero-right theorems never needed. See `nat_prelude::bitwise`.
    pub bitwise_zero_right: NameId,
    /// `Nat.bitwise_and_eq_land_three_five : Eq (bitwise and_fn 3 5) (land
    /// 3 5)` — concrete specialization check (both sides reduce to `1`), in
    /// place of the universal `∀ m n` equivalence this lane did not
    /// attempt. `and_fn` is built inline in `bitwise.rs`; this prelude
    /// declares no top-level `Bool.and`.
    pub bitwise_and_eq_land_three_five: NameId,
    /// `Nat.bitwise_or_eq_lor_three_five : Eq (bitwise or_fn 3 5) (lor 3
    /// 5)` — the `lor` twin of [`Self::bitwise_and_eq_land_three_five`]
    /// (both sides reduce to `7`).
    pub bitwise_or_eq_lor_three_five: NameId,
    /// `Nat.bitwise_xor_three_five : Eq (bitwise xor_fn 3 5) 6` — no prelude
    /// XOR sibling exists to cross-check against, so this closes against a
    /// hand-computed numeral (`0b011 xor 0b101 = 0b110`) instead.
    pub bitwise_xor_three_five: NameId,
    /// `Nat.xor m n := Nat.bitwise xor_fn m n` — bitwise XOR (`Mathlib`:
    /// `Nat.xor`, via the general `Nat.bitwise`, the SAME shape as the
    /// upstream definition). Landed as a direct partial application of
    /// `Nat.bitwise` rather than a fourth hand-rolled fuel recursion —
    /// see `nat_prelude::xor`.
    pub xor: NameId,
    /// `Nat.xor_three_five : Eq (xor 3 5) 6` — concrete sanity check, the
    /// same reduction `bitwise_xor_three_five` already checks, now against
    /// the public `Nat.xor` name.
    pub xor_three_five: NameId,
    /// `Nat.even_xor : ∀ m n, Iff (Even (xor m n)) (Iff (Even m) (Even n))`
    /// (`F:ml430-nat-even-xor-78a39432`) — proved via
    /// `even_iff_mod_two_eq_zero` at `xor m n`/`m`/`n`, a boundary case
    /// split (`xor 0 n`/`xor m 0` reduce by `refl` to `n`/`m`, closing the
    /// goal to a trivial "always-true side" iff), and — in the genuinely
    /// bitwise case — one step of `bitwiseAux`'s own recursor exposing the
    /// per-bit combine, related to `mod _ 2` via `mod_two_mul_add_of_lt`
    /// and a four-leaf `cases_mod_two` case split. See `xor_parity.rs`.
    pub even_xor: NameId,
    /// `Nat.xor_comm : ∀ m n, Eq (xor m n) (xor n m)` — a corollary of
    /// `Nat.bitwise_comm` at `f := xor_fn`, with the `hf` commutativity
    /// witness built the same way
    /// `nat_prelude_tests.rs::bool_fn_comm` already builds and tests it
    /// (nested `Bool.rec`, four `refl` leaves). See `nat_prelude::xor_order`.
    /// One of the pieces Mathlib's own `Nat.lt_xor_cases` proof composes
    /// (`F:ml430-nat-lt-xor-cases-c43a1e85`, which stays open — see that
    /// file's module doc for what else is missing).
    pub xor_comm: NameId,
    /// `Nat.testBit_xor : ∀ m n i, Eq (testBit (xor m n) i) (xor_bit
    /// (testBit m i) (testBit n i))` — bridges `testBitAux`'s INDEX
    /// recursion with `bitwiseAux`'s VALUE recursion (piece 1 of 4 toward
    /// `F:ml430-nat-lt-xor-cases-c43a1e85`; `xor_bit` is the same per-bit
    /// combine `bitwiseAux`'s own `succ_minor` row builds at bit 0,
    /// generalized to an arbitrary bit position). Nat-valued (Mathlib's
    /// `testBit` returns `Bool`), so this is a local fact, not an `ml430`
    /// mirror. See `nat_prelude::testbit_bitwise`.
    pub test_bit_xor: NameId,
    /// `Nat.testBit_land : ∀ m n i, Eq (testBit (land m n) i)
    /// (mul (testBit m i) (testBit n i))` -- the Nat-valued AND analogue
    /// of `Nat.testBit_xor`, transported from `testbit_bitwise.rs`'s
    /// technique. Mathlib's `Nat.testBit_land` is `Bool`-valued, so this
    /// is a local fact, not an `ml430` mirror. See
    /// `nat_prelude::testbit_bitwise`.
    pub test_bit_land: NameId,
    /// `Nat.testBit_lor : ∀ m n i, Eq (testBit (lor m n) i)
    /// (bool_select_nat (ble (testBit m i) (testBit n i)) (testBit n i)
    /// (testBit m i))` -- the Nat-valued OR analogue of
    /// `Nat.testBit_xor`. Mathlib's `Nat.testBit_lor` is `Bool`-valued, so
    /// this is a local fact, not an `ml430` mirror. See
    /// `nat_prelude::testbit_bitwise`.
    pub test_bit_lor: NameId,
    /// `Nat.self_lt_two_pow : ∀ n, Lt n (pow 2 n)` — induction on `n`. See
    /// `nat_prelude::bit_order`.
    pub self_lt_two_pow: NameId,
    /// `Nat.self_lt_two_pow_add : ∀ a b, Lt a (pow 2 (add a b))` — the
    /// generalization of [`Self::self_lt_two_pow`] used to bound TWO
    /// independent values (`n`, `m`) by a SINGLE common power of two without
    /// any general `pow` monotonicity lemma: apply this directly at
    /// `a := n`/`a := m` with the OTHER value (plus a margin) folded into
    /// `b`. See `nat_prelude::bit_order`.
    pub self_lt_two_pow_add: NameId,
    /// `Nat.lt_of_testBit : ∀ n m i, Eq (testBit n i) zero → Eq (testBit m
    /// i) one → (∀ j, Lt i j → Eq (testBit n j) (testBit m j)) → Lt n m` —
    /// Nat-valued (Mathlib's `testBit` returns `Bool`; the pinned
    /// `Nat.lt_of_testBit`, `F:ml430-nat-lt-of-testbit-72f64ab8`, stays
    /// `open` for that reason), so this is a local fact, not an `ml430`
    /// mirror. Piece 3 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`. See
    /// `nat_prelude::bit_order`.
    pub lt_of_test_bit: NameId,
    /// `Nat.testBit_eq_zero_of_lt : ∀ n j, Lt n (pow 2 j) → Eq (testBit n
    /// j) zero` — the "cheap half" of `Nat.exists_most_significant_bit`
    /// (piece 2 of 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`): every bit
    /// at or above a value's own magnitude bound is zero. Nat-valued
    /// (Mathlib's `Nat.testBit_eq_false_of_lt` returns `Bool`), so this is
    /// a local fact, not an `ml430` mirror. See `nat_prelude::bit_order`.
    pub test_bit_eq_zero_of_lt: NameId,
    /// `Nat.msb_exists_of_le_fuel : ∀ fuel n, Le n fuel → Not (Eq n zero) →
    /// ∃ i, And (Eq (testBit n i) one) (∀ j, Lt i j → Eq (testBit n j)
    /// zero)` — the fuel-generalized "hard half" of
    /// `Nat.exists_most_significant_bit` (piece 2 of 4 toward
    /// `F:ml430-nat-lt-xor-cases-c43a1e85`): the highest bit really IS set,
    /// not just that no higher bit is needed. `Nat.size` does not shortcut
    /// this (it only ever proves an upper bound). See
    /// `nat_prelude::bit_order`.
    pub msb_exists_of_le_fuel: NameId,
    /// `Nat.exists_most_significant_bit : ∀ n, Not (Eq n zero) →
    /// ∃ i, And (Eq (testBit n i) one) (∀ j, Lt i j → Eq (testBit n j)
    /// zero)` — the `fuel := n` instance of
    /// [`Self::msb_exists_of_le_fuel`], via `le_refl`. Nat-valued
    /// (Mathlib's `testBit` returns `Bool`), so this is a local fact
    /// (`F:nat-exists-most-significant-bit`), not an `ml430` mirror. See
    /// `nat_prelude::bit_order`.
    pub exists_most_significant_bit: NameId,
    /// `Nat.eq_of_testBit_eq : ∀ m n, (∀ i, Eq (testBit m i) (testBit n i))
    /// → Eq m n` — "same bits imply the same number", the general
    /// extensionality lemma `Nat.zero_of_testBit_eq_zero`'s ONE-SIDED case
    /// generalizes to. Built toward `Nat.xor_assoc`/`xor_xor_cancel`/
    /// `xor_ne_zero_iff` (piece 4 toward `F:ml430-nat-lt-xor-cases-c43a1e85`,
    /// not itself declared this lane). See `nat_prelude::xor_algebra`.
    pub eq_of_test_bit_eq: NameId,
    /// `Nat.xor_assoc : ∀ a b c, Eq (xor (xor a b) c) (xor a (xor b c))` ---
    /// piece 4 (partial) toward `F:ml430-nat-lt-xor-cases-c43a1e85`, via
    /// `Nat.testBit_xor` twice per side plus `Nat.eq_of_testBit_eq`. See
    /// `nat_prelude::xor_algebra`.
    pub xor_assoc: NameId,
    /// `Nat.xor_xor_cancel_left : ∀ a b, Eq (xor a (xor a b)) b` --- via
    /// `Nat.testBit_xor` plus a `y <= 1` round-trip lemma (`Nat.testBit` is
    /// always in `{0, 1}`, via `Nat.testBit_le_one`): the natural per-bit
    /// cancel identity is FALSE for a general `Nat`, only for a bit. See
    /// `nat_prelude::xor_algebra`.
    pub xor_xor_cancel_left: NameId,
    /// `Nat.xor_xor_cancel_right : ∀ a b, Eq (xor (xor a b) b) a` ---
    /// transported from [`Self::xor_xor_cancel_left`] via `Nat.xor_comm`
    /// twice. See `nat_prelude::xor_algebra`.
    pub xor_xor_cancel_right: NameId,
    /// `Nat.xor_ne_zero_iff : ∀ a b, Iff (Not (Eq (xor a b) 0)) (Not (Eq a
    /// b))` --- the last of the four sub-targets (`Nat.xor_assoc`,
    /// `Nat.xor_xor_cancel_left`/`_right`, `Nat.xor_ne_zero_iff`) piece 4
    /// toward `F:ml430-nat-lt-xor-cases-c43a1e85` names. Matches Lean core
    /// `Nat.xor_ne_zero_iff : x ^^^ y ≠ 0 ↔ x ≠ y` (read from the pinned
    /// Batteries checkout, `Batteries/Data/Nat/Bitwise/Lemmas.lean:68`, not
    /// Mathlib-authored). Built via `mt` (modus tollens) applied twice to a
    /// forward corollary (`Eq (xor a b) 0 → Eq a b`, a direct consequence of
    /// `Nat.eq_of_testBit_eq` + `Nat.testBit_xor`, needing no cancel lemma)
    /// and a reverse corollary (`Eq a b → Eq (xor a b) 0`, via a new
    /// `Nat.xor` self-cancellation-to-zero argument) --- NOT via an `Iff` of
    /// `xor_eq_zero_iff`, since `mt` already produces both `Not`-`Not`
    /// directions directly. See `nat_prelude::xor_algebra`.
    pub xor_ne_zero_iff: NameId,
    /// `Nat.xor_trichotomy : ∀ a b c, Not (Eq (xor (xor a b) c) 0) → Or (Lt
    /// (xor b c) a) (Or (Lt (xor c a) b) (Lt (xor a b) c))` — Mathlib's own
    /// route to `Nat.lt_xor_cases`, composing `Nat.exists_most_significant_bit`
    /// with `Nat.lt_of_testBit` and the `xor_assoc`/`xor_xor_cancel_left`/
    /// `xor_comm` family for the three rotation identities. See
    /// `nat_prelude::xor_trichotomy`.
    pub xor_trichotomy: NameId,
    /// `Nat.lt_xor_cases : ∀ a b c, Lt a (xor b c) → Or (Lt (xor a c) b) (Lt
    /// (xor a b) c)` — `F:ml430-nat-lt-xor-cases-c43a1e85`, fully `Nat`-valued
    /// (no `testBit`/`Bool` in the statement), so an honest mirror flip once
    /// proved. See `nat_prelude::xor_trichotomy`.
    pub lt_xor_cases: NameId,
    /// `Nat.lt_two_cases : ∀ r, Lt r 2 → Or (Eq r 0) (Eq r 1)` — the
    /// propositional form of the two-way bounded split. See
    /// `nat_prelude::rec_agreement`.
    pub lt_two_cases: NameId,
    /// `Nat.mod_two_eq_zero_or_one : ∀ n, Or (Eq (mod n 2) 0) (Eq (mod n 2)
    /// 1)` — the `Nat.mod _ 2 ∈ {0, 1}` fact `bitwise.rs`'s module doc named
    /// as a lemma "this prelude does not yet carry". The eliminator form
    /// (a motive varying with the remainder's value) is `ops::cases_mod_two`.
    pub mod_two_eq_zero_or_one: NameId,
    /// `Nat.bitwise_aux_eq_land_aux : ∀ fuel m n, Eq (bitwiseAux and_fn fuel
    /// m n) (landAux fuel m n)` — the FUEL-GENERALIZED agreement, true at
    /// arbitrary fuel rather than only the canonical `fuel = m`, of which
    /// [`Self::bitwise_and_eq_land`] is the instance at `fuel := m`. Exposed
    /// separately because a caller reasoning about a non-canonical fuel needs
    /// this form, and because it makes fuel-irrelevance for `bitwiseAux` and
    /// for `landAux` interderivable. See `nat_prelude::rec_agreement`.
    pub bitwise_aux_eq_land_aux: NameId,
    /// `Nat.bitwise_aux_eq_lor_aux : ∀ fuel m n, Eq (bitwiseAux or_fn fuel m
    /// n) (lorAux fuel m n)` — the `lor` twin of
    /// [`Self::bitwise_aux_eq_land_aux`].
    pub bitwise_aux_eq_lor_aux: NameId,
    /// `Nat.bitwise_and_eq_land : ∀ m n, Eq (bitwise and_fn m n) (land m n)`
    /// — the UNIVERSAL specialization equivalence, superseding
    /// [`Self::bitwise_and_eq_land_three_five`]'s single concrete witness.
    /// Proved by induction on the shared fuel counter with both operands
    /// generalized in the motive; see `nat_prelude::rec_agreement`.
    pub bitwise_and_eq_land: NameId,
    /// `Nat.bitwise_or_eq_lor : ∀ m n, Eq (bitwise or_fn m n) (lor m n)` —
    /// the `lor` twin of [`Self::bitwise_and_eq_land`], and the evidence that
    /// the agreement route is not specific to an operator with an absorbing
    /// zero on the fuel operand (`lor` has none; see `lor.rs`).
    pub bitwise_or_eq_lor: NameId,
    /// `Nat.land_aux_zero_left_any_fuel : ∀ fuel n, Eq (landAux fuel 0 n) 0`
    /// — unlike [`Self::land_zero_left`] (which needs no lemma because
    /// `Nat.land` supplies fuel `= m = 0` automatically), this holds at
    /// *any* fuel, sufficient or not: the base row is the constant `0`
    /// regardless of `m`, `n`, and at `fuel = succ f` the `m = 0` guard
    /// fires immediately (`m` is the LITERAL `0`), short-circuiting the
    /// recursive call. See `nat_prelude::rec_agreement`.
    pub land_aux_zero_left_any_fuel: NameId,
    /// `Nat.land_aux_agree_of_fuel : ∀ fuel1 m n fuel2, Le m fuel1 → Le m
    /// fuel2 → Eq (landAux fuel1 m n) (landAux fuel2 m n)` — TWO
    /// independently-chosen sufficient fuels agree, proved by induction on
    /// `fuel1` alone with `m`, `n`, `fuel2` all generalized
    /// ([`ops::agree_by_double_fuel_induction`]). The two-fuel form, not a
    /// fuel-vs-canonical form, is what avoids ever needing `landAux`'s OWN
    /// canonical instance (`landAux m m n`) to unfold via `m`'s shape — see
    /// `nat_prelude::rec_agreement`'s module doc.
    pub land_aux_agree_of_fuel: NameId,
    /// `Nat.land_aux_eq_land_of_le : ∀ fuel m n, Le m fuel → Eq (landAux
    /// fuel m n) (land m n)` — fuel-irrelevance for `landAux`, the blocker
    /// named by `land_comm`/`land_assoc`/`land_bit`/`lor_comm`/`lor_assoc`/
    /// `lor_bit`/`ldiff_bit`. A one-line corollary of
    /// [`Self::land_aux_agree_of_fuel`] at `fuel2 := m` (`le_refl`), since
    /// `landAux m m n` and `land m n` are the SAME term by definition.
    pub land_aux_eq_land_of_le: NameId,
    /// `Nat.lor_aux_zero_left_any_fuel : ∀ fuel n, Eq (lorAux fuel 0 n) n` —
    /// the `lor` twin of [`Self::land_aux_zero_left_any_fuel`], closing to
    /// `n` rather than `0` (`lorAux`'s fuel-exhaustion row RETURNS `n`; see
    /// `lor.rs`'s module doc). Unlike the `land` version, the `fuel = succ f`
    /// case genuinely needs `n`'s shape exposed (a nested case split), since
    /// its two guard branches are `m` (`= 0`, literal) and the reduced inner
    /// term (`= n`) — two DIFFERENT terms, not one repeated. See
    /// `nat_prelude::rec_agreement`.
    pub lor_aux_zero_left_any_fuel: NameId,
    /// `Nat.lor_aux_agree_of_fuel : ∀ fuel1 m n fuel2, Le m fuel1 → Le m
    /// fuel2 → Eq (lorAux fuel1 m n) (lorAux fuel2 m n)` — the `lor` twin of
    /// [`Self::land_aux_agree_of_fuel`]. See `nat_prelude::rec_agreement`.
    pub lor_aux_agree_of_fuel: NameId,
    /// `Nat.lor_aux_eq_lor_of_le : ∀ fuel m n, Le m fuel → Eq (lorAux fuel m
    /// n) (lor m n)` — fuel-irrelevance for `lorAux`, the `lor` twin of
    /// [`Self::land_aux_eq_land_of_le`].
    pub lor_aux_eq_lor_of_le: NameId,
    /// `Nat.ldiff_aux_zero_left_any_fuel : ∀ fuel n, Eq (ldiffAux fuel 0 n)
    /// 0` — the `ldiff` twin of [`Self::land_aux_zero_left_any_fuel`],
    /// byte-for-byte the same proof (`ldiffAux` shares `land`'s
    /// absorbing-zero base case exactly — see `ldiff.rs`'s module doc).
    pub ldiff_aux_zero_left_any_fuel: NameId,
    /// `Nat.ldiff_aux_agree_of_fuel : ∀ fuel1 m n fuel2, Le m fuel1 → Le m
    /// fuel2 → Eq (ldiffAux fuel1 m n) (ldiffAux fuel2 m n)` — the `ldiff`
    /// twin of [`Self::land_aux_agree_of_fuel`], with `ldiffAux`'s hybrid
    /// guards in the `m = succ predecessor` step (`on_n_zero = m`
    /// pass-through, `on_m_zero = 0` absorbing — see `ldiff.rs`'s module
    /// doc) and its `beq`-based per-bit combine.
    pub ldiff_aux_agree_of_fuel: NameId,
    /// `Nat.ldiff_aux_eq_ldiff_of_le : ∀ fuel m n, Le m fuel → Eq (ldiffAux
    /// fuel m n) (ldiff m n)` — fuel-irrelevance for `ldiffAux`, the `ldiff`
    /// twin of [`Self::land_aux_eq_land_of_le`].
    pub ldiff_aux_eq_ldiff_of_le: NameId,
    /// `Nat.land_aux_comm_of_fuel : ∀ fuel m n, Eq (landAux fuel m n)
    /// (landAux fuel n m)` — commutativity of `landAux` at a SHARED fuel.
    /// The second piece (beyond fuel-irrelevance) `land_comm` needs: since
    /// `land`'s guard is symmetric (both `on_n_zero`/`on_m_zero` are the
    /// constant `0`), swapping the value arguments only changes WHICH guard
    /// fires first, never the answer.
    pub land_aux_comm_of_fuel: NameId,
    /// `Nat.land_comm : ∀ m n, Eq (land m n) (land n m)` — one of the seven
    /// `natural-bitwise` facts fuel-irrelevance was blocking
    /// (`F:ml430-nat-land-comm-7e6ad72e`). Proved by routing
    /// [`Self::land_aux_comm_of_fuel`] and [`Self::land_aux_agree_of_fuel`]
    /// through the shared fuel `m + n`.
    pub land_comm: NameId,
    /// `Nat.lor_aux_comm_of_fuel : ∀ fuel m n, Le m fuel → Le n fuel →
    /// Eq (lorAux fuel m n) (lorAux fuel n m)` — the `lor` twin of
    /// [`Self::land_aux_comm_of_fuel`], and NOT unconditional the way
    /// `land`'s version is: `lorAux`'s fuel-exhaustion row returns `n`
    /// (pass-through, not the absorbing `0`), so at `fuel = 0` the
    /// statement `lorAux 0 m n = lorAux 0 n m` reduces to `n = m`, false
    /// for arbitrary `m ≠ n`. Both `Le m fuel` and `Le n fuel` are needed —
    /// they force `m = n = 0` at the base case and supply
    /// `half_le_predecessor_of_succ` for BOTH operands in the step (unlike
    /// `land_aux_comm_of_fuel`, which needs neither). See
    /// `nat_prelude::rec_agreement`.
    pub lor_aux_comm_of_fuel: NameId,
    /// `Nat.lor_comm : ∀ m n, Eq (lor m n) (lor n m)` — the `lor` twin of
    /// [`Self::land_comm`], one of the seven `natural-bitwise` facts
    /// fuel-irrelevance was blocking
    /// (`F:ml430-nat-lor-comm-2666d7ef`). Routes
    /// [`Self::lor_aux_comm_of_fuel`] and [`Self::lor_aux_agree_of_fuel`]
    /// through the shared fuel `m + n`, exactly as `land_comm` does.
    pub lor_comm: NameId,
    /// `Nat.land_aux_le_left : ∀ fuel m n, Le (landAux fuel m n) m` —
    /// `landAux` never exceeds its LEFT operand, at ANY fuel (sufficient or
    /// not). Needed to re-fuel a NESTED `landAux` occupying an argument
    /// position (e.g. `landAux fuel (landAux fuel a b) c`, `land_assoc`'s
    /// shape): [`Self::land_le_left`] gives `land a b ≤ a` for free, which
    /// [`Self::land_aux_agree_of_fuel`] then uses to move the outer
    /// application's fuel down to `land a b`'s own canonical fuel. See
    pub land_aux_le_left: NameId,
    /// `Nat.land_le_left : ∀ a b, Le (land a b) a` — [`Self::land_aux_le_left`]
    /// at `fuel := a`, `m := a` (`land a b` and `landAux a a b` are the SAME
    /// term by definition).
    pub land_le_left: NameId,
    /// `Nat.land_le_right : ∀ a b, Le (land a b) b` — the mirror of
    /// [`Self::land_le_left`], via [`Self::land_comm`] transporting
    /// `land_le_left b a : Le (land b a) b` along `Eq (land b a) (land a b)`.
    /// Needed only for `Nat.and_le_right`'s `ml430` mirror (Mathlib's
    /// `&&&` is our `Nat.land`, so this is a genuinely new lemma about an
    /// already-proved function, not fresh bitwise machinery).
    pub land_le_right: NameId,
    /// `Nat.land_aux_self_of_fuel : ∀ fuel a, Le a fuel → Eq (landAux fuel a
    /// a) a` — fuel induction on a SINGLE generalized value argument (`a`
    /// used in both the `m` and `n` slots), unlike
    /// [`Self::land_aux_comm_of_fuel`]'s two independent slots: since
    /// `land a a := landAux a a a` already puts the same value in the fuel
    /// slot, no second-fuel bridge is needed, only the ordinary sufficiency
    /// hypothesis (`nat_prelude::land_self`).
    pub land_aux_self_of_fuel: NameId,
    /// `Nat.land_self : ∀ x, Eq (land x x) x` — `F:ml430-nat-and-self-06a84ccc`
    /// (Mathlib's `&&&` is our `Nat.land`), [`Self::land_aux_self_of_fuel`]
    /// at `fuel := x`, `a := x` via `le_refl`.
    pub land_self: NameId,
    /// `Nat.land_one_is_mod : ∀ x, Eq (land x 1) (mod x 2)` —
    /// `F:ml430-nat-and-one-is-mod-d861e96b`. Via [`Self::land_comm`]
    /// (`land x 1 = land 1 x`) then ONE unfold of `landAux` at the now-FIXED
    /// concrete fuel `1`: the recursive sub-call's fuel becomes the LITERAL
    /// `0`, collapsing by `refl` with no induction at all
    /// (`nat_prelude::land_low_bit`).
    pub land_one_is_mod: NameId,
    /// `Nat.land_mod_two_eq_mul : ∀ a b, Eq (mod (land a b) 2) (mul (mod a 2)
    /// (mod b 2))` — the AND analogue of [`Self::even_xor`]'s technique: the
    /// goal only mentions the LOW BIT of `land a b`, so one unfold of
    /// `landAux`'s succ-row plus [`super::parity::mod_two_mul_add_of_lt`]
    /// erases the higher recursive term without any induction. Boundary
    /// cases (`a = 0`/`b = 0`) via [`Self::land_zero_left`]/
    /// [`Self::land_zero_right`] (`nat_prelude::land_low_bit`).
    pub land_mod_two_eq_mul: NameId,
    /// `Nat.land_mod_two_eq_one : ∀ a b, Iff (Eq (mod (land a b) 2) 1)
    /// (And (Eq (mod a 2) 1) (Eq (mod b 2) 1))` —
    /// `F:ml430-nat-and-mod-two-eq-one-3e873792`. [`Self::land_mod_two_eq_mul`]
    /// reduces this to a purely numeric fact about a product of two `{0,1}`
    /// values, closed by [`super::ops::cases_mod_two`] twice.
    pub land_mod_two_eq_one: NameId,
    /// `Nat.land_div_two : ∀ a b, Eq (div (land a b) 2) (land (div a 2)
    /// (div b 2))` — `F:ml430-nat-and-div-two-1a2f7c33`. The `div` twin of
    /// [`Self::land_mod_two_eq_mul`]: one unfold of `landAux`'s succ-row plus
    /// `div_two_mul_add_of_lt` erases the LOW bit, and fuel-irrelevance
    /// (`land_aux_agree_of_fuel`) relates the erased recursive term to the
    /// canonical `land (div a 2) (div b 2)` (`nat_prelude::land_div_two`).
    pub land_div_two: NameId,
    /// `Nat.bit_div_two : ∀ test n, Eq (div (bit test n) 2) n` — one half of
    /// the `Nat.bit` decode bridge (`nat_prelude::bit_decode`), via
    /// `div_mod_unique` against the executable `div_mod_exec` projections.
    pub bit_div_two: NameId,
    /// `Nat.bit_mod_two : ∀ test n, Eq (mod (bit test n) 2) (bool_select_nat
    /// test 1 0)` — the other half of the decode bridge, from the SAME
    /// `div_mod_unique` witness as [`Self::bit_div_two`].
    pub bit_mod_two: NameId,
    /// `Nat.land_bit : ∀ a m b n, Eq (land (bit a m) (bit b n)) (bit (and a
    /// b) (land m n))` — `F:ml430-nat-land-bit-b9ab7475`, closed via the
    /// `Nat.bit` decode bridge (`nat_prelude::bit_decode`).
    pub land_bit: NameId,
    /// `Nat.lor_bit : ∀ a m b n, Eq (lor (bit a m) (bit b n)) (bit (or a b)
    /// (lor m n))` — `F:ml430-nat-lor-bit-a2f98c7c`, same decode bridge as
    /// [`Self::land_bit`] with `lor`'s own guard rows and per-bit `max`
    /// combine.
    pub lor_bit: NameId,
    /// `Nat.ldiff_bit : ∀ a m b n, Eq (ldiff (bit a m) (bit b n)) (bit (and a
    /// (not b)) (ldiff m n))` — `F:ml430-nat-ldiff-bit-6be49bb8`, same decode
    /// bridge with `ldiff`'s hybrid guard rows.
    pub ldiff_bit: NameId,

    // --- `Nat.Pair` and `Nat.binaryRec` (`binary_rec.rs`) -------------------
    /// `Nat.Pair : Type 0` — the monomorphic `Nat x Nat` product, a
    /// zero-parameter one-constructor inductive. This prelude's FIRST product
    /// type; before it, a pair-shaped value had to be encoded as a
    /// `Bool`-selected function (`Nat.xgcdAux`, `Nat.divModState`).
    pub pair: NameId,
    /// `Nat.Pair.mk : Nat -> Nat -> Nat.Pair`.
    pub pair_mk: NameId,
    /// `Nat.Pair.rec` — the kernel-generated recursor both projections go
    /// through.
    pub pair_rec: NameId,
    /// `Nat.Pair.fst : Nat.Pair -> Nat`.
    pub pair_fst: NameId,
    /// `Nat.Pair.snd : Nat.Pair -> Nat`.
    pub pair_snd: NameId,
    /// `Nat.Pair.fst_mk : ∀ a b, Eq Nat (fst (mk a b)) a` — `refl`.
    pub pair_fst_mk: NameId,
    /// `Nat.Pair.snd_mk : ∀ a b, Eq Nat (snd (mk a b)) b` — `refl`.
    pub pair_snd_mk: NameId,
    /// `Nat.Pair.eta : ∀ q, Eq Pair (mk (fst q) (snd q)) q`.
    pub pair_eta: NameId,
    /// `Nat.Pair.ext : ∀ q r, Eq Nat (fst q) (fst r) -> Eq Nat (snd q) (snd r)
    /// -> Eq Pair q r`.
    pub pair_ext: NameId,
    /// `Nat.lt_two_mul_of_pos : ∀ n, Lt zero n -> Lt n (mul 2 n)` — the named
    /// home for arithmetic that existed as an unnamed private copy in
    /// `log.rs`, `binary.rs`, `powsq.rs` and `rec_agreement.rs`.
    pub lt_two_mul_of_pos: NameId,
    /// `Nat.half_le_of_succ_le_succ : ∀ m k, Le (succ m) (succ k) ->
    /// Le (div (succ m) 2) k` — the fuel-sufficiency step every halving family
    /// in this prelude needs, likewise previously duplicated four times.
    pub half_le_of_succ_le_succ: NameId,
    /// `Nat.binaryRecAux alpha z f fuel n` — bit-halving recursion with an
    /// explicit fuel counter (`binary_rec.rs`). NOT Mathlib's `Nat.binaryRec`,
    /// which is well-founded recursion on a `log2` measure with a dependent
    /// motive; see the module doc.
    pub binary_rec_aux: NameId,
    /// `Nat.binaryRec alpha z f n := binaryRecAux alpha z f n n` — the
    /// canonical instantiation, fuel `= n`.
    pub binary_rec: NameId,
    /// `Nat.binaryRecAux_zero_fuel : ∀ alpha z f n, binaryRecAux … 0 n = z` —
    /// `refl`.
    pub binary_rec_aux_zero_fuel: NameId,
    /// `Nat.binaryRecAux_zero : ∀ alpha z f fuel, binaryRecAux … fuel 0 = z` —
    /// holds at ANY fuel, sufficient or not.
    pub binary_rec_aux_zero: NameId,
    /// `Nat.binaryRecAux_succ : ∀ alpha z f k m, binaryRecAux … (succ k)
    /// (succ m) = f (beq ((succ m) % 2) 1) ((succ m) / 2)
    /// (binaryRecAux … k ((succ m) / 2))` — `refl`.
    pub binary_rec_aux_succ: NameId,
    /// `Nat.binaryRec_zero : ∀ alpha z f, binaryRec alpha z f 0 = z` — `refl`.
    pub binary_rec_zero: NameId,
    /// `Nat.binaryRecAux_agree_of_fuel : ∀ alpha z f fuel1 n fuel2,
    /// Le n fuel1 -> Le n fuel2 -> Eq alpha (binaryRecAux … fuel1 n)
    /// (binaryRecAux … fuel2 n)` — the DOUBLE-fuel irrelevance theorem.
    pub binary_rec_aux_agree_of_fuel: NameId,
    /// `Nat.binaryRec_succ : ∀ alpha z f m, binaryRec … (succ m) =
    /// f (beq ((succ m) % 2) 1) ((succ m) / 2) (binaryRec … ((succ m) / 2))` —
    /// the recursive equation Mathlib's well-founded `binaryRec` has
    /// definitionally and a fuel encoding has to prove.
    pub binary_rec_succ: NameId,
    /// `Nat.binaryRec_rebuilds_thirteen : Eq (binaryRec Nat 0
    /// (fun b _ acc => bit b acc) 13) 13` — the evaluation check the trusted
    /// gate cannot perform (a `Definition` is admitted on its TYPE).
    pub binary_rec_rebuilds_thirteen: NameId,
    /// `Nat.binaryRec_rebuilds_six : Eq (binaryRec Nat 0
    /// (fun b _ acc => bit b acc) 6) 6` — the same round trip at a value with
    /// a trailing zero bit.
    pub binary_rec_rebuilds_six: NameId,
    /// `Nat.bitwise_aux_zero_left_any_fuel : ∀ f fuel n, Eq (bitwiseAux f
    /// fuel 0 n) (bool_select_nat (f false true) n 0)` — unconditional in
    /// `f`, the `bitwise` twin of [`Self::land_aux_zero_left_any_fuel`].
    /// See `nat_prelude::bitwise`.
    pub bitwise_aux_zero_left_any_fuel: NameId,
    /// `Nat.bitwise_aux_agree_of_fuel : ∀ f fuel1 m n fuel2, Le m fuel1 → Le
    /// m fuel2 → Eq (bitwiseAux f fuel1 m n) (bitwiseAux f fuel2 m n)` —
    /// the `bitwise` twin of [`Self::land_aux_agree_of_fuel`], generalized
    /// over `f` (no commutativity hypothesis needed: fuel-irrelevance never
    /// swaps the value arguments). See `nat_prelude::bitwise`.
    pub bitwise_aux_agree_of_fuel: NameId,
    /// `Nat.bitwise_aux_comm_of_fuel : ∀ f, (∀ a b, Eq (f a b) (f b a)) → ∀
    /// fuel m n, Le m fuel → Le n fuel → Eq (bitwiseAux f fuel m n)
    /// (bitwiseAux f fuel n m)` — `lor`'s shape (both `Le` hypotheses), not
    /// `land`'s unconditional one: a Python simulation showed the
    /// unconditional form is false whenever `f false true = true` (`or`,
    /// `xor`). See `nat_prelude::bitwise`.
    pub bitwise_aux_comm_of_fuel: NameId,
    /// `Nat.bitwise_comm : ∀ f, (∀ a b, Eq (f a b) (f b a)) → ∀ m n, Eq
    /// (bitwise f m n) (bitwise f n m)` — `F:ml430-nat-bitwise-comm-1a273bae`.
    /// Routes [`Self::bitwise_aux_comm_of_fuel`] and
    /// [`Self::bitwise_aux_agree_of_fuel`] through the shared fuel `m + n`,
    /// exactly as `land_comm`/`lor_comm`. See `nat_prelude::bitwise`.
    pub bitwise_comm: NameId,
    /// `Nat.land_aux_eq_zero_of_left_eq_zero : ∀ fuel a b c,
    /// Eq (landAux fuel a b) 0 → Eq (landAux fuel a (landAux fuel b c)) 0`
    /// — "zero propagates through the other operand": built for
    /// `nat-land-assoc-impl`'s `land_aux_assoc_of_fuel`, the one theorem
    /// `docs/plan/status/252-nat-assoc-dichotomy.md` traced by hand and
    /// numerically cross-checked but did not build (both belonged in this
    /// file, under active concurrent edit at the time). Proved by a triple
    /// fuel induction ([`agree_by_double_fuel_induction`](rec_agreement)):
    /// 3 of 4 base leaves (`a=0`; `a=succ,b=0`; `a=succ,b=succ,c=0`) close
    /// by [`Self::land_aux_zero_left_any_fuel`] or pure defeq, and the
    /// fourth (`a,b,c` all positive) needs `Nat.add_eq_zero`/
    /// `Nat.mul_eq_zero`/`Nat.succ_ne_zero` to extract `rec=0 ∧ bit=0` from
    /// the hypothesis, then `Nat.zero_or_succ` to dichotomize the inner
    /// `landAux fuel b c`, then (in the nonzero sub-case)
    /// `Nat.div_mod_unique`+`Nat.div_mod_exec` to reconstruct that value's
    /// own halves and feed them back through the induction's own `ih`.
    pub land_aux_eq_zero_of_left_eq_zero: NameId,
    /// `Nat.bitwise_aux_swap_of_fuel : ∀ f fuel m n, Le m fuel → Le n fuel →
    /// Eq (bitwiseAux (swap f) fuel m n) (bitwiseAux f fuel n m)` — the
    /// `swap` counterpart of [`Self::bitwise_aux_comm_of_fuel`], and
    /// strictly simpler: no `hf` hypothesis, since `swap f` applied to any
    /// two `Bool`s beta-reduces directly to `f` applied to them in the
    /// other order. See `nat_prelude::bitwise`.
    pub bitwise_aux_swap_of_fuel: NameId,
    /// `Nat.bitwise_swap : ∀ f m n, Eq (bitwise (swap f) m n) (bitwise f n
    /// m)` — `F:ml430-nat-bitwise-swap-7175e90e`. Routes
    /// [`Self::bitwise_aux_swap_of_fuel`] and
    /// [`Self::bitwise_aux_agree_of_fuel`] through the shared fuel `m + n`,
    /// exactly as `bitwise_comm`'s own assembly. See `nat_prelude::bitwise`.
    pub bitwise_swap: NameId,
    /// `Nat.land_aux_assoc_of_fuel : ∀ fuel a b c,
    /// Eq (landAux fuel (landAux fuel a b) c) (landAux fuel a (landAux fuel b c))`
    /// — unconditional (no `Le` hypothesis; `land`'s fuel-exhaustion row is
    /// the absorbing constant `0`, so any fuel works). Proved by
    /// [`agree_by_double_fuel_induction`](rec_agreement::ops), with the
    /// step case split `c`, then `b`, then `a` (verified against
    /// `guarded`'s actual n-outermost guard order, per
    /// `docs/plan/status/257-nat-land-assoc-impl.md`): 3 of 4 base leaves
    /// close by pure computation or [`Self::land_aux_zero_left_any_fuel`],
    /// and the hard leaf (`a,b,c` all positive) dichotomizes the two
    /// nested values via [`Self::zero_or_succ`], using
    /// [`Self::land_aux_eq_zero_of_left_eq_zero`] directly for one
    /// sub-case, its mirror via [`Self::land_aux_comm_of_fuel`] for
    /// another, and a double `Nat.div_mod_unique` reconstruction (one per
    /// nested value) closing via the outer induction's own `ih` plus
    /// `Nat.mul_assoc` for the fully generic sub-case. See
    /// `nat_prelude::rec_agreement`.
    pub land_aux_assoc_of_fuel: NameId,
    /// `Nat.land_assoc : ∀ a b c, Eq (land (land a b) c) (land a (land b c))`
    /// — `F:ml430-nat-land-assoc-ad4775b8`. Routes
    /// [`Self::land_aux_assoc_of_fuel`] and
    /// [`Self::land_aux_agree_of_fuel`] through the shared fuel
    /// `add a b`, exactly as [`Self::land_comm`] (one argument wider; `c`
    /// itself never needs its own `Le` bound, since
    /// `land_aux_agree_of_fuel`'s hypotheses constrain only the `m`
    /// position). See `nat_prelude::rec_agreement`.
    pub land_assoc: NameId,
    /// `Nat.bitwise_bit' : ∀ f (a : Bool) (m : Nat) (b : Bool) (n : Nat), (Eq
    /// m 0 -> Eq a true) -> (Eq n 0 -> Eq b true) -> Eq (bitwise f (bit a m)
    /// (bit b n)) (bit (f a b) (bitwise f m n))` —
    /// `F:ml430-nat-bitwise-bit-4c4b28a8`, the generic-`f` counterpart of
    /// [`Self::land_bit`]/[`Self::lor_bit`]/[`Self::ldiff_bit`]. Same
    /// fuel-swap bridge, but the per-bit combine must undo `bitwiseAux`'s
    /// `beq _ 1` bit-to-`Bool` conversion, and the two side hypotheses close
    /// a leading-zero ambiguity the fixed-`f` specializations never have.
    /// See `nat_prelude::bitwise`.
    pub bitwise_bit: NameId,
    /// `Nat.lor_aux_ne_zero_of_right_ne_zero : ∀ fuel m n, Not (Eq n 0) →
    /// Not (Eq (lorAux (succ fuel) m n) 0)` — the invariant that plays
    /// `land_aux_eq_zero_of_left_eq_zero`'s role for `lor`, and NOT its
    /// direct analogue: OR has no absorbing zero, so "zero propagates" is
    /// false for `lor` (`lor a b = 0` forces `a = b = 0`, so
    /// `lor a (lor b c)` collapses to `c`, not `0`). What DOES hold,
    /// confirmed by exhaustive Python simulation before any Rust: at any
    /// fuel of the form `succ _`, a positive RIGHT operand alone forces a
    /// positive result, independent of the left operand's shape. Proved by
    /// induction on `fuel` ([`agree_by_fuel_induction`](rec_agreement::ops)):
    /// the `n = 0` branch is immediate from the hypothesis; the `m = 0`
    /// branch reduces to `Not (Eq (succ n') 0)` via `Nat.succ_ne_zero`; the
    /// both-positive branch case-splits `Nat.mod n 2` (`Nat.cases_mod_two`,
    /// folding `Nat.div_mod_exec`'s reconstruction equation into an
    /// ARROW-typed motive, since the split does not otherwise expose it as
    /// a usable hypothesis): bit 1 closes at either bit of `m` via
    /// `Nat.succ_ne_zero` alone (`add x 1` is defeq `succ x`); bit 0 needs
    /// `Nat.div_mod_exec` to show the half must itself be nonzero (else `n`
    /// would be `0`, contradicting its own literal `succ` shape), then the
    /// SAME `mul_eq_zero`/`succ_ne_zero` contrapositive `land`'s zero-
    /// propagation lemma uses, applied to the half (via `ih` in the step
    /// case, directly in the base case since `lorAux 0 _ _` is the
    /// zero-fuel row's own third argument). See `nat_prelude::rec_agreement`.
    pub lor_aux_ne_zero_of_right_ne_zero: NameId,
    /// `Nat.lor_aux_assoc_of_fuel : ∀ fuel a b c,
    /// Eq (lorAux fuel (lorAux fuel a b) c) (lorAux fuel a (lorAux fuel b c))`
    /// — `lor`'s counterpart of [`Self::land_aux_assoc_of_fuel`], via
    /// [`agree_by_double_fuel_induction`](rec_agreement::ops), same
    /// `c`-then-`b`-then-`a` split order. SIMPLER than `land`'s hard leaf:
    /// [`Self::lor_aux_ne_zero_of_right_ne_zero`] makes the two stuck
    /// intermediates unconditionally positive here, so both dichotomies'
    /// `= 0` branches close by direct contradiction rather than a mirrored
    /// propagation argument, and the per-bit step uses a new
    /// max-associativity fact (`bool_select_nat`/`ble` shape, three nested
    /// `Nat.mod _ 2` splits, 8 leaves) in place of `Nat.mul_assoc`. See
    /// `docs/plan/status/266-nat-lor-assoc.md` and
    /// `nat_prelude::rec_agreement`.
    pub lor_aux_assoc_of_fuel: NameId,
    /// `Nat.lor_aux_le_add : ∀ fuel m n, Le (lorAux fuel m n) (add m n)` —
    /// the refuel bound `lor_assoc`'s bookkeeping needs in place of
    /// [`Self::land_le_left`] (`Nat.lor` has no left-operand bound analogue:
    /// `lor` can exceed both operands, e.g. `lor 1 2 = 3`). Unconditional in
    /// `fuel`, confirmed by exhaustive Python simulation before any Rust.
    /// Proved by [`agree_by_fuel_induction`](rec_agreement::ops): the base
    /// case and the `n = 0`/`m = 0` step rows close via `Nat.le_add_right`
    /// plus an `Nat.add_comm`/`Nat.zero_add`/`Nat.add_zero` transport; the
    /// both-positive row combines the IH (`Le rec (add half_m half_n)`)
    /// with a new `max bit_m bit_n ≤ add bit_m bit_n` fact via
    /// `Nat.mul_le_mul_left`/`Nat.left_distrib`/`Nat.add_le_add_left`/
    /// `Nat.add_le_add_right`/`Nat.le_trans`, then rearranges
    /// `(2·half_m+2·half_n)+(bit_m+bit_n)` to `succ_m+succ_n` via the
    /// per-file `add_add_add_comm` four-term regrouping (see
    /// `nat_prelude::binomial`'s own copy) plus the two `Nat.div_mod_exec`
    /// decompositions. See `docs/plan/status/266-nat-lor-assoc.md` and
    /// `nat_prelude::rec_agreement`.
    pub lor_aux_le_add: NameId,
    /// `Nat.lor_assoc : ∀ a b c, Eq (lor (lor a b) c) (lor a (lor b c))` —
    /// `F:ml430-nat-lor-assoc-82c4d0fd`. Routes
    /// [`Self::lor_aux_assoc_of_fuel`] and [`Self::lor_aux_agree_of_fuel`]
    /// through the shared fuel `add a b`, exactly as [`Self::land_assoc`]
    /// (one argument wider; `c` itself never needs its own `Le` bound).
    /// Unlike `land_assoc`, the bound `Le (lor a b) (add a b)` comes
    /// directly from [`Self::lor_aux_le_add`] at `(a, a, b)` — the bound
    /// already targets the shared fuel exactly, so no `Nat.le_trans` chain
    /// is needed (`land_assoc` needs one, via `Nat.land_le_left`). See
    /// `nat_prelude::rec_agreement`.
    pub lor_assoc: NameId,

    // --- `Nat` ordering under multiplication and division (mul_order_lemmas.rs) --
    /// `Nat.lt_of_mul_lt_mul_left : ∀ a b c, Lt (mul a b) (mul a c) → Lt b c` —
    /// `F:ml430-nat-lt-of-mul-lt-mul-left-234e8530`. NO positivity hypothesis:
    /// true even at `a = 0`, since the hypothesis is then vacuous.
    pub lt_of_mul_lt_mul_left: NameId,
    /// `Nat.lt_of_mul_lt_mul_right : ∀ a b c, Lt (mul b a) (mul c a) → Lt b c`
    /// — `F:ml430-nat-lt-of-mul-lt-mul-right-54c1120b`, the mirror of
    /// [`Self::lt_of_mul_lt_mul_left`].
    pub lt_of_mul_lt_mul_right: NameId,
    /// `Nat.mul_lt_mul_left : ∀ a b c, Lt zero a → Iff (Lt (mul a b) (mul a
    /// c)) (Lt b c)` — `F:ml430-nat-mul-lt-mul-left-af33301e`. `mp` is
    /// [`Self::lt_of_mul_lt_mul_left`]; `mpr` is the positive-monotone core.
    pub mul_lt_mul_left: NameId,
    /// `Nat.mul_lt_mul_right : ∀ a b c, Lt zero a → Iff (Lt (mul b a) (mul c
    /// a)) (Lt b c)` — `F:ml430-nat-mul-lt-mul-right-de5b6046`, the mirror of
    /// [`Self::mul_lt_mul_left`].
    pub mul_lt_mul_right: NameId,
    /// `Nat.div_lt_of_lt_mul : ∀ m n k, Lt m (mul n k) → Lt (div m n) k` —
    /// `F:ml430-nat-div-lt-of-lt-mul-818dc4c7`. Case split on `n`: at `zero`
    /// the hypothesis is absurd (`zero_mul`/`not_lt_zero`); at `succ n'` this
    /// is `Nat.div_mod_lt_mul_iff`'s forward direction fed the canonical
    /// `Nat.div_mod_exec` witness.
    pub div_lt_of_lt_mul: NameId,
    /// `Nat.dvd_mul_left : ∀ a b, Dvd a (mul b a)` —
    /// `F:ml430-nat-dvd-mul-left-a1a8a4b8`. `dvd_mul a b : Dvd a (mul a b)`
    /// transported along `mul_comm a b`.
    pub dvd_mul_left: NameId,
    /// `Nat.dvd_mul_left_of_dvd : ∀ a b c, Dvd a b → Dvd a (mul c b)` —
    /// `F:ml430-nat-dvd-mul-left-of-dvd-200e20a4`. `dvd_mul_right_of_dvd`
    /// transported along `mul_comm b c`.
    pub dvd_mul_left_of_dvd: NameId,
    /// `Nat.eq_zero_of_gcd_eq_zero_left : ∀ m n, Eq (gcd m n) zero → Eq m
    /// zero` — `F:ml430-nat-eq-zero-of-gcd-eq-zero-left-72cc4246`.
    /// `gcd_dvd_left` transported along the hypothesis gives `Dvd zero m`;
    /// a `Dvd zero x` witness forces `x = zero` via `zero_mul`.
    pub eq_zero_of_gcd_eq_zero_left: NameId,
    /// `Nat.eq_zero_of_gcd_eq_zero_right : ∀ m n, Eq (gcd m n) zero → Eq n
    /// zero` — `F:ml430-nat-eq-zero-of-gcd-eq-zero-right-24054a86`, the
    /// mirror of [`Self::eq_zero_of_gcd_eq_zero_left`] via `gcd_dvd_right`.
    pub eq_zero_of_gcd_eq_zero_right: NameId,
    /// `Nat.dvd_mod_iff_gen : ∀ k m n, Dvd k n → (Dvd k (mod m n) ↔ Dvd k m)`
    /// — `F:ml430-nat-dvd-mod-iff-2d082f10`, the full-generality (every
    /// `n`, including zero) form of [`Self::dvd_mod_iff`], which only
    /// covers positive `n`. Case split on `n`: `zero` collapses `mod m 0`
    /// to `m` (`mod_zero`) so the goal is a reflexive `Iff`; `succ j` is
    /// exactly `dvd_mod_iff` at `(k, j, m)`.
    pub dvd_mod_iff_gen: NameId,
    /// `Nat.div_mul_cancel : ∀ n m, Dvd n m → Eq (mul (div m n) n) m` —
    /// `F:ml430-nat-div-mul-cancel-99799a00`, the full-generality (every
    /// `n`) form of `div_mul_cancel_of_dvd` (positive `n` only), factors
    /// commuted to Mathlib's `m / n * n = m` order. `n = zero`: `Dvd zero
    /// m` forces `m = zero` and both sides collapse. `n = succ j`: the
    /// existing lemma plus `mul_comm`.
    pub div_mul_cancel: NameId,
    /// `Nat.dvd_iff_mod_eq_zero : ∀ m n, Dvd m n ↔ Eq (mod n m) zero` —
    /// `F:ml430-nat-dvd-iff-mod-eq-zero-d795bfff`. Case split on `m`:
    /// `zero` reduces both sides to `Eq n zero`; `succ j` specializes
    /// `div_mod_remainder_eq_zero_iff_dvd` at the executable witness
    /// (`div_mod_exec`) and flips the `Iff` order.
    pub dvd_iff_mod_eq_zero: NameId,
    /// `Nat.div_gcd_pos_of_pos_left : ∀ a b, Lt zero a → Lt zero (div a
    /// (gcd a b))` — `F:ml430-nat-div-gcd-pos-of-pos-left-dd878a3f`.
    /// `gcd_dvd_left` plus `div_mul_cancel` give `(a/g)*g = a`; if `a/g`
    /// were `0` that forces `a = 0` (`zero_mul`), contradicting the
    /// hypothesis, so `Nat.zero_or_succ` on `a/g` leaves only the
    /// successor case.
    pub div_gcd_pos_of_pos_left: NameId,
    /// `Nat.div_gcd_pos_of_pos_right : ∀ a b, Lt zero b → Lt zero (div b
    /// (gcd a b))` — `F:ml430-nat-div-gcd-pos-of-pos-right-8d26808c`, the
    /// mirror of [`Self::div_gcd_pos_of_pos_left`] via `gcd_dvd_right`.
    pub div_gcd_pos_of_pos_right: NameId,

    // -- `int-gcd-mul-transport` lane: `dvd_add_iff_left.rs`.
    /// `Nat.dvd_add_iff_left : ∀ k m n, k ∣ n → (k ∣ m ↔ k ∣ (m+n))` —
    /// `F:ml430-nat-dvd-add-iff-left-332cbe04`. The mirror of the existing
    /// `dvd_add_iff_right` (`divisibility.rs`) with the two summands swapped:
    /// `dvd_add_iff_right(k,n,m,h) : Iff (dvd k m) (dvd k (n+m))`, transported
    /// along `add_comm n m : Eq (n+m) (m+n)`.
    pub dvd_add_iff_left: NameId,

    // -- `dvd-mul-split` lane: `dvd_mul_split.rs`.
    /// `Nat.dvd_mul_split : ∀ k m n, Iff (dvd k (m*n)) (∃ k1 k2, And (dvd k1
    /// m) (And (dvd k2 n) (Eq (k1*k2) k)))` — `F:ml430-nat-dvd-mul-ebd102e2`
    /// (Mathlib's `Nat.dvd_mul`). NOT named `dvd_mul`: that kernel name is
    /// already taken by the unrelated trivial lemma `∀ a q, dvd a (a*q)`
    /// ([`Self::dvd_mul`]). Forward direction (`k1 := gcd(k,m)`, `k2 :=
    /// k/gcd(k,m)`) needs [`Self::gcd_mul_right`]; reverse is uniform
    /// four-factor regrouping. See `dvd_mul_split.rs`'s module doc.
    pub dvd_mul_split: NameId,

    // -- `nat-dist-nth` lane: `dist.rs`/`nth.rs` —
    // `docs/plan/status/348-nat-dist-nth.md`.
    /// `Nat.dist n m := add (sub n m) (sub m n)` — Mathlib's own definition
    /// (`Mathlib.Data.Nat.Dist`), over our `sub`/`add`. See `dist.rs`'s
    /// module doc for why a mirror flip against it is honest.
    pub dist: NameId,
    /// `dist_comm : ∀ n m, Eq (dist n m) (dist m n)`.
    pub dist_comm: NameId,
    /// `dist_self : ∀ n, Eq (dist n n) zero`.
    pub dist_self: NameId,
    /// `dist_eq_sub_of_le : ∀ n m, Le n m → Eq (dist n m) (sub m n)`.
    pub dist_eq_sub_of_le: NameId,
    /// `dist_eq_sub_of_le_right : ∀ n m, Le m n → Eq (dist n m) (sub n m)`.
    pub dist_eq_sub_of_le_right: NameId,
    /// `dist_zero_right : ∀ n, Eq (dist n zero) n`.
    pub dist_zero_right: NameId,
    /// `dist_zero_left : ∀ n, Eq (dist zero n) n`.
    pub dist_zero_left: NameId,
    /// `dist_succ_succ : ∀ n m, Eq (dist (succ n) (succ m)) (dist n m)`.
    pub dist_succ_succ: NameId,
    /// `dist_eq_zero : ∀ n m, Eq n m → Eq (dist n m) zero` — `Eq.rec`
    /// transport of [`Self::dist_self`] along the hypothesis. Draw 9
    /// (`natural-distance`, ADR-0830).
    pub dist_eq_zero: NameId,
    /// `add_sub_add_left : ∀ k n m, Eq (sub (add k n) (add k m)) (sub n m)`
    /// — by induction on `k`, base via `zero_add` on both sides, step via
    /// `succ_add` congruence then `succ_sub_succ`. Pure arithmetic helper
    /// for [`Self::dist_add_add_left`]; not itself an `ml430` mirror.
    pub add_sub_add_left: NameId,
    /// `dist_add_add_left : ∀ k n m, Eq (dist (add k n) (add k m)) (dist n m)`
    /// — via [`Self::add_sub_add_left`] on both truncated subtractions
    /// `dist` sums. Draw 9 (`natural-distance`, ADR-0830).
    pub dist_add_add_left: NameId,
    /// `dist_add_add_right : ∀ n k m, Eq (dist (add n k) (add m k)) (dist n m)`
    /// — via [`Self::add_comm`] rewriting both operands to
    /// [`Self::dist_add_add_left`]'s shape (no new arithmetic beyond that).
    /// Draw 9 (`natural-distance`, ADR-0830).
    pub dist_add_add_right: NameId,
    /// `dist_mul_left : ∀ k n m, Eq (dist (mul k n) (mul k m)) (mul k (dist n m))`
    /// — via [`Self::mul_sub_left_distrib_total`] on both truncated
    /// subtractions and [`Self::left_distrib`] to recombine. Draw 9
    /// (`natural-distance`, ADR-0830).
    pub dist_mul_left: NameId,
    /// `dist_mul_right : ∀ n k m, Eq (dist (mul n k) (mul m k)) (mul (dist n m) k)`
    /// — via [`Self::mul_comm`] rewriting both operands to
    /// [`Self::dist_mul_left`]'s shape, then `mul_comm` again on the
    /// conclusion. Draw 9 (`natural-distance`, ADR-0830).
    pub dist_mul_right: NameId,
    /// `Nat.dist_pos_of_ne : ∀ i j, Not (Eq i j) → Lt zero (dist i j)` —
    /// `F:ml430-nat-dist-pos-of-ne-00f5e22f`. Case-split `i`/`j` via
    /// `lt_or_gt_of_ne_local` (`fermat_number_mirrors.rs`), then in each
    /// branch route through [`Self::dist_eq_sub_of_le`]/
    /// [`Self::dist_eq_sub_of_le_right`] and a direct `sub`-positivity
    /// argument from the strict order. `docs/plan/status/draw9-second-theorems.md`.
    pub dist_pos_of_ne: NameId,
    /// `Nat.dist_eq_intro : ∀ n m k l, Eq (add n m) (add k l) → Eq (dist n k)
    /// (dist l m)` — `F:ml430-nat-dist-eq-intro-294b44ad`. Case-split on
    /// `Le k n` vs `Le n k`; in each branch, write the larger side as the
    /// smaller plus a nonnegative excess `e`, cancel `add_left_cancel`
    /// against the hypothesis to relate `e` to the OTHER pair, and close via
    /// [`Self::dist_eq_sub_of_le`]/[`Self::dist_eq_sub_of_le_right`].
    pub dist_eq_intro: NameId,
    /// `Nat.dist_triangle_inequality : ∀ n m k, Le (dist n k) (add (dist n m)
    /// (dist m k))` — `F:ml430-nat-dist-triangle-inequality-b35e82d3`.
    pub dist_triangle_inequality: NameId,
    /// `Nat.nthAux (dec : Nat → Bool) (fuel k n : Nat) : Nat` — fuel-bounded
    /// search for the `n`-th (0-indexed) candidate `≥ k` satisfying `dec`,
    /// `0` if fewer than `n+1` are found within `fuel` steps. See `nth.rs`'s
    /// module doc for why this is NOT Mathlib's `Nat.nth` construction.
    pub nth_aux: NameId,
    /// `Nat.nth (dec : Nat → Bool) (bound n : Nat) : Nat := nthAux dec bound
    /// 0 n`. Type differs from Mathlib's `(ℕ → Prop) → ℕ → ℕ`; any `ml430`
    /// mirror against `Nat.nth` stays `open` (see `nth.rs`).
    pub nth: NameId,
    /// `Nat.nthRootAux (n a fuel : Nat) : Nat` — fuel-bounded linear search
    /// for the greatest `m` with `m ^ n <= a`. See `nth_root.rs`'s module
    /// doc for why this is structural fuel recursion rather than Mathlib's
    /// well-founded Newton iteration.
    pub nth_root_aux: NameId,
    /// `Nat.nthRoot (n a : Nat) : Nat := if n == 0 then 1 else nthRootAux n
    /// a a` — construction only, ADR-0653; opens `Mathlib.Analysis.
    /// SpecialFunctions.Pow.NthRootLemmas` for the autogenesis screen (see
    /// `nth_root.rs`).
    pub nth_root: NameId,
    /// `Nat.squarefreeAux (n fuel : Nat) : Nat -> Bool` — fuel-bounded
    /// linear search for a non-unit square factor of `n`. See
    /// `squarefree.rs`'s module doc.
    pub squarefree_aux: NameId,
    /// `Squarefree (n : Nat) : Bool` at the **bare root namespace** (not
    /// `Nat.squarefree`) — matches the literal constant token Mathlib's own
    /// `Squarefree` statements use, opening `Mathlib.Data.Nat.Squarefree`
    /// for the autogenesis screen. Construction only, ADR-0653; see
    /// `squarefree.rs`'s module doc for why this is `Bool`-valued with no
    /// `Prop` bridge.
    pub squarefree: NameId,

    // -- `nat-fermat-number` lane: `fermat_number.rs` —
    // `docs/research/09-decisions/adr-0653-declaring-the-unblocking-constant-contaminated-the-family-it-opened.md`.
    /// `Nat.fermatNumber n := add (pow 2 (pow 2 n)) 1` — Mathlib's own
    /// definition (`Mathlib.NumberTheory.Fermat`), over our `pow`/`add`.
    /// **Definition only, deliberately** — see `fermat_number.rs`'s module
    /// doc for why no theorem about it is declared here.
    pub fermat_number: NameId,

    // -- `pow-add-prime` lane: `pow_add_prime.rs` — toward
    // `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3`.
    /// `Nat.pow_mul : ∀ a e k, Eq (pow a (mul e k)) (pow (pow a e) k)`.
    pub pow_mul: NameId,
    /// `Nat.dvd_pow_add_one_of_odd_exp : ∀ x t, dvd (add x 1) (add (pow x
    /// (succ (mul 2 t))) 1)` — `x+1 ∣ x^{2t+1}+1` for every `x`.
    pub dvd_pow_add_one_of_odd_exp: NameId,
    /// `Nat.dvd_pow_add_one_of_odd_mul_exp : ∀ a e t, dvd (add (pow a e) 1)
    /// (add (pow a (mul e (succ (mul 2 t)))) 1)` — `a^e+1 ∣ a^{e*(2t+1)}+1`,
    /// the reusable odd-factor divisibility step behind the Fermat-prime
    /// lemma (`d := 2t+1` odd).
    pub dvd_pow_add_one_of_odd_mul_exp: NameId,
    /// `Nat.pow_two_or_has_odd_factor : ∀ n, Ne n zero → Or (∃ m, Eq n (pow 2
    /// m)) (∃ e t, Eq n (mul e (succ (mul 2 t))) ∧ Ne t zero)` — by
    /// structural induction on a fuel bound `Le n fuel` (NOT
    /// `WellFounded.fix`), instantiated at `fuel := n`.
    pub pow_two_or_has_odd_factor: NameId,
    /// `Nat.pow_of_pow_add_prime : ∀ a n, Lt 1 a → Ne n zero → (2 ≤
    /// (a^n+1) ∧ ∀ c, dvd c (a^n+1) → c = 1 ∨ c = a^n+1) → ∃ m, n = 2^m` —
    /// `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3`, the Fermat-prime lemma.
    pub pow_of_pow_add_prime: NameId,
    // -- `fermat-mirrors` lane: `fermat_number_mirrors.rs` --
    /// `Nat.fermatNumber_ne_one : ∀ n, Ne (fermatNumber n) 1`.
    pub fermatnumber_ne_one: NameId,
    /// `Nat.fermatNumber_mono : Monotone Nat.fermatNumber` (core-rendered
    /// `∀ x y, Le x y → Le (fermatNumber x) (fermatNumber y)`).
    pub fermatnumber_mono: NameId,
    /// `Nat.coprime_fermatNumber_fermatNumber : ∀ m n, Ne m n →
    /// Coprime (fermatNumber m) (fermatNumber n)` — Goldbach's coprimality
    /// theorem, `fermat_number_mirrors.rs`.
    pub coprime_fermatnumber_fermatnumber: NameId,
    // -- `fermat-easy` lane: `fermat_number_mirrors.rs` --
    /// `Nat.fermatNumber_zero : Eq (fermatNumber 0) 3`.
    pub fermatnumber_zero: NameId,
    /// `Nat.fermatNumber_one : Eq (fermatNumber 1) 5`.
    pub fermatnumber_one: NameId,
    /// `Nat.fermatNumber_two : Eq (fermatNumber 2) 17`.
    pub fermatnumber_two: NameId,
    /// `Nat.odd_fermatNumber : ∀ n, Odd (fermatNumber n)`.
    pub odd_fermatnumber: NameId,
    /// `Nat.fermatNumber_strictMono : StrictMono Nat.fermatNumber`
    /// (core-rendered `∀ x y, Lt x y → Lt (fermatNumber x) (fermatNumber
    /// y)`), `fermat_number_mirrors.rs`.
    pub fermatnumber_strictmono: NameId,

    // -- `lnp-implies-em` lane: `least_number.rs` — ADR-0603 row 2 for the
    // least-number principle over the naturals.
    /// `Nat.lnp_bounded_search : ∀ (Q : Nat → Prop), (∀ n, Or (Q n) (Not (Q n)))
    /// → ∀ n, Or (∀ k, Lt k n → Not (Q k)) (∃ m, And (Lt m n) (And (Q m) (∀ k,
    /// Lt k m → Not (Q k))))` — bounded least-element search for a
    /// pointwise-decided predicate, by ordinary induction on the bound.
    pub lnp_bounded_search: NameId,
    /// `Nat.lnp_of_pointwise_decision : ∀ (Q : Nat → Prop), (∀ n, Or (Q n) (Not
    /// (Q n))) → (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))` — the
    /// least-number principle, WITH a decidability hypothesis. Dropping that
    /// one hypothesis is exactly excluded middle
    /// ([`lnp_unrestricted_implies_em`](Self::lnp_unrestricted_implies_em) /
    /// [`em_implies_lnp`](Self::em_implies_lnp)).
    pub lnp_of_pointwise_decision: NameId,
    /// `Nat.lnp_decidable : ∀ (dec : Nat → Bool) (n : Nat), Eq Bool (dec n) true
    /// → ∃ m, And (Eq Bool (dec m) true) (∀ k, Lt k m → Eq Bool (dec k) false)`
    /// — the least-number principle for a `Bool`-valued predicate, admitted
    /// axiom-free. The NON-VACUITY anchor for
    /// [`lnp_unrestricted_implies_em`](Self::lnp_unrestricted_implies_em): the
    /// unrestricted form is not merely unproved here, its decidable
    /// restriction is a theorem.
    pub lnp_decidable: NameId,
    /// `Nat.em_implies_lnp : (∀ (P : Prop), Or P (Not P)) → ∀ (Q : Nat → Prop),
    /// (∃ n, Q n) → ∃ m, And (Q m) (∀ k, Lt k m → Not (Q k))` — the converse of
    /// [`lnp_unrestricted_implies_em`](Self::lnp_unrestricted_implies_em), so
    /// the two principles are interderivable.
    pub em_implies_lnp: NameId,
    /// `Nat.lnp_unrestricted_implies_em : (∀ (Q : Nat → Prop), (∃ n, Q n) → ∃ m,
    /// And (Q m) (∀ k, Lt k m → Not (Q k))) → ∀ (P : Prop), Or P (Not P)` —
    /// ADR-0603 row 2 for the least-number principle: the UNRESTRICTED form
    /// yields excluded middle for every proposition, strictly stronger than the
    /// LLPO the analysis row 2s (`creal/ivt_boundary.rs`,
    /// `creal/extreme_value.rs`) reach. See `least_number.rs`.
    pub lnp_unrestricted_implies_em: NameId,

    // -- `draw11-theorems` lane: `and_or_distrib.rs` --
    /// `Nat.and_or_distrib_left : ∀ x y z, Eq (land x (lor y z)) (lor (land
    /// x y) (land x z))` — `F:ml430-nat-and-or-distrib-left-fe131f64`. Via
    /// `Nat.eq_of_testBit_eq` plus `Nat.testBit_land`/`Nat.testBit_lor`
    /// twice per side and a per-bit AND-distributes-over-OR case split
    /// (`and_or_distrib.rs`'s `bit_and_or_distrib`, 8 leaves at `{0,1}`,
    /// each `refl`). See `nat_prelude::and_or_distrib`.
    pub and_or_distrib_left: NameId,
    /// `Nat.and_or_distrib_right : ∀ x y z, Eq (land (lor x y) z) (lor
    /// (land x z) (land y z))` — `F:ml430-nat-and-or-distrib-right-0daaa284`,
    /// the right-handed twin of [`Self::and_or_distrib_left`] via
    /// `and_or_distrib.rs`'s `bit_and_or_distrib_right`. See
    /// `nat_prelude::and_or_distrib`.
    pub and_or_distrib_right: NameId,
    // -- `draw11-theorems-b` lane: `draw11_mirrors.rs` --
    /// `Nat.coprime_dvd_mul_left : ∀ k m n, Eq (gcd k m) 1 → Iff (dvd k (mul
    /// m n)) (dvd k n)` — mirrors `Nat.Coprime.dvd_mul_left`.
    pub coprime_dvd_mul_left: NameId,
    /// `Nat.coprime_dvd_mul_right : ∀ k m n, Eq (gcd k n) 1 → Iff (dvd k
    /// (mul m n)) (dvd k m)` — mirrors `Nat.Coprime.dvd_mul_right`.
    pub coprime_dvd_mul_right: NameId,
    /// `Nat.coprime_eq_of_mul_eq_zero : ∀ m n, Eq (gcd m n) 1 → Eq (mul m n)
    /// 0 → Or (And (Eq m 0) (Eq n 1)) (And (Eq m 1) (Eq n 0))` — mirrors
    /// `Nat.Coprime.eq_of_mul_eq_zero`.
    pub coprime_eq_of_mul_eq_zero: NameId,
    /// `Nat.add_one_mul_choose_eq : ∀ n k, Eq (mul (succ n) (choose n k))
    /// (mul (choose (succ n) (succ k)) (succ k))` — mirrors
    /// `Nat.add_one_mul_choose_eq`.
    pub add_one_mul_choose_eq: NameId,
    /// `Nat.leastResidue pp a k := mod (mul a k) pp` (`gauss_lemma.rs`,
    /// toward Gauss's lemma / the second supplementary law).
    pub least_residue: NameId,
    /// `Nat.gaussSignNeg pp a k := ble (succ (div pp 2)) (leastResidue pp a
    /// k)` (`gauss_lemma.rs`).
    pub gauss_sign_neg: NameId,
    /// `Nat.gaussNegCount pp a m := countRange (fun j => gaussSignNeg pp a
    /// (succ j)) m` (`gauss_lemma.rs`).
    pub gauss_neg_count: NameId,
    /// `Nat.gauss_residue_two_eq_double_of_lt` (`gauss_lemma.rs`): at
    /// `a := 2`, `mul 2 k < pp → leastResidue pp 2 k = mul 2 k`.
    pub gauss_residue_two_eq_double_of_lt: NameId,
    /// `gaussNegCount 7 2 3 = 2` (`gauss_lemma.rs`).
    pub gauss_neg_count_seven_two: NameId,
    /// `gaussNegCount 11 2 5 = 3` (`gauss_lemma.rs`).
    pub gauss_neg_count_eleven_two: NameId,
    /// `gaussNegCount 13 2 6 = 3` (`gauss_lemma.rs`).
    pub gauss_neg_count_thirteen_two: NameId,
    /// `gaussNegCount 17 2 8 = 4` (`gauss_lemma.rs`).
    pub gauss_neg_count_seventeen_two: NameId,
    /// `gaussNegCount 19 2 9 = 5` (`gauss_lemma.rs`).
    pub gauss_neg_count_nineteen_two: NameId,
    /// `gaussNegCount 23 2 11 = 6` (`gauss_lemma.rs`).
    pub gauss_neg_count_twentythree_two: NameId,
    /// `gaussNegCount 7 3 3 = 1` (`gauss_lemma.rs`) — confirms the count
    /// depends on `a`, not only on `pp` (contrast `gauss_neg_count_seven_two`).
    pub gauss_neg_count_seven_three: NameId,
    /// `Nat.gaussCountBleClosedFormDisj : ∀ half n,
    ///   Or (And (Eq (countRange (fun j => ble (succ half) (mul 2 (succ j))) n) 0)
    ///           (Le n (div half 2)))
    ///      (And (Le (div half 2) n)
    ///           (Eq (add (countRange (fun j => ble (succ half) (mul 2 (succ j))) n)
    ///                    (div half 2))
    ///               n))`
    /// (`gauss_lemma.rs`) — by induction on `n` with `half` (and
    /// `t := div half 2`) held fixed as an outer parameter. Below `t` the
    /// count is exactly `0`; at or above `t` the count plus `t`
    /// reconstructs `n` exactly. The disjunctive shape avoids `Nat.sub`'s
    /// truncation inside the induction itself (ADR-0970/ADR-0985).
    pub gauss_count_ble_closed_form_disj: NameId,
    /// `Nat.gaussNegCountTwoClosedForm : ∀ m,
    ///   Eq (gaussNegCount (succ (mul 2 m)) 2 m) (sub m (div m 2))`
    /// (`gauss_lemma.rs`) — the symbolic closed form for `gaussNegCount` at
    /// `a := 2` and `pp := 2*m+1` (the classical odd-prime shape), landing
    /// the closed form ADR-0970 sized and left open (ADR-0985).
    pub gauss_neg_count_two_closed_form: NameId,
    /// `Nat.least_residue_injective_of_coprime : ∀ pp a k k', 0 < pp →
    ///   gcd a pp = 1 → k < pp → k' < pp → leastResidue pp a k =
    ///   leastResidue pp a k' → k = k'` (`gauss_lemma.rs`) — the least-residue
    /// map `k ↦ leastResidue pp a k` is injective on `[0, pp)` whenever `a`
    /// is coprime to `pp`. Piece 1 of the connecting theorem ADR-0970/
    /// ADR-0985 sized and left open (a caller supplies coprimality via
    /// `coprime_of_lt_prime` for the classical Gauss's-lemma setting `pp`
    /// prime, `0 < a < pp`; this theorem itself needs only positivity and
    /// coprimality, not primality).
    pub least_residue_injective_of_coprime: NameId,
    /// `Nat.least_residue_ne_zero_of_coprime : ∀ pp a k, gcd a pp = 1 →
    ///   0 < k → k < pp → 0 < leastResidue pp a k` (`gauss_lemma.rs`) — the
    /// one lemma ADR-0990 flagged as genuinely absent while sizing piece 2
    /// (the pairing lemma): `leastResidue` never lands on `0` for an index
    /// strictly between `0` and `pp` when `a` is coprime to `pp`, needed so
    /// the signed-fold self-map's two branches land in `[1, pp)`.
    pub least_residue_ne_zero_of_coprime: NameId,
    /// `Nat.gaussFold pp a k := if gaussSignNeg pp a k then sub pp
    /// (leastResidue pp a k) else leastResidue pp a k` (`gauss_lemma.rs`)
    /// — the signed-fold map ADR-0990 sized piece 2 around: folds a
    /// "negative" residue (`leastResidue > pp/2`) back to its symmetric
    /// partner `pp - leastResidue`, landing every value in `[1, pp/2]`.
    pub gauss_fold: NameId,
    /// `Nat.gauss_fold_injective_of_coprime : ∀ m a k k', gcd a (succ (mul 2
    ///   m)) = 1 → 0 < k → Le k m → 0 < k' → Le k' m → gaussFold (succ (mul
    ///   2 m)) a k = gaussFold (succ (mul 2 m)) a k' → k = k'`
    /// (`gauss_lemma.rs`) — piece 2 of the connecting theorem (ADR-0970/
    /// ADR-0985/ADR-0990): `gaussFold` is injective on `[1, m]` (the domain
    /// restriction to `Le · m` is load-bearing — unrestricted to `[1, pp)`
    /// the map is 2-to-1, `k` and `pp - k` always colliding). By cases on
    /// the two indices' signs: same-sign collisions close via
    /// `least_residue_injective_of_coprime` (piece 1, directly or after
    /// cancelling a shared `sub pp (·)`); opposite-sign collisions are
    /// vacuous — `pp = k + k'` would force `pp ∣ (k+k')` at a value strictly
    /// below `pp`, contradiction.
    pub gauss_fold_injective_of_coprime: NameId,
    /// `Nat.div_succ_two_mul_eq_self : ∀ m, div (succ (mul 2 m)) 2 = m`
    /// (`gauss_lemma.rs`) — the one new arithmetic fact ADR-1015 flagged as
    /// absent while sizing the `MapsInto` range bound: the classical
    /// modulus `pp := 2m+1`'s half, truncated, is exactly `m`. Via
    /// `add_mul_div_left` at `(x,z,y) := (1,m,2)` giving `(1+2m)/2 = 1/2+m`,
    /// bridged to `pp`'s actual `succ (mul 2 m)` shape by `add_comm` (`1 +
    /// 2m = 2m + 1`, and `2m + 1` is defeq `succ (mul 2 m)` since the
    /// literal `1` sits on `Nat.add`'s right-recursing side).
    pub div_succ_two_mul_eq_self: NameId,
    /// `Nat.gauss_fold_in_range : ∀ m a k, gcd a (succ (mul 2 m)) = 1 →
    ///   0 < k → Le k m → And (0 < gaussFold (succ (mul 2 m)) a k) (Le
    ///   (gaussFold (succ (mul 2 m)) a k) m)` (`gauss_lemma.rs`) — the
    /// `MapsInto` range bound ADR-1015 sized and left open: `gaussFold`
    /// never leaves `[1, m]` on the restricted domain. By cases on
    /// `gaussSignNeg pp a k`: the identity branch bounds `leastResidue`
    /// above by `div pp 2 = m` (`div_succ_two_mul_eq_self`) via the
    /// boolean-`≤` false witness; the negated branch bounds `pp -
    /// leastResidue` above by `m` via `sub_le_iff_le_add` once
    /// `leastResidue ≥ succ m` is in hand from the boolean-`≤` true
    /// witness, and below by `0` via a local `sub_pos_of_lt`.
    pub gauss_fold_in_range: NameId,
    /// `Nat.gauss_fold_shift_maps_into : ∀ m a, gcd a (succ (mul 2 m)) = 1 →
    ///   MapsInto (fun j => pred (gaussFold (succ (mul 2 m)) a (succ j))) m`
    /// (`gauss_lemma.rs`) — the 0-indexed shift wrapper's first half
    /// (ADR-1015): `σ(j) := pred (gaussFold pp a (succ j))` stays in `[0,
    /// m)`, directly from [`Self::gauss_fold_in_range`] plus
    /// `succ_pred_of_pos` (`Lt i m` is defeq `Le (succ i) m`, matching
    /// `gauss_fold_in_range`'s hypothesis shape with no bridging lemma
    /// needed).
    pub gauss_fold_shift_maps_into: NameId,
    /// `Nat.gauss_fold_shift_injective_on : ∀ m a, gcd a (succ (mul 2 m)) =
    ///   1 → InjectiveOn (fun j => pred (gaussFold (succ (mul 2 m)) a (succ
    ///   j))) m` (`gauss_lemma.rs`) — the shift wrapper's second half
    /// (ADR-1015): lifts the shifted map's injectivity from
    /// [`Self::gauss_fold_injective_of_coprime`] via `succ_pred_of_pos` (on
    /// both sides, to strip the `pred`) and `succ_injective` (to strip the
    /// outer `succ`). Completes piece 2 of the connecting theorem — with
    /// this and [`Self::gauss_fold_shift_maps_into`] landed,
    /// `Int.prodRange_permute`'s `InjectiveOn`/`MapsInto` hypotheses are
    /// both satisfied by the signed fold on `[0, m)`, no separate bijection
    /// or partner-index construction needed.
    pub gauss_fold_shift_injective_on: NameId,
}

/// Declare the natural-number prelude into `kernel`'s environment, returning the
/// [`NatPrelude`] of interned names.
///
/// The shared logical prelude is built or exact-validated first (as
/// [`build_int_prelude`](crate::build_int_prelude) does).
/// Every definition and theorem is admitted through the **trusted**
/// [`Kernel::add_declaration`](crate::Kernel::add_declaration) gate and `Nat.le`
/// through [`Kernel::add_inductive`](crate::Kernel::add_inductive) — the kernel
/// re-checks each proof term against its stated proposition, so a green build of
/// this function *is* a machine-checked proof of every theorem it declares.
///
/// Repeated construction validates and returns the exact registered package.
/// Any trusted-gate rejection is returned as [`KernelError`] and rolls back all
/// Nat declarations admitted by this invocation.
///
/// # Errors
///
/// Returns the trusted gate's rejection or an exact-package conflict. A failed
/// Nat build leaves the pre-call environment unchanged.
pub fn build_nat_prelude(kernel: &mut Kernel) -> Result<NatPrelude, KernelError> {
    if let Some(PreludeValue::Nat(prelude)) =
        crate::prelude_cache::try_restore(kernel, PreludeKey::Nat)
    {
        return Ok(*prelude);
    }
    build_nat_prelude_uncached(kernel)
}

/// [`build_nat_prelude`] without the process-wide template fast path.
///
/// This is the route that actually runs the trusted gate, and the one the
/// template itself is built through (ADR-0464).
pub(crate) fn build_nat_prelude_uncached(kernel: &mut Kernel) -> Result<NatPrelude, KernelError> {
    let logic = build_logic_prelude(kernel)?;
    if let Some(PreludeValue::Nat(prelude)) = kernel.cached_prelude(PreludeKey::Nat)? {
        return Ok(*prelude);
    }
    let checkpoint = kernel.prelude_checkpoint();
    let built = (|| -> Result<NatPrelude, KernelError> {
        let nat = logic.nat;

        // Intern every name up front so the `NatPrelude` (which the proof scripts
        // below consult for lemma handles) exists before anything is declared.
        let le = kernel.name_str(nat, "le");
        let fin = kernel.name_str(nat, "Fin");
        let pair = kernel.name_str(nat, "Pair");
        let p = NatPrelude {
            logic,
            nat,
            zero: logic.nat_zero,
            succ: logic.nat_succ,
            rec: logic.nat_rec,
            add: kernel.name_str(nat, "add"),
            mul: kernel.name_str(nat, "mul"),
            pow: kernel.name_str(nat, "pow"),
            beq: kernel.name_str(nat, "beq"),
            beq_refl: kernel.name_str(nat, "beq_refl"),
            eq_of_beq_eq_true: kernel.name_str(nat, "eq_of_beq_eq_true"),
            beq_eq_true_of_eq: kernel.name_str(nat, "beq_eq_true_of_eq"),
            beq_eq_true_iff: kernel.name_str(nat, "beq_eq_true_iff"),
            div_mod_state: kernel.name_str(nat, "divModState"),
            div: kernel.name_str(nat, "div"),
            mod_: kernel.name_str(nat, "mod"),
            gcd: kernel.name_str(nat, "gcd"),
            sum_range: kernel.name_str(nat, "sumRange"),
            factorial: kernel.name_str(nat, "factorial"),
            desc_factorial: kernel.name_str(nat, "descFactorial"),
            desc_factorial_zero: kernel.name_str(nat, "descFactorial_zero"),
            desc_factorial_succ: kernel.name_str(nat, "descFactorial_succ"),
            desc_factorial_one: kernel.name_str(nat, "descFactorial_one"),
            desc_factorial_of_lt: kernel.name_str(nat, "descFactorial_of_lt"),
            desc_factorial_succ_eq_succ_mul: kernel.name_str(nat, "descFactorial_succ_eq_succ_mul"),
            desc_factorial_eq_factorial_mul_choose: kernel
                .name_str(nat, "descFactorial_eq_factorial_mul_choose"),
            add_choose_mul_factorial_mul_factorial: kernel
                .name_str(nat, "add_choose_mul_factorial_mul_factorial"),
            add_choose: kernel.name_str(nat, "add_choose"),
            factorial_dvd_desc_factorial: kernel.name_str(nat, "factorial_dvd_descFactorial"),
            desc_factorial_self: kernel.name_str(nat, "descFactorial_self"),
            desc_factorial_le: kernel.name_str(nat, "descFactorial_le"),
            self_le_factorial: kernel.name_str(nat, "self_le_factorial"),
            asc_factorial: kernel.name_str(nat, "ascFactorial"),
            asc_factorial_zero: kernel.name_str(nat, "ascFactorial_zero"),
            asc_factorial_succ: kernel.name_str(nat, "ascFactorial_succ"),
            asc_factorial_one: kernel.name_str(nat, "ascFactorial_one"),
            zero_asc_factorial_succ: kernel.name_str(nat, "zero_ascFactorial_succ"),
            asc_factorial_succ_eq_factorial_mul_choose: kernel
                .name_str(nat, "ascFactorial_succ_eq_factorial_mul_choose"),
            factorial_dvd_asc_factorial: kernel.name_str(nat, "factorial_dvd_ascFactorial"),
            add_desc_factorial_eq_asc_factorial: kernel
                .name_str(nat, "add_descFactorial_eq_ascFactorial"),
            asc_factorial_eq_div: kernel.name_str(nat, "ascFactorial_eq_div"),
            multichoose: kernel.name_str(nat, "multichoose"),
            multichoose_zero_right: kernel.name_str(nat, "multichoose_zero_right"),
            multichoose_one: kernel.name_str(nat, "multichoose_one"),
            multichoose_one_right: kernel.name_str(nat, "multichoose_one_right"),
            pred: kernel.name_str(nat, "pred"),
            sub: kernel.name_str(nat, "sub"),
            no_confusion_type: kernel.name_str(nat, "noConfusionType"),
            no_confusion: kernel.name_str(nat, "noConfusion"),
            succ_ne_zero: kernel.name_str(nat, "succ_ne_zero"),
            not_lt_zero: kernel.name_str(nat, "not_lt_zero"),
            succ_pred_of_pos: kernel.name_str(nat, "succ_pred_of_pos"),
            div_zero: kernel.name_str(nat, "div_zero"),
            mod_zero: kernel.name_str(nat, "mod_zero"),
            zero_div: kernel.name_str(nat, "zero_div"),
            zero_mod: kernel.name_str(nat, "zero_mod"),
            div_succ: kernel.name_str(nat, "div_succ"),
            mod_succ: kernel.name_str(nat, "mod_succ"),
            add_zero: kernel.name_str(nat, "add_zero"),
            add_succ: kernel.name_str(nat, "add_succ"),
            mul_zero: kernel.name_str(nat, "mul_zero"),
            mul_succ: kernel.name_str(nat, "mul_succ"),
            pow_zero: kernel.name_str(nat, "pow_zero"),
            pow_add: kernel.name_str(nat, "pow_add"),
            pow_succ: kernel.name_str(nat, "pow_succ"),
            pred_zero: kernel.name_str(nat, "pred_zero"),
            pred_succ: kernel.name_str(nat, "pred_succ"),
            sub_zero: kernel.name_str(nat, "sub_zero"),
            sub_succ: kernel.name_str(nat, "sub_succ"),
            succ_sub_succ: kernel.name_str(nat, "succ_sub_succ"),
            sub_self: kernel.name_str(nat, "sub_self"),
            add_sub_cancel_left: kernel.name_str(nat, "add_sub_cancel_left"),
            sum_range_zero: kernel.name_str(nat, "sumRange_zero"),
            sum_range_succ: kernel.name_str(nat, "sumRange_succ"),
            sum_range_congr: kernel.name_str(nat, "sumRange_congr"),
            mul_sum_range: kernel.name_str(nat, "mul_sumRange"),
            mul_sum_range_pow: kernel.name_str(nat, "mul_sumRange_pow"),
            factorial_zero: kernel.name_str(nat, "factorial_zero"),
            factorial_succ: kernel.name_str(nat, "factorial_succ"),
            zero_add: kernel.name_str(nat, "zero_add"),
            succ_add: kernel.name_str(nat, "succ_add"),
            add_comm: kernel.name_str(nat, "add_comm"),
            add_assoc: kernel.name_str(nat, "add_assoc"),
            add_right_comm: kernel.name_str(nat, "add_right_comm"),
            succ_injective: kernel.name_str(nat, "succ_injective"),
            add_right_cancel: kernel.name_str(nat, "add_right_cancel"),
            add_left_cancel: kernel.name_str(nat, "add_left_cancel"),
            add_add_add_comm: kernel.name_str(nat, "add_add_add_comm"),
            add_eq: kernel.name_str(nat, "add_eq"),
            add_eq_left: kernel.name_str(nat, "add_eq_left"),
            add_eq_right: kernel.name_str(nat, "add_eq_right"),
            add_eq_zero_iff: kernel.name_str(nat, "add_eq_zero_iff"),
            add_eq_one_iff: kernel.name_str(nat, "add_eq_one_iff"),
            add_eq_two_iff: kernel.name_str(nat, "add_eq_two_iff"),
            add_eq_three_iff: kernel.name_str(nat, "add_eq_three_iff"),
            zero_mul: kernel.name_str(nat, "zero_mul"),
            succ_mul: kernel.name_str(nat, "succ_mul"),
            mul_comm: kernel.name_str(nat, "mul_comm"),
            left_distrib: kernel.name_str(nat, "left_distrib"),
            right_distrib: kernel.name_str(nat, "right_distrib"),
            mul_assoc: kernel.name_str(nat, "mul_assoc"),
            one_mul: kernel.name_str(nat, "one_mul"),
            mul_one: kernel.name_str(nat, "mul_one"),
            le,
            lt: kernel.name_str(nat, "lt"),
            in_closed_interval: kernel.name_str(nat, "inClosedInterval"),
            le_refl: kernel.name_str(le, "refl"),
            le_step: kernel.name_str(le, "step"),
            le_rec: kernel.name_str(le, "rec"),
            zero_le: kernel.name_str(nat, "zero_le"),
            le_succ_succ: kernel.name_str(nat, "le_succ_succ"),
            le_of_succ_le_succ: kernel.name_str(nat, "le_of_succ_le_succ"),
            le_trans: kernel.name_str(nat, "le_trans"),
            monotone_of_le_succ: kernel.name_str(nat, "monotone_of_le_succ"),
            lt_or_eq_of_le: kernel.name_str(nat, "lt_or_eq_of_le"),
            lt_of_lt_of_le: kernel.name_str(nat, "lt_of_lt_of_le"),
            lt_of_le_of_lt: kernel.name_str(nat, "lt_of_le_of_lt"),
            lt_irrefl: kernel.name_str(nat, "lt_irrefl"),
            lt_well_founded: kernel.name_str(nat, "lt_well_founded"),
            le_total: kernel.name_str(nat, "le_total"),
            not_succ_le_zero: kernel.name_str(nat, "not_succ_le_zero"),
            le_antisymm: kernel.name_str(nat, "le_antisymm"),
            le_intro: kernel.name_str(nat, "le_intro"),
            le_dest: kernel.name_str(nat, "le_dest"),
            le_add_right: kernel.name_str(nat, "le_add_right"),
            add_le_add_left: kernel.name_str(nat, "add_le_add_left"),
            add_lt_add_left: kernel.name_str(nat, "add_lt_add_left"),
            add_le_add_right: kernel.name_str(nat, "add_le_add_right"),
            le_of_add_le_add_left: kernel.name_str(nat, "le_of_add_le_add_left"),
            le_of_add_le_add_right: kernel.name_str(nat, "le_of_add_le_add_right"),
            mul_le_mul_left: kernel.name_str(nat, "mul_le_mul_left"),
            mul_succ_add_lt_of_le_of_lt: kernel.name_str(nat, "mul_succ_add_lt_of_le_of_lt"),
            le_of_mul_le_mul_left_succ: kernel.name_str(nat, "le_of_mul_le_mul_left_succ"),
            le_of_mul_le_mul_left: kernel.name_str(nat, "le_of_mul_le_mul_left"),
            mul_left_cancel_of_pos: kernel.name_str(nat, "mul_left_cancel_of_pos"),
            sub_add_cancel: kernel.name_str(nat, "sub_add_cancel"),
            sub_eq_zero_of_le: kernel.name_str(nat, "sub_eq_zero_of_le"),
            sub_le_iff_le_add: kernel.name_str(nat, "sub_le_iff_le_add"),
            mul_sub_left_distrib: kernel.name_str(nat, "mul_sub_left_distrib"),
            mul_sub_left_distrib_total: kernel.name_str(nat, "mul_sub_left_distrib_total"),
            le_refl_thm: kernel.name_str(nat, "le_refl"),
            le_succ: kernel.name_str(nat, "le_succ"),
            succ_le_succ: kernel.name_str(nat, "succ_le_succ"),
            le_of_lt_succ: kernel.name_str(nat, "le_of_lt_succ"),
            lt_succ_self: kernel.name_str(nat, "lt_succ_self"),
            lt_succ_of_le: kernel.name_str(nat, "lt_succ_of_le"),
            lt_add_one: kernel.name_str(nat, "lt_add_one"),
            not_succ_le_self: kernel.name_str(nat, "not_succ_le_self"),
            le_succ_of_le: kernel.name_str(nat, "le_succ_of_le"),
            zero_lt_succ: kernel.name_str(nat, "zero_lt_succ"),
            pred_le: kernel.name_str(nat, "pred_le"),
            pred_le_pred: kernel.name_str(nat, "pred_le_pred"),
            sub_le: kernel.name_str(nat, "sub_le"),
            sub_lt: kernel.name_str(nat, "sub_lt"),
            succ_sub_succ_eq_sub: kernel.name_str(nat, "succ_sub_succ_eq_sub"),
            lt_of_not_le: kernel.name_str(nat, "lt_of_not_le"),
            lt_or_ge: kernel.name_str(nat, "lt_or_ge"),
            le_of_lt_add_one: kernel.name_str(nat, "le_of_lt_add_one"),
            zero_lt_of_ne_zero: kernel.name_str(nat, "zero_lt_of_ne_zero"),
            ne_of_beq_eq_false: kernel.name_str(nat, "ne_of_beq_eq_false"),
            add_pos_right: kernel.name_str(nat, "add_pos_right"),
            ble: kernel.name_str(nat, "ble"),
            ble_self_eq_true: kernel.name_str(nat, "ble_self_eq_true"),
            ble_succ_eq_true: kernel.name_str(nat, "ble_succ_eq_true"),
            ble_eq_true_of_le: kernel.name_str(nat, "ble_eq_true_of_le"),
            le_of_ble_eq_true: kernel.name_str(nat, "le_of_ble_eq_true"),
            not_le_of_not_ble_eq_true: kernel.name_str(nat, "not_le_of_not_ble_eq_true"),
            div_mod: kernel.name_str(nat, "divMod"),
            div_mod_exists: kernel.name_str(nat, "div_mod_exists"),
            div_mod_unique: kernel.name_str(nat, "div_mod_unique"),
            div_mod_bounds: kernel.name_str(nat, "div_mod_bounds"),
            div_mod_mul_le_iff: kernel.name_str(nat, "div_mod_mul_le_iff"),
            div_mod_lt_mul_iff: kernel.name_str(nat, "div_mod_lt_mul_iff"),
            div_mod_add_multiple: kernel.name_str(nat, "div_mod_add_multiple"),
            add_div_left: kernel.name_str(nat, "add_div_left"),
            add_div_right: kernel.name_str(nat, "add_div_right"),
            add_mod_left: kernel.name_str(nat, "add_mod_left"),
            add_mod_right: kernel.name_str(nat, "add_mod_right"),
            add_mul_div_left: kernel.name_str(nat, "add_mul_div_left"),
            add_mul_div_right: kernel.name_str(nat, "add_mul_div_right"),
            add_mul_mod_self_left: kernel.name_str(nat, "add_mul_mod_self_left"),
            add_mul_mod_self_right: kernel.name_str(nat, "add_mul_mod_self_right"),
            add_div_of_dvd_add_add_one: kernel.name_str(nat, "add_div_of_dvd_add_add_one"),
            base_induction: kernel.name_str(nat, "base_induction"),
            mod_mul: kernel.name_str(nat, "mod_mul"),
            mod_mul_left_mod: kernel.name_str(nat, "mod_mul_left_mod"),
            mod_mul_right_mod: kernel.name_str(nat, "mod_mul_right_mod"),
            mod_mul_left_div_self: kernel.name_str(nat, "mod_mul_left_div_self"),
            mod_mul_right_div_self: kernel.name_str(nat, "mod_mul_right_div_self"),
            dvd: kernel.name_str(nat, "dvd"),
            div_mod_remainder_eq_zero_iff_dvd: kernel
                .name_str(nat, "div_mod_remainder_eq_zero_iff_dvd"),
            div_mod_exact_exists: kernel.name_str(nat, "div_mod_exact_exists"),
            mod_self: kernel.name_str(nat, "mod_self"),
            div_mod_exec: kernel.name_str(nat, "div_mod_exec"),
            mod_lt: kernel.name_str(nat, "mod_lt"),
            gcd_zero_left: kernel.name_str(nat, "gcd_zero_left"),
            gcd_succ: kernel.name_str(nat, "gcd_succ"),
            gcd_dvd: kernel.name_str(nat, "gcd_dvd"),
            gcd_dvd_left: kernel.name_str(nat, "gcd_dvd_left"),
            gcd_dvd_right: kernel.name_str(nat, "gcd_dvd_right"),
            dvd_gcd: kernel.name_str(nat, "dvd_gcd"),
            dvd_gcd_iff: kernel.name_str(nat, "dvd_gcd_iff"),
            gcd_mul_right: kernel.name_str(nat, "gcd_mul_right"),
            dvd_gcd_mul_iff_dvd_mul: kernel.name_str(nat, "dvd_gcd_mul_iff_dvd_mul"),
            dvd_gcd_mul_gcd_iff_dvd_mul: kernel.name_str(nat, "dvd_gcd_mul_gcd_iff_dvd_mul"),
            dvd_mul_gcd_iff_dvd_mul: kernel.name_str(nat, "dvd_mul_gcd_iff_dvd_mul"),
            mod_eq_cancel_left_div_gcd: kernel.name_str(nat, "mod_eq_cancel_left_div_gcd"),
            mod_eq_cancel_right_div_gcd: kernel.name_str(nat, "mod_eq_cancel_right_div_gcd"),
            mod_eq_cancel_left_div_gcd_general: kernel
                .name_str(nat, "mod_eq_cancel_left_div_gcd_general"),
            lcm: kernel.name_str(nat, "lcm"),
            lcm_zero_left: kernel.name_str(nat, "lcm_zero_left"),
            dvd_lcm_left: kernel.name_str(nat, "dvd_lcm_left"),
            dvd_lcm_right: kernel.name_str(nat, "dvd_lcm_right"),
            gcd_mul_lcm: kernel.name_str(nat, "gcd_mul_lcm"),
            gauss_lemma: kernel.name_str(nat, "gauss_lemma"),
            lcm_dvd: kernel.name_str(nat, "lcm_dvd"),
            dvd_antisymm: kernel.name_str(nat, "dvd_antisymm"),
            dvd_lcm_of_dvd_left: kernel.name_str(nat, "dvd_lcm_of_dvd_left"),
            dvd_lcm_of_dvd_right: kernel.name_str(nat, "dvd_lcm_of_dvd_right"),
            dvd_of_lcm_left_dvd: kernel.name_str(nat, "dvd_of_lcm_left_dvd"),
            dvd_of_lcm_right_dvd: kernel.name_str(nat, "dvd_of_lcm_right_dvd"),
            catalan: kernel.name_str(nat, "catalan"),
            catalan_mul_succ: kernel.name_str(nat, "catalan_mul_succ"),
            lcm_comm: kernel.name_str(nat, "lcm_comm"),
            gcd_comm: kernel.name_str(nat, "gcd_comm"),
            coprime_mul_of_coprime: kernel.name_str(nat, "coprime_mul_of_coprime"),
            gcd_mod_left_eq_gcd: kernel.name_str(nat, "gcd_mod_left_eq_gcd"),
            coprime_mul_iff: kernel.name_str(nat, "coprime_mul_iff"),
            coprime_lcm_eq_mul: kernel.name_str(nat, "coprime_lcm_eq_mul"),
            gcd_dvd_mul: kernel.name_str(nat, "gcd_dvd_mul"),
            gcd_le_mul: kernel.name_str(nat, "gcd_le_mul"),
            eq_zero_of_lcm_eq_zero: kernel.name_str(nat, "eq_zero_of_lcm_eq_zero"),
            lcm_assoc: kernel.name_str(nat, "lcm_assoc"),
            lcm_div: kernel.name_str(nat, "lcm_div"),
            bezout: kernel.name_str(nat, "bezout"),
            gcd_bezout: kernel.name_str(nat, "gcd_bezout"),
            mod_eq: kernel.name_str(nat, "modEq"),
            mod_eq_refl: kernel.name_str(nat, "mod_eq_refl"),
            mod_eq_symm: kernel.name_str(nat, "mod_eq_symm"),
            mod_eq_trans: kernel.name_str(nat, "mod_eq_trans"),
            mod_eq_add_left: kernel.name_str(nat, "mod_eq_add_left"),
            mod_eq_add_right: kernel.name_str(nat, "mod_eq_add_right"),
            mod_eq_add: kernel.name_str(nat, "mod_eq_add"),
            mod_eq_mul_left: kernel.name_str(nat, "mod_eq_mul_left"),
            mod_eq_mul_right: kernel.name_str(nat, "mod_eq_mul_right"),
            mod_eq_mul: kernel.name_str(nat, "mod_eq_mul"),
            div_mod_same_remainder_mod_eq: kernel.name_str(nat, "div_mod_same_remainder_mod_eq"),
            div_mod_remainder_eq_of_mod_eq: kernel.name_str(nat, "div_mod_remainder_eq_of_mod_eq"),
            mod_eq_iff_div_mod_remainder_eq: kernel
                .name_str(nat, "mod_eq_iff_div_mod_remainder_eq"),
            mod_eq_zero_of_dvd: kernel.name_str(nat, "mod_eq_zero_of_dvd"),
            dvd_of_mod_eq_zero_of_pos: kernel.name_str(nat, "dvd_of_mod_eq_zero_of_pos"),
            mod_eq_zero_iff_dvd: kernel.name_str(nat, "mod_eq_zero_iff_dvd"),
            mod_eq_cancel: kernel.name_str(nat, "mod_eq_cancel"),
            mod_eq_gcd_eq: kernel.name_str(nat, "mod_eq_gcd_eq"),
            mod_eq_add_left_cancel: kernel.name_str(nat, "mod_eq_add_left_cancel"),
            mod_eq_add_right_cancel: kernel.name_str(nat, "mod_eq_add_right_cancel"),
            mod_eq_add_iff_left: kernel.name_str(nat, "mod_eq_add_iff_left"),
            mod_eq_add_iff_right: kernel.name_str(nat, "mod_eq_add_iff_right"),
            mod_eq_cancel_left: kernel.name_str(nat, "mod_eq_cancel_left"),
            mod_eq_add_le_of_lt: kernel.name_str(nat, "mod_eq_add_le_of_lt"),
            valuation_at: kernel.name_str(nat, "valuationAt"),
            dvd_mul: kernel.name_str(nat, "dvd_mul"),
            dvd_refl: kernel.name_str(nat, "dvd_refl"),
            dvd_zero: kernel.name_str(nat, "dvd_zero"),
            dvd_trans: kernel.name_str(nat, "dvd_trans"),
            dvd_mul_right_of_dvd: kernel.name_str(nat, "dvd_mul_right_of_dvd"),
            dvd_add_iff_right: kernel.name_str(nat, "dvd_add_iff_right"),
            dvd_mod_iff: kernel.name_str(nat, "dvd_mod_iff"),
            dvd_add: kernel.name_str(nat, "dvd_add"),
            dvd_add_right_cancel_of_pos: kernel.name_str(nat, "dvd_add_right_cancel_of_pos"),
            euclid_lemma: kernel.name_str(nat, "euclid_lemma"),
            prime_one_lt: kernel.name_str(nat, "prime_one_lt"),
            prime_one_le: kernel.name_str(nat, "prime_one_le"),
            prime_pos: kernel.name_str(nat, "prime_pos"),
            prime_ne_one: kernel.name_str(nat, "prime_ne_one"),
            prime_ne_zero: kernel.name_str(nat, "prime_ne_zero"),
            prime_not_dvd_one: kernel.name_str(nat, "prime_not_dvd_one"),
            prime_eq_one_or_self_of_dvd: kernel.name_str(nat, "prime_eq_one_or_self_of_dvd"),
            prime_dvd_iff_eq: kernel.name_str(nat, "prime_dvd_iff_eq"),
            prime_dvd_mul_iff: kernel.name_str(nat, "prime_dvd_mul_iff"),
            prime_coprime_iff_not_dvd: kernel.name_str(nat, "prime_coprime_iff_not_dvd"),
            prime_eq_two_or_odd: kernel.name_str(nat, "prime_eq_two_or_odd"),
            prime_eq_two_or_mod_two_eq_one: kernel.name_str(nat, "prime_eq_two_or_mod_two_eq_one"),
            prime_mod_two_eq_one_iff_ne_two: kernel
                .name_str(nat, "prime_mod_two_eq_one_iff_ne_two"),
            prime_coprime_pow_of_not_dvd: kernel.name_str(nat, "prime_coprime_pow_of_not_dvd"),
            prime_dvd_choose: kernel.name_str(nat, "prime_dvd_choose"),
            one_le_factorial: kernel.name_str(nat, "one_le_factorial"),
            exists_prime_gt: kernel.name_str(nat, "exists_prime_gt"),
            not_dvd_one_of_two_le: kernel.name_str(nat, "not_dvd_one_of_two_le"),
            eq_one_of_dvd_one: kernel.name_str(nat, "eq_one_of_dvd_one"),
            coprime_of_bezout_one: kernel.name_str(nat, "coprime_of_bezout_one"),
            bezout_of_scaled: kernel.name_str(nat, "bezout_of_scaled"),
            gcd_cofactors_coprime: kernel.name_str(nat, "gcd_cofactors_coprime"),
            div_mul_cancel_of_dvd: kernel.name_str(nat, "div_mul_cancel_of_dvd"),
            div_dvd_div_left: kernel.name_str(nat, "div_dvd_div_left"),
            one_le_right_of_mul: kernel.name_str(nat, "one_le_right_of_mul"),
            one_le_left_of_mul: kernel.name_str(nat, "one_le_left_of_mul"),
            one_le_of_dvd_pos: kernel.name_str(nat, "one_le_of_dvd_pos"),
            one_le_mul: kernel.name_str(nat, "one_le_mul"),
            mul_eq_zero: kernel.name_str(nat, "mul_eq_zero"),
            add_eq_zero: kernel.name_str(nat, "add_eq_zero"),
            zero_or_succ: kernel.name_str(nat, "zero_or_succ"),
            dvd_factorial_of_le: kernel.name_str(nat, "dvd_factorial_of_le"),
            factorial_dvd_factorial: kernel.name_str(nat, "factorial_dvd_factorial"),
            factorial_le: kernel.name_str(nat, "factorial_le"),
            factorial_lt_of_lt: kernel.name_str(nat, "factorial_lt_of_lt"),
            factorial_ne_zero: kernel.name_str(nat, "factorial_ne_zero"),
            add_factorial_le_factorial_add: kernel.name_str(nat, "add_factorial_le_factorial_add"),
            add_factorial_succ_le_factorial_add_succ: kernel
                .name_str(nat, "add_factorial_succ_le_factorial_add_succ"),
            add_factorial_lt_factorial_add: kernel.name_str(nat, "add_factorial_lt_factorial_add"),
            add_factorial_succ_lt_factorial_add_succ: kernel
                .name_str(nat, "add_factorial_succ_lt_factorial_add_succ"),
            not_dvd_one_add_mul_of_two_le: kernel.name_str(nat, "not_dvd_one_add_mul_of_two_le"),
            valuation_at_two_mul_sq: kernel.name_str(nat, "valuation_at_two_mul_sq"),
            le_of_dvd: kernel.name_str(nat, "le_of_dvd"),
            two_le_succ_or_eq_one: kernel.name_str(nat, "two_le_succ_or_eq_one"),
            least_divisor_search: kernel.name_str(nat, "least_divisor_search"),
            exists_prime_dvd: kernel.name_str(nat, "exists_prime_dvd"),
            coprime_of_lt_prime: kernel.name_str(nat, "coprime_of_lt_prime"),
            coprime_of_dvd_left: kernel.name_str(nat, "coprime_of_dvd_left"),
            coprime_of_dvd_right: kernel.name_str(nat, "coprime_of_dvd_right"),
            prime_dvd_iff_not_coprime: kernel.name_str(nat, "prime_dvd_iff_not_coprime"),
            coprime_add_self_right: kernel.name_str(nat, "coprime_add_self_right"),
            coprime_of_dvd: kernel.name_str(nat, "coprime_of_dvd"),
            coprime_dvd_left: kernel.name_str(nat, "coprime_dvd_left"),
            coprime_dvd_right: kernel.name_str(nat, "coprime_dvd_right"),
            coprime_mul_left: kernel.name_str(nat, "coprime_mul_left"),
            coprime_mul_right: kernel.name_str(nat, "coprime_mul_right"),
            coprime_mul_left_right: kernel.name_str(nat, "coprime_mul_left_right"),
            coprime_mul_right_right: kernel.name_str(nat, "coprime_mul_right_right"),
            dvd_of_dvd_mul_left: kernel.name_str(nat, "dvd_of_dvd_mul_left"),
            dvd_of_dvd_mul_right: kernel.name_str(nat, "dvd_of_dvd_mul_right"),
            coprime_div_right: kernel.name_str(nat, "coprime_div_right"),
            coprime_div_left: kernel.name_str(nat, "coprime_div_left"),
            coprime_of_forall_prime_dvd: kernel.name_str(nat, "coprime_of_forall_prime_dvd"),
            dvd_of_forall_prime_mul_dvd: kernel.name_str(nat, "dvd_of_forall_prime_mul_dvd"),
            is_rel_prime: kernel.name_str(nat, "IsRelPrime"),
            coprime_iff_is_rel_prime: kernel.name_str(nat, "coprime_iff_isRelPrime"),
            min_fac_aux: kernel.name_str(nat, "minFacAux"),
            min_fac: kernel.name_str(nat, "minFac"),
            min_fac_aux_minimal: kernel.name_str(nat, "minFacAuxMinimal"),
            min_fac_minimal_of_two_le: kernel.name_str(nat, "min_fac_minimal_of_two_le"),
            coprime_of_lt_min_fac: kernel.name_str(nat, "coprime_of_lt_min_fac"),
            coprime_self_add_right: kernel.name_str(nat, "coprime_self_add_right"),
            coprime_symmetric: kernel.name_str(nat, "coprime_symmetric"),
            coprime_mul_add_mul_ne_mul: kernel.name_str(nat, "coprime_mul_add_mul_ne_mul"),
            not_coprime_zero_zero: kernel.name_str(nat, "not_coprime_zero_zero"),
            coprime_one_left_iff: kernel.name_str(nat, "coprime_one_left_iff"),
            coprime_one_right_iff: kernel.name_str(nat, "coprime_one_right_iff"),
            coprime_add_self_left: kernel.name_str(nat, "coprime_add_self_left"),
            coprime_self_add_left: kernel.name_str(nat, "coprime_self_add_left"),
            coprime_or_dvd_of_prime: kernel.name_str(nat, "coprime_or_dvd_of_prime"),
            coprime_two_left: kernel.name_str(nat, "coprime_two_left"),
            coprime_two_right: kernel.name_str(nat, "coprime_two_right"),
            coprime_odd_of_left: kernel.name_str(nat, "coprime_odd_of_left"),
            coprime_odd_of_right: kernel.name_str(nat, "coprime_odd_of_right"),
            prime_odd_of_ne_two: kernel.name_str(nat, "prime_odd_of_ne_two"),
            prime_even_iff: kernel.name_str(nat, "prime_even_iff"),
            prime_not_dvd_mul: kernel.name_str(nat, "prime_not_dvd_mul"),
            prime_dvd_of_dvd_pow: kernel.name_str(nat, "prime_dvd_of_dvd_pow"),
            coprime_primes: kernel.name_str(nat, "coprime_primes"),
            not_prime_of_dvd_of_ne: kernel.name_str(nat, "not_prime_of_dvd_of_ne"),
            five_le_of_ne_two_of_ne_three: kernel.name_str(nat, "five_le_of_ne_two_of_ne_three"),
            prime_pred_pos: kernel.name_str(nat, "prime_pred_pos"),
            succ_pred_prime: kernel.name_str(nat, "succ_pred_prime"),
            prime_not_prime_pow_two_le: kernel.name_str(nat, "prime_not_prime_pow_two_le"),
            prime_not_prime_pow_ne_one: kernel.name_str(nat, "prime_not_prime_pow_ne_one"),
            prime_eq_one_of_pow: kernel.name_str(nat, "prime_eq_one_of_pow"),
            prime_not_coprime_iff_dvd: kernel.name_str(nat, "prime_not_coprime_iff_dvd"),
            prime_mul_eq_prime_sq_iff: kernel.name_str(nat, "prime_mul_eq_prime_sq_iff"),
            prime_dvd_mul_of_dvd_ne: kernel.name_str(nat, "prime_dvd_mul_of_dvd_ne"),
            choose: kernel.name_str(nat, "choose"),
            choose_zero_right: kernel.name_str(nat, "choose_zero_right"),
            choose_succ_succ: kernel.name_str(nat, "choose_succ_succ"),
            zero_choose_succ: kernel.name_str(nat, "zero_choose_succ"),
            choose_succ_self_eq_zero: kernel.name_str(nat, "choose_succ_self_eq_zero"),
            choose_self: kernel.name_str(nat, "choose_self"),
            choose_symm: kernel.name_str(nat, "choose_symm"),
            choose_one_right: kernel.name_str(nat, "choose_one_right"),
            choose_eq_zero_of_lt: kernel.name_str(nat, "choose_eq_zero_of_lt"),
            choose_ne_zero: kernel.name_str(nat, "choose_ne_zero"),
            choose_le_succ: kernel.name_str(nat, "choose_le_succ"),
            choose_symm_of_eq_add: kernel.name_str(nat, "choose_symm_of_eq_add"),
            choose_le_add: kernel.name_str(nat, "choose_le_add"),
            choose_symm_add: kernel.name_str(nat, "choose_symm_add"),
            choose_le_choose: kernel.name_str(nat, "choose_le_choose"),
            choose_mono: kernel.name_str(nat, "choose_mono"),
            sum_range_add: kernel.name_str(nat, "sumRange_add"),
            sum_range_shift_front: kernel.name_str(nat, "sumRange_shiftFront"),
            sum_range_congr_lt: kernel.name_str(nat, "sumRange_congr_lt"),
            add_pow_zero: kernel.name_str(nat, "add_pow_zero"),
            add_pow_one: kernel.name_str(nat, "add_pow_one"),
            add_pow: kernel.name_str(nat, "add_pow"),
            one_pow: kernel.name_str(nat, "one_pow"),
            le_sum_range_of_lt: kernel.name_str(nat, "le_sumRange_of_lt"),
            sum_choose_row: kernel.name_str(nat, "sum_choose_row"),
            choose_le_two_pow: kernel.name_str(nat, "choose_le_two_pow"),
            succ_sub_of_le: kernel.name_str(nat, "succ_sub_of_le"),
            succ_mul_choose_eq: kernel.name_str(nat, "succ_mul_choose_eq"),
            mod_eq_pow: kernel.name_str(nat, "modEq_pow"),
            dvd_sum_range_of_forall_lt: kernel.name_str(nat, "dvd_sumRange_of_forall_lt"),
            add_pow_modeq_prime: kernel.name_str(nat, "add_pow_modeq_prime"),
            pow_prime_modeq_self: kernel.name_str(nat, "pow_prime_modeq_self"),
            mod_eq_iff_mod_eq: kernel.name_str(nat, "mod_eq_iff_mod_eq"),
            not_prime_of_pow_mod_ne: kernel.name_str(nat, "not_prime_of_pow_mod_ne"),
            count_range: kernel.name_str(nat, "countRange"),
            count_range_zero: kernel.name_str(nat, "countRange_zero"),
            count_range_succ: kernel.name_str(nat, "countRange_succ"),
            count_range_le: kernel.name_str(nat, "countRange_le"),
            count_range_congr: kernel.name_str(nat, "countRange_congr"),
            count_range_split: kernel.name_str(nat, "countRange_split"),
            count_range_congr_lt: kernel.name_str(nat, "countRange_congr_lt"),
            count_range_point_change: kernel.name_str(nat, "countRange_point_change"),
            count_range_permute: kernel.name_str(nat, "countRange_permute"),
            count_range_product: kernel.name_str(nat, "countRange_product"),
            div_mod_block: kernel.name_str(nat, "div_mod_block"),
            crt_self_map_maps_into: kernel.name_str(nat, "crtSelfMap_mapsInto"),
            crt_self_map_injective_on: kernel.name_str(nat, "crtSelfMap_injectiveOn"),
            totient_mul_of_coprime: kernel.name_str(nat, "totient_mul_of_coprime"),
            count_range_const_true: kernel.name_str(nat, "countRange_const_true"),
            coprime_mul_iff_of_dvd: kernel.name_str(nat, "coprime_mul_iff_of_dvd"),
            totient_mul_of_dvd: kernel.name_str(nat, "totient_mul_of_dvd"),
            totient_pow_succ_of_prime: kernel.name_str(nat, "totient_pow_succ_of_prime"),
            totient_prime_pow: kernel.name_str(nat, "totient_prime_pow"),
            totient_dvd_totient_mul_prime: kernel.name_str(nat, "totient_dvd_totient_mul_prime"),
            totient_dvd_totient_mul: kernel.name_str(nat, "totient_dvd_totient_mul"),
            totient_dvd_of_dvd: kernel.name_str(nat, "totient_dvd_of_dvd"),
            totient_mul_cofactor_bound: kernel.name_str(nat, "totient_mul_cofactor_bound"),
            eq_or_eq_of_totient_eq_totient: kernel.name_str(nat, "eq_or_eq_of_totient_eq_totient"),
            totient_gcd_mul_aux: kernel.name_str(nat, "totient_gcd_mul_aux"),
            totient_gcd_mul_totient_mul: kernel.name_str(nat, "totient_gcd_mul_totient_mul"),
            count_range_reversal_even: kernel.name_str(nat, "countRange_reversal_even"),
            totient_even: kernel.name_str(nat, "totient_even"),
            odd_totient_iff_eq_one: kernel.name_str(nat, "odd_totient_iff_eq_one"),
            odd_totient_iff: kernel.name_str(nat, "odd_totient_iff"),
            totient_coprime_totient_iff: kernel.name_str(nat, "totient_coprime_totient_iff"),
            beq_eq_false_of_ne: kernel.name_str(nat, "beq_eq_false_of_ne"),
            totient: kernel.name_str(nat, "totient"),
            count_range_eq_pred_of_only_zero_false: kernel
                .name_str(nat, "countRange_eq_pred_of_only_zero_false"),
            totient_prime: kernel.name_str(nat, "totient_prime"),
            coprime_succ_self: kernel.name_str(nat, "coprime_succ_self"),
            totient_eq_zero: kernel.name_str(nat, "totient_eq_zero"),
            count_range_succ_of_true: kernel.name_str(nat, "countRange_succ_of_true"),
            count_range_le_of_le: kernel.name_str(nat, "countRange_le_of_le"),
            count_range_ge_two_of_two_witnesses: kernel
                .name_str(nat, "countRange_ge_two_of_two_witnesses"),
            dvd_two_of_totient_le_one: kernel.name_str(nat, "dvd_two_of_totient_le_one"),
            totient_eq_one_iff: kernel.name_str(nat, "totient_eq_one_iff"),
            fin,
            fin_mk: kernel.name_str(fin, "mk"),
            fin_rec: kernel.name_str(fin, "rec"),
            fin_val: kernel.name_str(fin, "val"),
            fin_is_lt: kernel.name_str(fin, "isLt"),
            fin_val_mk: kernel.name_str(fin, "val_mk"),
            injective_on: kernel.name_str(nat, "injectiveOn"),
            surjective_on: kernel.name_str(nat, "surjectiveOn"),
            maps_into: kernel.name_str(nat, "mapsInto"),
            injective_on_imp_surjective_on: kernel.name_str(nat, "injective_on_imp_surjective_on"),
            restrict_injective: kernel.name_str(nat, "restrict_injective"),
            restrict_maps_into: kernel.name_str(nat, "restrict_maps_into"),
            transposition: kernel.name_str(nat, "transposition"),
            transposition_involutive: kernel.name_str(nat, "transposition_involutive"),
            transposition_injective: kernel.name_str(nat, "transposition_injective"),
            transposition_maps_into: kernel.name_str(nat, "transposition_maps_into"),
            conjugate_injective: kernel.name_str(nat, "conjugate_injective"),
            conjugate_maps_into: kernel.name_str(nat, "conjugate_maps_into"),
            setwise_fixed: kernel.name_str(nat, "setwise_fixed"),
            add_sub_cancel_of_le: kernel.name_str(nat, "add_sub_cancel_of_le"),
            sum_range_diagonal: kernel.name_str(nat, "sumRange_diagonal"),
            sum_range_split: kernel.name_str(nat, "sumRange_split"),
            sum_range_rect_eq_diag_add_corner: kernel
                .name_str(nat, "sumRange_rect_eq_diag_add_corner"),
            choose_add_convolution: kernel.name_str(nat, "choose_add_convolution"),
            sum_choose_sq: kernel.name_str(nat, "sum_choose_sq"),
            restrict_pair_injective: kernel.name_str(nat, "restrict_pair_injective"),
            restrict_pair_maps_into: kernel.name_str(nat, "restrict_pair_maps_into"),
            test_bit_aux: kernel.name_str(nat, "testBitAux"),
            test_bit: kernel.name_str(nat, "testBit"),
            test_bit_zero: kernel.name_str(nat, "testBit_zero"),
            test_bit_succ: kernel.name_str(nat, "testBit_succ"),
            test_bit_le_one: kernel.name_str(nat, "testBit_le_one"),
            test_bit_of_zero: kernel.name_str(nat, "testBit_of_zero"),
            mod_two_mul_split: kernel.name_str(nat, "mod_two_mul_split"),
            sum_test_bit_lt: kernel.name_str(nat, "sum_testBit_lt"),
            size_aux: kernel.name_str(nat, "sizeAux"),
            size: kernel.name_str(nat, "size"),
            size_zero: kernel.name_str(nat, "size_zero"),
            size_aux_lt_pow: kernel.name_str(nat, "size_aux_lt_pow"),
            lt_pow_size: kernel.name_str(nat, "lt_pow_size"),
            size_one: kernel.name_str(nat, "size_one"),
            size_eq_zero: kernel.name_str(nat, "size_eq_zero"),
            mod_eq_self_of_lt: kernel.name_str(nat, "mod_eq_self_of_lt"),
            sum_test_bit_eq: kernel.name_str(nat, "sum_testBit_eq"),
            sum_range_const_zero: kernel.name_str(nat, "sumRange_const_zero"),
            zero_of_test_bit_eq_zero: kernel.name_str(nat, "zero_of_testBit_eq_zero"),
            fib_aux: kernel.name_str(nat, "fibAux"),
            fib: kernel.name_str(nat, "fib"),
            fib_add_two: kernel.name_str(nat, "fib_add_two"),
            fib_le_succ: kernel.name_str(nat, "fib_le_succ"),
            fib_mono: kernel.name_str(nat, "fib_mono"),
            fib_pos_of_pos: kernel.name_str(nat, "fib_pos_of_pos"),
            sum_fib: kernel.name_str(nat, "sum_fib"),
            fib_add: kernel.name_str(nat, "fib_add"),
            coprime_fib_succ: kernel.name_str(nat, "coprime_fib_succ"),
            fib_add_two_strictmono: kernel.name_str(nat, "fib_add_two_strictmono"),
            fib_strictmonoon: kernel.name_str(nat, "fib_strictmonoOn"),
            fib_lt_fib: kernel.name_str(nat, "fib_lt_fib"),
            le_fib_self: kernel.name_str(nat, "le_fib_self"),
            le_fib_add_one: kernel.name_str(nat, "le_fib_add_one"),
            reflexive_on: kernel.name_str(nat, "reflexiveOn"),
            symmetric_on: kernel.name_str(nat, "symmetricOn"),
            transitive_on: kernel.name_str(nat, "transitiveOn"),
            equivalence_on: kernel.name_str(nat, "equivalenceOn"),
            eq_equivalence_on: kernel.name_str(nat, "eq_equivalence_on"),
            mod_eq_equivalence_on: kernel.name_str(nat, "modEq_equivalence_on"),
            bijective_on: kernel.name_str(nat, "bijectiveOn"),
            bijective_of_injective_on: kernel.name_str(nat, "bijective_of_injective_on"),
            comp: kernel.name_str(nat, "comp"),
            injective_on_comp: kernel.name_str(nat, "injective_on_comp"),
            set_union: kernel.name_str(nat, "setUnion"),
            set_inter: kernel.name_str(nat, "setInter"),
            set_compl: kernel.name_str(nat, "setCompl"),
            set_diff: kernel.name_str(nat, "setDiff"),
            subset: kernel.name_str(nat, "Subset"),
            count_range_union_add_inter: kernel.name_str(nat, "countRange_union_add_inter"),
            count_range_le_of_subset: kernel.name_str(nat, "countRange_le_of_subset"),
            count_range_compl: kernel.name_str(nat, "countRange_compl"),
            pigeonhole: kernel.name_str(nat, "pigeonhole"),
            set_union_comm: kernel.name_str(nat, "setUnion_comm"),
            set_inter_comm: kernel.name_str(nat, "setInter_comm"),
            set_union_assoc: kernel.name_str(nat, "setUnion_assoc"),
            set_inter_assoc: kernel.name_str(nat, "setInter_assoc"),
            set_union_idem: kernel.name_str(nat, "setUnion_idem"),
            set_inter_idem: kernel.name_str(nat, "setInter_idem"),
            set_inter_union_distrib: kernel.name_str(nat, "setInter_union_distrib"),
            set_union_inter_distrib: kernel.name_str(nat, "setUnion_inter_distrib"),
            set_union_absorb: kernel.name_str(nat, "setUnion_absorb"),
            set_inter_absorb: kernel.name_str(nat, "setInter_absorb"),
            set_compl_union: kernel.name_str(nat, "setCompl_union"),
            set_compl_inter: kernel.name_str(nat, "setCompl_inter"),
            set_compl_involutive: kernel.name_str(nat, "setCompl_involutive"),
            is_group_on: kernel.name_str(nat, "isGroupOn"),
            group_identity_unique: kernel.name_str(nat, "group_identity_unique"),
            group_inverse_unique: kernel.name_str(nat, "group_inverse_unique"),
            group_left_cancel: kernel.name_str(nat, "group_left_cancel"),
            mod_add_is_group: kernel.name_str(nat, "modAdd_isGroup"),
            subset_refl: kernel.name_str(nat, "subset_refl"),
            subset_trans: kernel.name_str(nat, "subset_trans"),
            subset_antisymm: kernel.name_str(nat, "subset_antisymm"),
            set_diff_eq_inter_compl: kernel.name_str(nat, "setDiff_eq_inter_compl"),
            union_eq_right_of_subset: kernel.name_str(nat, "union_eq_right_of_subset"),
            subset_union_left: kernel.name_str(nat, "subset_union_left"),
            subset_inter_left: kernel.name_str(nat, "subset_inter_left"),
            perm_inverse: kernel.name_str(nat, "permInverse"),
            perm_inverse_right: kernel.name_str(nat, "permInverse_right"),
            perm_inverse_left: kernel.name_str(nat, "permInverse_left"),
            id: kernel.name_str(nat, "id"),
            comp_assoc: kernel.name_str(nat, "comp_assoc"),
            is_group_on_fn: kernel.name_str(nat, "isGroupOnFn"),
            bijective_on_comp: kernel.name_str(nat, "bijective_on_comp"),
            bijective_on_perm_inverse: kernel.name_str(nat, "bijective_on_perm_inverse"),
            eq_on: kernel.name_str(nat, "eqOn"),
            eq_on_refl: kernel.name_str(nat, "eqOn_refl"),
            eq_on_symm: kernel.name_str(nat, "eqOn_symm"),
            eq_on_trans: kernel.name_str(nat, "eqOn_trans"),
            symmetric_group_is_group_on_fn: kernel.name_str(nat, "symmetric_group_isGroupOnFn"),
            prod_range: kernel.name_str(nat, "prodRange"),
            prod_range_zero: kernel.name_str(nat, "prodRange_zero"),
            prod_range_succ: kernel.name_str(nat, "prodRange_succ"),
            exists_prime_factorization: kernel.name_str(nat, "exists_prime_factorization"),
            coprime_mul_dvd: kernel.name_str(nat, "coprime_mul_dvd"),
            crt_unique: kernel.name_str(nat, "crt_unique"),
            mod_lcm: kernel.name_str(nat, "mod_lcm"),
            pow_sq_aux: kernel.name_str(nat, "powSqAux"),
            pow_sq: kernel.name_str(nat, "powSq"),
            pow_half_split: kernel.name_str(nat, "pow_half_split"),
            even_or_odd: kernel.name_str(nat, "even_or_odd"),
            pow_sq_aux_eq_pow: kernel.name_str(nat, "pow_sq_aux_eq_pow"),
            pow_sq_eq_pow: kernel.name_str(nat, "pow_sq_eq_pow"),
            pow_sq_zero: kernel.name_str(nat, "pow_sq_zero"),
            pow_sq_succ: kernel.name_str(nat, "pow_sq_succ"),
            prod_range_if: kernel.name_str(nat, "prodRangeIf"),
            prod_range_if_zero: kernel.name_str(nat, "prodRangeIf_zero"),
            prod_range_if_succ: kernel.name_str(nat, "prodRangeIf_succ"),
            prod_range_if_congr_lt: kernel.name_str(nat, "prodRangeIf_congr_lt"),
            injective_on_p: kernel.name_str(nat, "injectiveOnP"),
            maps_into_p: kernel.name_str(nat, "mapsIntoP"),
            surjective_on_p: kernel.name_str(nat, "surjectiveOnP"),
            injective_on_p_imp_surjective_on_p: kernel
                .name_str(nat, "injective_on_p_imp_surjective_on_p"),
            sum_divisors: kernel.name_str(nat, "sumDivisors"),
            sum_divisors_one: kernel.name_str(nat, "sumDivisors_one"),
            sum_divisors_prime: kernel.name_str(nat, "sumDivisors_prime"),
            perfect: kernel.name_str(nat, "Perfect"),
            pow2_geom_sum: kernel.name_str(nat, "pow2_geom_sum"),
            cantor_diagonal: kernel.name_str(nat, "cantor_diagonal"),
            cantor_diagonal_neg: kernel.name_str(nat, "cantor_diagonal_neg"),
            cantor_no_fixed_point: kernel.name_str(nat, "cantor_no_fixed_point"),
            dvd_two_pow_mul_classify: kernel.name_str(nat, "dvd_two_pow_mul_classify"),
            dvd_two_pow_classify: kernel.name_str(nat, "dvd_two_pow_classify"),
            pow_two_ne_pow_two_mul_prime: kernel.name_str(nat, "pow_two_ne_pow_two_mul_prime"),
            pow_pos: kernel.name_str(nat, "pow_pos"),
            pow_lt_pow_succ: kernel.name_str(nat, "pow_lt_pow_succ"),
            pow_lt_pow_of_lt: kernel.name_str(nat, "pow_lt_pow_of_lt"),
            pow_injective: kernel.name_str(nat, "pow_injective"),
            pow_mul_prime_injective: kernel.name_str(nat, "pow_mul_prime_injective"),
            dvd_two_pow_succ_iff_of_le: kernel.name_str(nat, "dvd_two_pow_succ_iff_of_le"),
            sum_divisors_two_pow_eq_geom_sum: kernel
                .name_str(nat, "sumDivisors_two_pow_eq_geom_sum"),
            sum_divisors_two_pow: kernel.name_str(nat, "sumDivisors_two_pow"),
            even_of_even_sq: kernel.name_str(nat, "even_of_even_sq"),
            no_rational_sqrt_two: kernel.name_str(nat, "no_rational_sqrt_two"),
            even: kernel.name_str(nat, "Even"),
            odd: kernel.name_str(nat, "Odd"),
            even_or_odd_exists: kernel.name_str(nat, "even_or_odd_exists"),
            add_self_ne_succ_add_self: kernel.name_str(nat, "add_self_ne_succ_add_self"),
            even_not_odd: kernel.name_str(nat, "even_not_odd"),
            odd_not_even: kernel.name_str(nat, "odd_not_even"),
            even_iff_odd_succ: kernel.name_str(nat, "even_iff_odd_succ"),
            even_iff_mod_two_eq_zero: kernel.name_str(nat, "even_iff_mod_two_eq_zero"),
            odd_iff_mod_two_eq_one: kernel.name_str(nat, "odd_iff_mod_two_eq_one"),
            div_two_mul_two_of_even: kernel.name_str(nat, "div_two_mul_two_of_even"),
            div_two_mul_two_add_one_of_odd: kernel.name_str(nat, "div_two_mul_two_add_one_of_odd"),
            add_one_lt_of_even: kernel.name_str(nat, "add_one_lt_of_even"),
            even_mul_of_even_left: kernel.name_str(nat, "even_mul_of_even_left"),
            odd_of_mul_left: kernel.name_str(nat, "odd_of_mul_left"),
            odd_of_mul_right: kernel.name_str(nat, "odd_of_mul_right"),
            even_add_one: kernel.name_str(nat, "even_add_one"),
            even_add: kernel.name_str(nat, "even_add"),
            even_add_prime: kernel.name_str(nat, "even_add'"),
            even_div: kernel.name_str(nat, "even_div"),
            log_aux: kernel.name_str(nat, "logAux"),
            log: kernel.name_str(nat, "log"),
            log_zero_right: kernel.name_str(nat, "log_zero_right"),
            log_zero_left: kernel.name_str(nat, "log_zero_left"),
            log_one_left: kernel.name_str(nat, "log_one_left"),
            log_one_right: kernel.name_str(nat, "log_one_right"),
            ble_eq_false_of_lt: kernel.name_str(nat, "ble_eq_false_of_lt"),
            log_of_lt: kernel.name_str(nat, "log_of_lt"),
            sqrt_aux: kernel.name_str(nat, "sqrtAux"),
            sqrt: kernel.name_str(nat, "sqrt"),
            sqrt_zero: kernel.name_str(nat, "sqrt_zero"),
            sqrt_one: kernel.name_str(nat, "sqrt_one"),
            clog_aux: kernel.name_str(nat, "clogAux"),
            clog: kernel.name_str(nat, "clog"),
            clog_zero_right: kernel.name_str(nat, "clog_zero_right"),
            clog_zero_left: kernel.name_str(nat, "clog_zero_left"),
            clog_one_left: kernel.name_str(nat, "clog_one_left"),
            clog_one_right: kernel.name_str(nat, "clog_one_right"),
            log_aux_le_fuel: kernel.name_str(nat, "logAux_le_fuel"),
            log_le_self: kernel.name_str(nat, "log_le_self"),
            div_le_div_right: kernel.name_str(nat, "div_le_div_right"),
            log_aux_mono: kernel.name_str(nat, "log_aux_mono"),
            log_mono_right: kernel.name_str(nat, "log_mono_right"),
            log_monotone: kernel.name_str(nat, "log_monotone"),
            clog_aux_mono: kernel.name_str(nat, "clog_aux_mono"),
            clog_mono_right: kernel.name_str(nat, "clog_mono_right"),
            clog_monotone: kernel.name_str(nat, "clog_monotone"),
            clog_pos: kernel.name_str(nat, "clog_pos"),
            log_aux_le_clog_aux: kernel.name_str(nat, "log_aux_le_clog_aux"),
            log_le_clog: kernel.name_str(nat, "log_le_clog"),
            div_lt_self: kernel.name_str(nat, "div_lt_self"),
            log_aux_lt_of_pos: kernel.name_str(nat, "log_aux_lt_of_pos"),
            log_lt_self: kernel.name_str(nat, "log_lt_self"),
            div_le_div_left: kernel.name_str(nat, "div_le_div_left"),
            log_aux_antitone_base: kernel.name_str(nat, "log_aux_antitone_base"),
            log_antitone_left: kernel.name_str(nat, "log_antitone_left"),
            clog_aux_antitone_base: kernel.name_str(nat, "clog_aux_antitone_base"),
            clog_antitone_left: kernel.name_str(nat, "clog_antitone_left"),
            log2: kernel.name_str(nat, "log2"),
            log2_eq_log_two: kernel.name_str(nat, "log2_eq_log_two"),
            bit: kernel.name_str(nat, "bit"),
            bit_false: kernel.name_str(nat, "bit_false"),
            bit_true: kernel.name_str(nat, "bit_true"),
            bit_true_pos: kernel.name_str(nat, "bit_true_pos"),
            bit_false_le_bit_true: kernel.name_str(nat, "bit_false_le_bit_true"),
            bit_false_zero: kernel.name_str(nat, "bit_false_zero"),
            bit_le: kernel.name_str(nat, "bit_le"),
            bit_ne_zero: kernel.name_str(nat, "bit_ne_zero"),
            bit_lt_bit: kernel.name_str(nat, "bit_lt_bit"),
            bit_add_left: kernel.name_str(nat, "bit_add_left"),
            bit_add_right: kernel.name_str(nat, "bit_add_right"),
            land_aux: kernel.name_str(nat, "landAux"),
            land: kernel.name_str(nat, "land"),
            land_zero_left: kernel.name_str(nat, "land_zero_left"),
            land_zero_right: kernel.name_str(nat, "land_zero_right"),
            land_one_one: kernel.name_str(nat, "land_one_one"),
            land_three_five: kernel.name_str(nat, "land_three_five"),
            lor_aux: kernel.name_str(nat, "lorAux"),
            lor: kernel.name_str(nat, "lor"),
            lor_zero_left: kernel.name_str(nat, "lor_zero_left"),
            lor_zero_right: kernel.name_str(nat, "lor_zero_right"),
            lor_three_five: kernel.name_str(nat, "lor_three_five"),
            ldiff_aux: kernel.name_str(nat, "ldiffAux"),
            ldiff: kernel.name_str(nat, "ldiff"),
            ldiff_zero_left: kernel.name_str(nat, "ldiff_zero_left"),
            ldiff_zero_right: kernel.name_str(nat, "ldiff_zero_right"),
            ldiff_three_five: kernel.name_str(nat, "ldiff_three_five"),
            ldiff_five_three: kernel.name_str(nat, "ldiff_five_three"),
            bitwise_aux: kernel.name_str(nat, "bitwiseAux"),
            bitwise: kernel.name_str(nat, "bitwise"),
            bitwise_zero_left: kernel.name_str(nat, "bitwise_zero_left"),
            bitwise_zero_right: kernel.name_str(nat, "bitwise_zero_right"),
            bitwise_and_eq_land_three_five: kernel.name_str(nat, "bitwise_and_eq_land_three_five"),
            bitwise_or_eq_lor_three_five: kernel.name_str(nat, "bitwise_or_eq_lor_three_five"),
            bitwise_xor_three_five: kernel.name_str(nat, "bitwise_xor_three_five"),
            xor: kernel.name_str(nat, "xor"),
            xor_three_five: kernel.name_str(nat, "xor_three_five"),
            even_xor: kernel.name_str(nat, "even_xor"),
            xor_comm: kernel.name_str(nat, "xor_comm"),
            test_bit_xor: kernel.name_str(nat, "testBit_xor"),
            test_bit_land: kernel.name_str(nat, "testBit_land"),
            test_bit_lor: kernel.name_str(nat, "testBit_lor"),
            self_lt_two_pow: kernel.name_str(nat, "self_lt_two_pow"),
            self_lt_two_pow_add: kernel.name_str(nat, "self_lt_two_pow_add"),
            lt_of_test_bit: kernel.name_str(nat, "lt_of_testBit"),
            test_bit_eq_zero_of_lt: kernel.name_str(nat, "testBit_eq_zero_of_lt"),
            msb_exists_of_le_fuel: kernel.name_str(nat, "msb_exists_of_le_fuel"),
            exists_most_significant_bit: kernel.name_str(nat, "exists_most_significant_bit"),
            eq_of_test_bit_eq: kernel.name_str(nat, "eq_of_testBit_eq"),
            xor_assoc: kernel.name_str(nat, "xor_assoc"),
            xor_xor_cancel_left: kernel.name_str(nat, "xor_xor_cancel_left"),
            xor_xor_cancel_right: kernel.name_str(nat, "xor_xor_cancel_right"),
            xor_ne_zero_iff: kernel.name_str(nat, "xor_ne_zero_iff"),
            xor_trichotomy: kernel.name_str(nat, "xor_trichotomy"),
            lt_xor_cases: kernel.name_str(nat, "lt_xor_cases"),
            lt_two_cases: kernel.name_str(nat, "lt_two_cases"),
            mod_two_eq_zero_or_one: kernel.name_str(nat, "mod_two_eq_zero_or_one"),
            bitwise_aux_eq_land_aux: kernel.name_str(nat, "bitwise_aux_eq_land_aux"),
            bitwise_aux_eq_lor_aux: kernel.name_str(nat, "bitwise_aux_eq_lor_aux"),
            bitwise_and_eq_land: kernel.name_str(nat, "bitwise_and_eq_land"),
            bitwise_or_eq_lor: kernel.name_str(nat, "bitwise_or_eq_lor"),
            land_aux_zero_left_any_fuel: kernel.name_str(nat, "land_aux_zero_left_any_fuel"),
            land_aux_agree_of_fuel: kernel.name_str(nat, "land_aux_agree_of_fuel"),
            land_aux_eq_land_of_le: kernel.name_str(nat, "land_aux_eq_land_of_le"),
            lor_aux_zero_left_any_fuel: kernel.name_str(nat, "lor_aux_zero_left_any_fuel"),
            lor_aux_agree_of_fuel: kernel.name_str(nat, "lor_aux_agree_of_fuel"),
            lor_aux_eq_lor_of_le: kernel.name_str(nat, "lor_aux_eq_lor_of_le"),
            ldiff_aux_zero_left_any_fuel: kernel.name_str(nat, "ldiff_aux_zero_left_any_fuel"),
            ldiff_aux_agree_of_fuel: kernel.name_str(nat, "ldiff_aux_agree_of_fuel"),
            ldiff_aux_eq_ldiff_of_le: kernel.name_str(nat, "ldiff_aux_eq_ldiff_of_le"),
            land_aux_comm_of_fuel: kernel.name_str(nat, "land_aux_comm_of_fuel"),
            land_comm: kernel.name_str(nat, "land_comm"),
            lor_aux_comm_of_fuel: kernel.name_str(nat, "lor_aux_comm_of_fuel"),
            lor_comm: kernel.name_str(nat, "lor_comm"),
            land_aux_le_left: kernel.name_str(nat, "land_aux_le_left"),
            land_le_left: kernel.name_str(nat, "land_le_left"),
            land_le_right: kernel.name_str(nat, "land_le_right"),
            land_aux_self_of_fuel: kernel.name_str(nat, "land_aux_self_of_fuel"),
            land_self: kernel.name_str(nat, "land_self"),
            land_one_is_mod: kernel.name_str(nat, "land_one_is_mod"),
            land_mod_two_eq_mul: kernel.name_str(nat, "land_mod_two_eq_mul"),
            land_mod_two_eq_one: kernel.name_str(nat, "land_mod_two_eq_one"),
            land_div_two: kernel.name_str(nat, "land_div_two"),
            bit_div_two: kernel.name_str(nat, "bit_div_two"),
            bit_mod_two: kernel.name_str(nat, "bit_mod_two"),
            land_bit: kernel.name_str(nat, "land_bit"),
            lor_bit: kernel.name_str(nat, "lor_bit"),
            ldiff_bit: kernel.name_str(nat, "ldiff_bit"),
            pair,
            pair_mk: kernel.name_str(pair, "mk"),
            pair_rec: kernel.name_str(pair, "rec"),
            pair_fst: kernel.name_str(pair, "fst"),
            pair_snd: kernel.name_str(pair, "snd"),
            pair_fst_mk: kernel.name_str(pair, "fst_mk"),
            pair_snd_mk: kernel.name_str(pair, "snd_mk"),
            pair_eta: kernel.name_str(pair, "eta"),
            pair_ext: kernel.name_str(pair, "ext"),
            lt_two_mul_of_pos: kernel.name_str(nat, "lt_two_mul_of_pos"),
            half_le_of_succ_le_succ: kernel.name_str(nat, "half_le_of_succ_le_succ"),
            binary_rec_aux: kernel.name_str(nat, "binaryRecAux"),
            binary_rec: kernel.name_str(nat, "binaryRec"),
            binary_rec_aux_zero_fuel: kernel.name_str(nat, "binaryRecAux_zero_fuel"),
            binary_rec_aux_zero: kernel.name_str(nat, "binaryRecAux_zero"),
            binary_rec_aux_succ: kernel.name_str(nat, "binaryRecAux_succ"),
            binary_rec_zero: kernel.name_str(nat, "binaryRec_zero"),
            binary_rec_aux_agree_of_fuel: kernel.name_str(nat, "binaryRecAux_agree_of_fuel"),
            binary_rec_succ: kernel.name_str(nat, "binaryRec_succ"),
            binary_rec_rebuilds_thirteen: kernel.name_str(nat, "binaryRec_rebuilds_thirteen"),
            binary_rec_rebuilds_six: kernel.name_str(nat, "binaryRec_rebuilds_six"),
            bitwise_aux_zero_left_any_fuel: kernel.name_str(nat, "bitwise_aux_zero_left_any_fuel"),
            bitwise_aux_agree_of_fuel: kernel.name_str(nat, "bitwise_aux_agree_of_fuel"),
            bitwise_aux_comm_of_fuel: kernel.name_str(nat, "bitwise_aux_comm_of_fuel"),
            bitwise_comm: kernel.name_str(nat, "bitwise_comm"),
            land_aux_eq_zero_of_left_eq_zero: kernel
                .name_str(nat, "land_aux_eq_zero_of_left_eq_zero"),
            bitwise_aux_swap_of_fuel: kernel.name_str(nat, "bitwise_aux_swap_of_fuel"),
            bitwise_swap: kernel.name_str(nat, "bitwise_swap"),
            land_aux_assoc_of_fuel: kernel.name_str(nat, "land_aux_assoc_of_fuel"),
            land_assoc: kernel.name_str(nat, "land_assoc"),
            bitwise_bit: kernel.name_str(nat, "bitwise_bit'"),
            lor_aux_ne_zero_of_right_ne_zero: kernel
                .name_str(nat, "lor_aux_ne_zero_of_right_ne_zero"),
            lor_aux_assoc_of_fuel: kernel.name_str(nat, "lor_aux_assoc_of_fuel"),
            lor_aux_le_add: kernel.name_str(nat, "lor_aux_le_add"),
            lor_assoc: kernel.name_str(nat, "lor_assoc"),
            lt_of_mul_lt_mul_left: kernel.name_str(nat, "lt_of_mul_lt_mul_left"),
            lt_of_mul_lt_mul_right: kernel.name_str(nat, "lt_of_mul_lt_mul_right"),
            mul_lt_mul_left: kernel.name_str(nat, "mul_lt_mul_left"),
            mul_lt_mul_right: kernel.name_str(nat, "mul_lt_mul_right"),
            div_lt_of_lt_mul: kernel.name_str(nat, "div_lt_of_lt_mul"),
            dvd_mul_left: kernel.name_str(nat, "dvd_mul_left"),
            dvd_mul_left_of_dvd: kernel.name_str(nat, "dvd_mul_left_of_dvd"),
            eq_zero_of_gcd_eq_zero_left: kernel.name_str(nat, "eq_zero_of_gcd_eq_zero_left"),
            eq_zero_of_gcd_eq_zero_right: kernel.name_str(nat, "eq_zero_of_gcd_eq_zero_right"),
            dvd_mod_iff_gen: kernel.name_str(nat, "dvd_mod_iff_gen"),
            div_mul_cancel: kernel.name_str(nat, "div_mul_cancel"),
            dvd_iff_mod_eq_zero: kernel.name_str(nat, "dvd_iff_mod_eq_zero"),
            div_gcd_pos_of_pos_left: kernel.name_str(nat, "div_gcd_pos_of_pos_left"),
            div_gcd_pos_of_pos_right: kernel.name_str(nat, "div_gcd_pos_of_pos_right"),
            dvd_add_iff_left: kernel.name_str(nat, "dvd_add_iff_left"),
            dvd_mul_split: kernel.name_str(nat, "dvd_mul_split"),
            dist: kernel.name_str(nat, "dist"),
            dist_comm: kernel.name_str(nat, "dist_comm"),
            dist_self: kernel.name_str(nat, "dist_self"),
            dist_eq_sub_of_le: kernel.name_str(nat, "dist_eq_sub_of_le"),
            dist_eq_sub_of_le_right: kernel.name_str(nat, "dist_eq_sub_of_le_right"),
            dist_zero_right: kernel.name_str(nat, "dist_zero_right"),
            dist_zero_left: kernel.name_str(nat, "dist_zero_left"),
            dist_succ_succ: kernel.name_str(nat, "dist_succ_succ"),
            dist_eq_zero: kernel.name_str(nat, "dist_eq_zero"),
            add_sub_add_left: kernel.name_str(nat, "add_sub_add_left"),
            dist_add_add_left: kernel.name_str(nat, "dist_add_add_left"),
            dist_add_add_right: kernel.name_str(nat, "dist_add_add_right"),
            dist_mul_left: kernel.name_str(nat, "dist_mul_left"),
            dist_mul_right: kernel.name_str(nat, "dist_mul_right"),
            dist_pos_of_ne: kernel.name_str(nat, "dist_pos_of_ne"),
            dist_eq_intro: kernel.name_str(nat, "dist_eq_intro"),
            dist_triangle_inequality: kernel.name_str(nat, "dist_triangle_inequality"),
            nth_aux: kernel.name_str(nat, "nthAux"),
            nth: kernel.name_str(nat, "nth"),
            nth_root_aux: kernel.name_str(nat, "nthRootAux"),
            nth_root: kernel.name_str(nat, "nthRoot"),
            squarefree_aux: kernel.name_str(nat, "squarefreeAux"),
            // Bare root namespace, deliberately -- see `squarefree.rs`'s
            // module doc: the pinned inventory's raw `Lean.Expr` dump for
            // Mathlib's `Squarefree` applies the constant `` `Squarefree ``
            // directly, never `` `Nat.Squarefree ``.
            squarefree: {
                let root = kernel.anon();
                kernel.name_str(root, "Squarefree")
            },
            fermat_number: kernel.name_str(nat, "fermatNumber"),
            pow_mul: kernel.name_str(nat, "pow_mul"),
            dvd_pow_add_one_of_odd_exp: kernel.name_str(nat, "dvd_pow_add_one_of_odd_exp"),
            dvd_pow_add_one_of_odd_mul_exp: kernel.name_str(nat, "dvd_pow_add_one_of_odd_mul_exp"),
            pow_two_or_has_odd_factor: kernel.name_str(nat, "pow_two_or_has_odd_factor"),
            pow_of_pow_add_prime: kernel.name_str(nat, "pow_of_pow_add_prime"),
            fermatnumber_ne_one: kernel.name_str(nat, "fermatNumber_ne_one"),
            fermatnumber_mono: kernel.name_str(nat, "fermatNumber_mono"),
            coprime_fermatnumber_fermatnumber: kernel
                .name_str(nat, "coprime_fermatNumber_fermatNumber"),
            fermatnumber_zero: kernel.name_str(nat, "fermatNumber_zero"),
            fermatnumber_one: kernel.name_str(nat, "fermatNumber_one"),
            fermatnumber_two: kernel.name_str(nat, "fermatNumber_two"),
            odd_fermatnumber: kernel.name_str(nat, "odd_fermatNumber"),
            fermatnumber_strictmono: kernel.name_str(nat, "fermatNumber_strictMono"),
            lnp_bounded_search: kernel.name_str(nat, "lnp_bounded_search"),
            lnp_of_pointwise_decision: kernel.name_str(nat, "lnp_of_pointwise_decision"),
            lnp_decidable: kernel.name_str(nat, "lnp_decidable"),
            em_implies_lnp: kernel.name_str(nat, "em_implies_lnp"),
            lnp_unrestricted_implies_em: kernel.name_str(nat, "lnp_unrestricted_implies_em"),
            and_or_distrib_left: kernel.name_str(nat, "and_or_distrib_left"),
            and_or_distrib_right: kernel.name_str(nat, "and_or_distrib_right"),
            coprime_dvd_mul_left: kernel.name_str(nat, "coprime_dvd_mul_left"),
            coprime_dvd_mul_right: kernel.name_str(nat, "coprime_dvd_mul_right"),
            coprime_eq_of_mul_eq_zero: kernel.name_str(nat, "coprime_eq_of_mul_eq_zero"),
            add_one_mul_choose_eq: kernel.name_str(nat, "add_one_mul_choose_eq"),
            least_residue: kernel.name_str(nat, "leastResidue"),
            gauss_sign_neg: kernel.name_str(nat, "gaussSignNeg"),
            gauss_neg_count: kernel.name_str(nat, "gaussNegCount"),
            gauss_residue_two_eq_double_of_lt: kernel
                .name_str(nat, "gauss_residue_two_eq_double_of_lt"),
            gauss_neg_count_seven_two: kernel.name_str(nat, "gauss_neg_count_seven_two"),
            gauss_neg_count_eleven_two: kernel.name_str(nat, "gauss_neg_count_eleven_two"),
            gauss_neg_count_thirteen_two: kernel.name_str(nat, "gauss_neg_count_thirteen_two"),
            gauss_neg_count_seventeen_two: kernel.name_str(nat, "gauss_neg_count_seventeen_two"),
            gauss_neg_count_nineteen_two: kernel.name_str(nat, "gauss_neg_count_nineteen_two"),
            gauss_neg_count_twentythree_two: kernel
                .name_str(nat, "gauss_neg_count_twentythree_two"),
            gauss_neg_count_seven_three: kernel.name_str(nat, "gauss_neg_count_seven_three"),
            gauss_count_ble_closed_form_disj: kernel.name_str(nat, "gaussCountBleClosedFormDisj"),
            gauss_neg_count_two_closed_form: kernel.name_str(nat, "gaussNegCountTwoClosedForm"),
            least_residue_injective_of_coprime: kernel
                .name_str(nat, "least_residue_injective_of_coprime"),
            least_residue_ne_zero_of_coprime: kernel
                .name_str(nat, "least_residue_ne_zero_of_coprime"),
            gauss_fold: kernel.name_str(nat, "gaussFold"),
            gauss_fold_injective_of_coprime: kernel
                .name_str(nat, "gauss_fold_injective_of_coprime"),
            div_succ_two_mul_eq_self: kernel.name_str(nat, "div_succ_two_mul_eq_self"),
            gauss_fold_in_range: kernel.name_str(nat, "gauss_fold_in_range"),
            gauss_fold_shift_maps_into: kernel.name_str(nat, "gauss_fold_shift_maps_into"),
            gauss_fold_shift_injective_on: kernel.name_str(nat, "gauss_fold_shift_injective_on"),
        };

        let mut d = NatDev::new(kernel, p);
        declare_arithmetic(&mut d, &p)?;
        declare_boolean_equality(&mut d, &p)?;
        declare_executable_division(&mut d, &p)?;
        declare_subtraction(&mut d, &p)?;
        declare_finite_ranges(&mut d, &p)?;
        declare_defining_equations(&mut d, &p)?;
        declare_subtraction_theorems(&mut d, &p)?;
        declare_additive_theorems(&mut d, &p)?;
        declare_multiplicative_theorems(&mut d, &p)?;
        declare_finite_sum_theorems(&mut d, &p)?;
        declare_order(&mut d, &p)?;
        declare_no_confusion(&mut d, &p)?;
        declare_mul_no_zero_divisors(&mut d, &p)?;
        declare_add_no_zero_summands(&mut d, &p)?;
        declare_zero_or_succ(&mut d, &p)?;
        declare_order_extra(&mut d, &p)?;
        declare_order_more(&mut d, &p)?;
        declare_add_pos(&mut d, &p)?;
        declare_add_basics(&mut d, &p)?;
        declare_boolean_le(&mut d, &p)?;
        declare_euclidean_division(&mut d, &p)?;
        declare_divisibility(&mut d, &p)?;
        declare_div_dvd_div_left(&mut d, &p)?;
        declare_executable_gcd(&mut d, &p)?;
        declare_gcd_semantics(&mut d, &p)?;
        declare_lcm(&mut d, &p)?;
        declare_gcd_bezout(&mut d, &p)?;
        declare_gauss_lemma(&mut d, &p)?;
        declare_lcm_dvd(&mut d, &p)?;
        declare_euclid_lemma(&mut d, &p)?;
        declare_modular_congruence(&mut d, &p)?;
        declare_mod_eq_cancel(&mut d, &p)?;
        declare_primes(&mut d, &p)?;
        // Needs `le_of_dvd` (just declared by `declare_primes`), so these
        // cannot run inside `declare_lcm` above despite conceptually
        // belonging there — see `dvd_antisymm`'s doc comment.
        declare_dvd_antisymm(&mut d, &p)?;
        declare_modeq_gcd_eq(&mut d, &p)?;
        declare_lcm_comm(&mut d, &p)?;
        // Needs `gcd_dvd_left`/`gcd_dvd_right`/`dvd_gcd` (from
        // `declare_gcd_semantics`, far above) and `dvd_antisymm` (just
        // declared above) -- the identical shape `declare_lcm_comm` uses.
        declare_gcd_comm(&mut d, &p)?;
        // Needs `gcd_comm` (just declared above) for `mod_eq_cancel_left`'s
        // coprimality-order flip, and `mod_eq_cancel` (from
        // `declare_mod_eq_cancel`, far above) for the same theorem.
        declare_mod_eq_add_cancel(&mut d, &p)?;
        declare_coprime_lcm_eq_mul(&mut d, &p)?;
        // Needs `dvd_antisymm` (just declared above) for `lcm_assoc`/`lcm_div`,
        // and `le_of_dvd` (from `declare_primes`, already run above this
        // point) for `gcd_le_mul`. `lcm_dvd`/`dvd_lcm_left`/`dvd_lcm_right`/
        // `gcd_mul_lcm` come from `declare_lcm` far above, and `one_le_mul`/
        // `dvd_mul_right_of_dvd` from `declare_divisibility`, earlier still.
        declare_lcm_gcd_lemmas(&mut d, &p)?;
        declare_coprime_of_lt_prime(&mut d, &p)?;
        declare_coprime_of_dvd(&mut d, &p)?;
        declare_coprime_of_dvd_both(&mut d, &p)?;
        // Needs `coprime_of_dvd_left`/`coprime_of_dvd_right` (just declared
        // above), `gauss_lemma` (`declare_gauss_lemma`, far above), and the
        // basic arithmetic/divisibility lemmas (`dvd_mul`, `mul_comm`,
        // `zero_mul`, `div_zero`, `div_mul_cancel_of_dvd`,
        // `mul_left_cancel_of_pos`, `mul_assoc`, `zero_lt_succ`), all
        // declared well before this point.
        declare_coprime_lemmas(&mut d, &p)?;
        declare_prime_dvd_iff_not_coprime(&mut d, &p)?;
        declare_coprime_add_self_right(&mut d, &p)?;
        declare_coprime_self_add_right(&mut d, &p)?;
        declare_coprime_symmetric(&mut d, &p)?;
        declare_not_coprime_zero_zero(&mut d, &p)?;
        declare_coprime_one_iff(&mut d, &p)?;
        declare_coprime_add_self_left(&mut d, &p)?;
        declare_coprime_self_add_left(&mut d, &p)?;
        declare_dvd_lcm_of_dvd(&mut d, &p)?;
        declare_dvd_of_lcm_dvd(&mut d, &p)?;
        declare_coprime_or_dvd_of_prime(&mut d, &p)?;
        declare_coprime_primes(&mut d, &p)?;
        declare_not_prime_of_dvd_of_ne(&mut d, &p)?;
        declare_five_le_of_ne_two_of_ne_three(&mut d, &p)?;
        declare_euclid(&mut d, &p)?;
        // Needs `one_le_factorial` (just declared by `declare_euclid`), so
        // this cannot run inside `declare_divisibility` above despite
        // conceptually belonging there — see `declare_factorial_order`'s doc
        // comment.
        declare_factorial_order(&mut d, &p)?;
        // Needs `Nat.one_le_factorial` (`declare_euclid`, just above),
        // `Nat.one_le_mul` (`declare_divisibility`, far above), and
        // `zero_add`/`succ_add`/`add_comm`/`le_refl`/`le_succ_succ`/
        // `le_add_right`/`add_le_add_left`/`le_trans` (all basic
        // algebra/order theorems, far above); nothing needs these closed
        // `ml430` mirrors, so they go here.
        declare_add_factorial_le_factorial_add(&mut d, &p)?;
        declare_add_factorial_succ_le_factorial_add_succ(&mut d, &p)?;
        // Same dependency footprint as the `≤` pair just above, plus
        // `Nat.factorial_lt_of_lt`/`Nat.factorial_le`/`Nat.mul_le_mul_left`/
        // `Nat.mul_one`/`Nat.le_succ`/`Nat.lt_succ_self` (`declare_factorial_order`
        // and the general order/algebra block, both far above `declare_euclid`).
        declare_add_factorial_lt_factorial_add(&mut d, &p)?;
        declare_add_factorial_succ_lt_factorial_add_succ(&mut d, &p)?;
        declare_choose_all(&mut d, &p)?;
        declare_binomial_theorem(&mut d, &p)?;
        declare_combinatorial_identities(&mut d, &p)?;
        declare_succ_sub_of_le(&mut d, &p)?;
        declare_succ_mul_choose_eq(&mut d, &p)?;
        declare_prime_dvd_choose(&mut d, &p)?;
        // Must run before `declare_fermat`/`declare_totient_all`: both build
        // proofs of `Lt zero n -> Eq n (succ (pred n))` on the fly today and
        // are being migrated to call this declared theorem instead.
        declare_succ_pred_of_pos(&mut d, &p)?;
        // Needs `succ_pred_of_pos` (just declared above, via
        // `div_mod_reconstructed`'s local copy of `group.rs`'s helper), plus
        // `div_mod_exec` (`declare_divisibility`, far above) and
        // `div_mod_unique`/`div_mod_add_multiple` (`declare_euclidean_division`,
        // further above still).
        declare_add_div_mod_shift_family(&mut d, &p)?;
        // Needs the same shift-family dependencies (`div_mod_exec`,
        // `div_mod_unique`) plus `left_distrib`/`succ_injective`
        // (`declare_multiplicative_theorems`/`declare_additive_theorems`,
        // far above) and `lt_or_ge`/`sub_add_cancel`/`le_of_succ_le_succ`/
        // `le_succ_succ`/`add_le_add_left`/`add_le_add_right`/`le_trans`
        // (`declare_order`/`declare_order_more`, also above) -- placed right
        // after the shift family since it is the ninth mirror in the same
        // dispatched batch and needs no dependency declared later than these.
        declare_add_div_of_dvd_add_add_one(&mut d, &p)?;
        // Needs `div_mod_exec`/`div_mod_unique` (`declare_divisibility`/
        // `declare_euclidean_division`, far above), `one_le_mul`
        // (`declare_divisibility`), `add_mul_div_left` (just declared by
        // `declare_add_div_mod_shift_family` above), `mod_lt` (`declare_divisibility`,
        // far above) and `mul_assoc`/`left_distrib`/`add_assoc`/`add_comm`/
        // `mul_succ`/`mul_le_mul_left`/`add_lt_add_left`/`lt_of_lt_of_le`/
        // `zero_mul`/`mul_zero`/`add_zero`/`zero_add`/`mod_zero`/`div_zero`/
        // `zero_mod`/`mul_comm`/`zero_lt_succ` (all `declare_additive_theorems`/
        // `declare_multiplicative_theorems`/`declare_order`/`declare_order_more`,
        // far above). Placed here since it is the natural continuation of the
        // `ml430` `Nat` mod/mul family dispatched alongside the shift family.
        declare_mod_mul_family(&mut d, &p)?;
        // Needs `lt_well_founded`/`WellFounded.fix` (`declare_gcd_semantics`,
        // far above -- the same primitive `declare_gcd_bezout`/
        // `declare_exists_prime_factorization`/`declare_irrational` already
        // use), `lt_or_ge`/`le_add_right`/`le_succ_succ`/`le_trans`/
        // `lt_of_lt_of_le`/`lt_of_le_of_lt`/`lt_irrefl` (`declare_order`/
        // `declare_order_more`, above), `div_mod_exec`
        // (`declare_divisibility`) and `succ_pred_of_pos` (just declared
        // above), and `mul_comm`/`mul_le_mul_left`/`zero_add`/`zero_lt_succ`
        // (`declare_additive_theorems`/`declare_multiplicative_theorems`/
        // `declare_order`, all far above).
        declare_base_induction(&mut d, &p)?;
        // Needs `succ_pred_of_pos`, just declared above: `prime_two`
        // (`two_divisor_dichotomy`) is not available before this point.
        declare_coprime_of_forall_prime_dvd(&mut d, &p)?;
        // Needs `coprime_of_forall_prime_dvd` (just above) and `euclid_lemma`
        // (`declare_euclid_lemma`, far above).
        declare_coprime_mul_of_coprime(&mut d, &p)?;
        // Needs `mod_zero` (`declare_executable_division`, far above),
        // `gcd_succ`/`gcd_comm` (`declare_executable_gcd`, above) --
        // `301`'s Step 1, mod-gcd invariance.
        declare_gcd_mod_left_eq_gcd(&mut d, &p)?;
        // Needs `coprime_mul_right_right`/`coprime_mul_left_right`
        // (`declare_coprime_lemmas`, above) and `coprime_mul_of_coprime`
        // (just above) -- `301`'s Step 3, the pointwise coprimality `Iff`.
        declare_coprime_mul_iff(&mut d, &p)?;
        declare_dvd_of_forall_prime_mul_dvd(&mut d, &p)?;
        // `IsRelPrime` only needs `dvd_gcd`/`gcd_dvd_left`/`gcd_dvd_right`/
        // `eq_one_of_dvd_one`, all declared long before this point; placed
        // here to sit next to the other `Coprime` characterisation theorems.
        declare_is_rel_prime(&mut d, &p)?;
        declare_coprime_iff_is_rel_prime(&mut d, &p)?;
        // `Nat.minFacAux`/`Nat.minFac` need only `Nat.modulo`/`Nat.beq`/
        // `Nat.sub` (all declared long before this point); placed here to
        // sit next to the other prime/coprimality declarations.
        declare_min_fac_all(&mut d, &p)?;
        declare_prime_pred_pos(&mut d, &p)?;
        declare_succ_pred_prime(&mut d, &p)?;
        declare_fermat(&mut d, &p)?;
        declare_fermat_witness_all(&mut d, &p)?;
        declare_totient_all(&mut d, &p)?;
        // Needs `coprime_add_self_right`/`coprime_one_right_iff` (declared
        // far above, alongside the other `Coprime` characterisations) plus
        // `count_range`/`totient`, just declared above.
        declare_totient_lemmas_all(&mut d, &p)?;
        declare_perfect_all(&mut d, &p)?;
        declare_finite_set_all(&mut d, &p)?;
        declare_fin(&mut d, &p)?;
        declare_injective_surjective(&mut d, &p)?;
        declare_pigeonhole(&mut d, &p)?;
        declare_nat_pigeonhole(&mut d, &p)?;
        declare_restrict_injective(&mut d, &p)?;
        declare_restrict_maps_into(&mut d, &p)?;
        // `count_range_permute.rs`: needs `countRange`/`countRange_succ`
        // (`declare_totient_all`, above), the pigeonhole
        // (`declare_pigeonhole`) and BOTH restriction lemmas immediately
        // above — its successor step is exactly their intended consumer.
        declare_count_range_congr_lt(&mut d, &p)?;
        declare_count_range_point_change(&mut d, &p)?;
        declare_count_range_permute(&mut d, &p)?;
        declare_count_range_product(&mut d, &p)?;
        declare_div_mod_block(&mut d, &p)?;
        declare_transposition(&mut d, &p)?;
        declare_transposition_involutive(&mut d, &p)?;
        declare_transposition_injective(&mut d, &p)?;
        declare_transposition_maps_into(&mut d, &p)?;
        declare_conjugate_injective(&mut d, &p)?;
        declare_conjugate_maps_into(&mut d, &p)?;
        declare_setwise_fixed(&mut d, &p)?;
        declare_restrict_pair_injective(&mut d, &p)?;
        declare_restrict_pair_maps_into(&mut d, &p)?;
        declare_diagonal(&mut d, &p)?;
        declare_rectangle(&mut d, &p)?;
        // `Nat.sumDivisors_two_pow{,_eq_geom_sum}` (`perfect.rs`) need
        // `Nat.sumRange_split`, just declared by `declare_rectangle` above —
        // `declare_perfect_all` runs much earlier in this pipeline, before
        // `sumRange_split` exists, so these two are called from here instead.
        declare_sum_divisors_two_pow_eq_geom_sum(&mut d, &p)?;
        declare_sum_divisors_two_pow(&mut d, &p)?;
        declare_vandermonde_all(&mut d, &p)?;
        declare_catalan_all(&mut d, &p)?;
        declare_binary_all(&mut d, &p)?;
        declare_size_all(&mut d, &p)?;
        // Needs `Nat.size`/`lt_pow_size`/`size_zero` (`declare_size_all`,
        // just above) plus basic order lemmas from far above
        // (`le_of_lt_succ`, `zero_le`, `le_antisymm`); nothing needs these
        // two closed `ml430` mirrors, so they go right after `Nat.size`.
        declare_size_extra_all(&mut d, &p)?;
        declare_zero_of_test_bit(&mut d, &p)?;
        declare_fib_all(&mut d, &p)?;
        declare_relation_properties(&mut d, &p)?;
        declare_eq_equivalence_on(&mut d, &p)?;
        declare_mod_eq_equivalence_on(&mut d, &p)?;
        declare_bijective_on(&mut d, &p)?;
        declare_bijective_of_injective_on(&mut d, &p)?;
        declare_comp(&mut d, &p)?;
        declare_injective_on_comp(&mut d, &p)?;
        declare_group_all(&mut d, &p)?;
        declare_permutation_all(&mut d, &p)?;
        declare_prod_range(&mut d, &p)?;
        declare_prod_range_if_all(&mut d, &p)?;
        declare_pigeonhole_p_all(&mut d, &p)?;
        declare_exists_prime_factorization(&mut d, &p)?;
        declare_crt(&mut d, &p)?;
        // Needs `lcm_dvd` (declared much earlier by `declare_lcm_dvd`) and
        // `gap_dvd`/`modeq_of_dvd_gap` (`crt.rs`, just declared above via
        // `declare_crt`'s `mod_eq`/`sub_add_cancel` dependencies).
        declare_mod_lcm(&mut d, &p)?;
        declare_prime_dvd_mul_of_dvd_ne(&mut d, &p)?;
        declare_powsq_all(&mut d, &p)?;
        // Needs `Nat.even_or_odd`, just declared by `declare_powsq_all` above.
        declare_parity_all(&mut d, &p)?;
        // The parity/division-by-two mirror cluster (`parity_div.rs`, lane
        // nat-parity-div, 2026-08-30). Needs `Nat.Even`/`Nat.Odd` and their
        // bridges, just declared above by `declare_parity_all`, plus
        // `div_mod_exec`/`div_mod_unique` (`division.rs`, far above),
        // `lt_or_eq_of_le` (order lemmas, far above) and `right_distrib`/
        // `mul_comm`/`add_zero` (basic arithmetic, far above).
        declare_parity_div_all(&mut d, &p)?;
        // `Nat.even_add`/`Nat.even_add'` (`even_add_family.rs`, lane
        // parity-finish, 2026-08-30). Needs `Nat.Even`/`Nat.Odd`,
        // `even_or_odd_exists`/`even_not_odd`/`odd_not_even`
        // (`declare_parity_all`, just above) and `add_add_add_comm`
        // (`declare_add_basics`, far above)/`succ_add` (additive theorems,
        // far above).
        declare_even_add_family_all(&mut d, &p)?;
        // `Nat.even_div` (`even_div.rs`, lane parity-finish, 2026-08-30).
        // Needs `Nat.even_iff_mod_two_eq_zero` (`declare_parity_all`, just
        // above), `Nat.mod_mul_right_div_self` (`declare_mod_mul_family`,
        // far above) and `mul_comm` (additive/multiplicative theorems, far
        // above).
        declare_even_div(&mut d, &p)?;
        // `Nat.countRange_reversal_even`: general, `totient`-independent.
        // Needs `count_range`/`count_range_split` (`declare_totient_all`,
        // far above), `Nat.Even` (`declare_parity_all`, just above),
        // `lt_well_founded`/`WellFounded.fix` (`declare_gcd_semantics`,
        // far above), `zero_or_succ` (declared alongside the other basic
        // `Nat` equational facts, far above), `succ_sub_succ`/
        // `succ_sub_of_le`/`succ_pred_of_pos`/`zero_le`/`le_succ`/
        // `le_trans`/`succ_le_succ`/`le_of_succ_le_succ`/`lt_succ_self`/
        // `zero_lt_succ` (order lemmas, far above), and `add_assoc`/
        // `add_comm`/`zero_add`/`succ_add` (additive theorems, far above).
        declare_count_range_reversal_even(&mut d, &p)?;
        // `Nat.totient_even`: needs `Nat.countRange_reversal_even`, just
        // declared above, and `Nat.Even` (`declare_parity_all`, just above
        // that) -- see `totient_lemmas.rs`'s module doc / the doc comment on
        // `declare_totient_lemmas_all` for why this cannot be dispatched
        // alongside the rest of that file's `declare_totient_lemmas_all`
        // call, far above.
        declare_totient_even(&mut d, &p)?;
        // `Nat.odd_totient_iff_eq_one`/`Nat.odd_totient_iff`: need
        // `Nat.totient_even`, just declared above, and `Nat.odd_not_even`
        // (`declare_parity_all`, above that).
        declare_odd_totient_iff_eq_one(&mut d, &p)?;
        declare_odd_totient_iff(&mut d, &p)?;
        // `Nat.totient_coprime_totient_iff`: needs `Nat.totient_even`, just
        // declared above.
        declare_totient_coprime_totient_iff(&mut d, &p)?;
        // Needs `Nat.Even`/`Nat.Odd`/`even_or_odd_exists`/`even_not_odd`, just
        // declared by `declare_parity_all` above -- cannot run alongside the
        // other `coprime_*` declarations near `declare_primes` since parity
        // does not exist yet at that point in the build.
        declare_coprime_two_left(&mut d, &p)?;
        declare_coprime_two_right(&mut d, &p)?;
        declare_coprime_odd_of_left(&mut d, &p)?;
        declare_coprime_odd_of_right(&mut d, &p)?;
        // Also needs `Nat.Odd`/`even_not_odd`/`coprime_two_left`'s bridges,
        // just declared above, plus `euclid_lemma` (declared much earlier by
        // `declare_euclid_lemma`).
        declare_prime_odd_of_ne_two(&mut d, &p)?;
        declare_prime_even_iff(&mut d, &p)?;
        declare_prime_not_dvd_mul(&mut d, &p)?;
        declare_prime_dvd_of_dvd_pow(&mut d, &p)?;
        // `prime_char.rs`: the surviving "no prime is a proper power"
        // family (`declare_prime_not_prime_pow_all`, needs only
        // `pow_succ`/`pow_zero`/`one_pow`/`mul_left_cancel_of_pos`/
        // `not_dvd_one_of_two_le`, all far above) and the `Coprime`/prime
        // bridge (`declare_prime_not_coprime_iff_dvd`, needs
        // `dvd_gcd`/`gcd_dvd_left`/`gcd_dvd_right`/`exists_prime_dvd`/
        // `lt_or_ge`, all far above, and this file's own `prime_two`
        // built from `ops::two_divisor_dichotomy`). The six numeric-bound
        // facts, the parity facts, and `prime_eq_one_or_self_of_dvd` that
        // used to live here now come from `prime_dvd_mirrors.rs`, declared
        // far below (`declare_prime_dvd_mirrors_all`) -- see that call site
        // for why it goes last, and see `declare_prime_mul_eq_prime_sq_iff`
        // just after it for why THIS family's hardest fact has to wait for
        // it too.
        declare_prime_not_prime_pow_all(&mut d, &p)?;
        declare_prime_not_coprime_iff_dvd(&mut d, &p)?;
        declare_cantor_all(&mut d, &p)?;
        declare_even_of_even_sq(&mut d, &p)?;
        declare_no_rational_sqrt_two(&mut d, &p)?;
        // Needs `Nat.div` (`declare_executable_division`) and `Nat.ble`
        // (`declare_boolean_le`), both far above; nothing needs `Nat.log`, so
        // it goes last.
        declare_log_all(&mut d, &p)?;
        // Needs `Nat.mul` (`declare_arithmetic`) and `Nat.ble`
        // (`declare_boolean_le`), both far above; nothing needs `Nat.sqrt`.
        declare_sqrt_all(&mut d, &p)?;
        // Needs `Nat.add`/`Nat.sub`/`Nat.div`/`Nat.ble`, all far above, and
        // nothing needs `Nat.clog`, so it goes last too.
        declare_clog_all(&mut d, &p)?;
        // Needs `Nat.add`/`Nat.mul` (`declare_arithmetic`), `Nat.le_succ`
        // (`order_extra`) and the `zero_lt_succ` term-builder, all far above;
        // nothing needs `Nat.bit`, so it goes last too.
        declare_bit_all(&mut d, &p)?;
        // Needs `Nat.sub`/`Nat.mul` (`declare_arithmetic`/`declare_subtraction`,
        // both far above) and the order/algebra theorems (`not_lt_zero`,
        // `le_of_lt_succ`, `lt_or_eq_of_le`, `sub_self`, `zero_mul`,
        // `mul_zero`, `mul_one`); nothing needs `Nat.descFactorial`, so it
        // goes last too.
        declare_desc_factorial_all(&mut d, &p)?;
        // Needs `Nat.descFactorial_eq_factorial_mul_choose`/
        // `Nat.descFactorial_succ_eq_succ_mul` (`declare_desc_factorial_all`,
        // just above) plus `mul_comm`/`mul_assoc`/`one_mul`/`factorial_succ`,
        // all far above; nothing needs this closed `ml430` mirror.
        declare_add_choose_mul_factorial_mul_factorial(&mut d, &p)?;
        // Needs `Nat.add_choose_mul_factorial_mul_factorial` (just above)
        // plus `Nat.div`/`div_mul_cancel_of_dvd`/`dvd_mul`
        // (`declare_euclidean_division`, far above),
        // `mul_assoc`/`mul_comm`/`mul_left_cancel_of_pos`/`one_le_factorial`/
        // `one_le_mul`, all far above; nothing needs this closed `ml430`
        // division-normal-form mirror.
        declare_add_choose(&mut d, &p)?;
        // Needs `Nat.add`/`Nat.mul`/`Nat.beq` (`declare_arithmetic`/
        // `declare_boolean_equality`) and `Nat.div`/`Nat.mod`
        // (`declare_executable_division`), all far above; nothing needs
        // `Nat.land`, so it goes last too.
        declare_land_all(&mut d, &p)?;
        // Needs `Nat.add`/`Nat.mul`/`Nat.beq`/`Nat.ble`
        // (`declare_arithmetic`/`declare_boolean_equality`/
        // `declare_boolean_le`) and `Nat.div`/`Nat.mod`
        // (`declare_executable_division`), all far above; nothing needs
        // `Nat.lor`, so it goes last too.
        declare_lor_all(&mut d, &p)?;
        // Needs `Nat.add`/`Nat.mul`/`Nat.beq` (`declare_arithmetic`/
        // `declare_boolean_equality`) and `Nat.div`/`Nat.mod`
        // (`declare_executable_division`), all far above; nothing needs
        // `Nat.ldiff`, so it goes last too.
        declare_ldiff_all(&mut d, &p)?;
        // Needs `Nat.add`/`Nat.mul`/`Nat.beq` (`declare_arithmetic`/
        // `declare_boolean_equality`) and `Nat.div`/`Nat.mod`
        // (`declare_executable_division`), all far above, plus `Nat.land`
        // and `Nat.lor` (just above) for its concrete specialization
        // checks; nothing needs `Nat.bitwise`, so it goes last too.
        declare_bitwise_all(&mut d, &p)?;
        // `Nat.xor := Nat.bitwise xor_fn`: needs `Nat.bitwise`
        // (`declare_bitwise_all`, just above) and nothing else; a direct
        // partial application, not a new recursion. Nothing needs
        // `Nat.xor`, so it goes right after `Nat.bitwise`.
        declare_xor_all(&mut d, &p)?;
        // Needs `Nat.xor` (just above) and `Nat.even_iff_mod_two_eq_zero`
        // (`declare_parity_all`, far above) -- the parity <-> low-bit bridge.
        declare_xor_parity_all(&mut d, &p)?;
        // Needs `Nat.bitwise` and `Nat.land`/`Nat.lor` (all just above),
        // `Nat.mod_lt` (`declare_gcd_all`, far above) and the bounded-cases
        // eliminator's own lemmas (`le_of_lt_succ`, `lt_or_eq_of_le`,
        // `zero_le`, `le_antisymm`). Nothing needs these agreement theorems,
        // so they go after everything they relate.
        declare_rec_agreement_all(&mut d, &p)?;
        // Needs `Nat.mod_two_eq_zero_or_one`, just declared above by
        // `declare_rec_agreement_all` (`parity_div.rs`, lane nat-parity-div,
        // 2026-08-30 -- see that file's `declare_parity_div_all` doc for why
        // this one call is separate from the rest of its cluster).
        declare_even_add_one(&mut d, &p)?;
        // Needs `Nat.landAux`/`Nat.land` (`declare_land_all`, far above) and
        // the order/division lemmas `half_le_predecessor_of_succ` composes
        // (`le_of_succ_le_succ`, `lt_of_lt_of_le`, `div_mod_lt_mul_iff`,
        // `div_mod_exec`, `succ_pred_of_pos`, `le_trans`, `zero_lt_succ`);
        // nothing needs fuel-irrelevance, so it goes last too.
        declare_land_fuel_irrelevance_all(&mut d, &p)?;
        // Transport of the same fuel-irrelevance to `lorAux`: needs
        // `Nat.lorAux`/`Nat.lor` (`declare_lor_all`, far above) and the same
        // order/division lemmas `declare_land_fuel_irrelevance_all` composes;
        // nothing needs it, so it goes right after its `land` sibling.
        declare_lor_fuel_irrelevance_all(&mut d, &p)?;
        // Transport to `ldiffAux`: needs `Nat.ldiffAux`/`Nat.ldiff`
        // (`declare_ldiff_all`, far above) and the same order/division
        // lemmas; nothing needs it, so it goes last of the three.
        declare_ldiff_fuel_irrelevance_all(&mut d, &p)?;
        // `Nat.land_comm`: needs `Nat.land_aux_agree_of_fuel` (just above)
        // plus `Nat.le_add_right`/`Nat.add_comm`/`Nat.le_refl`, all far
        // above; nothing needs it, so it goes right after fuel-irrelevance.
        declare_land_comm(&mut d, &p)?;
        // `Nat.lor_comm`: needs `Nat.lor_aux_agree_of_fuel`
        // (`declare_lor_fuel_irrelevance_all`, just above),
        // `half_le_predecessor_of_succ`'s composed order/division lemmas,
        // and the `ble`-based per-bit max-commutativity split; nothing
        // needs it, so it goes right after its `land` sibling.
        declare_lor_comm(&mut d, &p)?;
        // `Nat.bitwise_comm`: needs `Nat.bitwise`/`Nat.bitwiseAux`
        // (`declare_bitwise_all`, far above) and
        // `half_le_predecessor_of_succ`'s composed order/division lemmas
        // (same as `land_comm`/`lor_comm`, all far above) -- self-contained
        // otherwise (its own fuel-irrelevance and same-fuel commutativity
        // are declared inside `declare_bitwise_comm` itself, generalized
        // over a symbolic `f`, unlike `land`/`lor`'s fixed-`f` versions);
        // nothing needs it, so it goes right after its `land`/`lor` siblings.
        declare_bitwise_comm(&mut d, &p)?;
        // `Nat.bitwise_swap`: needs `Nat.bitwise`/`Nat.bitwiseAux`
        // (`declare_bitwise_all`, far above) and the ALREADY-DECLARED
        // `Nat.bitwise_aux_agree_of_fuel` (declared inside
        // `declare_bitwise_comm`, just above) — so it must come after its
        // `bitwise_comm` sibling, not merely after `bitwise` itself.
        declare_bitwise_swap(&mut d, &p)?;
        // `Nat.land_aux_le_left`/`Nat.land_le_left`: needs `Nat.landAux`
        // (`declare_land_all`, far above) and division lemmas
        // (`div_mod_exec`, `mul_le_mul_left`, `add_le_add_left/right`,
        // `mod_lt`, `le_of_lt_succ`, all far above); nothing needs it, so it
        // goes right after `land_comm`.
        declare_land_le_left_all(&mut d, &p)?;
        // `Nat.land_le_right`: needs only `Nat.land_le_left` (just above)
        // and `Nat.land_comm` (`declare_land_comm`, above) -- a transport,
        // no new `landAux` machinery. Needed for `Nat.and_le_right`'s
        // `ml430` mirror (draw 9, `natural-bitwise-basics`).
        declare_land_le_right_all(&mut d, &p)?;
        // `Nat.bit_div_two`/`Nat.bit_mod_two`/`Nat.land_bit`: needs `Nat.bit`
        // (`declare_bit_all`, far above), `Nat.div_mod_exec`/
        // `Nat.div_mod_unique` (`declare_euclidean_division`/
        // `declare_executable_division_spec`, far above), and
        // `Nat.land_aux_eq_land_of_le` plus `Nat.land_zero_left`/
        // `Nat.land_zero_right` (`declare_land_fuel_irrelevance_all`/
        // `declare_land_all`, both above); nothing needs the decode bridge,
        // so it goes last too.
        declare_bit_decode_all(&mut d, &p)?;
        // `Nat.bitwise_bit'`: needs `Nat.bit_div_two`/`Nat.bit_mod_two`
        // (`declare_bit_decode_all`, just above) and the ALREADY-DECLARED
        // `Nat.bitwise_aux_agree_of_fuel` (declared inside
        // `declare_bitwise_comm`, far above) -- so it must come after both.
        declare_bitwise_bit(&mut d, &p)?;
        // `Nat.land_aux_eq_zero_of_left_eq_zero`: needs `Nat.landAux`
        // (`declare_land_all`), `Nat.land_aux_zero_left_any_fuel`
        // (`declare_land_fuel_irrelevance_all`, both far above),
        // `Nat.add_eq_zero`/`Nat.zero_or_succ` (`declare_add_no_zero_summands`/
        // `declare_zero_or_succ`, both far above), `Nat.mul_eq_zero`
        // (`declare_mul_no_zero_divisors`, far above), and
        // `Nat.div_mod_unique`/`Nat.div_mod_exec`/`Nat.mod_lt`/`Nat.mul_assoc`/
        // `Nat.zero_mul`/`Nat.mul_zero`/`Nat.succ_ne_zero` (all far above);
        // nothing needs it yet, so it goes right after `land_le_left`.
        declare_land_zero_propagation_all(&mut d, &p)?;
        // `Nat.land_aux_assoc_of_fuel`/`Nat.land_assoc`: needs
        // `Nat.landAux`/`Nat.land` (`declare_land_all`, far above),
        // `Nat.land_aux_zero_left_any_fuel`/`Nat.land_aux_agree_of_fuel`
        // (`declare_land_fuel_irrelevance_all`, far above),
        // `Nat.land_aux_comm_of_fuel` (`declare_land_comm`, above),
        // `Nat.land_le_left` (`declare_land_le_left_all`, above),
        // `Nat.land_aux_eq_zero_of_left_eq_zero` (`declare_land_zero_
        // propagation_all`, just above), `Nat.zero_or_succ` (far above),
        // and `Nat.div_mod_unique`/`Nat.div_mod_exec`/`Nat.mod_lt`/
        // `Nat.mul_assoc`/`Nat.le_add_right`/`Nat.add_comm`/`Nat.le_trans`
        // (all far above); nothing needs it, so it goes last of the
        // `land` family.
        declare_land_assoc_all(&mut d, &p)?;
        // `Nat.land_aux_self_of_fuel`/`Nat.land_self`: needs only
        // `Nat.landAux`/`Nat.land` (`declare_land_all`, far above),
        // `Nat.le_antisymm`/`Nat.zero_le`/`Nat.le_of_succ_le_succ`/
        // `Nat.le_refl` (order theorems, far above), and
        // `half_le_predecessor_of_succ` (`rec_agreement.rs`,
        // `declare_land_fuel_irrelevance_all`'s neighbourhood, far above).
        // Draw 9 (`natural-bitwise-basics`,
        // `docs/plan/status/draw9-second-theorems.md`).
        declare_land_self_all(&mut d, &p)?;
        // `Nat.land_one_is_mod`/`Nat.land_mod_two_eq_mul`/
        // `Nat.land_mod_two_eq_one`: needs `Nat.landAux`/`Nat.land`
        // (`declare_land_all`), `Nat.land_comm` (above),
        // `Nat.land_zero_left`/`Nat.land_zero_right` (`declare_land_all`),
        // `Nat.mod_eq_self_of_lt`/`Nat.mod_lt`/`Nat.zero_mod`/`Nat.zero_mul`/
        // `Nat.one_mul`/`Nat.mul_zero`/`Nat.zero_add` (order/arithmetic, far
        // above), and `mod_two_mul_add_of_lt` (`parity.rs`, far above).
        // Draw 9 (`natural-bitwise-basics`,
        // `docs/plan/status/draw9-second-theorems.md`).
        declare_land_low_bit_all(&mut d, &p)?;
        // `Nat.land_div_two`: needs `Nat.landAux`/`Nat.land` (`declare_land_all`,
        // far above), `Nat.land_zero_left`/`Nat.land_zero_right`
        // (`declare_land_all`), `Nat.land_aux_agree_of_fuel`
        // (`declare_land_fuel_irrelevance_all`, far above), and
        // `half_le_predecessor_of_succ`/`Nat.div_mod_exec`/
        // `Nat.div_mod_unique`/`Nat.zero_div`/`Nat.zero_mul`/`Nat.one_mul`/
        // `Nat.mod_lt`/`Nat.le_refl` (all far above). Draw 9
        // (`natural-bitwise-basics`,
        // `docs/plan/status/draw9-second-theorems.md`).
        declare_land_div_two_all(&mut d, &p)?;
        // `Nat.lor_aux_ne_zero_of_right_ne_zero`: needs `Nat.lorAux`
        // (`declare_lor_all`, far above), `Nat.succ_ne_zero`
        // (`declare_no_confusion_all`, far above), `Nat.mul_eq_zero`
        // (`declare_mul_no_zero_divisors`, far above), and
        // `Nat.div_mod_exec`/`Nat.mod_lt` (far above); nothing needs it yet,
        // so it goes right after the `land` family. See
        // `docs/plan/status/266-nat-lor-assoc.md` for why this is the
        // "invariant that replaces zero propagation" for `lor` rather than
        // a transport of `land_aux_eq_zero_of_left_eq_zero`.
        declare_lor_aux_ne_zero_of_right_ne_zero_all(&mut d, &p)?;
        // `Nat.lor_aux_le_add`/`Nat.lor_aux_assoc_of_fuel`/`Nat.lor_assoc`:
        // needs `Nat.lorAux`/`Nat.lor` (`declare_lor_all`, far above),
        // `Nat.lor_aux_zero_left_any_fuel`/`Nat.lor_aux_agree_of_fuel`
        // (`declare_lor_fuel_irrelevance_all`, far above),
        // `Nat.lor_aux_ne_zero_of_right_ne_zero` (just above),
        // `Nat.zero_or_succ` (far above), and
        // `Nat.div_mod_unique`/`Nat.div_mod_exec`/`Nat.mod_lt`/
        // `Nat.left_distrib`/`Nat.mul_le_mul_left`/`Nat.add_le_add_left`/
        // `Nat.add_le_add_right`/`Nat.le_trans`/`Nat.le_add_right`/
        // `Nat.add_comm`/`Nat.add_assoc` (all far above); nothing needs it,
        // so it goes last of the `lor` family. See
        // `docs/plan/status/266-nat-lor-assoc.md`.
        declare_lor_assoc_all(&mut d, &p)?;
        // Needs `Nat.add`/`Nat.mul` (`declare_arithmetic`) and `Nat.mul_one`
        // (`declare_multiplicative_theorems`), both far above; nothing needs
        // `Nat.ascFactorial`, so it goes last too.
        declare_asc_factorial_all(&mut d, &p)?;
        // Needs `Nat.descFactorial_eq_factorial_mul_choose`
        // (`declare_desc_factorial_all`, far above) and
        // `Nat.ascFactorial_succ_eq_factorial_mul_choose`
        // (`declare_asc_factorial_all`, just above); nothing needs this
        // closed `ml430` mirror.
        declare_add_desc_factorial_eq_asc_factorial(&mut d, &p)?;
        // Needs `Nat.add_descFactorial_eq_ascFactorial` (just above),
        // `choose_factorial_add::desc_factorial_add_eq_factorial_at`
        // (`declare_add_choose_mul_factorial_mul_factorial`'s home module,
        // far above) and `Nat.div`/`div_mul_cancel_of_dvd`/`dvd_mul`
        // (`declare_euclidean_division`, far above); nothing needs this
        // closed `ml430` mirror.
        declare_asc_factorial_eq_div(&mut d, &p)?;
        // Needs `Nat.add`/`Nat.pred`/`Nat.choose`, all far above (`choose`'s
        // own `choose_zero_right`/`choose_self`/`choose_one_right`, all
        // declared by `declare_choose_all`); nothing needs `Nat.multichoose`,
        // so it goes last too.
        declare_multichoose_all(&mut d, &p)?;
        // `Nat.minFacAuxMinimal`/`min_fac_minimal_of_two_le`/
        // `coprime_of_lt_min_fac` need `Nat.add_sub_cancel_of_le`
        // (`declare_diagonal`, far above), `Nat.gcd_dvd_left`/`_right`,
        // `Nat.le_of_dvd`, `Nat.zero_lt_of_ne_zero` and the other
        // order/divisibility lemmas used throughout this file, all declared
        // long before this point; nothing needs these, so they go last too.
        declare_min_fac_minimal_all(&mut d, &p)?;
        // `Nat.Pair` and `Nat.binaryRec`: needs `Nat.div`/`Nat.mod`
        // (`declare_executable_division`), `Nat.beq`
        // (`declare_boolean_equality`), `Nat.bit` (`declare_bit_all`, above)
        // for its evaluation checks, and the order/division lemmas
        // `half_le_of_succ_le_succ` composes (`add_lt_add_left`, `succ_mul`,
        // `one_mul`, `div_mod_lt_mul_iff`, `div_mod_exec`, `lt_of_lt_of_le`,
        // `le_of_succ_le_succ`, `succ_pred_of_pos`, `le_antisymm`,
        // `le_trans`). Nothing needs it, so it goes last -- and dispatching a
        // declaration before a dependency exists gives `UnknownConst`, which
        // `cargo check` cannot see.
        declare_binary_rec_all(&mut d, &p)?;
        // `Nat.xor_comm`: needs `Nat.bitwise_comm` (`declare_bitwise_comm`,
        // far above) and `Nat.xor`/`xor_fn` (`declare_xor_all`, far above,
        // and `bitwise::xor_fn`). Nothing needs it, so it goes last.
        declare_xor_order_all(&mut d, &p)?;
        // `Nat.testBit_xor`: needs `Nat.testBit`/`test_bit_succ`/
        // `test_bit_zero` (`declare_binary_all`, far above),
        // `Nat.xor`/`xor_fn`/`bitwiseAux` (`declare_xor_all`/
        // `declare_bitwise_all`, far above), `Nat.bitwise_aux_agree_of_fuel`/
        // `Nat.bitwise_zero_right` (`declare_bitwise_all`, far above),
        // `half_le_predecessor_of_succ` (`rec_agreement.rs`, a Rust fn, no
        // ordering constraint of its own beyond the kernel names IT calls,
        // all declared far above), and `Nat.div_mod_exec`/`div_mod_unique`/
        // `mod_lt`/`cases_mod_two`'s own dependencies (all far above).
        // Nothing needs it, so it goes last.
        declare_testbit_bitwise_all(&mut d, &p)?;
        // `Nat.self_lt_two_pow`/`Nat.self_lt_two_pow_add`/`Nat.lt_of_testBit`:
        // needs `Nat.testBit`/`sum_test_bit_lt`/`mod_eq_self_of_lt`
        // (`declare_binary_all`/`declare_size_all`, far above),
        // `sum_range_split` (`rectangle.rs`, far above), `sum_range_succ`/
        // `sum_range_congr` (`declare_finite_sum_theorems`, far above), and
        // general order/arithmetic (`add_assoc`/`add_comm`/`add_right_comm`/
        // `le_add_right`/`le_trans`/`mod_lt`/`pow_pos`, all far above).
        // Nothing needs it, so it goes last.
        declare_bit_order_all(&mut d, &p)?;
        // `Nat.eq_of_testBit_eq`: needs `Nat.testBit`/`test_bit_of_zero`
        // (`declare_binary_all`, far above), `Nat.zero_of_testBit_eq_zero`
        // (`declare_size_all`, far above), `Nat.zero_le`/`Nat.le_antisymm`/
        // `Nat.le_refl`/`Nat.le_of_succ_le_succ` (far above),
        // `half_le_predecessor_of_succ` (`rec_agreement.rs`, a Rust fn,
        // needs `Nat.div_mod_exec`/`div_mod_lt_mul_iff`/etc, all far above),
        // and `Nat.div_mod_exec` directly for the reconstruction identity.
        // `Nat.xor_assoc`/`xor_xor_cancel_left`/`_right` additionally need
        // `Nat.testBit_xor` (`declare_testbit_bitwise_all`, far above),
        // `Nat.testBit_le_one` (`declare_binary_all`, far above),
        // `Nat.le_succ_succ`/`Nat.lt_two_cases` (far above/`rec_agreement.rs`),
        // and `Nat.xor_comm` (`declare_xor_order_all`, far above; `_right`
        // only). `Nat.xor_ne_zero_iff` is NOT declared this lane — see
        // `xor_algebra.rs`'s module doc. Nothing needs any of this, so it
        // goes last.
        declare_xor_algebra_all(&mut d, &p)?;
        // `Nat.xor_trichotomy`/`Nat.lt_xor_cases`: the composition step for
        // `F:ml430-nat-lt-xor-cases-c43a1e85`, needing `Nat.testBit_xor`
        // (`declare_testbit_bitwise_all`, far above),
        // `Nat.exists_most_significant_bit`/`Nat.lt_of_testBit`
        // (`declare_bit_order_all`, far above), and `Nat.xor_assoc`/
        // `Nat.xor_xor_cancel_left`/`Nat.xor_ne_zero_iff`/`Nat.xor_comm`
        // (`declare_xor_algebra_all` just above / `declare_xor_order_all`,
        // far above). Nothing needs it, so it goes last.
        declare_xor_trichotomy_all(&mut d, &p)?;
        // `Nat` ordering under multiplication/division: needs
        // `Nat.mul_le_mul_left`/`Nat.mul_comm`/`Nat.add_le_add_left`/
        // `Nat.le_trans`/`Nat.lt_or_ge`/`Nat.lt_irrefl` (`declare_order`/
        // `declare_order_more`/`declare_multiplicative_theorems`, all far
        // above) plus `Nat.zero_mul`/`Nat.not_lt_zero`/`Nat.div_mod_exec`/
        // `Nat.div_mod_lt_mul_iff` (`declare_multiplicative_theorems`/
        // `declare_no_confusion`/`declare_divisibility`/
        // `declare_euclidean_division`, all far above). Nothing needs it,
        // so it goes last.
        declare_lt_of_mul_lt_mul(&mut d, &p)?;
        declare_mul_lt_mul_iff(&mut d, &p)?;
        declare_div_lt_of_lt_mul(&mut d, &p)?;
        // Needs `Nat.bit` (`declare_bit_all`, far above) plus order/algebra
        // machinery from all over this file, the last piece being
        // `Nat.mul_lt_mul_left` (`declare_mul_lt_mul_iff`, just above) --
        // that ordering dependency is why these five closed `ml430` mirrors
        // sit here rather than right after `Nat.bit` itself (a `bit_ne_zero`
        // draft placed there hit `UnknownConst` on `mul_lt_mul_left`, which
        // is not declared until here). Nothing needs these theorems, so
        // moving them later than `Nat.bit` costs nothing.
        declare_bit_extra_all(&mut d, &p)?;
        declare_gcd_dvd_mirrors(&mut d, &p)?;
        // Needs `Nat.log`/`Nat.clog` (`declare_log_all`/`declare_clog_all`,
        // far above) and `Nat.div_mod_exec`/`Nat.div_mod_lt_mul_iff`/
        // `Nat.div_lt_of_lt_mul` (`declare_executable_division_spec`/
        // `declare_multiplicative_theorems`/just above -- `div_lt_of_lt_mul`
        // specifically is declared immediately above and nothing else in
        // this builder needs it, which is why it was last until now).
        // Nothing needs these order mirrors, so they go last.
        declare_log_clog_order_all(&mut d, &p)?;
        // Needs `Nat.gcd_zero_left`/`Nat.gcd_succ` (`declare_executable_gcd`,
        // far above), `Nat.div_mod_exec`/`Nat.div_mod_unique`/`Nat.mod_lt`/
        // `Nat.succ_pred_of_pos` (`declare_divisibility`/
        // `declare_euclidean_division`, far above) and
        // `Nat.mul_lt_mul_right`/`Nat.one_le_mul`/`Nat.mul_assoc`/
        // `Nat.right_distrib`/`Nat.mul_comm`/`Nat.zero_mul`/`Nat.mul_zero`
        // (`declare_multiplicative_theorems`, far above). Nothing later
        // needs it, so it goes last.
        declare_gcd_mul_right(&mut d, &p)?;
        // Needs `Nat.gcd_mul_right` (just above), `Nat.dvd_gcd_iff`/
        // `Nat.dvd_mul`/`Nat.mul_comm` (`declare_divisibility`/
        // `declare_gcd_semantics`/`declare_multiplicative_theorems`, far
        // above). Nothing needs it, so it goes last.
        declare_gcd_mul_right_mirrors(&mut d, &p)?;
        // Needs only `Nat.dvd_add_iff_right`/`Nat.add_comm`
        // (`declare_divisibility`/`declare_arithmetic`, far above). Nothing
        // needs it, so it goes last.
        declare_dvd_add_iff_left(&mut d, &p)?;
        // Needs `Nat.gcd_mul_right` (just above, `declare_gcd_mul_right`),
        // `Nat.gcd_dvd_left`/`Nat.gcd_dvd_right`/`Nat.dvd_gcd`/`Nat.dvd_mul`/
        // `Nat.one_le_of_dvd_pos`/`Nat.mul_left_cancel_of_pos`/
        // `Nat.mul_assoc`/`Nat.mul_eq_zero`/`Nat.dvd_refl`/`Nat.zero_mul`/
        // `Nat.mul_zero` (`declare_gcd_semantics`/`declare_divisibility`/
        // `declare_multiplicative_theorems`/`declare_arithmetic`, far
        // above) and `mul_left_comm` (`binomial.rs`). Nothing needs it, so
        // it goes last.
        declare_dvd_mul_split(&mut d, &p)?;
        // Needs `Nat.gcd_dvd_left`/`_right`/`Nat.gcd_comm` (`gcd.rs`),
        // `Nat.div_mul_cancel_of_dvd`/`Nat.one_le_of_dvd_pos`
        // (`divisibility.rs`), `Nat.gcd_cofactors_coprime` (`bezout.rs`,
        // far above), `Nat.mul_assoc`/`Nat.mul_comm`/`Nat.left_distrib`/
        // `Nat.mul_left_cancel_of_pos` (`declare_multiplicative_theorems`,
        // far above), and `Nat.mod_eq_cancel`/`Nat.mod_eq_symm`/
        // `Nat.mod_eq_trans`/`Nat.mod_eq_mul_right` (`euler.rs`/`modular.rs`,
        // far above). Nothing needs it, so it goes last.
        declare_modeq_cancel_div_gcd(&mut d, &p)?;
        // `Nat.dist`: needs only `Nat.sub`/`Nat.add` (`declare_subtraction`/
        // `declare_arithmetic`, far above) and the order/additive lemmas
        // `sub_eq_zero_of_le`/`zero_le`/`sub_zero`/`add_zero`/`zero_add`/
        // `add_comm`/`succ_sub_succ` (`declare_order`/`declare_defining_
        // equations`/`declare_additive_theorems`/`declare_subtraction_
        // theorems`, all far above). Nothing needs it, so it goes last —
        // `docs/plan/status/348-nat-dist-nth.md`.
        declare_dist_all(&mut d, &p)?;
        // `Nat.dist_eq_zero`/`Nat.add_sub_add_left`/`Nat.dist_add_add_left`/
        // `Nat.dist_add_add_right`/`Nat.dist_mul_left`/`Nat.dist_mul_right`:
        // needs `Nat.dist`/`Nat.dist_self` (just above),
        // `Nat.succ_add`/`Nat.succ_sub_succ`/`Nat.zero_add`/`Nat.add_comm`
        // (`declare_additive_theorems`/`declare_subtraction_theorems`, far
        // above), and `Nat.mul_sub_left_distrib_total`/`Nat.left_distrib`/
        // `Nat.mul_comm` (`declare_order`/`declare_multiplicative_
        // theorems`, far above). Draw 9 (`natural-distance`, ADR-0830).
        declare_dist_more_all(&mut d, &p)?;
        // `Nat.dist_pos_of_ne`/`Nat.dist_eq_intro`/
        // `Nat.dist_triangle_inequality`: needs `Nat.dist`/`Nat.dist_comm`/
        // `Nat.dist_eq_sub_of_le`/`Nat.dist_eq_sub_of_le_right`
        // (`declare_dist_all`, just above), `Nat.dist_add_add_left`
        // (`declare_dist_more_all`, just above), `Nat.le_total`/
        // `Nat.lt_or_eq_of_le`/`Nat.not_succ_le_self`/`Nat.add_left_cancel`/
        // `Nat.add_sub_cancel_left`/`Nat.sub_add_cancel` (order/additive
        // theorems, far above), and `lt_or_gt_of_ne_local`
        // (`fermat_number_mirrors.rs`, far above). Draw 9
        // (`natural-distance`, `docs/plan/status/draw9-second-theorems.md`).
        declare_dist_more2_all(&mut d, &p)?;
        // `Nat.nthAux`/`Nat.nth`: needs only `Nat.beq`/`Nat.pred`/`Nat.succ`
        // (`declare_boolean_equality`/`declare_defining_equations`, far
        // above) and `bool_select_nat` (an inlined `Bool.rec` application,
        // `ops.rs`, no ordering constraint of its own). Nothing needs it, so
        // it goes last — `docs/plan/status/348-nat-dist-nth.md`.
        declare_nth_all(&mut d, &p)?;
        // `Nat.totient_mul_of_coprime` and its two CRT self-map facts
        // (`totient_mul.rs`). Needs, all far above: `Nat.countRange_permute`/
        // `countRange_product`/`div_mod_block` (`declare_count_range_permute`
        // and neighbours), `Nat.countRange_congr`/`Nat.totient`
        // (`declare_totient_all`), `Nat.crt_unique` (`declare_crt`),
        // `Nat.mod_eq_iff_div_mod_remainder_eq` (`modular.rs`),
        // `Nat.gcd_mod_left_eq_gcd`/`Nat.coprime_mul_iff`
        // (`totient_mul_coprime.rs`), `Nat.mul_succ_add_lt_of_le_of_lt`
        // (`order.rs`), `Nat.div_mod_exec`, `Nat.mod_eq_self_of_lt`,
        // `Nat.mod_lt`, `Nat.le_of_lt_succ`, `Nat.mul_comm`/`Nat.zero_mul`,
        // and the `beq` bridges `eq_of_beq_eq_true`/`beq_eq_true_of_eq`/
        // `beq_eq_false_of_ne`. Nothing needs it, so it goes last.
        declare_totient_mul_all(&mut d, &p)?;
        // `Nat.totient_prime_pow` and the counting law under it
        // (`totient_prime_pow.rs`). Needs `Nat.totient_mul_of_dvd`'s own
        // ingredients, all far above: `Nat.countRange_congr`/
        // `countRange_product`/`countRange_succ_of_true`/`countRange_zero`
        // (`declare_totient_all` and `count_range_permute.rs`),
        // `Nat.div_mod_block`, `Nat.gcd_mod_left_eq_gcd`/`Nat.coprime_mul_iff`
        // (`totient_mul_coprime.rs`), `Nat.coprime_of_dvd_right`,
        // `Nat.totient_prime` (`declare_totient_all`), `Nat.dvd_mul_left`,
        // `Nat.pow_succ`/`mul_assoc`/`mul_comm`/`add_comm`/`one_mul`/
        // `mul_one`/`sub_succ`/`sub_zero`/`add_sub_cancel_left`, and the
        // `beq` bridges. It does NOT need `declare_totient_mul_all`, but is
        // placed after it because both are last and this one is the newer.
        // Nothing needs it, so it goes last.
        declare_totient_prime_pow_all(&mut d, &p)?;
        // `Nat.totient_dvd_of_dvd`: needs `Nat.totient_dvd_totient_mul_prime`
        // (just above), `Nat.exists_prime_dvd`, `Nat.two_le_succ_or_eq_one`,
        // `Nat.dvd_zero`/`dvd_refl`/`dvd_trans`, `Nat.mul_assoc`/`mul_comm`/
        // `mul_one`, and the `WellFounded.fix` machinery `Nat.gcd` and
        // `Nat.exists_prime_factorization` already use. ADR-0668.
        declare_totient_dvd_chain_all(&mut d, &p)?;
        // `Nat.totient_gcd_mul_totient_mul` (the last of the three `ml430`
        // totient mirrors, ADR-0668): needs `Nat.totient_mul_of_coprime`/
        // `Nat.totient_mul_of_dvd` (`declare_totient_all` /
        // `declare_totient_prime_pow_all`, both above),
        // `Nat.coprime_or_dvd_of_prime`/`Nat.exists_prime_dvd`/
        // `Nat.gcd_mul_right`/`Nat.dvd_gcd`/`Nat.coprime_of_dvd_right`/
        // `Nat.coprime_mul_of_coprime`/the two `dvd_mul_{left,right}_of_dvd`
        // lemmas, and the `WellFounded.fix` machinery this file's siblings
        // already use. Placed after `totient_dvd_chain` since it is the
        // last of the three mirrors to close.
        declare_totient_gcd_mul_all(&mut d, &p)?;
        // Needs only `Nat.log` (`declare_log_all`, far above). Nothing needs
        // it, so it goes last.
        declare_log2_all(&mut d, &p)?;
        // `Nat.fermatNumber`: needs only `Nat.pow`/`Nat.add`
        // (`declare_arithmetic`, far above). Nothing needs it, so it goes
        // last — `docs/research/09-decisions/adr-0653-…`.
        declare_fermat_number_all(&mut d, &p)?;
        // `Nat.mod_eq_add_le_of_lt`: needs only `Nat.add_le_add_left`/
        // `Nat.le_of_add_le_add_left`/`Nat.le_of_add_le_add_right`
        // (`declare_order`, far above), `Nat.mul_le_mul_left`/
        // `Nat.lt_of_mul_lt_mul_left` (`declare_lt_of_mul_lt_mul`, above)
        // and `Nat.add_comm`/`Nat.add_assoc` (`declare_algebra`-family, far
        // above) plus the `modEq` witness helpers (`declare_modular_congruence`,
        // far above). Nothing needs it, so it goes last.
        declare_mod_eq_add_le_of_lt(&mut d, &p)?;
        // `ml430` prime-divisibility mirrors (`prime_dvd_mirrors.rs`): needs
        // `prime_condition`/`euclid_lemma`/`prime_even_iff`
        // (`primes.rs`, far above), `dvd_gcd`/`gcd_dvd_left`/`gcd_dvd_right`/
        // `dvd_mul_right_of_dvd`/`dvd_mul_left_of_dvd`, `coprime_symmetric`
        // (`primes.rs`), `coprime_mul_of_coprime`
        // (`totient_multiplicative.rs`, far above),
        // `even_or_odd_exists`/`even_iff_mod_two_eq_zero`/
        // `odd_iff_mod_two_eq_one` (`declare_parity_all`, far above), and
        // `ne_of_lt`/`ne_symm` (`finite.rs`). Nothing needs it, so it goes
        // last.
        declare_prime_dvd_mirrors_all(&mut d, &p)?;
        // `prime_char.rs`'s hardest fact needs `prime_eq_one_or_self_of_dvd`
        // (`prime_dvd_mirrors.rs`, just above) plus `euclid_lemma`
        // (`bezout.rs`, far above) and `pow_succ`/`pow_zero`/`mul_assoc`/
        // `mul_left_cancel_of_pos` (all far above), so it goes here rather
        // than beside `declare_prime_not_prime_pow_all`.
        declare_prime_mul_eq_prime_sq_iff(&mut d, &p)?;
        // `pow_add_prime.rs`: needs only `Nat.pow_add`/`mul`/`add`/`dvd_add`/
        // `dvd_mul_left` (all far above). Nothing needs it, so it goes last.
        declare_pow_add_prime_all(&mut d, &p)?;
        // `fermat-mirrors` lane: needs only `Nat.fermatNumber`
        // (`declare_fermat_number_all`, far above), `Nat.pow_pos`/
        // `Nat.pow_lt_pow_of_lt`/`Nat.succ_pred_of_pos` (`declare_order`/
        // `perfect.rs`, far above), `Nat.mod_eq_pow`/`Nat.mod_eq_gcd_eq`
        // (`declare_modular_congruence`, far above), `Nat.coprime_two_left`/
        // `Nat.coprime_symmetric` (`primes.rs`, far above) and
        // `Nat.even_iff_odd_succ` (`declare_parity_all`, far above). Nothing
        // needs it, so it goes last.
        declare_fermat_number_mirrors_all(&mut d, &p)?;
        // `fermat-easy` lane: the three closed reductions need only
        // `Nat.fermatNumber` (`declare_fermat_number_all`, far above);
        // `Nat.odd_fermatNumber` reuses `odd_fermat_number_local`
        // (`fermat_number_mirrors.rs`, just above, needs the same
        // dependencies as `declare_fermat_number_mirrors_all`);
        // `Nat.fermatNumber_strictMono` needs `Nat.pow_lt_pow_of_lt`
        // (`declare_order`, far above) and `Nat.add_lt_add_left`/
        // `Nat.add_comm` (far above). Nothing needs it, so it goes last.
        declare_fermat_number_easy_all(&mut d, &p)?;
        // `least_number.rs`: needs only the order fragment (`not_lt_zero`,
        // `le_of_lt_succ`, `lt_or_eq_of_le`, `lt_succ_self`, `le_succ`,
        // `lt_of_lt_of_le`, `succ_ne_zero`, all far above) and the logic
        // prelude. Nothing needs it, so it goes last.
        declare_least_number_all(&mut d, &p)?;
        // `Nat.nthRootAux`/`Nat.nthRoot` (`nth_root.rs`): needs only
        // `Nat.pow`/`Nat.ble`/`Nat.beq`/`Nat.succ`/`bool_select_nat`, all far
        // above. Opens `Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas`
        // for the autogenesis screen (ADR-0762/ADR-0830). Nothing needs it,
        // so it goes last.
        declare_nth_root_all(&mut d, &p)?;
        // `Nat.squarefreeAux`/`Squarefree` (`squarefree.rs`): needs only
        // `Nat.mul`/`Nat.mod`/`Nat.beq`/`Nat.succ`/`bool_select`, all far
        // above. Opens `Mathlib.Data.Nat.Squarefree` for the autogenesis
        // screen, paired with `Nat.nthRoot` above (ADR-0762/ADR-0830).
        // Nothing needs it, so it goes last.
        declare_squarefree_all(&mut d, &p)?;
        // `Nat.and_or_distrib_left`/`_right` (`and_or_distrib.rs`): needs
        // `Nat.testBit_land`/`Nat.testBit_lor` (`declare_testbit_bitwise_all`,
        // far above), `Nat.eq_of_testBit_eq` (`declare_xor_algebra_all`, far
        // above), `Nat.testBit_le_one` (`declare_binary_all`, far above),
        // and `Nat.le_succ_succ`/`Nat.lt_two_cases`/`Nat.le_of_lt_succ`/
        // `Nat.zero_le`/`Nat.le_antisymm`/`Nat.lt_or_eq_of_le` (far above,
        // via `ops::cases_lt_bound`). Nothing needs it, so it goes last.
        declare_and_or_distrib_all(&mut d, &p)?;
        // `draw11-theorems-b` lane mirrors (`draw11_mirrors.rs`): needs
        // `gauss_lemma`/`dvd_mul`/`dvd_trans`/`mul_comm` (`declare_lcm`/
        // `declare_gauss_lemma`/`declare_divisibility`, far above),
        // `gcd_zero_left`/`gcd_comm` (`declare_gcd_semantics`/
        // `declare_gcd_comm`, far above), `mul_eq_zero`
        // (`declare_mul_no_zero_divisors`, far above) and
        // `succ_mul_choose_eq` (`declare_succ_mul_choose_eq`, above).
        // Nothing later needs it, so it goes last.
        declare_draw11_mirrors_all(&mut d, &p)?;
        // `gauss_lemma.rs`: needs only `Nat.countRange` (`declare_totient_all`,
        // far above), `Nat.mod_eq_self_of_lt` (`declare_size_all`, far above),
        // and `Nat.mod`/`Nat.mul`/`Nat.div`/`Nat.ble` (all far above). Nothing
        // needs it, so it goes last.
        declare_gauss_lemma_all(&mut d, &p)?;
        // `draw11-theorems-e` lane: `Nat.Coprime.mul_add_mul_ne_mul`, an
        // `ml430` mirror. Needs `Nat.gauss_lemma`, `Nat.coprime_symmetric`,
        // `Nat.dvd_add_iff_left`/`_right`, `Nat.le_of_dvd`,
        // `Nat.zero_lt_of_ne_zero`, `Nat.one_le_mul`, `Nat.lt_irrefl` (all
        // above). Nothing later needs it, so it goes last.
        declare_coprime_mul_add_mul_ne_mul(&mut d, &p)?;
        Ok(p)
    })();
    match built {
        Ok(prelude) => {
            kernel.register_prelude(
                PreludeKey::Nat,
                PreludeValue::Nat(Box::new(prelude)),
                checkpoint,
            );
            Ok(prelude)
        }
        Err(error) => {
            kernel.rollback_prelude(checkpoint);
            Err(error)
        }
    }
}

#[cfg(test)]
mod nat_prelude_tests;

#[cfg(test)]
mod bit_extra_tests;

#[cfg(test)]
mod size_extra_tests;

#[cfg(test)]
mod choose_factorial_add_tests;

#[cfg(test)]
mod add_choose_div_tests;

#[cfg(test)]
mod add_desc_factorial_asc_factorial_tests;

#[cfg(test)]
mod asc_factorial_div_tests;

#[cfg(test)]
mod add_factorial_le_tests;
