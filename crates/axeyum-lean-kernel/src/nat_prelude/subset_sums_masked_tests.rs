//! Concrete-instance tests for `nat_prelude::subset_sums_masked`.
//!
//! `Nat.Subsets.sumSubsetsOn` and `Nat.Subsets.sumSelOn` are `Definition`s, and
//! **the trusted gate cannot tell a `Definition` is wrong** — a fold that
//! ignores its mask, or reads it at the wrong index, has exactly the right
//! type. The theorems in `subset_sums_masked.rs` are also weaker than they look
//! on this point: the split law, the grading law and even the vanishing law are
//! ALL satisfied by a fold that ignores the mask entirely, because none of them
//! compares the masked fold to anything that counts. Only
//! `Nat.Subsets.sumSubsetsOn_card` and the evaluations below can see it.
//!
//! Each check is paired with the specific wrong value it rules out:
//!
//! - `sumSubsetsOn (· = 1) 3 (fun _ => 1) = 2` rules out `8` (`2^3`, what a fold
//!   ignoring the mask gives) and `1` (a fold that never takes the high half).
//! - The same mask with the summand `fun s => if s 1 then 3 else 5` gives `8`,
//!   not `32`: the enumeration visits `∅` and `{1}` and nothing else.
//! - Reading the same summand at index `0` instead gives `10`, not `8` — a fold
//!   that read the mask at the wrong index would visit `{0}` and disagree.
//! - The graded halves at a NON-constant summand are DIFFERENT (`5` against
//!   `3`), so a `sumSelOn` that ignored its parity argument fails here even
//!   though it would satisfy the vanishing law.
//!
//! The last test is a **necessity** control rather than a wrong-value one.
//! `Nat.Subsets.sumSelOn_const_of_mem` needs a masked index below the width,
//! and at the EMPTY mask the conclusion is false: the fold visits only `∅`,
//! which is even, so the even half is `c` and the odd half is `0`. Dropping the
//! hypothesis would make the theorem false, not merely weaker — which is the
//! same shape as `Σ_{d ∣ n} μ(d) = 0` failing at `n = 1`, and this is the check
//! that stands in for it until the divisor transfer exists.
//!
//! Every magnitude here is tiny on purpose: this prelude's numerals are unary
//! `Nat.succ` towers, so cost is superlinear in the largest magnitude FORMED.
//! The largest value any check below builds is `32`.

use crate::expr::{BinderInfo, ExprId};
use crate::name::NameId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// `Nat -> Bool`.
    fn set_ty(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let b = self.bool_ty();
        self.arrow(nat, b)
    }

    /// `fun q => Nat.beq q k` — the mask (or subset) holding exactly `k`.
    fn only(&mut self, k: u32) -> ExprId {
        let nat = self.nat_ty();
        let q_fv = self.fresh_fvar();
        let q = self.k.fvar(q_fv);
        let lit = self.num(k);
        let body = self.beq(q, lit);
        self.lam_fv(q_fv, nat, body)
    }

    /// `fun _ => false` — the empty mask.
    fn no_mask(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let fal = self.bool_false();
        self.k.lam(anon, nat, fal, BinderInfo::Default)
    }

    /// `fun _ => true` — the full mask.
    fn all_mask(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let anon = self.anon_name();
        let tv = self.bool_true();
        self.k.lam(anon, nat, tv, BinderInfo::Default)
    }

    /// `fun _ => c` — the constant summand.
    fn konst(&mut self, c: u32) -> ExprId {
        let sty = self.set_ty();
        let anon = self.anon_name();
        let lit = self.num(c);
        self.k.lam(anon, sty, lit, BinderInfo::Default)
    }

    /// `fun s => if s k then hit else miss` — a summand that reads exactly one
    /// index of the subset it is handed.
    fn reads(&mut self, k: u32, hit: u32, miss: u32) -> ExprId {
        let sty = self.set_ty();
        let s_fv = self.fresh_fvar();
        let s = self.k.fvar(s_fv);
        let lit = self.num(k);
        let at_k = self.apply(s, &[lit]);
        let yes = self.num(hit);
        let no = self.num(miss);
        let body = self.bool_select_nat(at_k, yes, no);
        self.lam_fv(s_fv, sty, body)
    }

    /// `Nat.Subsets.sumSubsetsOn mask n F`.
    fn masked_sum(&mut self, mask: ExprId, n: u32, f: ExprId) -> ExprId {
        let lit = self.num(n);
        let name = self.p.subsets_sum_subsets_on;
        self.const_app(name, &[mask, lit, f])
    }

    /// `Nat.Subsets.sumSelOn mask n F b`.
    fn masked_sel(&mut self, mask: ExprId, n: u32, f: ExprId, even: bool) -> ExprId {
        let lit = self.num(n);
        let parity = if even {
            self.bool_true()
        } else {
            self.bool_false()
        };
        let name = self.p.subsets_sum_sel_on;
        self.const_app(name, &[mask, lit, f, parity])
    }

    /// `Nat.Subsets.sumSubsets n F` — the unrestricted fold.
    fn plain_sum(&mut self, n: u32, f: ExprId) -> ExprId {
        let lit = self.num(n);
        let name = self.p.subsets_sum_subsets;
        self.const_app(name, &[lit, f])
    }
}

/// The masked fold visits `2 ^ (masked indices below n)` subsets, not `2 ^ n`.
///
/// The `8` control is the one that matters: it is what a fold whose step took
/// the high half unconditionally gives, and NO theorem in
/// `subset_sums_masked.rs` other than `sumSubsetsOn_card` would notice.
#[test]
fn the_masked_fold_visits_only_the_masked_indices() {
    let mut f = Fixture::new();
    let mask = f.only(1);
    let ones = f.konst(1);
    let counted = f.masked_sum(mask, 3, ones);

    let two = f.num(2);
    assert!(
        f.k.def_eq(counted, two),
        "sumSubsetsOn (· = 1) 3 (fun _ => 1) must be 2 -- the mask holds one \
         index below 3, so the fold visits ∅ and {{1}} -- got {}",
        f.k.render_lean(counted)
    );

    let eight = f.num(8);
    assert!(
        !f.k.def_eq(counted, eight),
        "negative control: it must NOT be 8 -- that is 2^3, what a fold \
         IGNORING the mask gives, and the split, grading and vanishing laws \
         all hold for that fold"
    );
    let one = f.num(1);
    assert!(
        !f.k.def_eq(counted, one),
        "negative control: it must NOT be 1 -- that is what a fold that never \
         takes the high half gives"
    );

    // A wider mask gives a strictly bigger count, so a fold reading a constant
    // mask cannot pass both.
    let wide = f.all_mask();
    let all_counted = f.masked_sum(wide, 3, ones);
    assert!(
        f.k.def_eq(all_counted, eight),
        "sumSubsetsOn (fun _ => true) 3 (fun _ => 1) must be 8, got {}",
        f.k.render_lean(all_counted)
    );
}

/// `Nat.Subsets.sumSubsetsOn_card` at a concrete mask, read as an evaluation
/// rather than as a type: the two sides really do reduce to the same numeral,
/// and to a different one than the unmasked count.
#[test]
fn the_card_law_agrees_with_the_fold_at_a_concrete_mask() {
    let mut f = Fixture::new();
    let mask = f.only(1);
    let ones = f.konst(1);
    let counted = f.masked_sum(mask, 3, ones);

    let three = f.num(3);
    let range = f.p.count_range;
    let masked_count = f.const_app(range, &[mask, three]);
    let two = f.num(2);
    let powered = f.pow(two, masked_count);
    assert!(
        f.k.def_eq(counted, powered),
        "sumSubsetsOn P 3 (fun _ => 1) must equal pow 2 (countRange P 3), got \
         {} against {}",
        f.k.render_lean(counted),
        f.k.render_lean(powered)
    );

    let two_again = f.num(2);
    let three_again = f.num(3);
    let unmasked = f.pow(two_again, three_again);
    assert!(
        !f.k.def_eq(counted, unmasked),
        "negative control: the masked count must NOT be pow 2 3 -- the whole \
         point of the mask is that the exponent is the MASKED count"
    );
}

/// The enumeration is over the subsets of the mask, which a summand that reads
/// one index can see directly.
#[test]
fn the_enumerated_subsets_are_exactly_the_subsets_of_the_mask() {
    let mut f = Fixture::new();
    let mask = f.only(1);

    // Visits ∅ (misses, 5) and {1} (hits, 3).
    let reads_one = f.reads(1, 3, 5);
    let total = f.masked_sum(mask, 3, reads_one);
    let eight = f.num(8);
    assert!(
        f.k.def_eq(total, eight),
        "the fold must visit ∅ and {{1}} only, giving 5 + 3 = 8, got {}",
        f.k.render_lean(total)
    );

    let thirty_two = f.num(32);
    let unrestricted = f.plain_sum(3, reads_one);
    assert!(
        f.k.def_eq(unrestricted, thirty_two),
        "the UNRESTRICTED fold over [0,3) must give 4*3 + 4*5 = 32, got {}",
        f.k.render_lean(unrestricted)
    );
    assert!(
        !f.k.def_eq(total, thirty_two),
        "negative control: the masked and unmasked folds must DISAGREE on this \
         summand"
    );

    // Neither visited subset contains 0, so a summand reading index 0 sees only
    // the miss branch. A fold reading its mask at the wrong index would visit
    // {0} and disagree.
    let reads_zero = f.reads(0, 3, 5);
    let at_zero = f.masked_sum(mask, 3, reads_zero);
    let ten = f.num(10);
    assert!(
        f.k.def_eq(at_zero, ten),
        "no visited subset contains 0, so the sum must be 5 + 5 = 10, got {}",
        f.k.render_lean(at_zero)
    );
    assert!(
        !f.k.def_eq(at_zero, eight),
        "negative control: it must NOT be 8 -- that is what a fold that visited \
         {{0}} would give"
    );
}

/// The grading really is by parity: at a summand that is not constant the two
/// halves differ, and together they are the ungraded fold.
#[test]
fn the_graded_masked_halves_differ_and_add_to_the_whole() {
    let mut f = Fixture::new();
    let mask = f.only(1);
    let reads_one = f.reads(1, 3, 5);

    let even = f.masked_sel(mask, 3, reads_one, true);
    let odd = f.masked_sel(mask, 3, reads_one, false);

    let five = f.num(5);
    let three = f.num(3);
    assert!(
        f.k.def_eq(even, five),
        "∅ is the only even visited subset, so the even half is 5, got {}",
        f.k.render_lean(even)
    );
    assert!(
        f.k.def_eq(odd, three),
        "{{1}} is the only odd visited subset, so the odd half is 3, got {}",
        f.k.render_lean(odd)
    );
    assert!(
        !f.k.def_eq(even, odd),
        "negative control: the two halves must DISAGREE at a non-constant \
         summand, or a `sumSelOn` ignoring its parity argument would pass \
         every law here"
    );

    let joined = f.add(even, odd);
    let whole = f.masked_sum(mask, 3, reads_one);
    assert!(
        f.k.def_eq(joined, whole),
        "sumSelOn_add at a concrete instance: {} + {} must be the ungraded \
         fold",
        f.k.render_lean(even),
        f.k.render_lean(odd)
    );
}

/// NECESSITY CONTROL for `Nat.Subsets.sumSelOn_const_of_mem`.
///
/// With a masked index below the width the two halves of a constant summand
/// agree; with the EMPTY mask they do not, because the fold visits only `∅`,
/// which is even. So the `Lt i n → P i = true` hypothesis is not defensive —
/// the statement is FALSE without it. This is the same shape as
/// `Σ_{d ∣ n} μ(d) = 0` failing at `n = 1`, where the only divisor is `1` and
/// the even side carries it alone.
#[test]
fn the_constant_vanishing_law_is_false_without_a_masked_index() {
    let mut f = Fixture::new();
    let four = f.konst(4);

    let mask = f.only(1);
    let even = f.masked_sel(mask, 3, four, true);
    let odd = f.masked_sel(mask, 3, four, false);
    assert!(
        f.k.def_eq(even, odd),
        "with 1 masked and below the width, the two halves of a constant \
         summand must agree, got {} against {}",
        f.k.render_lean(even),
        f.k.render_lean(odd)
    );

    let empty = f.no_mask();
    let even_empty = f.masked_sel(empty, 3, four, true);
    let odd_empty = f.masked_sel(empty, 3, four, false);
    let four_lit = f.num(4);
    let zero = f.zero();
    assert!(
        f.k.def_eq(even_empty, four_lit),
        "at the empty mask the fold visits only ∅, which is EVEN, so the even \
         half is 4, got {}",
        f.k.render_lean(even_empty)
    );
    assert!(
        f.k.def_eq(odd_empty, zero),
        "at the empty mask the odd half is 0, got {}",
        f.k.render_lean(odd_empty)
    );
    assert!(
        !f.k.def_eq(even_empty, odd_empty),
        "NECESSITY: without a masked index below the width the conclusion is \
         FALSE, so the hypothesis cannot be dropped"
    );

    // And the mask has to be below the WIDTH, not merely non-empty: masking
    // only index 5 leaves the fold over [0,3) with nothing to branch on.
    let far = f.only(5);
    let even_far = f.masked_sel(far, 3, four, true);
    let odd_far = f.masked_sel(far, 3, four, false);
    assert!(
        !f.k.def_eq(even_far, odd_far),
        "NECESSITY: `Lt i n` is load-bearing too -- a masked index at or above \
         the width leaves the fold with nothing to branch on"
    );
}

/// The full mask recovers the unrestricted folds, at a concrete instance as
/// well as by `Eq.refl`.
#[test]
fn the_full_mask_recovers_the_unrestricted_folds() {
    let mut f = Fixture::new();
    let wide = f.all_mask();
    let reads_one = f.reads(1, 3, 5);

    let masked = f.masked_sum(wide, 2, reads_one);
    let plain = f.plain_sum(2, reads_one);
    assert!(
        f.k.def_eq(masked, plain),
        "sumSubsetsOn (fun _ => true) 2 F must be sumSubsets 2 F, got {} \
         against {}",
        f.k.render_lean(masked),
        f.k.render_lean(plain)
    );

    let sixteen = f.num(16);
    assert!(
        f.k.def_eq(masked, sixteen),
        "over [0,2) the four subsets give 3 + 3 + 5 + 5 = 16, got {}",
        f.k.render_lean(masked)
    );

    let narrow = f.only(1);
    let restricted = f.masked_sum(narrow, 2, reads_one);
    assert!(
        !f.k.def_eq(restricted, masked),
        "negative control: a proper mask must give a DIFFERENT answer, or the \
         full-mask bridge says nothing"
    );
}

/// Every name this module declares is present, is derived rather than asserted,
/// and rests on ZERO axioms.
///
/// `Kernel::axiom_footprint` returns an empty set for a name that does not
/// exist, so `Environment::contains` is asserted FIRST for each — otherwise a
/// renamed or never-declared theorem would pass this test silently.
#[test]
fn every_masked_subset_sum_declaration_is_present_and_axiom_free() {
    let f = Fixture::new();
    let p = f.p;
    let names: [NameId; 11] = [
        p.subsets_sum_subsets_on,
        p.subsets_sum_sel_on,
        p.subsets_sum_subsets_on_zero,
        p.subsets_sum_subsets_on_succ,
        p.subsets_sum_sel_on_zero,
        p.subsets_sum_sel_on_succ,
        p.subsets_sum_subsets_on_all,
        p.subsets_sum_sel_on_all,
        p.subsets_sum_sel_on_add,
        p.subsets_sum_subsets_on_card,
        p.subsets_sum_sel_on_const,
    ];
    for name in names {
        let shown = f.k.display_name(name).to_string();
        assert!(
            f.k.environment().contains(name),
            "{shown} must be declared -- an absent name has an EMPTY axiom \
             footprint, so the check below would pass without it"
        );
        let footprint = f.k.axiom_footprint(name);
        assert!(
            footprint.is_empty(),
            "{shown} must rest on zero axioms, found {:?}",
            footprint
                .iter()
                .map(|n| f.k.display_name(*n).to_string())
                .collect::<Vec<_>>()
        );
    }
}
