//! Concrete-instance tests for `nat_prelude::finset_singleton` (ADR-1630).
//!
//! **The kernel cannot tell a `Definition` is wrong.** `Nat.Finset.empty` is
//! admitted on its type — `Nat.Finset` — and so is `Nat.Finset.range 7`, or
//! `mk (fun _ => true) 3`, or anything else of that type. So the checks below
//! reduce closed terms with the kernel's own `def_eq` and compare against
//! independently hand-computed values, and every positive is paired with the
//! specific wrong definition it rules out.
//!
//! The theorems get a different treatment: an empty axiom footprint is ALSO
//! what a missing name returns, so each footprint assertion is preceded by an
//! `Environment::contains` assertion on the same name.
//!
//! Magnitudes are tiny on purpose (largest numeral formed: `4`); this
//! prelude's numerals are unary `Nat.succ` towers.

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::{Kernel, NameId, NatOps, NatPrelude, NatState, build_nat_prelude};

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

    /// `Nat.Finset.empty`.
    fn empty(&mut self) -> ExprId {
        let name = self.p.finset_empty;
        self.k.const_(name, vec![])
    }

    /// `Nat.Finset.singleton a`.
    fn singleton(&mut self, a: u32) -> ExprId {
        let lit = self.num(a);
        let name = self.p.finset_singleton;
        self.const_app(name, &[lit])
    }

    fn memb(&mut self, s: ExprId, i: u32) -> ExprId {
        let lit = self.num(i);
        let name = self.p.finset_mem_b;
        self.const_app(name, &[s, lit])
    }

    fn card(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_card;
        self.const_app(name, &[s])
    }

    fn bound(&mut self, s: ExprId) -> ExprId {
        let name = self.p.finset_bound;
        self.const_app(name, &[s])
    }
}

/// `Nat.Finset.empty` really is empty, and its bound really is `zero`.
///
/// Both halves are needed and neither implies the other here. A wrong
/// definition that got the PREDICATE right but the bound wrong
/// (`mk (fun _ => false) 4`) still has no members, so only the bound check
/// rules it out; a wrong definition that got the BOUND right but the predicate
/// wrong (`mk (fun _ => true) 0`) still has no members either, because `memB`
/// truncates — which is exactly why the module comment says the predicate
/// choice is about the proof of `memB_empty`, not about the members.
///
/// The `range 0` comparison is the sharp one: `Nat.Finset.range 0` is
/// EXTENSIONALLY the same set, and the assertion records that it is not
/// definitionally this one, so a future edit that redefines `empty` as
/// `range 0` is a visible change rather than a silent one.
#[test]
fn empty_has_no_members_and_bound_zero() {
    let mut f = Fixture::new();
    let t = f.bool_true();
    let fa = f.bool_false();
    let zero = f.zero();
    let four = f.num(4);

    let e = f.empty();
    for i in [0u32, 1, 3] {
        let at_i = f.memb(e, i);
        assert!(f.k.def_eq(at_i, fa), "memB empty {i} must be false");
        assert!(
            !f.k.def_eq(at_i, t),
            "negative control: memB empty {i} must NOT be true"
        );
    }

    let b = f.bound(e);
    assert!(f.k.def_eq(b, zero), "bound empty must be zero");
    assert!(
        !f.k.def_eq(b, four),
        "negative control: bound empty must NOT be 4 -- rules out \
         `mk (fun _ => false) 4`, which has the same members"
    );

    let c = f.card(e);
    assert!(f.k.def_eq(c, zero), "card empty must be zero");
    let one = f.num(1);
    assert!(
        !f.k.def_eq(c, one),
        "negative control: card empty must NOT be 1"
    );

    // `range 0` is extensionally equal but not definitionally this set.
    let r0 = {
        let lit = f.zero();
        let name = f.p.finset_range;
        f.const_app(name, &[lit])
    };
    assert!(
        !f.k.def_eq(e, r0),
        "`Nat.Finset.empty` is deliberately NOT `Nat.Finset.range 0`: the \
         stored predicate is `fun _ => false`, not `fun _ => true`"
    );
}

/// `Nat.Finset.card (singleton a) = 1` at a concrete `a`, evaluated rather
/// than derived from the theorem.
///
/// The negative controls are `0` and `2`: a `card` that counted only BELOW the
/// top index would give `0`, and one that double-counted the peel would give
/// `2`. `a = 3` rather than `a = 0` on purpose — at `a = 0` the body of the
/// count is empty and a definition that ignored the body entirely would still
/// land on `1`.
#[test]
fn card_of_a_singleton_is_one() {
    let mut f = Fixture::new();
    let zero = f.zero();
    let one = f.num(1);
    let two = f.num(2);

    for a in [0u32, 3] {
        let s = f.singleton(a);
        let c = f.card(s);
        assert!(f.k.def_eq(c, one), "card (singleton {a}) must be 1");
        assert!(
            !f.k.def_eq(c, zero),
            "negative control: card (singleton {a}) must NOT be 0"
        );
        assert!(
            !f.k.def_eq(c, two),
            "negative control: card (singleton {a}) must NOT be 2"
        );
    }
}

/// `Nat.Finset.memB (singleton a) i` is `Nat.beq i a` at concrete indices on
/// BOTH sides of the bound.
///
/// The index `4` is above `bound (singleton 3) = 4`, so it is decided by the
/// truncation branch rather than by `beq`; `memB_singleton`'s `on_above` case
/// is the only thing that covers it, and a proof that only ever handled the
/// `below` case could not have been admitted with the index `4` in range.
#[test]
fn mem_b_singleton_agrees_with_beq_on_both_sides_of_the_bound() {
    let mut f = Fixture::new();
    let t = f.bool_true();
    let fa = f.bool_false();

    let s3 = f.singleton(3);
    for (i, expected) in [(0u32, false), (2, false), (3, true), (4, false)] {
        let at_i = f.memb(s3, i);
        let want = if expected { t } else { fa };
        let other = if expected { fa } else { t };
        assert!(
            f.k.def_eq(at_i, want),
            "memB (singleton 3) {i} must be {expected}"
        );
        assert!(
            !f.k.def_eq(at_i, other),
            "negative control: memB (singleton 3) {i} must NOT be {}",
            !expected
        );
    }
}

/// Every declaration this module lands is present, of the promised kind, and
/// rests on ZERO axioms.
///
/// The `contains` assertion is not decoration: `Kernel::axiom_footprint` of a
/// name that was never declared is EMPTY, so a footprint assertion on its own
/// passes for a typo. The names are read from the `NatPrelude` struct, so a
/// rename cannot leave this test measuring a stale spelling.
#[test]
fn the_singleton_shelf_is_admitted_and_axiom_free() {
    let mut f = Fixture::new();
    let p = f.p;

    let definitions: [NameId; 1] = [p.finset_empty];
    let theorems: [NameId; 8] = [
        p.finset_mem_b_empty,
        p.finset_card_empty,
        p.finset_mem_b_singleton,
        p.finset_mem_b_singleton_self,
        p.finset_eq_of_mem_b_singleton,
        p.finset_card_singleton,
        p.finset_card_eq_zero_of_no_mem_b,
        p.finset_exists_mem_b_of_card_pos,
    ];

    for name in definitions {
        let shown = f.k.display_name(name).to_string();
        assert!(
            f.k.environment().contains(name),
            "{shown} must be declared before its footprint means anything"
        );
        let decl = f.k.environment().get(name).expect("just checked");
        assert!(
            matches!(decl, Declaration::Definition { .. }),
            "{shown} must be a Definition"
        );
        let ty = decl.ty();
        println!("def {shown} : {}", f.k.render_lean(ty));
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{shown} must rest on zero axioms"
        );
    }

    for name in theorems {
        let shown = f.k.display_name(name).to_string();
        assert!(
            f.k.environment().contains(name),
            "{shown} must be declared before its footprint means anything"
        );
        let decl = f.k.environment().get(name).expect("just checked");
        assert!(
            matches!(decl, Declaration::Theorem { .. }),
            "{shown} must be a checked Theorem, not an Axiom or Opaque"
        );
        let ty = decl.ty();
        println!("theorem {shown} : {}", f.k.render_lean(ty));
        assert!(
            f.k.axiom_footprint(name).is_empty(),
            "{shown} must rest on zero axioms"
        );
    }

    // The control the paragraph above describes: a name that was never
    // declared has an EMPTY footprint too, so `contains` is what carries the
    // weight.
    let bogus = f.k.name_str(p.finset, "memB_singleton_not_a_real_lemma");
    assert!(
        !f.k.environment().contains(bogus),
        "the control name must be absent"
    );
    assert!(
        f.k.axiom_footprint(bogus).is_empty(),
        "an ABSENT name also has an empty footprint -- this is why every \
         footprint assertion above is preceded by `contains`"
    );
}
