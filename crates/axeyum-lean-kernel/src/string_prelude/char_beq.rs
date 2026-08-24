//! `Char.beq : Char → Char → Bool` — decidable equality on the alphabet
//! enum — plus `char_beq_refl` and both propositional spec directions
//! (`char_eq_of_beq_eq_true`, `char_beq_eq_true_of_eq`): the computational
//! foundation every `Bool`-valued string decision procedure over `Char`
//! needs (`Str.beq`'s head comparison, `Str.all`'s predicate test, …).
//!
//! # Design — a checked truth table, not a numeric comparison
//!
//! `Char` is a finite enum with one **nullary** constructor per distinct code
//! point (`string_prelude.rs`'s module doc); it may have **zero**
//! constructors (`empty_alphabet_admits` in `tests.rs`). `char_beq` is built
//! the way [`super::StringPrelude::char_eq_fn`] already builds its private,
//! per-call closed term: a **double `Char.rec`** truth table — the outer
//! recursor selects the row `i`, the inner one the cell `j`, both ι-folding
//! to a concrete `Bool` constructor (`Bool.true` iff `i == j`). This module
//! duplicates that construction as a **named, checked `Declaration::Definition`**
//! — `char_eq_fn` builds an anonymous term inline, at a point before
//! `StringPrelude` itself exists to hold a stable name for it — see
//! `all.rs`'s module doc for the same "duplicate a sibling's private helper
//! rather than import across a module boundary" rule.
//!
//! **`num_chars == 0`**: `Char.rec` then has **zero** minor premises (a
//! 0-constructor eliminator, exactly like `False.rec`), so `char_beq` and
//! every law below is admitted **vacuously** — every loop below over
//! `0..n` simply contributes no minors, and `Char.rec` is applied directly
//! to the (uninhabited) argument with nothing to case-split. The kernel
//! accepts this unconditionally: `Char.rec`'s typing rule does not require
//! `n > 0`. `char_beq_names_are_registered`/`char_beq_is_axiom_free` in
//! `tests.rs` run at `num_chars == 0` to pin exactly this.
//!
//! # What is proved, and how
//!
//! | law                        | statement                                             | route |
//! |-----------------------------|--------------------------------------------------------|-------|
//! | `char_beq_refl`             | `∀ a, Eq Bool (char_beq a a) Bool.true`                | `Char.rec` induction; each row's proof is `Eq.refl Bool Bool.true` (the diagonal ι-reduces to `Bool.true` by construction) |
//! | `char_eq_of_beq_eq_true`    | `∀ a b, Eq Bool (char_beq a b) Bool.true → Eq Char a b` | double `Char.rec` induction over the `n × n` constructor pairs; off-diagonal cells discharge the impossible `Eq Bool Bool.false Bool.true` hypothesis via `False.rec` |
//! | `char_beq_eq_true_of_eq`    | `∀ a b, Eq Char a b → Eq Bool (char_beq a b) Bool.true` | `Eq.rec` transport of `char_beq_refl a` along the hypothesis — no induction needed |
//!
//! `char_eq_of_beq_eq_true` and `char_beq_eq_true_of_eq` are the two
//! directions that make `char_beq` a **decision procedure** rather than a
//! function that happens to return `Bool`: together they say
//! `char_beq a b = true ↔ a = b`. Neither needs `Classical.em`, `propext`,
//! `funext`, or `Quot.sound` — the finite off-diagonal case split is
//! exhaustive by construction (`n × n` constructor pairs, each handled
//! individually), never an appeal to excluded middle.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// The interned names [`declare_char_beq_and_laws`] declares into, plus the
/// already-admitted `Char` handles its terms are built from.
#[derive(Debug, Clone)]
pub(super) struct CharBeqNames {
    pub logic: LogicPrelude,
    pub char_ind: NameId,
    pub char_ctors: Vec<NameId>,
    pub char_rec: NameId,
    pub char_beq: NameId,
    pub char_beq_refl: NameId,
    pub char_eq_of_beq_eq_true: NameId,
    pub char_beq_eq_true_of_eq: NameId,
}

/// Declare `char_beq` as a checked double-`Char.rec` truth table and prove
/// its laws, in dependency order.
pub(super) fn declare_char_beq_and_laws(
    kernel: &mut Kernel,
    // By reference: `CharBeqNames` embeds `LogicPrelude` and so exceeds
    // clippy's 256-byte `large_types_passed_by_value` limit, exactly the
    // trap `MonoidNames`/`AllNames`/`MapNames` already hit.
    names: &CharBeqNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.define_char_beq()?;
    dev.prove_char_beq_refl()?;
    dev.prove_char_eq_of_beq_eq_true()?;
    dev.prove_char_beq_eq_true_of_eq()?;
    Ok(())
}

/// Offset clear of the sibling modules' bases purely for readability; ids
/// never leak past `abstract_fvars`.
const FVAR_BASE: u64 = 30_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: CharBeqNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    char_ty: ExprId,
    bool_ty: ExprId,
    prop: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &CharBeqNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let char_ty = k.const_(n.char_ind, vec![]);
        let bool_ty = k.const_(n.logic.bool_, vec![]);
        let prop = k.sort_zero();
        Self {
            k,
            n: n.clone(),
            anon,
            zero,
            one,
            char_ty,
            bool_ty,
            prop,
            next_fvar: FVAR_BASE,
        }
    }

    // --- small builders -----------------------------------------------------

    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    fn fvar(&mut self) -> (u64, ExprId) {
        let id = self.fresh();
        let e = self.k.fvar(id);
        (id, e)
    }

    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.k.app(e, a);
        }
        e
    }

    fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.k.abstract_fvars(body, &[fv]);
        self.k.lam(self.anon, ty, b, BinderInfo::Default)
    }

    fn pi_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.k.abstract_fvars(body, &[fv]);
        self.k.pi(self.anon, ty, b, BinderInfo::Default)
    }

    fn arrow(&mut self, dom: ExprId, cod: ExprId) -> ExprId {
        self.k.pi(self.anon, dom, cod, BinderInfo::Default)
    }

    fn char_at(&mut self, idx: usize) -> ExprId {
        self.k.const_(self.n.char_ctors[idx], vec![])
    }

    fn bool_true_val(&mut self) -> ExprId {
        self.k.const_(self.n.logic.bool_true, vec![])
    }

    fn bool_false_val(&mut self) -> ExprId {
        self.k.const_(self.n.logic.bool_false, vec![])
    }

    /// `char_beq a b` — the declared constant applied, not inlined.
    fn char_beq_of(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.n.char_beq, vec![]);
        self.apply(f, &[a, b])
    }

    /// `Eq.{1} Bool x y`.
    fn eq_bool(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let bt = self.bool_ty;
        self.apply(eq, &[bt, x, y])
    }

    /// `Eq.refl.{1} Bool x : Eq Bool x x`.
    fn refl_bool(&mut self, x: ExprId) -> ExprId {
        let r = self.k.const_(self.n.logic.eq_refl, vec![self.one]);
        let bt = self.bool_ty;
        self.apply(r, &[bt, x])
    }

    /// `Eq.{1} Char x y`.
    fn eq_char(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let ct = self.char_ty;
        self.apply(eq, &[ct, x, y])
    }

    /// `Eq.refl.{1} Char x : Eq Char x x`.
    fn refl_char(&mut self, x: ExprId) -> ExprId {
        let r = self.k.const_(self.n.logic.eq_refl, vec![self.one]);
        let ct = self.char_ty;
        self.apply(r, &[ct, x])
    }

    fn declare_theorem(
        &mut self,
        name: NameId,
        ty: ExprId,
        value: ExprId,
    ) -> Result<(), KernelError> {
        self.k.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
    }

    /// Eliminate an impossible `Eq Bool Bool.false Bool.true` into
    /// `target : Prop`: `discriminator : Bool → Prop` with
    /// `discriminator false ≡ True`, `discriminator true ≡ False` (built
    /// from `Bool.rec`), transport `True.intro : discriminator false` along
    /// `equality` to `discriminator true ≡ False`, then `False.rec` into
    /// `target`. Duplicated from `nat_prelude::ops::NatDev::false_true_elim`
    /// (that module is off-limits to edit this slice) — see `all.rs`'s
    /// module doc for the same "duplicate rather than import across a
    /// module boundary" rule.
    fn false_bool_elim(&mut self, target: ExprId, equality: ExprId) -> ExprId {
        let bool_ty = self.bool_ty;
        let false_v = self.bool_false_val();
        let true_v = self.bool_true_val();
        let prop = self.prop;
        let discriminator = {
            let motive = self.k.lam(self.anon, bool_ty, prop, BinderInfo::Default);
            let rec = self.k.const_(self.n.logic.bool_rec, vec![self.one]);
            let true_prop = self.k.const_(self.n.logic.true_, vec![]);
            let false_prop = self.k.const_(self.n.logic.false_, vec![]);
            self.apply(rec, &[motive, true_prop, false_prop])
        };
        let motive = {
            let (v_fv, v) = self.fvar();
            let eq_ty = self.eq_bool(false_v, v);
            let body = self.k.app(discriminator, v);
            let inner = self.k.lam(self.anon, eq_ty, body, BinderInfo::Default);
            self.lam_fv(v_fv, bool_ty, inner)
        };
        let true_intro = self.k.const_(self.n.logic.true_intro, vec![]);
        let eq_rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let impossible = self.apply(
            eq_rec,
            &[bool_ty, false_v, motive, true_intro, true_v, equality],
        );
        let false_rec = self.k.const_(self.n.logic.false_rec, vec![self.zero]);
        let false_ty = self.k.const_(self.n.logic.false_, vec![]);
        let false_motive = self.k.lam(self.anon, false_ty, target, BinderInfo::Default);
        self.apply(false_rec, &[false_motive, impossible])
    }

    // --- the definition -----------------------------------------------------

    /// `char_beq : Char → Char → Bool`, a double `Char.rec` truth table:
    /// `char_beq (Char.c_i) (Char.c_j)` ι-reduces to `Bool.true` iff `i == j`.
    fn define_char_beq(&mut self) -> Result<(), KernelError> {
        let char_ty = self.char_ty;
        let bool_ty = self.bool_ty;
        let n = self.n.char_ctors.len();
        let char_to_bool = self.arrow(char_ty, bool_ty);

        let outer_motive = self
            .k
            .lam(self.anon, char_ty, char_to_bool, BinderInfo::Default);
        let outer_rec = self.k.const_(self.n.char_rec, vec![self.one]);
        let mut outer = self.k.app(outer_rec, outer_motive);
        for i in 0..n {
            let inner_motive = self.k.lam(self.anon, char_ty, bool_ty, BinderInfo::Default);
            let inner_rec = self.k.const_(self.n.char_rec, vec![self.one]);
            let mut inner = self.k.app(inner_rec, inner_motive);
            for j in 0..n {
                let v = if i == j {
                    self.bool_true_val()
                } else {
                    self.bool_false_val()
                };
                inner = self.k.app(inner, v);
            }
            let (b_fv, b) = self.fvar();
            let applied = self.k.app(inner, b);
            let row = self.lam_fv(b_fv, char_ty, applied);
            outer = self.k.app(outer, row);
        }
        let (a_fv, a) = self.fvar();
        let applied = self.k.app(outer, a);
        let value = self.lam_fv(a_fv, char_ty, applied);
        let ty = {
            let inner = self.arrow(char_ty, bool_ty);
            self.arrow(char_ty, inner)
        };
        self.k.add_declaration(Declaration::Definition {
            name: self.n.char_beq,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
    }

    // --- the laws -------------------------------------------------------------

    /// `char_beq_refl : ∀ (a : Char), Eq Bool (char_beq a a) Bool.true`.
    ///
    /// `Char.rec` induction: each row's minor is `Eq.refl Bool Bool.true`,
    /// accepted because the diagonal `char_beq c_i c_i` ι-reduces to
    /// `Bool.true` by construction (`define_char_beq`'s truth table always
    /// sets `f(i, i) = true`). Vacuous when `num_chars == 0` (no rows).
    fn prove_char_beq_refl(&mut self) -> Result<(), KernelError> {
        let char_ty = self.char_ty;
        let n = self.n.char_ctors.len();
        let (a_fv, a) = self.fvar();
        let goal = |d: &mut Self, x: ExprId| {
            let cb = d.char_beq_of(x, x);
            let t = d.bool_true_val();
            d.eq_bool(cb, t)
        };
        let stmt = goal(self, a);
        let motive = {
            let (x_fv, x) = self.fvar();
            let body = goal(self, x);
            self.lam_fv(x_fv, char_ty, body)
        };
        let rec = self.k.const_(self.n.char_rec, vec![self.zero]);
        let mut term = self.k.app(rec, motive);
        for _ in 0..n {
            let t = self.bool_true_val();
            let pf = self.refl_bool(t);
            term = self.k.app(term, pf);
        }
        let proof = self.k.app(term, a);
        let ty = self.pi_fv(a_fv, char_ty, stmt);
        let value = self.lam_fv(a_fv, char_ty, proof);
        let name = self.n.char_beq_refl;
        self.declare_theorem(name, ty, value)
    }

    /// `char_eq_of_beq_eq_true : ∀ (a b : Char),
    ///     Eq Bool (char_beq a b) Bool.true → Eq Char a b`.
    ///
    /// Double `Char.rec` induction over the `n × n` constructor pairs
    /// (outer on `a`, inner on `b`, both `Prop`-motive). On the diagonal
    /// (`i == j`) the premise ι-reduces to `Eq Bool Bool.true Bool.true`
    /// and the goal closes by `Eq.refl`; off the diagonal it ι-reduces to
    /// the impossible `Eq Bool Bool.false Bool.true`, discharged by
    /// [`Self::false_bool_elim`]. Vacuous when `num_chars == 0`.
    fn prove_char_eq_of_beq_eq_true(&mut self) -> Result<(), KernelError> {
        let char_ty = self.char_ty;
        let n = self.n.char_ctors.len();

        let row_type = |d: &mut Self, a: ExprId| {
            let (b_fv, b) = d.fvar();
            let cb = d.char_beq_of(a, b);
            let t = d.bool_true_val();
            let premise = d.eq_bool(cb, t);
            let concl = d.eq_char(a, b);
            let imp = d.arrow(premise, concl);
            d.pi_fv(b_fv, char_ty, imp)
        };

        let (a_fv, a) = self.fvar();
        let stmt = row_type(self, a);

        let outer_motive = {
            let (x_fv, x) = self.fvar();
            let body = row_type(self, x);
            self.lam_fv(x_fv, char_ty, body)
        };
        let outer_rec = self.k.const_(self.n.char_rec, vec![self.zero]);
        let mut outer = self.k.app(outer_rec, outer_motive);

        for i in 0..n {
            let ci = self.char_at(i);
            let inner_motive = {
                let (y_fv, y) = self.fvar();
                let cb = self.char_beq_of(ci, y);
                let t = self.bool_true_val();
                let premise = self.eq_bool(cb, t);
                let concl = self.eq_char(ci, y);
                let body = self.arrow(premise, concl);
                self.lam_fv(y_fv, char_ty, body)
            };
            let inner_rec = self.k.const_(self.n.char_rec, vec![self.zero]);
            let mut inner = self.k.app(inner_rec, inner_motive);
            for j in 0..n {
                let cj = self.char_at(j);
                let cb = self.char_beq_of(ci, cj);
                let t = self.bool_true_val();
                let premise_ty = self.eq_bool(cb, t);
                let (h_fv, h) = self.fvar();
                let body = if i == j {
                    self.refl_char(ci)
                } else {
                    let target = self.eq_char(ci, cj);
                    self.false_bool_elim(target, h)
                };
                let minor = self.lam_fv(h_fv, premise_ty, body);
                inner = self.k.app(inner, minor);
            }
            outer = self.k.app(outer, inner);
        }

        let proof = self.k.app(outer, a);
        let ty = self.pi_fv(a_fv, char_ty, stmt);
        let value = self.lam_fv(a_fv, char_ty, proof);
        let name = self.n.char_eq_of_beq_eq_true;
        self.declare_theorem(name, ty, value)
    }

    /// `char_beq_eq_true_of_eq : ∀ (a b : Char),
    ///     Eq Char a b → Eq Bool (char_beq a b) Bool.true`.
    ///
    /// Pure `Eq.rec` transport of `char_beq_refl a` along the hypothesis —
    /// no induction on `Char` needed, exactly [`super::string_prelude`]'s
    /// `nat_prelude::defs::declare_boolean_equality`'s `beq_eq_true_of_eq`.
    fn prove_char_beq_eq_true_of_eq(&mut self) -> Result<(), KernelError> {
        let char_ty = self.char_ty;
        let (a_fv, a) = self.fvar();
        let (b_fv, b) = self.fvar();
        let source = self.eq_char(a, b);
        let target = {
            let cb = self.char_beq_of(a, b);
            let t = self.bool_true_val();
            self.eq_bool(cb, t)
        };
        let (heq_fv, heq) = self.fvar();

        let motive = {
            let (z_fv, z) = self.fvar();
            let cb = self.char_beq_of(a, z);
            let t = self.bool_true_val();
            let concl = self.eq_bool(cb, t);
            let hyp = self.eq_char(a, z);
            let inner = self.k.lam(self.anon, hyp, concl, BinderInfo::Default);
            self.lam_fv(z_fv, char_ty, inner)
        };
        let base = {
            let lemma = self.k.const_(self.n.char_beq_refl, vec![]);
            self.k.app(lemma, a)
        };
        let rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let body = self.apply(rec, &[char_ty, a, motive, base, b, heq]);

        let value = {
            let with_heq = self.lam_fv(heq_fv, source, body);
            let with_b = self.lam_fv(b_fv, char_ty, with_heq);
            self.lam_fv(a_fv, char_ty, with_b)
        };
        let ty = {
            let inner = self.arrow(source, target);
            let with_b = self.pi_fv(b_fv, char_ty, inner);
            self.pi_fv(a_fv, char_ty, with_b)
        };
        let name = self.n.char_beq_eq_true_of_eq;
        self.declare_theorem(name, ty, value)
    }
}
