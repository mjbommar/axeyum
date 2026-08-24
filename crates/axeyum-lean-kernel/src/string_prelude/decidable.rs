//! `Char.decidable_eq` / `Str.decidable_eq` / `Str.decidable_isPrefix` :
//! `Π (a b : carrier), Decidable (prop a b)` — the `logic` prelude's
//! `Decidable.ofBool` bridge (`crates/axeyum-lean-kernel/src/prelude.rs`)
//! applied to a `Bool`-valued short-circuit decision (`char_beq`/`str_beq`/
//! `isPrefixBool`) and its two already-proved spec directions. One builder
//! serves all three: the per-instance inputs are the target `Prop`
//! (`Eq carrier a b`, via [`PropKind::CarrierEq`], or an arbitrary
//! two-argument predicate such as `isPrefix`, via [`PropKind::Predicate`]),
//! the `Bool`-valued decision function, and that function's positive
//! (`bexpr = true → prop`) and completeness (`prop → bexpr = true`) lemmas —
//! all already declared by `char_beq.rs`/`str_beq.rs`/`bool_predicates.rs`
//! before this module runs.
//!
//! # The one piece `Decidable.ofBool` does not supply: the negative direction
//!
//! `Decidable.ofBool` takes BOTH `(b = true → p)` and `(b = false → ¬p)` as
//! hypotheses (`prelude.rs`'s module doc on `decidable_of_bool`) — it is a
//! generic bridge, not a prover. The `positive` lemma above supplies the
//! first directly. None of `char_beq.rs`/`str_beq.rs`/`bool_predicates.rs`
//! proves the second (`bexpr = false → ¬prop`); only its converse,
//! `completeness` (`prop → bexpr = true`), exists. So this module derives it
//! by contraposition, generically over which `prop`/`bexpr` pair is in play:
//! given `hf : bexpr a b = false` and `hp : prop a b`, completeness turns
//! `hp` into `hc : bexpr a b = true`; `hf` and `hc` share the same left-hand
//! side `bexpr a b`, so `Eq.rec` transports `hf` along `hc` into
//! `Eq Bool Bool.true Bool.false` (the exact `eq_symm`-style single-step
//! transport `prelude.rs` uses throughout — no `Eq.trans` is declared
//! anywhere in this kernel, so this one direct `Eq.rec` application is the
//! whole derivation), and `logic.bool_true_ne_false` closes it to `False`.

use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::prelude::LogicPrelude;
use crate::{BinderInfo, Kernel, KernelError};

/// Which `Prop` is being decided: an equality on the carrier itself, or an
/// arbitrary two-argument predicate (e.g. `isPrefix : Str → Str → Prop`)
/// applied directly to the same two arguments `bexpr` takes.
#[derive(Debug, Clone, Copy)]
pub(super) enum PropKind {
    /// `Eq.{one} carrier a b`.
    CarrierEq,
    /// `pred a b` for the given predicate `NameId`.
    Predicate(NameId),
}

/// The interned names [`declare_decidable`] needs: the `logic` prelude (for
/// `Decidable`/`Decidable.ofBool`/`Eq`/`Bool`/`bool_true_ne_false`), the
/// carrier type, which `Prop` is being decided, the `Bool`-valued decision
/// function, and that function's two already-proved spec directions.
#[derive(Debug, Clone, Copy)]
pub(super) struct DecidableNames {
    pub logic: LogicPrelude,
    /// `Char` or `Str` : `Sort 1` — the type of both `a` and `b`.
    pub carrier: NameId,
    /// Which `Prop` is being decided.
    pub prop: PropKind,
    /// `char_beq` / `str_beq` / `isPrefixBool` : `carrier → carrier → Bool`.
    pub bexpr: NameId,
    /// The positive direction: `Eq Bool (bexpr a b) Bool.true → prop a b`.
    pub positive: NameId,
    /// Completeness: `prop a b → Eq Bool (bexpr a b) Bool.true`.
    pub completeness: NameId,
    /// The name to declare: `Char.decidable_eq` / `Str.decidable_eq` /
    /// `Str.decidable_isPrefix`.
    pub decidable_name: NameId,
}

/// Declare `names.decidable_name : Π (a b : carrier), Decidable (prop a b)`.
pub(super) fn declare_decidable(
    kernel: &mut Kernel,
    names: &DecidableNames,
    one: LevelId,
) -> Result<(), KernelError> {
    let mut dev = Dev::new(kernel, names, one);
    dev.declare()
}

/// Offset clear of the sibling modules' fvar bases purely for readability;
/// ids never leak past `abstract_fvars`, and each call to
/// [`declare_decidable`] is a fully self-contained term-building scope, so
/// reusing this same base across every call is safe.
const FVAR_BASE: u64 = 33_000;

struct Dev<'k> {
    k: &'k mut Kernel,
    n: DecidableNames,
    anon: NameId,
    zero: LevelId,
    one: LevelId,
    carrier_ty: ExprId,
    bool_ty: ExprId,
    next_fvar: u64,
}

impl<'k> Dev<'k> {
    fn new(k: &'k mut Kernel, n: &DecidableNames, one: LevelId) -> Self {
        let anon = k.anon();
        let zero = k.level_zero();
        let carrier_ty = k.const_(n.carrier, vec![]);
        let bool_ty = k.const_(n.logic.bool_, vec![]);
        Self {
            k,
            n: *n,
            anon,
            zero,
            one,
            carrier_ty,
            bool_ty,
            next_fvar: FVAR_BASE,
        }
    }

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

    fn bool_true_val(&mut self) -> ExprId {
        self.k.const_(self.n.logic.bool_true, vec![])
    }

    fn bool_false_val(&mut self) -> ExprId {
        self.k.const_(self.n.logic.bool_false, vec![])
    }

    /// `Eq.{1} Bool x y`.
    fn eq_bool(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let bt = self.bool_ty;
        self.apply(eq, &[bt, x, y])
    }

    /// `Eq.{1} carrier x y`.
    fn eq_carrier(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let eq = self.k.const_(self.n.logic.eq, vec![self.one]);
        let ct = self.carrier_ty;
        self.apply(eq, &[ct, x, y])
    }

    /// The `Prop` being decided, applied at `(a, b)` — either `Eq carrier a b`
    /// or `pred a b` per [`PropKind`].
    fn prop_of(&mut self, a: ExprId, b: ExprId) -> ExprId {
        match self.n.prop {
            PropKind::CarrierEq => self.eq_carrier(a, b),
            PropKind::Predicate(pred) => {
                let f = self.k.const_(pred, vec![]);
                self.apply(f, &[a, b])
            }
        }
    }

    /// `bexpr a b` — the declared `Bool`-valued decision, applied.
    fn bexpr_of(&mut self, a: ExprId, b: ExprId) -> ExprId {
        let f = self.k.const_(self.n.bexpr, vec![]);
        self.apply(f, &[a, b])
    }

    /// The negative direction `Eq Bool (bexpr a b) Bool.false → (prop a b →
    /// False)` — see the module doc for the contraposition-by-`Eq.rec` this
    /// builds.
    fn neg_direction(&mut self, a: ExprId, b: ExprId, bexpr_ab: ExprId, prop_ab: ExprId) -> ExprId {
        let (hf_fv, hf) = self.fvar();
        let (hp_fv, hp) = self.fvar();
        let (xvar_fv, xvar) = self.fvar();

        let bool_ty = self.bool_ty;
        let false_v = self.bool_false_val();
        let true_v = self.bool_true_val();

        // hc := completeness a b hp : Eq Bool (bexpr a b) Bool.true.
        let completeness = self.k.const_(self.n.completeness, vec![]);
        let hc = self.apply(completeness, &[a, b, hp]);

        // motive(x) := Eq Bool x Bool.false, indexed by a proof of
        // `Eq Bool (bexpr a b) x` (unused beyond selecting x).
        let motive = {
            let eq_bexpr_x = self.eq_bool(bexpr_ab, xvar);
            let target = self.eq_bool(xvar, false_v);
            let inner = self
                .k
                .lam(self.anon, eq_bexpr_x, target, BinderInfo::Default);
            self.lam_fv(xvar_fv, bool_ty, inner)
        };

        // transported : Eq Bool Bool.true Bool.false, transporting `hf`
        // (proved at the base point `bexpr a b`) along `hc` to the point
        // `Bool.true`.
        let eq_rec = self
            .k
            .const_(self.n.logic.eq_rec, vec![self.zero, self.one]);
        let transported = self.apply(eq_rec, &[bool_ty, bexpr_ab, motive, hf, true_v, hc]);

        let true_ne_false = self.k.const_(self.n.logic.bool_true_ne_false, vec![]);
        let contradiction = self.k.app(true_ne_false, transported); // False

        let with_hp = self.lam_fv(hp_fv, prop_ab, contradiction);
        let hf_ty = self.eq_bool(bexpr_ab, false_v);
        self.lam_fv(hf_fv, hf_ty, with_hp)
    }

    /// `names.decidable_name : Π (a b : carrier), Decidable (prop a b) :=
    ///   fun a b => Decidable.ofBool (prop a b) (bexpr a b)
    ///     (positive a b)         -- positive: bexpr=true → prop
    ///     (neg_direction a b …)`. -- negative: bexpr=false → ¬prop
    fn declare(&mut self) -> Result<(), KernelError> {
        let carrier_ty = self.carrier_ty;
        let (a_fv, a) = self.fvar();
        let (b_fv, b) = self.fvar();

        let prop_ab = self.prop_of(a, b);
        let decidable_const = self.k.const_(self.n.logic.decidable, vec![]);
        let dec_prop_ab = self.k.app(decidable_const, prop_ab);

        // type: Π (a b : carrier), Decidable (prop a b).
        let with_b = self.pi_fv(b_fv, carrier_ty, dec_prop_ab);
        let ty = self.pi_fv(a_fv, carrier_ty, with_b);

        let bexpr_ab = self.bexpr_of(a, b);

        let positive = self.k.const_(self.n.positive, vec![]);
        let pos = self.apply(positive, &[a, b]);

        let neg = self.neg_direction(a, b, bexpr_ab, prop_ab);

        let of_bool = self.k.const_(self.n.logic.decidable_of_bool, vec![]);
        let body = self.apply(of_bool, &[prop_ab, bexpr_ab, pos, neg]);

        let value_with_b = self.lam_fv(b_fv, carrier_ty, body);
        let value = self.lam_fv(a_fv, carrier_ty, value_with_b);

        self.k.add_declaration(Declaration::Definition {
            name: self.n.decidable_name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(0),
        })
    }
}
