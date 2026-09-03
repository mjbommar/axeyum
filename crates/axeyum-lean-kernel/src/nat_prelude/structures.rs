//! `Alg.*` — the abstract algebraic structure spine of ADR-1578: ten
//! independent one-constructor `Sort 2` records
//! `Magma -> Semigroup -> Monoid -> CommMonoid -> Group -> CommGroup ->
//! Semiring -> Ring -> CommRing -> Field`, each carrying `carrier : Sort 1`
//! as a genuine FIELD (not a parameter), exactly ADR-1495's
//! `bundled_structure_probe.rs` mechanism, generalized into a reusable
//! builder and applied ten times.
//!
//! ## Why this lives under `nat_prelude/` but not under the `Nat` namespace
//!
//! Every record here is fully abstract (`Sort 1` carrier, caller-supplied
//! operations) and needs nothing from `Nat` at all — only [`LogicPrelude`]
//! (`Eq`, `False`, `Sort`). It is declared here, ahead of `Int`/`Rat`, purely
//! because `NatPrelude` is the first prelude built and the ℕ instance
//! (`rat_prelude/algebra_instances.rs`) needs these records to already exist.
//! The kernel NAMES live under their own `Alg` root, never `Nat.*`, so a
//! future carrier-specific declaration named `Group`/`Ring`/`Field` inside
//! `Nat`'s own namespace (as `nat_prelude::group`'s `Nat.IsGroupOn` already
//! is) cannot collide with it — see
//! `docs/contributor-guide/kernel-proof-engineering.md`'s "a prelude can
//! declare into another prelude's namespace" entry.
//!
//! ## What each record mirrors, and what is deliberately absent
//!
//! | record | new fields | mirrors | absent |
//! | --- | --- | --- | --- |
//! | `Magma` | `op` | `Mathlib.Mul` | — |
//! | `Semigroup` | `assoc` | `Mathlib.Semigroup` | — |
//! | `Monoid` | `e`, `identL`, `identR` | `Mathlib.Monoid` | `npow` |
//! | `CommMonoid` | `comm` | `Mathlib.CommMonoid` | — |
//! | `Group` | `inv`, `invL`, `invR` | `Mathlib.Group` | `zpow` |
//! | `CommGroup` | `comm` | `Mathlib.CommGroup` | — |
//! | `Semiring` | `zero one add mul addAssoc addComm addZero mulAssoc mulOneL mulOneR distribL distribR` | `Mathlib.Semiring` | `nsmul`, order |
//! | `Ring` | `neg`, `negAdd` | `Mathlib.Ring` | — |
//! | `CommRing` | `mulComm` | `Mathlib.CommRing` | — |
//! | `Field` | `inv`, `oneNeZero`, `mulInv` (conditional) | `Mathlib.Field` | — |
//!
//! No record embeds another — **no inheritance, no coercion, no instance
//! resolution.** `CommMonoid` restates `Monoid`'s six fields plus `comm`
//! rather than carrying a `Monoid` value, the same "third independent copy"
//! shape `int_prelude/ring.rs`'s `Int.IsCommRing` already uses for a single
//! carrier; here it is generalized over `(α : Sort 1)` instead of
//! hand-duplicated per carrier. **An instance is a term you pass** — see
//! `rat_prelude/algebra_instances.rs`.
//!
//! ## The universe guard, measured per record
//!
//! Every record's constructor carries `carrier : Sort 1` as a field, so by
//! ADR-1495's `KernelError::ConstructorFieldUniverseTooBig` guard every one
//! of the ten **must** live at `Sort 2`; the same field list at `Sort 1` is
//! refused. [`declare_record`] runs both as a control for every record (not
//! only once, as ADR-1495's own probe did for `Field` alone) — see
//! `docs/plan/status/453-structures-1.md` for all ten pairs.
//!
//! ## The generic construction
//!
//! Each field is specified once as a [`FieldSpec`] whose `build` closure
//! computes the field's TYPE from the earlier fields' VALUES — during
//! constructor-type construction those values are the constructor's own
//! fresh free variables; during selector construction (by large elimination
//! off the auto-generated recursor, `carrier` motive level `Sort 2`, every
//! other field motive level `Sort 1` for data or `Sort 0`/`Prop` for a law)
//! the same closure is called again with the EARLIER SELECTORS applied to
//! the bound structure variable `s`. This is the same shape
//! `bundled_structure_probe.rs` hand-unrolls per field; here it is looped.

use crate::BinderInfo;
use crate::Kernel;
use crate::KernelError;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;

// ---------------------------------------------------------------------------
// Generic term-building toolkit (carrier-free; ports
// `bundled_structure_probe.rs`'s free functions into reusable prelude code).
// ---------------------------------------------------------------------------

pub(crate) fn pi_over(k: &mut Kernel, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = k.abstract_fvars(body, &[fv]);
    let anon = k.anon();
    k.pi(anon, ty, b, BinderInfo::Default)
}

pub(crate) fn lam_over(k: &mut Kernel, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = k.abstract_fvars(body, &[fv]);
    let anon = k.anon();
    k.lam(anon, ty, b, BinderInfo::Default)
}

pub(crate) fn arrow(k: &mut Kernel, dom: ExprId, cod: ExprId) -> ExprId {
    let anon = k.anon();
    k.pi(anon, dom, cod, BinderInfo::Default)
}

pub(crate) fn app2(k: &mut Kernel, f: ExprId, x: ExprId, y: ExprId) -> ExprId {
    let fx = k.app(f, x);
    k.app(fx, y)
}

pub(crate) fn eq_of(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
) -> ExprId {
    let c = k.const_(lg.eq, vec![lvl]);
    let e = k.app(c, ty);
    let e = k.app(e, a);
    k.app(e, b)
}

pub(crate) fn refl_of(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
) -> ExprId {
    let c = k.const_(lg.eq_refl, vec![lvl]);
    let e = k.app(c, ty);
    k.app(e, a)
}

pub(crate) fn symm_of(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let c = k.const_(lg.eq_symm, vec![lvl]);
    let e = k.app(c, ty);
    let e = k.app(e, a);
    let e = k.app(e, b);
    k.app(e, h)
}

/// `Eq.rec` transport with the carrier's universe `lvl` and a `Prop` motive.
#[allow(clippy::too_many_arguments)]
fn transport(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    p: ExprId,
    motive: ExprId,
    refl_case: ExprId,
    q: ExprId,
    h: ExprId,
) -> ExprId {
    let zero = k.level_zero();
    let rec = k.const_(lg.eq_rec, vec![zero, lvl]);
    let e = k.app(rec, ty);
    let e = k.app(e, p);
    let e = k.app(e, motive);
    let e = k.app(e, refl_case);
    let e = k.app(e, q);
    k.app(e, h)
}

/// `fun (x : ty) (_ : Eq ty a x) => body x`.
fn eq_motive(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    x_fv: u64,
    body: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
) -> ExprId {
    let x = k.fvar(x_fv);
    let concl = body(k, x);
    let hyp = eq_of(k, lg, lvl, ty, a, x);
    let anon = k.anon();
    let inner = k.lam(anon, hyp, concl, BinderInfo::Default);
    lam_over(k, x_fv, ty, inner)
}

/// `h1 : Eq a b`, `h2 : Eq b c` |- `Eq a c`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn trans_of(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
    scratch_fv: u64,
) -> ExprId {
    let motive = eq_motive(k, lg, lvl, ty, b, scratch_fv, &|k2, x| {
        eq_of(k2, lg, lvl, ty, a, x)
    });
    transport(k, lg, lvl, ty, b, motive, h1, c, h2)
}

/// `h : Eq a b` |- `Eq (f a) (f b)`, for a carrier-generic `f`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn congr_arg(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    scratch_fv: u64,
    f: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
) -> ExprId {
    let fa = f(k, a);
    let motive = eq_motive(k, lg, lvl, ty, a, scratch_fv, &|k2, x| {
        let fx = f(k2, x);
        eq_of(k2, lg, lvl, ty, fa, fx)
    });
    let refl_case = refl_of(k, lg, lvl, ty, fa);
    transport(k, lg, lvl, ty, a, motive, refl_case, b, h)
}

/// `h : Eq ty a b`, `pa : P a` |- `P b`, for an arbitrary carrier-generic
/// predicate `P` (a `Prop`-valued closure, not necessarily an `Eq`) — the
/// same `Eq.rec` shape [`congr_arg`] uses, generalized so `P` need not be
/// `Eq ty2 (f _) (f _)`. Used by ADR-1584's `OrderedRing` theorem to
/// transport a `le` fact along a `Ring`-level equality.
#[allow(clippy::too_many_arguments)]
pub(crate) fn subst(
    k: &mut Kernel,
    lg: &LogicPrelude,
    lvl: LevelId,
    ty: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
    scratch_fv: u64,
    pred: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
    proof_at_a: ExprId,
) -> ExprId {
    let motive = eq_motive(k, lg, lvl, ty, a, scratch_fv, pred);
    transport(k, lg, lvl, ty, a, motive, proof_at_a, b, h)
}

/// ADR-1585: a small stateful wrapper around the free-function toolkit above,
/// so a multi-step `Eq`/`le` derivation over one fixed carrier (e.g. building
/// `linarith::generic`'s derived order lemmas, or `Alg.ofNat`'s laws) reads
/// as a sequence of method calls rather than re-threading `lg`/`lvl`/`ty` and
/// a fresh scratch fvar through every call by hand. Every method here is a
/// thin forward to the matching free function; nothing new is proved.
pub(crate) struct EqB<'a> {
    k: &'a mut Kernel,
    lg: LogicPrelude,
    lvl: LevelId,
    carrier: ExprId,
    next_fvar: u64,
}

impl<'a> EqB<'a> {
    /// `base` should be a range this construction (and nothing running
    /// concurrently with it) otherwise uses — the same discipline every
    /// fixed `_FV` constant in this file already follows; reuse across
    /// unrelated, sequential top-level constructions is safe (each scratch
    /// fvar is abstracted away before the call returns).
    pub(crate) fn new(
        k: &'a mut Kernel,
        lg: &LogicPrelude,
        lvl: LevelId,
        carrier: ExprId,
        base: u64,
    ) -> Self {
        Self {
            k,
            lg: *lg,
            lvl,
            carrier,
            next_fvar: base,
        }
    }

    pub(crate) fn kernel(&mut self) -> &mut Kernel {
        self.k
    }

    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    pub(crate) fn symm(&mut self, a: ExprId, b: ExprId, h: ExprId) -> ExprId {
        symm_of(self.k, &self.lg, self.lvl, self.carrier, a, b, h)
    }

    pub(crate) fn trans(
        &mut self,
        a: ExprId,
        b: ExprId,
        c: ExprId,
        h1: ExprId,
        h2: ExprId,
    ) -> ExprId {
        let s = self.fresh();
        trans_of(self.k, &self.lg, self.lvl, self.carrier, a, b, c, h1, h2, s)
    }

    pub(crate) fn congr(
        &mut self,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        f: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
    ) -> ExprId {
        let s = self.fresh();
        congr_arg(self.k, &self.lg, self.lvl, self.carrier, a, b, h, s, f)
    }

    pub(crate) fn subst(
        &mut self,
        a: ExprId,
        b: ExprId,
        h: ExprId,
        pred: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
        proof_at_a: ExprId,
    ) -> ExprId {
        let s = self.fresh();
        subst(
            self.k,
            &self.lg,
            self.lvl,
            self.carrier,
            a,
            b,
            h,
            s,
            pred,
            proof_at_a,
        )
    }

    pub(crate) fn app(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.k.app(e, a);
        }
        e
    }

    pub(crate) fn app2(&mut self, f: ExprId, x: ExprId, y: ExprId) -> ExprId {
        app2(self.k, f, x, y)
    }
}

pub(crate) fn close_pi(k: &mut Kernel, fields: &[(u64, ExprId)], result: ExprId) -> ExprId {
    let mut t = result;
    for &(fv, ty) in fields.iter().rev() {
        t = pi_over(k, fv, ty, t);
    }
    t
}

pub(crate) fn close_lam(k: &mut Kernel, fields: &[(u64, ExprId)], body: ExprId) -> ExprId {
    let mut t = body;
    for &(fv, ty) in fields.iter().rev() {
        t = lam_over(k, fv, ty, t);
    }
    t
}

// ---------------------------------------------------------------------------
// ADR-1587: instance-construction helpers and `Alg.mul_left_cancel`, homed
// here (not `rat_prelude/algebra_instances.rs`/`algebra_ext.rs`) so a carrier
// prelude that is NOT `rat_prelude` (i.e. `int_prelude`, which is built
// BEFORE `rat_prelude` even starts) can build an `Alg.*` record instance and
// apply a generic theorem to it WITHOUT depending on `rat_prelude` --
// `nat_prelude` is the one module every later prelude already depends on.
// This is what makes it possible for `Int.add_left_cancel` (declared deep
// inside `int_prelude::add_basics`, long before `rat_prelude` exists at all)
// to retire to `Alg.mul_left_cancel` applied at an inline `Alg.Group` value:
// both the instance-building helpers and the generic theorem itself live at
// a point in the module graph reachable from `int_prelude`. See ADR-1587.
// ---------------------------------------------------------------------------

/// Apply selector `i` of record `rn` to structure term `s`. Mirrors (and
/// replaces the sole prior copy of) `rat_prelude::algebra_instances::sel` --
/// moved here, not merely duplicated, so there is exactly one definition.
pub(crate) fn sel(k: &mut Kernel, rn: &RecordNames, i: usize, s: ExprId) -> ExprId {
    let c = k.const_(rn.sel(i), vec![]);
    k.app(c, s)
}

/// `<Record>.mk arg0 arg1 ...` in field order. Moved here from
/// `rat_prelude::algebra_instances` for the same reason as [`sel`].
pub(crate) fn mk_instance(k: &mut Kernel, rn: &RecordNames, args: &[ExprId]) -> ExprId {
    let mut v = k.const_(rn.mk, vec![]);
    for a in args {
        v = k.app(v, *a);
    }
    v
}

/// Builds `∀ a, op unit a = a` (a VALUE, i.e. a proof term of that type) from
/// `comm : ∀ x y, op x y = op y x` and `right_unit : ∀ x, op x unit = x`.
/// Moved here from `rat_prelude::algebra_instances` for the same reason as
/// [`sel`]; still used there for `Rat`'s missing `one_mul`, and here for
/// `Int`'s missing `zero_add`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn derive_left_unit(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    carrier_ty: ExprId,
    op: ExprId,
    unit: ExprId,
    comm: ExprId,
    right_unit: ExprId,
    a_fv: u64,
    scratch_fv: u64,
) -> ExprId {
    let a = k.fvar(a_fv);
    let op_unit_a = app2(k, op, unit, a);
    let op_a_unit = app2(k, op, a, unit);
    let comm_applied = {
        let c1 = k.app(comm, unit);
        k.app(c1, a)
    }; // : Eq (op unit a) (op a unit)
    let ru_applied = k.app(right_unit, a); // : Eq (op a unit) a
    let body = trans_of(
        k,
        lg,
        l1,
        carrier_ty,
        op_unit_a,
        op_a_unit,
        a,
        comm_applied,
        ru_applied,
        scratch_fv,
    );
    lam_over(k, a_fv, carrier_ty, body)
}

/// `Alg.mul_left_cancel : forall (g : Group) (a b c : g.carrier), g.op a b =
/// g.op a c -> b = c`. Moved here (from `rat_prelude/algebra_ext.rs`'s
/// `build_mul_left_cancel`, ADR-1584) verbatim except for using this
/// module's own [`sel`], because this theorem needs only the abstract
/// `Group` record -- no carrier at all -- so it can be declared at the
/// EARLIEST possible position in the whole build: immediately after the
/// structures spine itself. `declare_algebra_ext_all` no longer declares
/// this name (would be a duplicate); `AlgebraExtNames.mul_left_cancel`'s own
/// `name_str` interning is idempotent and still resolves to this
/// declaration.
fn build_mul_left_cancel_generic(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l1: LevelId,
    group: &RecordNames,
) -> (ExprId, ExprId) {
    use idx::group::{ASSOC, CARRIER, E, IDENT_L, INV, INV_L, OP};
    const G_FV: u64 = 22_100;
    const A_FV: u64 = 22_101;
    const B_FV: u64 = 22_102;
    const C_FV: u64 = 22_103;
    const H_FV: u64 = 22_104;
    const S1: u64 = 22_105;
    const S2: u64 = 22_106;
    const S3: u64 = 22_107;
    const S4: u64 = 22_108;
    const S5: u64 = 22_109;
    const S6: u64 = 22_110;

    let ind_ty = k.const_(group.ind, vec![]);
    let g = k.fvar(G_FV);
    let carrier = sel(k, group, CARRIER, g);
    let op = sel(k, group, OP, g);
    let e = sel(k, group, E, g);
    let inv = sel(k, group, INV, g);
    let ident_l = sel(k, group, IDENT_L, g);
    let inv_l = sel(k, group, INV_L, g);
    let assoc = sel(k, group, ASSOC, g);

    let a = k.fvar(A_FV);
    let b = k.fvar(B_FV);
    let c = k.fvar(C_FV);
    let inv_a = k.app(inv, a);

    let op_a_b = app2(k, op, a, b);
    let op_a_c = app2(k, op, a, c);
    let hyp_ty = eq_of(k, lg, l1, carrier, op_a_b, op_a_c);
    let h = k.fvar(H_FV);

    // r0 : b = op e b
    let op_e_b = app2(k, op, e, b);
    let ident_l_b = k.app(ident_l, b); // op e b = b
    let r0 = symm_of(k, lg, l1, carrier, op_e_b, b, ident_l_b);

    // r1 : op e b = op (op inv_a a) b
    let inv_l_a = k.app(inv_l, a); // op inv_a a = e
    let op_invaa = app2(k, op, inv_a, a);
    let symm_inv_l_a = symm_of(k, lg, l1, carrier, op_invaa, e, inv_l_a); // e = op inv_a a
    let op_invaa_b = app2(k, op, op_invaa, b);
    let r1 = congr_arg(
        k,
        lg,
        l1,
        carrier,
        e,
        op_invaa,
        symm_inv_l_a,
        S1,
        &|k2, w| app2(k2, op, w, b),
    );

    // r2 : op (op inv_a a) b = op inv_a (op a b)  (assoc inv_a a b)
    let op_inva_opab = app2(k, op, inv_a, op_a_b);
    let r2 = {
        let e1 = k.app(assoc, inv_a);
        let e2 = k.app(e1, a);
        k.app(e2, b)
    };

    // r3 : op inv_a (op a b) = op inv_a (op a c)  (congr via h)
    let op_inva_opac = app2(k, op, inv_a, op_a_c);
    let r3 = congr_arg(k, lg, l1, carrier, op_a_b, op_a_c, h, S2, &|k2, w| {
        app2(k2, op, inv_a, w)
    });

    // r4 : op inv_a (op a c) = op (op inv_a a) c  (symm assoc inv_a a c)
    let op_invaa_c = app2(k, op, op_invaa, c);
    let assoc_invaac = {
        let e1 = k.app(assoc, inv_a);
        let e2 = k.app(e1, a);
        k.app(e2, c)
    };
    let r4 = symm_of(k, lg, l1, carrier, op_invaa_c, op_inva_opac, assoc_invaac);

    // r5 : op (op inv_a a) c = op e c  (congr via inv_l_a)
    let op_e_c = app2(k, op, e, c);
    let r5 = congr_arg(k, lg, l1, carrier, op_invaa, e, inv_l_a, S3, &|k2, w| {
        app2(k2, op, w, c)
    });

    // r6 : op e c = c
    let r6 = k.app(ident_l, c);

    let step1 = trans_of(k, lg, l1, carrier, b, op_e_b, op_invaa_b, r0, r1, S4);
    let step2 = trans_of(
        k,
        lg,
        l1,
        carrier,
        b,
        op_invaa_b,
        op_inva_opab,
        step1,
        r2,
        S5,
    );
    let step3 = trans_of(
        k,
        lg,
        l1,
        carrier,
        b,
        op_inva_opab,
        op_inva_opac,
        step2,
        r3,
        S6,
    );
    let step4 = trans_of(
        k,
        lg,
        l1,
        carrier,
        b,
        op_inva_opac,
        op_invaa_c,
        step3,
        r4,
        S1,
    );
    let step5 = trans_of(k, lg, l1, carrier, b, op_invaa_c, op_e_c, step4, r5, S2);
    let result = trans_of(k, lg, l1, carrier, b, op_e_c, c, step5, r6, S3);

    let value = lam_over(k, H_FV, hyp_ty, result);
    let value = lam_over(k, C_FV, carrier, value);
    let value = lam_over(k, B_FV, carrier, value);
    let value = lam_over(k, A_FV, carrier, value);
    let value = lam_over(k, G_FV, ind_ty, value);

    let concl = eq_of(k, lg, l1, carrier, b, c);
    let ty = pi_over(k, H_FV, hyp_ty, concl);
    let ty = pi_over(k, C_FV, carrier, ty);
    let ty = pi_over(k, B_FV, carrier, ty);
    let ty = pi_over(k, A_FV, carrier, ty);
    let ty = pi_over(k, G_FV, ind_ty, ty);

    (ty, value)
}

/// Declares `Alg.mul_left_cancel` at the earliest possible build position
/// (right after [`declare_structures_all`]) and returns its `NameId`. See
/// the module-doc block above this section and ADR-1587 §1.
pub(crate) fn declare_mul_left_cancel_early(
    k: &mut Kernel,
    lg: &LogicPrelude,
    group: &RecordNames,
) -> Result<NameId, KernelError> {
    let l0 = k.level_zero();
    let l1 = k.level_succ(l0);
    let (ty, value) = build_mul_left_cancel_generic(k, lg, l1, group);
    let anon = k.anon();
    let alg = k.name_str(anon, "Alg");
    let name = k.name_str(alg, "mul_left_cancel");
    k.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

// ---------------------------------------------------------------------------
// Field-shape combinators. Each closure computes a field's TYPE from the
// (index-selected) VALUE expressions of the earlier fields, `vals`. Reused
// unchanged for the constructor's own field types (`vals[i]` a fresh fvar)
// and for a selector's motive body (`vals[i]` the i-th earlier selector
// applied to the bound structure variable).
// ---------------------------------------------------------------------------

const V_A: u64 = 9_900;
const V_B: u64 = 9_901;
const V_C: u64 = 9_902;

pub(crate) type Build = Box<dyn Fn(&mut Kernel, &LogicPrelude, LevelId, &[ExprId]) -> ExprId>;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum FieldKind {
    CarrierSort,
    Data,
    Law,
}

pub(crate) struct FieldSpec {
    pub(crate) suffix: &'static str,
    pub(crate) kind: FieldKind,
    pub(crate) build: Build,
}

fn carrier_field() -> FieldSpec {
    FieldSpec {
        suffix: "carrier",
        kind: FieldKind::CarrierSort,
        build: Box::new(|k, _lg, l1, _vals| k.sort(l1)),
    }
}

/// A caller-supplied `α -> α -> α`.
fn binop_field(name: &'static str, carrier_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[carrier_idx];
            let inner = arrow(k, a, a);
            arrow(k, a, inner)
        }),
    }
}

/// A caller-supplied `α -> α`.
fn unop_field(name: &'static str, carrier_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[carrier_idx];
            arrow(k, a, a)
        }),
    }
}

/// A caller-supplied element `: α`.
fn elem_field(name: &'static str, carrier_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Data,
        build: Box::new(move |_k, _lg, _l1, vals| vals[carrier_idx]),
    }
}

/// `forall a b c, op (op a b) c = op a (op b c)`.
fn assoc_field(name: &'static str, carrier_idx: usize, op_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let op = vals[op_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let vc = k.fvar(V_C);
            let ab = app2(k, op, va, vb);
            let lhs = app2(k, op, ab, vc);
            let bc = app2(k, op, vb, vc);
            let rhs = app2(k, op, va, bc);
            let body = eq_of(k, lg, l1, a_ty, lhs, rhs);
            let t = pi_over(k, V_C, a_ty, body);
            let t = pi_over(k, V_B, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b, op a b = op b a`.
fn comm_field(name: &'static str, carrier_idx: usize, op_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let op = vals[op_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let lhs = app2(k, op, va, vb);
            let rhs = app2(k, op, vb, va);
            let body = eq_of(k, lg, l1, a_ty, lhs, rhs);
            let t = pi_over(k, V_B, a_ty, body);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a, op unit a = a`.
fn unit_left_field(
    name: &'static str,
    carrier_idx: usize,
    op_idx: usize,
    unit_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let op = vals[op_idx];
            let unit = vals[unit_idx];
            let va = k.fvar(V_A);
            let lhs = app2(k, op, unit, va);
            let body = eq_of(k, lg, l1, a_ty, lhs, va);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a, op a unit = a`.
fn unit_right_field(
    name: &'static str,
    carrier_idx: usize,
    op_idx: usize,
    unit_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let op = vals[op_idx];
            let unit = vals[unit_idx];
            let va = k.fvar(V_A);
            let lhs = app2(k, op, va, unit);
            let body = eq_of(k, lg, l1, a_ty, lhs, va);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a, op (inv a) a = e`.
fn inv_left_field(
    name: &'static str,
    carrier_idx: usize,
    op_idx: usize,
    inv_idx: usize,
    e_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let op = vals[op_idx];
            let inv = vals[inv_idx];
            let e = vals[e_idx];
            let va = k.fvar(V_A);
            let ia = k.app(inv, va);
            let lhs = app2(k, op, ia, va);
            let body = eq_of(k, lg, l1, a_ty, lhs, e);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a, op a (inv a) = e`.
fn inv_right_field(
    name: &'static str,
    carrier_idx: usize,
    op_idx: usize,
    inv_idx: usize,
    e_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let op = vals[op_idx];
            let inv = vals[inv_idx];
            let e = vals[e_idx];
            let va = k.fvar(V_A);
            let ia = k.app(inv, va);
            let lhs = app2(k, op, va, ia);
            let body = eq_of(k, lg, l1, a_ty, lhs, e);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a b c, mul a (add b c) = add (mul a b) (mul a c)`.
fn distrib_left_field(
    name: &'static str,
    carrier_idx: usize,
    add_idx: usize,
    mul_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let add = vals[add_idx];
            let mul = vals[mul_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let vc = k.fvar(V_C);
            let bc = app2(k, add, vb, vc);
            let lhs = app2(k, mul, va, bc);
            let ab = app2(k, mul, va, vb);
            let ac = app2(k, mul, va, vc);
            let rhs = app2(k, add, ab, ac);
            let body = eq_of(k, lg, l1, a_ty, lhs, rhs);
            let t = pi_over(k, V_C, a_ty, body);
            let t = pi_over(k, V_B, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b c, mul (add a b) c = add (mul a c) (mul b c)`.
fn distrib_right_field(
    name: &'static str,
    carrier_idx: usize,
    add_idx: usize,
    mul_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let add = vals[add_idx];
            let mul = vals[mul_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let vc = k.fvar(V_C);
            let ab = app2(k, add, va, vb);
            let lhs = app2(k, mul, ab, vc);
            let ac = app2(k, mul, va, vc);
            let bc = app2(k, mul, vb, vc);
            let rhs = app2(k, add, ac, bc);
            let body = eq_of(k, lg, l1, a_ty, lhs, rhs);
            let t = pi_over(k, V_C, a_ty, body);
            let t = pi_over(k, V_B, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a, add a (neg a) = zero`.
fn neg_add_field(
    name: &'static str,
    carrier_idx: usize,
    add_idx: usize,
    neg_idx: usize,
    zero_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let add = vals[add_idx];
            let neg = vals[neg_idx];
            let zero = vals[zero_idx];
            let va = k.fvar(V_A);
            let na = k.app(neg, va);
            let lhs = app2(k, add, va, na);
            let body = eq_of(k, lg, l1, a_ty, lhs, zero);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `Eq x y -> False` (the unfolding of `Not (Eq x y)`).
fn not_eq_field(name: &'static str, carrier_idx: usize, x_idx: usize, y_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let x = vals[x_idx];
            let y = vals[y_idx];
            let eq = eq_of(k, lg, l1, a_ty, x, y);
            let false_ = k.const_(lg.false_, vec![]);
            arrow(k, eq, false_)
        }),
    }
}

/// `forall a, (Eq a zero -> False) -> mul a (inv a) = one`.
fn cond_inv_field(
    name: &'static str,
    carrier_idx: usize,
    mul_idx: usize,
    one_idx: usize,
    zero_idx: usize,
    inv_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let mul = vals[mul_idx];
            let one = vals[one_idx];
            let zero = vals[zero_idx];
            let inv = vals[inv_idx];
            let va = k.fvar(V_A);
            let is_zero = eq_of(k, lg, l1, a_ty, va, zero);
            let false_ = k.const_(lg.false_, vec![]);
            let hyp = arrow(k, is_zero, false_);
            let ia = k.app(inv, va);
            let lhs = app2(k, mul, va, ia);
            let concl = eq_of(k, lg, l1, a_ty, lhs, one);
            let body = arrow(k, hyp, concl);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

// ---------------------------------------------------------------------------
// ADR-1584: `OrderedRing` field specs — a `Ring` (restated, no inheritance,
// same "third copy" pattern the rest of the spine uses) plus a relation
// `le : alpha -> alpha -> Prop` and five order laws.
// ---------------------------------------------------------------------------

/// A caller-supplied `α -> α -> Prop`.
pub(crate) fn rel_field(name: &'static str, carrier_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Data,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a = vals[carrier_idx];
            let l0 = k.level_zero();
            let prop = k.sort(l0);
            let inner = arrow(k, a, prop);
            arrow(k, a, inner)
        }),
    }
}

/// `forall a, le a a`.
pub(crate) fn le_refl_field(name: &'static str, carrier_idx: usize, le_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let le = vals[le_idx];
            let va = k.fvar(V_A);
            let body = app2(k, le, va, va);
            pi_over(k, V_A, a_ty, body)
        }),
    }
}

/// `forall a b c, le a b -> le b c -> le a c`.
pub(crate) fn le_trans_field(name: &'static str, carrier_idx: usize, le_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let le = vals[le_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let vc = k.fvar(V_C);
            let hab = app2(k, le, va, vb);
            let hbc = app2(k, le, vb, vc);
            let hac = app2(k, le, va, vc);
            let inner = arrow(k, hbc, hac);
            let inner2 = arrow(k, hab, inner);
            let t = pi_over(k, V_C, a_ty, inner2);
            let t = pi_over(k, V_B, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b, le a b -> le b a -> a = b`.
fn le_antisymm_field(name: &'static str, carrier_idx: usize, le_idx: usize) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, lg, l1, vals| {
            let a_ty = vals[carrier_idx];
            let le = vals[le_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let hab = app2(k, le, va, vb);
            let hba = app2(k, le, vb, va);
            let eq = eq_of(k, lg, l1, a_ty, va, vb);
            let inner = arrow(k, hba, eq);
            let inner2 = arrow(k, hab, inner);
            let t = pi_over(k, V_B, a_ty, inner2);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b c, le a b -> le (add c a) (add c b)`.
pub(crate) fn add_le_add_left_field(
    name: &'static str,
    carrier_idx: usize,
    add_idx: usize,
    le_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let add = vals[add_idx];
            let le = vals[le_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let vc = k.fvar(V_C);
            let hab = app2(k, le, va, vb);
            let ca = app2(k, add, vc, va);
            let cb = app2(k, add, vc, vb);
            let concl = app2(k, le, ca, cb);
            let inner = arrow(k, hab, concl);
            let t = pi_over(k, V_C, a_ty, inner);
            let t = pi_over(k, V_B, a_ty, t);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

/// `forall a b, le zero a -> le zero b -> le zero (mul a b)`.
pub(crate) fn mul_nonneg_field(
    name: &'static str,
    carrier_idx: usize,
    mul_idx: usize,
    zero_idx: usize,
    le_idx: usize,
) -> FieldSpec {
    FieldSpec {
        suffix: name,
        kind: FieldKind::Law,
        build: Box::new(move |k, _lg, _l1, vals| {
            let a_ty = vals[carrier_idx];
            let mul = vals[mul_idx];
            let zero = vals[zero_idx];
            let le = vals[le_idx];
            let va = k.fvar(V_A);
            let vb = k.fvar(V_B);
            let h1 = app2(k, le, zero, va);
            let h2 = app2(k, le, zero, vb);
            let mul_ab = app2(k, mul, va, vb);
            let concl = app2(k, le, zero, mul_ab);
            let inner = arrow(k, h2, concl);
            let inner2 = arrow(k, h1, inner);
            let t = pi_over(k, V_B, a_ty, inner2);
            pi_over(k, V_A, a_ty, t)
        }),
    }
}

// ---------------------------------------------------------------------------
// The generic record builder.
// ---------------------------------------------------------------------------

/// The largest field count among the records this spine and its `AlgS`
/// twin declare (`AlgS.OrderedRing`, ADR-1592: `AlgS.CommRing`'s 23 fields
/// plus 7 order fields = 30), with headroom -- fixed so [`RecordNames`]
/// (and therefore [`StructuresNames`] and `NatPrelude`) stays `Copy`,
/// matching every other prelude handle in this crate.
pub const MAX_FIELDS: usize = 32;

/// One selector per field, in declaration order, plus the constructor/
/// recursor names. `Copy` via a fixed-size array (`selectors[len..]` is
/// unused padding); index a field with [`RecordNames::sel`], never by
/// reading `selectors` past `len`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecordNames {
    pub ind: NameId,
    pub mk: NameId,
    pub rec: NameId,
    pub(crate) selectors: [NameId; MAX_FIELDS],
    pub(crate) len: usize,
}

impl RecordNames {
    pub fn sel(&self, i: usize) -> NameId {
        assert!(
            i < self.len,
            "field index {i} out of range (len {})",
            self.len
        );
        self.selectors[i]
    }

    pub fn field_count(&self) -> usize {
        self.len
    }
}

pub(crate) const CTOR_FVAR_BASE: u64 = 10_000;
pub(crate) const SELECTOR_S_FV: u64 = 10_900;

/// Declare one record: the inductive at `Sort 2` (with a `Sort 1`-refused
/// universe control run first), then every field's selector by large
/// elimination.
pub(crate) fn declare_record(
    k: &mut Kernel,
    lg: &LogicPrelude,
    l0: LevelId,
    l1: LevelId,
    l2: LevelId,
    ind: NameId,
    specs: &[FieldSpec],
) -> Result<RecordNames, KernelError> {
    let mk = k.name_str(ind, "mk");
    let rec = k.name_str(ind, "rec");

    // 1. Build the constructor field types against fresh fvars.
    let fvars: Vec<u64> = (0..specs.len())
        .map(|i| CTOR_FVAR_BASE + i as u64)
        .collect();
    let mut ctor_fields: Vec<(u64, ExprId)> = Vec::with_capacity(specs.len());
    let mut vals: Vec<ExprId> = Vec::with_capacity(specs.len());
    for (i, spec) in specs.iter().enumerate() {
        let ty = (spec.build)(k, lg, l1, &vals);
        ctor_fields.push((fvars[i], ty));
        vals.push(k.fvar(fvars[i]));
    }

    // Universe control: the SAME field list at `Sort 1` must be refused.
    {
        let ctl_ind = k.name_str(ind, "sort1Control");
        let ctl_mk = k.name_str(ctl_ind, "mk");
        let sort1 = k.sort(l1);
        let ctl_const = k.const_(ctl_ind, vec![]);
        let ctl_ctor = close_pi(k, &ctor_fields, ctl_const);
        assert!(
            k.add_inductive(ctl_ind, &[], 0, sort1, &[(ctl_mk, ctl_ctor)])
                .is_err(),
            "ADR-1578 universe control failed: {ctl_ind:?} (a Sort-1-carrying \
             record) was ACCEPTED at Sort 1 -- the ADR-1495 \
             ConstructorFieldUniverseTooBig guard did not fire"
        );
    }

    // 2. Admit the real inductive at Sort 2.
    let sort2 = k.sort(l2);
    let ind_const = k.const_(ind, vec![]);
    let ctor_ty = close_pi(k, &ctor_fields, ind_const);
    k.add_inductive(ind, &[], 0, sort2, &[(mk, ctor_ty)])?;

    // 3. Selectors, one per field, threading each already-declared selector
    //    into the next field's motive via the same `build` closures.
    let ind_ty = k.const_(ind, vec![]);
    let mut sel_names: Vec<NameId> = Vec::with_capacity(specs.len());
    for (i, spec) in specs.iter().enumerate() {
        let sel_name = k.name_str(ind, spec.suffix);
        let motive_lvl = match spec.kind {
            FieldKind::CarrierSort => l2,
            FieldKind::Data => l1,
            FieldKind::Law => l0,
        };
        let sel_names_so_far = sel_names.clone();
        let build = &spec.build;
        let motive_body = |k2: &mut Kernel, s: ExprId| {
            let mut vs: Vec<ExprId> = Vec::with_capacity(sel_names_so_far.len());
            for name in &sel_names_so_far {
                let c = k2.const_(*name, vec![]);
                vs.push(k2.app(c, s));
            }
            build(k2, lg, l1, &vs)
        };
        declare_selector(
            k,
            ind_ty,
            rec,
            sel_name,
            motive_lvl,
            SELECTOR_S_FV,
            &motive_body,
            i,
            &ctor_fields,
        )?;
        sel_names.push(sel_name);
    }

    assert!(
        sel_names.len() <= MAX_FIELDS,
        "record {:?} has {} fields, over MAX_FIELDS={MAX_FIELDS}",
        ind,
        sel_names.len()
    );
    // `mk` fills unused padding slots -- a valid, harmless `NameId` that is
    // never read (every access goes through `sel(i)`, which asserts `i <
    // len`).
    let mut selectors = [mk; MAX_FIELDS];
    for (i, n) in sel_names.iter().enumerate() {
        selectors[i] = *n;
    }
    Ok(RecordNames {
        ind,
        mk,
        rec,
        selectors,
        len: sel_names.len(),
    })
}

/// One field selector, built out of the auto-generated recursor:
/// `name : Pi (s : Ind), motive s := fun s => Ind.rec.{motive_lvl} motive
/// (fun fields... => field_i) s`. `ctor_fields` is the SAME `(fvar, type)`
/// list the constructor was built from — the minor premise closes over all
/// of them (in the same order the constructor declares them) and returns the
/// one at `index`.
#[allow(clippy::too_many_arguments)]
pub(crate) fn declare_selector(
    k: &mut Kernel,
    ind_ty: ExprId,
    rec: NameId,
    name: NameId,
    motive_lvl: LevelId,
    s_fv: u64,
    motive_body: &dyn Fn(&mut Kernel, ExprId) -> ExprId,
    index: usize,
    ctor_fields: &[(u64, ExprId)],
) -> Result<(), KernelError> {
    let s = k.fvar(s_fv);
    let mb = motive_body(k, s);
    let motive = lam_over(k, s_fv, ind_ty, mb);

    let picked = k.fvar(ctor_fields[index].0);
    let minor = close_lam(k, ctor_fields, picked);

    let rec_c = k.const_(rec, vec![motive_lvl]);
    let applied = {
        let e = k.app(rec_c, motive);
        let e = k.app(e, minor);
        let s2 = k.fvar(s_fv);
        k.app(e, s2)
    };
    let value = lam_over(k, s_fv, ind_ty, applied);

    let s3 = k.fvar(s_fv);
    let result = motive_body(k, s3);
    let ty = pi_over(k, s_fv, ind_ty, result);

    k.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

// ---------------------------------------------------------------------------
// The ten field lists (ADR-1578's spine).
// ---------------------------------------------------------------------------

fn magma_fields() -> Vec<FieldSpec> {
    vec![carrier_field(), binop_field("op", 0)]
}

fn semigroup_fields() -> Vec<FieldSpec> {
    vec![
        carrier_field(),
        binop_field("op", 0),
        assoc_field("assoc", 0, 1),
    ]
}

fn monoid_fields() -> Vec<FieldSpec> {
    vec![
        carrier_field(),
        binop_field("op", 0),
        elem_field("e", 0),
        assoc_field("assoc", 0, 1),
        unit_left_field("identL", 0, 1, 2),
        unit_right_field("identR", 0, 1, 2),
    ]
}

fn comm_monoid_fields() -> Vec<FieldSpec> {
    let mut f = monoid_fields();
    f.push(comm_field("comm", 0, 1));
    f
}

fn group_fields() -> Vec<FieldSpec> {
    vec![
        carrier_field(),
        binop_field("op", 0),
        elem_field("e", 0),
        unop_field("inv", 0),
        assoc_field("assoc", 0, 1),
        unit_left_field("identL", 0, 1, 2),
        unit_right_field("identR", 0, 1, 2),
        inv_left_field("invL", 0, 1, 3, 2),
        inv_right_field("invR", 0, 1, 3, 2),
    ]
}

fn comm_group_fields() -> Vec<FieldSpec> {
    let mut f = group_fields();
    f.push(comm_field("comm", 0, 1));
    f
}

fn semiring_fields() -> Vec<FieldSpec> {
    vec![
        carrier_field(),
        elem_field("zero", 0),
        elem_field("one", 0),
        binop_field("add", 0),
        binop_field("mul", 0),
        assoc_field("addAssoc", 0, 3),
        comm_field("addComm", 0, 3),
        unit_right_field("addZero", 0, 3, 1),
        assoc_field("mulAssoc", 0, 4),
        unit_left_field("mulOneL", 0, 4, 2),
        unit_right_field("mulOneR", 0, 4, 2),
        distrib_left_field("distribL", 0, 3, 4),
        distrib_right_field("distribR", 0, 3, 4),
    ]
}

fn ring_fields() -> Vec<FieldSpec> {
    let mut f = semiring_fields();
    f.push(unop_field("neg", 0));
    f.push(neg_add_field("negAdd", 0, 3, 13, 1));
    f
}

fn comm_ring_fields() -> Vec<FieldSpec> {
    let mut f = ring_fields();
    f.push(comm_field("mulComm", 0, 4));
    f
}

fn field_fields() -> Vec<FieldSpec> {
    let mut f = comm_ring_fields();
    f.push(unop_field("inv", 0));
    f.push(not_eq_field("oneNeZero", 0, 2, 1));
    f.push(cond_inv_field("mulInv", 0, 4, 2, 1, 16));
    f
}

/// ADR-1584: `Ring`'s 15 fields, restated (no inheritance, same pattern
/// every later record in the spine already uses), plus `le` and five order
/// laws.
fn ordered_ring_fields() -> Vec<FieldSpec> {
    use idx::ring::{ADD, CARRIER, MUL, ZERO};
    let mut f = ring_fields();
    f.push(rel_field("le", CARRIER));
    let le_idx = f.len() - 1;
    f.push(le_refl_field("le_refl", CARRIER, le_idx));
    f.push(le_trans_field("le_trans", CARRIER, le_idx));
    f.push(le_antisymm_field("le_antisymm", CARRIER, le_idx));
    f.push(add_le_add_left_field(
        "add_le_add_left",
        CARRIER,
        ADD,
        le_idx,
    ));
    f.push(mul_nonneg_field("mul_nonneg", CARRIER, MUL, ZERO, le_idx));
    f
}

/// Field-index constants, one module per record, so a consumer never counts
/// positions by hand. Mirrors the `*_fields()` functions above exactly --
/// keep both in sync if either changes. A complete reference table:
/// `#[allow(dead_code, unused_imports)]` because not every record's every
/// constant (or re-export, for the ones a later record inherits textually,
/// e.g. `comm_group`'s from `group`) has a consumer yet.
#[allow(dead_code, unused_imports)]
pub mod idx {
    pub mod magma {
        pub const CARRIER: usize = 0;
        pub const OP: usize = 1;
    }
    pub mod semigroup {
        pub const CARRIER: usize = 0;
        pub const OP: usize = 1;
        pub const ASSOC: usize = 2;
    }
    pub mod monoid {
        pub const CARRIER: usize = 0;
        pub const OP: usize = 1;
        pub const E: usize = 2;
        pub const ASSOC: usize = 3;
        pub const IDENT_L: usize = 4;
        pub const IDENT_R: usize = 5;
    }
    pub mod comm_monoid {
        pub use super::monoid::{ASSOC, CARRIER, E, IDENT_L, IDENT_R, OP};
        pub const COMM: usize = 6;
    }
    pub mod group {
        pub const CARRIER: usize = 0;
        pub const OP: usize = 1;
        pub const E: usize = 2;
        pub const INV: usize = 3;
        pub const ASSOC: usize = 4;
        pub const IDENT_L: usize = 5;
        pub const IDENT_R: usize = 6;
        pub const INV_L: usize = 7;
        pub const INV_R: usize = 8;
    }
    pub mod comm_group {
        pub use super::group::{ASSOC, CARRIER, E, IDENT_L, IDENT_R, INV, INV_L, INV_R, OP};
        pub const COMM: usize = 9;
    }
    pub mod semiring {
        pub const CARRIER: usize = 0;
        pub const ZERO: usize = 1;
        pub const ONE: usize = 2;
        pub const ADD: usize = 3;
        pub const MUL: usize = 4;
        pub const ADD_ASSOC: usize = 5;
        pub const ADD_COMM: usize = 6;
        pub const ADD_ZERO: usize = 7;
        pub const MUL_ASSOC: usize = 8;
        pub const MUL_ONE_L: usize = 9;
        pub const MUL_ONE_R: usize = 10;
        pub const DISTRIB_L: usize = 11;
        pub const DISTRIB_R: usize = 12;
    }
    pub mod ring {
        pub use super::semiring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC,
            MUL_ONE_L, MUL_ONE_R, ONE, ZERO,
        };
        pub const NEG: usize = 13;
        pub const NEG_ADD: usize = 14;
    }
    pub mod comm_ring {
        pub use super::ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC,
            MUL_ONE_L, MUL_ONE_R, NEG, NEG_ADD, ONE, ZERO,
        };
        pub const MUL_COMM: usize = 15;
    }
    pub mod field {
        pub use super::comm_ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC,
            MUL_COMM, MUL_ONE_L, MUL_ONE_R, NEG, NEG_ADD, ONE, ZERO,
        };
        pub const INV: usize = 16;
        pub const ONE_NE_ZERO: usize = 17;
        pub const MUL_INV: usize = 18;
    }
    /// ADR-1584: `Ring`'s 15 fields (re-exported) plus `le` and five order
    /// laws.
    pub mod ordered_ring {
        pub use super::ring::{
            ADD, ADD_ASSOC, ADD_COMM, ADD_ZERO, CARRIER, DISTRIB_L, DISTRIB_R, MUL, MUL_ASSOC,
            MUL_ONE_L, MUL_ONE_R, NEG, NEG_ADD, ONE, ZERO,
        };
        pub const LE: usize = 15;
        pub const LE_REFL: usize = 16;
        pub const LE_TRANS: usize = 17;
        pub const LE_ANTISYMM: usize = 18;
        pub const ADD_LE_ADD_LEFT: usize = 19;
        pub const MUL_NONNEG: usize = 20;
    }
}

// ---------------------------------------------------------------------------
// Assembly: names, then declarations.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuresPrelude {
    pub alg: NameId,
    pub magma: NameId,
    pub semigroup: NameId,
    pub monoid: NameId,
    pub comm_monoid: NameId,
    pub group: NameId,
    pub comm_group: NameId,
    pub semiring: NameId,
    pub ring: NameId,
    pub comm_ring: NameId,
    pub field: NameId,
    /// ADR-1584.
    pub ordered_ring: NameId,
}

/// Intern the ten record names (and nothing else) under a fresh `Alg` root,
/// deliberately not under `Nat` — see the module doc.
pub(crate) fn intern_structures_names(kernel: &mut Kernel) -> StructuresPrelude {
    let anon = kernel.anon();
    let alg = kernel.name_str(anon, "Alg");
    StructuresPrelude {
        alg,
        magma: kernel.name_str(alg, "Magma"),
        semigroup: kernel.name_str(alg, "Semigroup"),
        monoid: kernel.name_str(alg, "Monoid"),
        comm_monoid: kernel.name_str(alg, "CommMonoid"),
        group: kernel.name_str(alg, "Group"),
        comm_group: kernel.name_str(alg, "CommGroup"),
        semiring: kernel.name_str(alg, "Semiring"),
        ring: kernel.name_str(alg, "Ring"),
        comm_ring: kernel.name_str(alg, "CommRing"),
        field: kernel.name_str(alg, "Field"),
        ordered_ring: kernel.name_str(alg, "OrderedRing"),
    }
}

/// The declared records, keyed by [`StructuresPrelude`]'s names, holding
/// each record's selector names in field-declaration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StructuresNames {
    pub magma: RecordNames,
    pub semigroup: RecordNames,
    pub monoid: RecordNames,
    pub comm_monoid: RecordNames,
    pub group: RecordNames,
    pub comm_group: RecordNames,
    pub semiring: RecordNames,
    pub ring: RecordNames,
    pub comm_ring: RecordNames,
    pub field: RecordNames,
    /// ADR-1584.
    pub ordered_ring: RecordNames,
}

/// Declare all ten records (`add_inductive` + selectors, each with a
/// `Sort 1`-refused universe control run first).
pub(crate) fn declare_structures_all(
    kernel: &mut Kernel,
    p: &StructuresPrelude,
    logic: &LogicPrelude,
) -> Result<StructuresNames, KernelError> {
    let l0 = kernel.level_zero();
    let l1 = kernel.level_succ(l0);
    let l2 = kernel.level_succ(l1);

    let magma = declare_record(kernel, logic, l0, l1, l2, p.magma, &magma_fields())?;
    let semigroup = declare_record(kernel, logic, l0, l1, l2, p.semigroup, &semigroup_fields())?;
    let monoid = declare_record(kernel, logic, l0, l1, l2, p.monoid, &monoid_fields())?;
    let comm_monoid = declare_record(
        kernel,
        logic,
        l0,
        l1,
        l2,
        p.comm_monoid,
        &comm_monoid_fields(),
    )?;
    let group = declare_record(kernel, logic, l0, l1, l2, p.group, &group_fields())?;
    let comm_group = declare_record(
        kernel,
        logic,
        l0,
        l1,
        l2,
        p.comm_group,
        &comm_group_fields(),
    )?;
    let semiring = declare_record(kernel, logic, l0, l1, l2, p.semiring, &semiring_fields())?;
    let ring = declare_record(kernel, logic, l0, l1, l2, p.ring, &ring_fields())?;
    let comm_ring = declare_record(kernel, logic, l0, l1, l2, p.comm_ring, &comm_ring_fields())?;
    let field = declare_record(kernel, logic, l0, l1, l2, p.field, &field_fields())?;
    let ordered_ring = declare_record(
        kernel,
        logic,
        l0,
        l1,
        l2,
        p.ordered_ring,
        &ordered_ring_fields(),
    )?;

    Ok(StructuresNames {
        magma,
        semigroup,
        monoid,
        comm_monoid,
        group,
        comm_group,
        semiring,
        ring,
        comm_ring,
        field,
        ordered_ring,
    })
}

#[cfg(test)]
mod structures_tests {
    use super::*;
    use crate::build_logic_prelude;

    /// The universe guard is exercised for EVERY record (not asserted, since
    /// [`declare_record`] panics if a `Sort 1` control is ever accepted); this
    /// test additionally pins the field counts so a spec-list edit that drops
    /// a field is caught here rather than only downstream.
    #[test]
    fn every_record_admits_at_sort2_with_the_expected_field_count() {
        let mut k = Kernel::new();
        let logic = build_logic_prelude(&mut k).expect("logic prelude must build");
        let names = intern_structures_names(&mut k);
        let records = declare_structures_all(&mut k, &names, &logic).expect("spine must build");

        let expected: &[(&str, usize)] = &[
            ("Magma", 2),
            ("Semigroup", 3),
            ("Monoid", 6),
            ("CommMonoid", 7),
            ("Group", 9),
            ("CommGroup", 10),
            ("Semiring", 13),
            ("Ring", 15),
            ("CommRing", 16),
            ("Field", 19),
            ("OrderedRing", 21),
        ];
        let actual = [
            records.magma.field_count(),
            records.semigroup.field_count(),
            records.monoid.field_count(),
            records.comm_monoid.field_count(),
            records.group.field_count(),
            records.comm_group.field_count(),
            records.semiring.field_count(),
            records.ring.field_count(),
            records.comm_ring.field_count(),
            records.field.field_count(),
            records.ordered_ring.field_count(),
        ];
        for (i, (name, want)) in expected.iter().enumerate() {
            assert_eq!(actual[i], *want, "{name} field count");
        }

        // Every record's inductive, recursor, and every selector must
        // actually be present in the environment (the DECLARATION exists,
        // not merely that no error was returned).
        for rn in [
            &records.magma,
            &records.semigroup,
            &records.monoid,
            &records.comm_monoid,
            &records.group,
            &records.comm_group,
            &records.semiring,
            &records.ring,
            &records.comm_ring,
            &records.field,
            &records.ordered_ring,
        ] {
            assert!(k.environment().get(rn.ind).is_some(), "inductive missing");
            assert!(k.environment().get(rn.rec).is_some(), "recursor missing");
            for i in 0..rn.field_count() {
                assert!(
                    k.environment().get(rn.sel(i)).is_some(),
                    "selector {i} missing"
                );
            }
        }
    }

    /// Negative control for the universe guard itself: a record with NO
    /// `Sort 1`-carrying field (an all-`Prop` shape) is legitimately
    /// admissible at `Sort 1`, so `declare_record`'s blanket "Sort 1 must be
    /// refused" behaviour is specific to carrying a carrier field, not a
    /// property of `add_inductive` in general -- mirroring
    /// `inductive_universe_probe.rs`'s own positivity control.
    #[test]
    fn a_record_with_no_carrier_field_is_legitimately_accepted_at_sort1() {
        let mut k = Kernel::new();
        let _logic = build_logic_prelude(&mut k).expect("logic prelude must build");
        let anon = k.anon();
        let ind = k.name_str(anon, "AllPropCtl");
        let mk = k.name_str(ind, "mk");
        let l0 = k.level_zero();
        let sort0 = k.sort(l0);
        let ind_const = k.const_(ind, vec![]);
        let ctor_ty = arrow(&mut k, sort0, ind_const);
        assert!(
            k.add_inductive(ind, &[], 0, sort0, &[(mk, ctor_ty)])
                .is_ok(),
            "a Prop-only field carries no Sort-1 payload, so Sort 1 is legitimate"
        );
    }
}
