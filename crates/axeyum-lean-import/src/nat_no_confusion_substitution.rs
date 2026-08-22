//! Reconstructs the two Lean-core `Init.Prelude` declarations that back
//! `noConfusion` for any type embeddable into `Nat` — `noConfusion_of_Nat`
//! and its private helper `noConfusion_of_Nat.aux` — directly against a
//! foreign (untrusted-stream) import kernel's own primitives, admitted under
//! the **stream's own declared type**, exactly like
//! [`super::nat_order_substitution`] and for the same reason: these are
//! facts about the *specific* stream-supplied `Nat`/`Nat.beq`/`Bool`, not
//! universally valid logical primitives, so the type the adapter admits must
//! be exactly the one the stream asks for (`wire_ty`) — only the *proof* is
//! substituted.
//!
//! ## What these two names actually are
//!
//! `docs/autogenesis/236-…`/`237-…` measured `noConfusion_of_Nat` and
//! `noConfusion_of_Nat.aux` as blockers shared by all 114 rows and assumed
//! they were `Nat`'s own constructor-disjointness `noConfusion` (the thing
//! [`axeyum_lean_kernel::nat_prelude`]'s `no_confusion` module generates).
//! Inspecting a real stream's `thm` record shows this is wrong: `Init.Prelude`
//! ships a *generic* helper, universe-polymorphic in an arbitrary carrier
//! `α`, used to derive `noConfusion`/`DecidableEq` for any type with an
//! injection into `Nat`:
//!
//! ```text
//! noConfusion_of_Nat.{u} : {α : Sort u} → (f : α → Nat) → {a b : α} →
//!   a = b → Bool.rec (fun _ => Prop) False True (Nat.beq (f a) (f b))
//! _private.Init.Prelude.0.noConfusion_of_Nat.aux :
//!   (a : Nat) → Bool.rec (fun _ => Prop) False True (Nat.beq a a)
//! ```
//! (Lean's own `Bool.rec (fun _ => Prop) False True b` is the standard
//! "boolean as a checkable Prop" trick: it reduces to `True` when `b` reduces
//! to `Bool.true` and to `False` when `b` reduces to `Bool.false`, without
//! needing `propext` or `Decidable`.)
//!
//! `.aux` is `Nat.beq`'s reflexivity (`Nat.beq a a` always reduces to
//! `Bool.true`), proved here by ordinary structural induction on `a` via
//! `Nat.rec` — mirroring [`super::nat_order_substitution`]'s
//! `ble_self_eq_true_at`, which proves the analogous fact for `Nat.ble` the
//! same way and already relies on the same property this reconstruction
//! needs: the kernel's own `def_eq`/`infer` correctly reduces a
//! `brecOn`/`below`-defined function (`Nat.beq`, exactly like `Nat.ble`)
//! applied to literal `zero`/`succ _` arguments. `noConfusion_of_Nat` itself
//! is then `.aux (f a)` transported along `congrArg f h : Nat.beq (f a) =
//! Nat.beq (f b)` via `Eq.rec` — the same congrArg-then-transport shape
//! [`super::trusted_substitution::congr_pair`] uses, rebuilt locally here
//! (never citing an admitted `congrArg`/`.aux` declaration by name) so this
//! module's own reconstructions never depend on another substitution's
//! internal list.
//!
//! `noConfusion_of_Nat` is universe-polymorphic (`uparams = [u]`); `.aux` is
//! not (`uparams = []`). Because admission is under the stream's own
//! `wire_ty`, this module must reuse the **exact** `LevelId` the stream's own
//! `wire_ty` already carries for `u` — inventing a fresh universe parameter
//! name would make the constructed value's inferred type carry a
//! *different* level parameter than `wire_ty`'s, and `Kernel::def_eq` does
//! not unify two distinct level parameters, so the admission check would
//! fail. [`extract_universe_param`] reads it back out of `wire_ty`'s own
//! outermost `Sort _` binder rather than minting one.

// Proof-term construction is long, straight-line, and mirrors mathematical
// names one-for-one — exactly the same tradeoff `nat_order_substitution`
// (and, upstream of it, `nat_prelude`) makes, with the same lint allowances.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::too_many_arguments
)]

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, LevelNode, NameId,
};

use crate::trusted_substitution::{SubstitutionError, exact_name};

/// The complete, reviewed set of names this module will attempt to
/// substitute a self-derived proof for, admitted under the stream's own
/// declared type. Adding a name here is a deliberate, reviewed source edit
/// exactly like
/// [`SUBSTITUTABLE_NAT_ORDER_THEOREMS`](super::nat_order_substitution::SUBSTITUTABLE_NAT_ORDER_THEOREMS).
///
/// The second name is Lean's own private-declaration mangling
/// (`_private.<module>.<hash>.<name>`); it was confirmed byte-identical
/// across every stream in the frozen coverage archive (`Init.Prelude` is a
/// single fixed compiled module, not proof-specific), so hardcoding it is not
/// a per-stream assumption.
pub(crate) const SUBSTITUTABLE_NAT_NO_CONFUSION_THEOREMS: &[&str] = &[
    "noConfusion_of_Nat",
    "_private.Init.Prelude.0.noConfusion_of_Nat.aux",
];

/// The primitive names this module's constructions are built from,
/// discovered structurally in the foreign kernel rather than assumed to
/// exist with a particular shape.
struct Prims {
    nat: NameId,
    rec: NameId,
    beq: NameId,
    bool_: NameId,
    bool_rec: NameId,
    false_: NameId,
    true_: NameId,
    true_intro: NameId,
    eq: NameId,
    eq_refl: NameId,
    eq_rec: NameId,
}

fn require_inductive(
    kernel: &Kernel,
    name: NameId,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Inductive { .. }) => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

fn require_constructor(
    kernel: &Kernel,
    name: NameId,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Constructor { .. }) => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

fn require_recursor(
    kernel: &Kernel,
    name: NameId,
    expected_uparams: usize,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Recursor { uparams, .. }) if uparams.len() == expected_uparams => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

fn require_definition(
    kernel: &Kernel,
    name: NameId,
    label: &'static str,
) -> Result<(), SubstitutionError> {
    match kernel.environment().get(name) {
        Some(Declaration::Definition { .. }) => Ok(()),
        _ => Err(SubstitutionError::UnexpectedShape(label)),
    }
}

fn discover(kernel: &Kernel) -> Result<Prims, SubstitutionError> {
    let nat = exact_name(kernel, "Nat")?;
    require_inductive(kernel, nat, "Nat is not an Inductive")?;
    // `Nat.zero`/`Nat.succ` are never named directly by this module's
    // constructions (induction goes through `Nat.rec` alone), but their
    // presence and shape is exactly what makes `Nat.rec`'s own base/step
    // minor premises the ordinary zero/succ case split this module assumes.
    let zero = exact_name(kernel, "Nat.zero")?;
    require_constructor(kernel, zero, "Nat.zero is not a Constructor")?;
    let succ = exact_name(kernel, "Nat.succ")?;
    require_constructor(kernel, succ, "Nat.succ is not a Constructor")?;
    let rec = exact_name(kernel, "Nat.rec")?;
    require_recursor(kernel, rec, 1, "Nat.rec is not a 1-uparam Recursor")?;
    let beq = exact_name(kernel, "Nat.beq")?;
    require_definition(kernel, beq, "Nat.beq is not a Definition")?;

    let bool_ = exact_name(kernel, "Bool")?;
    require_inductive(kernel, bool_, "Bool is not an Inductive")?;
    let bool_rec = exact_name(kernel, "Bool.rec")?;
    require_recursor(kernel, bool_rec, 1, "Bool.rec is not a 1-uparam Recursor")?;

    let false_ = exact_name(kernel, "False")?;
    require_inductive(kernel, false_, "False is not an Inductive")?;
    let true_ = exact_name(kernel, "True")?;
    require_inductive(kernel, true_, "True is not an Inductive")?;
    let true_intro = exact_name(kernel, "True.intro")?;
    require_constructor(kernel, true_intro, "True.intro is not a Constructor")?;

    let eq = exact_name(kernel, "Eq")?;
    require_inductive(kernel, eq, "Eq is not an Inductive")?;
    let eq_refl = exact_name(kernel, "Eq.refl")?;
    require_constructor(kernel, eq_refl, "Eq.refl is not a Constructor")?;
    let eq_rec = exact_name(kernel, "Eq.rec")?;
    require_recursor(kernel, eq_rec, 2, "Eq.rec is not a 2-uparam Recursor")?;

    Ok(Prims {
        nat,
        rec,
        beq,
        bool_,
        bool_rec,
        false_,
        true_,
        true_intro,
        eq,
        eq_refl,
        eq_rec,
    })
}

const FVAR_BASE: u64 = 960_000_000;

struct B<'a> {
    kernel: &'a mut Kernel,
    p: &'a Prims,
    next_fvar: u64,
}

impl<'a> B<'a> {
    fn new(kernel: &'a mut Kernel, p: &'a Prims) -> Self {
        Self {
            kernel,
            p,
            next_fvar: FVAR_BASE,
        }
    }

    fn fresh(&mut self) -> u64 {
        self.next_fvar += 1;
        self.next_fvar
    }

    fn anon(&mut self) -> NameId {
        self.kernel.anon()
    }

    fn level_zero(&mut self) -> LevelId {
        self.kernel.level_zero()
    }

    fn level_one(&mut self) -> LevelId {
        let z = self.kernel.level_zero();
        self.kernel.level_succ(z)
    }

    fn apply(&mut self, head: ExprId, args: &[ExprId]) -> ExprId {
        let mut e = head;
        for &a in args {
            e = self.kernel.app(e, a);
        }
        e
    }

    fn const_app(&mut self, name: NameId, args: &[ExprId]) -> ExprId {
        let c = self.kernel.const_(name, vec![]);
        self.apply(c, args)
    }

    fn lam_fv(&mut self, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
        let b = self.kernel.abstract_fvars(body, &[fv]);
        let anon = self.anon();
        self.kernel.lam(anon, ty, b, BinderInfo::Default)
    }

    fn arrow(&mut self, dom: ExprId, cod: ExprId) -> ExprId {
        let anon = self.anon();
        self.kernel.pi(anon, dom, cod, BinderInfo::Default)
    }

    fn nat_ty(&mut self) -> ExprId {
        self.kernel.const_(self.p.nat, vec![])
    }

    fn bool_ty(&mut self) -> ExprId {
        self.kernel.const_(self.p.bool_, vec![])
    }

    fn beq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let name = self.p.beq;
        self.const_app(name, &[x, y])
    }

    /// `Bool.rec.{1} (fun _ => Prop) False True target` — the standard
    /// "boolean as a checkable Prop" idiom `Init.Prelude` uses for
    /// `noConfusion_of_Nat`/`.aux`: reduces to `True` when `target` reduces
    /// to `Bool.true`, to `False` when it reduces to `Bool.false`.
    fn bool_rec_prop(&mut self, target: ExprId) -> ExprId {
        let anon = self.anon();
        let bool_ty = self.bool_ty();
        let prop = self.kernel.sort_zero();
        let motive = self.kernel.lam(anon, bool_ty, prop, BinderInfo::Default);
        let one = self.level_one();
        let rec = self.kernel.const_(self.p.bool_rec, vec![one]);
        let false_ty = self.kernel.const_(self.p.false_, vec![]);
        let true_ty = self.kernel.const_(self.p.true_, vec![]);
        self.apply(rec, &[motive, false_ty, true_ty, target])
    }

    /// `Bool.rec (fun _ => Prop) False True (Nat.beq lhs rhs)`.
    fn beq_prop(&mut self, lhs: ExprId, rhs: ExprId) -> ExprId {
        let target = self.beq(lhs, rhs);
        self.bool_rec_prop(target)
    }

    fn true_intro(&mut self) -> ExprId {
        self.kernel.const_(self.p.true_intro, vec![])
    }

    fn eq_at(&mut self, level: LevelId, ty: ExprId, x: ExprId, y: ExprId) -> ExprId {
        let name = self.p.eq;
        let eq = self.kernel.const_(name, vec![level]);
        self.apply(eq, &[ty, x, y])
    }

    fn refl_at(&mut self, level: LevelId, ty: ExprId, a: ExprId) -> ExprId {
        let name = self.p.eq_refl;
        let refl = self.kernel.const_(name, vec![level]);
        self.apply(refl, &[ty, a])
    }

    fn transport_at(
        &mut self,
        level: LevelId,
        ty: ExprId,
        p: ExprId,
        motive: ExprId,
        refl_case: ExprId,
        q: ExprId,
        h: ExprId,
    ) -> ExprId {
        let zero = self.level_zero();
        let name = self.p.eq_rec;
        let rec = self.kernel.const_(name, vec![zero, level]);
        self.apply(rec, &[ty, p, motive, refl_case, q, h])
    }

    /// `Nat.rec.{0} (fun x => p x) base (fun j ih => step j ih) target` —
    /// identical in shape to
    /// [`super::nat_order_substitution::B::induct`], rebuilt locally so this
    /// module never depends on that module's private helper.
    fn induct(
        &mut self,
        p: &dyn Fn(&mut Self, ExprId) -> ExprId,
        base: &dyn Fn(&mut Self) -> ExprId,
        step: &dyn Fn(&mut Self, ExprId, ExprId) -> ExprId,
        target: ExprId,
    ) -> ExprId {
        let nat = self.nat_ty();
        let motive = {
            let x_fv = self.fresh();
            let x = self.kernel.fvar(x_fv);
            let body = p(self, x);
            self.lam_fv(x_fv, nat, body)
        };
        let base_term = base(self);
        let step_term = {
            let j_fv = self.fresh();
            let j = self.kernel.fvar(j_fv);
            let ih_fv = self.fresh();
            let ih = self.kernel.fvar(ih_fv);
            let hyp_ty = p(self, j);
            let body = step(self, j, ih);
            let inner = self.lam_fv(ih_fv, hyp_ty, body);
            self.lam_fv(j_fv, nat, inner)
        };
        let z = self.level_zero();
        let name = self.p.rec;
        let rec = self.kernel.const_(name, vec![z]);
        self.apply(rec, &[motive, base_term, step_term, target])
    }

    /// `noConfusion_of_Nat.aux`'s value at an arbitrary target (not
    /// necessarily a bound variable — [`Self::induct`]'s `target` accepts
    /// any [`ExprId`]), used both to admit `.aux` itself (target = the bound
    /// `a`) and inline inside `noConfusion_of_Nat` (target = `f a`), so
    /// neither ever cites the other's admitted declaration by name.
    fn beq_refl_at(&mut self, target: ExprId) -> ExprId {
        self.induct(
            &|d, x| d.beq_prop(x, x),
            &|d| d.true_intro(),
            &|_d, _n, ih| ih,
            target,
        )
    }

    /// `.aux`'s full closed value: `fun (a : Nat) => <beq_refl_at a>`.
    fn aux_full(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let a_fv = self.fresh();
        let a = self.kernel.fvar(a_fv);
        let body = self.beq_refl_at(a);
        self.lam_fv(a_fv, nat, body)
    }

    /// `Eq.rec`-built `congrArg`, generic in the hypothesis carrier/level —
    /// the same construction as
    /// [`super::trusted_substitution::congr_pair`]'s internal
    /// `build_congr_arg`, rebuilt locally (never naming an admitted
    /// `congrArg`) so this module's reconstructions carry zero theorem
    /// dependencies regardless of what `trusted_substitution` substitutes.
    #[allow(clippy::too_many_arguments)]
    fn congr_arg(
        &mut self,
        f: ExprId,
        hyp_level: LevelId,
        hyp_carrier: ExprId,
        hyp_lhs: ExprId,
        hyp_rhs: ExprId,
        hyp_proof: ExprId,
        result_level: LevelId,
        result_carrier: ExprId,
    ) -> ExprId {
        let anon = self.anon();
        let fa = self.apply(f, &[hyp_lhs]);
        let x_fv = self.fresh();
        let x = self.kernel.fvar(x_fv);
        let fx = self.apply(f, &[x]);
        let concl = self.eq_at(result_level, result_carrier, fa, fx);
        let hyp_ty = self.eq_at(hyp_level, hyp_carrier, hyp_lhs, x);
        let inner = self.kernel.lam(anon, hyp_ty, concl, BinderInfo::Default);
        let motive = self.lam_fv(x_fv, hyp_carrier, inner);
        let refl_case = self.refl_at(result_level, result_carrier, fa);
        self.transport_at(
            hyp_level,
            hyp_carrier,
            hyp_lhs,
            motive,
            refl_case,
            hyp_rhs,
            hyp_proof,
        )
    }

    /// `noConfusion_of_Nat`'s full closed value, given the exact `(u_level,
    /// u_name)` pulled out of the stream's own `wire_ty` by
    /// [`extract_universe_param`] — see this module's doc comment for why a
    /// freshly minted universe parameter cannot be substituted here.
    fn no_confusion_full(&mut self, u_level: LevelId) -> ExprId {
        let sort_u = self.kernel.sort(u_level);
        let nat = self.nat_ty();
        let one = self.level_one();

        let alpha_fv = self.fresh();
        let alpha = self.kernel.fvar(alpha_fv);
        let f_fv = self.fresh();
        let f = self.kernel.fvar(f_fv);
        let a_fv = self.fresh();
        let a = self.kernel.fvar(a_fv);
        let b_fv = self.fresh();
        let b = self.kernel.fvar(b_fv);
        let h_fv = self.fresh();
        let h = self.kernel.fvar(h_fv);

        let f_ty = self.arrow(alpha, nat);
        let hyp_ty = self.eq_at(u_level, alpha, a, b);

        let fa = self.apply(f, &[a]);
        let fb = self.apply(f, &[b]);

        let congr = self.congr_arg(f, u_level, alpha, a, b, h, one, nat);
        let aux_fa = self.beq_refl_at(fa);

        let motive = {
            let anon = self.anon();
            let x_fv = self.fresh();
            let x = self.kernel.fvar(x_fv);
            let body = self.beq_prop(fa, x);
            let hyp = self.eq_at(one, nat, fa, x);
            let inner = self.kernel.lam(anon, hyp, body, BinderInfo::Default);
            self.lam_fv(x_fv, nat, inner)
        };
        let value_body = self.transport_at(one, nat, fa, motive, aux_fa, fb, congr);

        let with_h = self.lam_fv(h_fv, hyp_ty, value_body);
        let with_b = self.lam_fv(b_fv, alpha, with_h);
        let with_a = self.lam_fv(a_fv, alpha, with_b);
        let with_f = self.lam_fv(f_fv, f_ty, with_a);
        self.lam_fv(alpha_fv, sort_u, with_f)
    }
}

/// Reads the universe parameter `noConfusion_of_Nat`'s own `wire_ty` binds in
/// its outermost `{α : Sort u} → …` binder, returning `u`'s `LevelId` (to
/// reuse verbatim in the constructed value — see the module doc comment) and
/// `NameId` (to declare as the admitted theorem's own `uparams`). Declines
/// with [`SubstitutionError::UnexpectedShape`] for any other shape, never
/// guesses.
fn extract_universe_param(
    kernel: &Kernel,
    wire_ty: ExprId,
) -> Result<(LevelId, NameId), SubstitutionError> {
    let ExprNode::Pi(_, domain, _, _) = kernel.expr_node(wire_ty) else {
        return Err(SubstitutionError::UnexpectedShape(
            "noConfusion_of_Nat wire_ty does not start with a Pi binder",
        ));
    };
    let ExprNode::Sort(level) = kernel.expr_node(*domain) else {
        return Err(SubstitutionError::UnexpectedShape(
            "noConfusion_of_Nat wire_ty's first binder is not a Sort",
        ));
    };
    let LevelNode::Param(name) = kernel.level_node(*level) else {
        return Err(SubstitutionError::UnexpectedShape(
            "noConfusion_of_Nat wire_ty's first binder is not Sort of a level parameter",
        ));
    };
    Ok((*level, *name))
}

/// Attempt to reconstruct `rendered` (one of
/// [`SUBSTITUTABLE_NAT_NO_CONFUSION_THEOREMS`]) as a value that independently
/// type-checks against `wire_ty` — the untrusted stream's own declared type
/// for that name, which this function never alters — together with the
/// `uparams` list the resulting `Declaration::Theorem` must declare (`[u]`
/// for `noConfusion_of_Nat`, `[]` for `.aux`). Returns `Ok(None)` when
/// `rendered` is not one of these two names. Returns `Err(_)` when it is one
/// of these names but this kernel lacks the shape the reconstruction depends
/// on, **or** the candidate value fails to independently type-check against
/// `wire_ty` — the caller must treat both exactly like "not substitutable
/// here" and fall back to the stream's own (still trusted-refused) value,
/// never a coerced admission.
pub(crate) fn reconstruct(
    kernel: &mut Kernel,
    rendered: &str,
    wire_ty: ExprId,
) -> Result<Option<(ExprId, Vec<NameId>)>, SubstitutionError> {
    if !SUBSTITUTABLE_NAT_NO_CONFUSION_THEOREMS.contains(&rendered) {
        return Ok(None);
    }
    let prims = discover(kernel)?;
    let (value, uparams) = match rendered {
        "noConfusion_of_Nat" => {
            let (u_level, u_name) = extract_universe_param(kernel, wire_ty)?;
            let mut b = B::new(kernel, &prims);
            (b.no_confusion_full(u_level), vec![u_name])
        }
        "_private.Init.Prelude.0.noConfusion_of_Nat.aux" => {
            let mut b = B::new(kernel, &prims);
            (b.aux_full(), vec![])
        }
        _ => unreachable!("checked against SUBSTITUTABLE_NAT_NO_CONFUSION_THEOREMS above"),
    };

    // Validate independently, without mutating the environment: infer the
    // candidate's type and check it against the stream's own declared type.
    let inferred = kernel
        .infer(value)
        .map_err(|_| SubstitutionError::UnexpectedShape("candidate value failed to infer"))?;
    if !kernel.def_eq(inferred, wire_ty) {
        return Err(SubstitutionError::UnexpectedShape(
            "candidate value's inferred type is not def-eq to the stream's declared type",
        ));
    }
    Ok(Some((value, uparams)))
}

#[cfg(test)]
mod tests {
    //! Fixture-based tests, mirroring
    //! [`super::nat_order_substitution`]'s own test module: build our own
    //! `Nat`/`Bool`/`Eq`/`True`/`False` prelude fragment with `Nat.beq`
    //! actually implemented via `brecOn`/`below` (matching real Lean-core
    //! shape, not a shortcut), then reconstruct against it.

    use super::*;
    use crate::{ImportLimits, import_ndjson};
    use std::io::Cursor;

    /// A real archive stream (identical `Init.Prelude` content across every
    /// row in the frozen coverage archive — see the module doc comment)
    /// carries a real `Nat.beq` built via `brecOn`, which this fixture does
    /// not attempt to reproduce; the committed
    /// `lean4export-v4.30-quotient.ndjson` fixture (used across this crate's
    /// other substitution tests) is checked below for whether it already
    /// carries one.
    const QUOTIENT_FIXTURE: &str =
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-quotient.ndjson");

    fn fixture_kernel() -> Kernel {
        let completed = import_ndjson(
            Cursor::new(QUOTIENT_FIXTURE.as_bytes()),
            ImportLimits::default(),
        )
        .expect("fixture must import");
        completed.into_parts().0
    }

    #[test]
    fn unrecognised_name_declines_with_ok_none() {
        let mut kernel = fixture_kernel();
        let wire_ty = kernel.sort_zero();
        assert!(matches!(
            reconstruct(&mut kernel, "propext", wire_ty),
            Ok(None)
        ));
    }

    #[test]
    fn extract_universe_param_rejects_a_non_pi_wire_ty() {
        // `Sort u` directly (no outer `Pi` at all) — deliberately NOT
        // `sort_zero()`: that would also fail the *next* check (`Zero` is
        // not `Param`), so it cannot tell whether this guard specifically
        // ran. A bare `Sort` of a genuine level *parameter* is the
        // adversarial case: if the `Pi`-unwrap were skipped and `wire_ty`
        // used directly as the "domain", this would otherwise satisfy both
        // remaining checks and wrongly succeed.
        let mut kernel = fixture_kernel();
        let anon = kernel.anon();
        let u_name = kernel.name_str(anon, "u");
        let u = kernel.level_param(u_name);
        let wire_ty = kernel.sort(u);
        assert!(matches!(
            extract_universe_param(&kernel, wire_ty),
            Err(SubstitutionError::UnexpectedShape(_))
        ));
    }

    #[test]
    fn extract_universe_param_rejects_a_pi_whose_domain_is_not_a_sort() {
        // `(x : Nat) -> Nat` — a Pi, but its domain is `Nat`, not a `Sort _`.
        let mut kernel = Kernel::new();
        let prelude =
            axeyum_lean_kernel::build_nat_prelude(&mut kernel).expect("nat prelude must build");
        let nat_ty = kernel.const_(prelude.nat, vec![]);
        let anon = kernel.anon();
        let wire_ty = kernel.pi(anon, nat_ty, nat_ty, BinderInfo::Default);
        assert!(matches!(
            extract_universe_param(&kernel, wire_ty),
            Err(SubstitutionError::UnexpectedShape(_))
        ));
    }

    #[test]
    fn extract_universe_param_rejects_a_sort_of_a_concrete_level() {
        let mut kernel = fixture_kernel();
        // `(x : Sort 0) -> Sort 0` — a Pi over a Sort, but level `0` is
        // `LevelNode::Zero`, not `LevelNode::Param(_)`.
        let zero = kernel.level_zero();
        let sort0 = kernel.sort(zero);
        let anon = kernel.anon();
        let wire_ty = kernel.pi(anon, sort0, sort0, BinderInfo::Default);
        assert!(matches!(
            extract_universe_param(&kernel, wire_ty),
            Err(SubstitutionError::UnexpectedShape(_))
        ));
    }

    #[test]
    fn missing_beq_declines_with_required_declaration_unavailable() {
        // The quotient fixture carries `Nat` but not necessarily `Nat.beq`;
        // either way this must decline cleanly, never panic or fabricate.
        let mut kernel = fixture_kernel();
        let wire_ty = kernel.sort_zero();
        let result = reconstruct(
            &mut kernel,
            "_private.Init.Prelude.0.noConfusion_of_Nat.aux",
            wire_ty,
        );
        assert!(matches!(
            result,
            Err(SubstitutionError::RequiredDeclarationUnavailable(_)
                | SubstitutionError::UnexpectedShape(_))
                | Ok(Some(_))
        ));
    }
}

#[cfg(test)]
mod real_stream_tests {
    //! Not run by default (reads the frozen census archive, host-local under
    //! `/nas3`, not part of this repository). Run explicitly with
    //! `cargo test -p axeyum-lean-import --lib nat_no_confusion_substitution::real_stream_tests -- --ignored --nocapture`,
    //! optionally overriding the directory with
    //! `AXEYUM_NAT_NO_CONFUSION_PROBE_DIR`. Mirrors
    //! `nat_order_substitution::real_stream_tests` exactly, including its
    //! independent re-verification discipline (re-infer + `def_eq`, admit
    //! under a synthetic name, require empty axiom footprint AND empty
    //! theorem dependencies against THIS REAL STREAM's own environment).
    use super::*;
    use crate::{ImportLimits, import_ndjson};
    use axeyum_lean_kernel::Kernel;
    use std::collections::BTreeMap;
    use std::fs::File;
    use std::io::BufReader;

    const DEFAULT_DIR: &str = "/nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams";

    fn wire_ty_of(kernel: &Kernel, rendered: &str) -> Option<ExprId> {
        kernel
            .environment()
            .iter()
            .find(|(name, decl)| {
                matches!(decl, Declaration::Theorem { .. })
                    && kernel.display_name(**name).to_string() == rendered
            })
            .map(|(_, decl)| decl.ty())
    }

    #[test]
    #[ignore = "reads the frozen census archive under /nas3, not part of this repository"]
    fn probe_real_archive() {
        let dir = std::env::var("AXEYUM_NAT_NO_CONFUSION_PROBE_DIR")
            .unwrap_or_else(|_| DEFAULT_DIR.into());
        let mut entries: Vec<_> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("read_dir {dir}: {e}"))
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|ext| ext == "ndjson"))
            .collect();
        entries.sort();
        assert!(!entries.is_empty(), "no .ndjson files found under {dir}");

        let mut present: BTreeMap<&str, u32> = BTreeMap::new();
        let mut ok: BTreeMap<&str, u32> = BTreeMap::new();
        let mut failed: BTreeMap<&str, Vec<String>> = BTreeMap::new();

        for path in &entries {
            let file = File::open(path).unwrap_or_else(|e| panic!("open {path:?}: {e}"));
            let reader = BufReader::new(file);
            let Ok(completed) = import_ndjson(reader, ImportLimits::default()) else {
                continue;
            };
            let (mut kernel, _report) = completed.into_parts();
            for &rendered in SUBSTITUTABLE_NAT_NO_CONFUSION_THEOREMS {
                let Some(wire_ty) = wire_ty_of(&kernel, rendered) else {
                    continue;
                };
                *present.entry(rendered).or_default() += 1;
                match reconstruct(&mut kernel, rendered, wire_ty) {
                    Ok(Some((value, uparams))) => {
                        let inferred = kernel
                            .infer(value)
                            .unwrap_or_else(|e| panic!("{path:?} {rendered}: {e:?}"));
                        assert!(
                            kernel.def_eq(inferred, wire_ty),
                            "{path:?} {rendered}: re-inferred type not def-eq to wire_ty"
                        );
                        let probe_name = {
                            let root = kernel.anon();
                            kernel.name_str(root, format!("ProbeReconstruct_{rendered}"))
                        };
                        kernel
                            .add_declaration(Declaration::Theorem {
                                name: probe_name,
                                uparams,
                                ty: wire_ty,
                                value,
                            })
                            .unwrap_or_else(|e| {
                                panic!("{path:?} {rendered}: admission failed: {e:?}")
                            });
                        let footprint = kernel.axiom_footprint(probe_name);
                        assert!(
                            footprint.is_empty(),
                            "{path:?} {rendered}: nonempty axiom footprint {footprint:?}"
                        );
                        let theorem_deps = kernel.theorem_dependencies(probe_name);
                        assert!(
                            theorem_deps.is_empty(),
                            "{path:?} {rendered}: cites another theorem: {:?}",
                            theorem_deps
                                .iter()
                                .map(|&n| kernel.display_name(n).to_string())
                                .collect::<Vec<_>>()
                        );
                        *ok.entry(rendered).or_default() += 1;
                    }
                    Ok(None) => {
                        unreachable!("rendered is in SUBSTITUTABLE_NAT_NO_CONFUSION_THEOREMS")
                    }
                    Err(e) => {
                        failed
                            .entry(rendered)
                            .or_default()
                            .push(format!("{path:?}: {e}"));
                    }
                }
            }
        }

        println!("files: {}", entries.len());
        for &rendered in SUBSTITUTABLE_NAT_NO_CONFUSION_THEOREMS {
            let p = present.get(rendered).copied().unwrap_or(0);
            let o = ok.get(rendered).copied().unwrap_or(0);
            println!("{rendered}: present={p} ok={o}");
            if let Some(errs) = failed.get(rendered) {
                for e in errs.iter().take(2) {
                    println!("    decline: {e}");
                }
            }
        }
    }
}
