//! `Nat.casesOn` and `Nat.Primrec` — the primitive-recursive predicate.
//!
//! Two constructions, declared for cycle index 0 of the autogenesis nursery
//! draw (ADR-1240). Construction only, ADR-0653: **no theorem about either is
//! declared here.** `Nat.Primrec.add`, `.mul`, `.pow`, `.pred`, `.const`,
//! `.of_eq` and the rest are exactly the ordinary supporting theorems that
//! land the day after a draw, from `development`, where they cost nothing.
//!
//! # `Nat.casesOn`
//!
//! ```text
//! Nat.casesOn.{u} {motive : Nat → Sort u} (t : Nat)
//!     (zero : motive Nat.zero) (succ : (n : Nat) → motive n.succ) : motive t
//!   := Nat.rec.{u} motive zero (fun n _ih => succ n) t
//! ```
//!
//! Lean generates this from the inductive; this kernel does not, so it is a
//! plain definition over the already-declared `Nat.rec`, discarding the
//! induction hypothesis. It is universe-polymorphic because Mathlib's is: the
//! two rows that consume it here (`Nat.Primrec.casesOn'`, `.casesOn1`)
//! instantiate `motive := fun _ => Nat`, but declaring a `Nat`-only version
//! would be a *different construction* from Mathlib's, which is the
//! `Nat.multichoose` side of the mirror-flip criterion and would make every
//! statement over it a divergent mirror rather than the same proposition.
//!
//! Note the argument ORDER: the scrutinee `t` comes before the two minor
//! premises, which is Lean's order for `casesOn` and the reverse of `Nat.rec`'s.
//! Mathlib's statements are written `Nat.casesOn n (f z) fun y => g …`, so
//! getting this backwards would make every consuming statement fail to
//! elaborate — but it would still type-check *here*, since a wrong-but-total
//! eliminator is as well-typed as the right one.
//!
//! # `Nat.Primrec`
//!
//! ```text
//! inductive Nat.Primrec : (Nat → Nat) → Prop
//!   | zero  : Nat.Primrec (fun _ => 0)
//!   | succ  : Nat.Primrec Nat.succ
//!   | left  : Nat.Primrec Nat.unpairLeft
//!   | right : Nat.Primrec Nat.unpairRight
//!   | pair  {f g} : Nat.Primrec f → Nat.Primrec g →
//!                   Nat.Primrec (fun n => Nat.pair (f n) (g n))
//!   | comp  {f g} : Nat.Primrec f → Nat.Primrec g →
//!                   Nat.Primrec (fun n => f (g n))
//!   | prec  {f g} : Nat.Primrec f → Nat.Primrec g →
//!                   Nat.Primrec (Nat.unpaired fun z n =>
//!                     Nat.rec (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n)
//! ```
//!
//! The function argument is an INDEX, not a parameter (`num_params = 0`):
//! every constructor concludes at a different function, which is the whole
//! content of the predicate.
//!
//! Mathlib's `left` and `right` are stated `fun n => n.unpair.1` and
//! `fun n => n.unpair.2`. This kernel has no `Prod`, so `Nat.unpair` is out of
//! reach — but the two PROJECTIONS are not, and `unpair.rs` (ADR-1220)
//! declared them as the scalar functions `Nat.unpairLeft`/`Nat.unpairRight`.
//! They denote exactly Lean core's two components, so these constructors state
//! the same closure property Mathlib's do.
//!
//! Positivity is immediate: every recursive occurrence is a bare hypothesis
//! `Nat.Primrec f`, never under a binder or to the left of an arrow inside a
//! field, so the kernel's positivity check has nothing to reject and the
//! generated recursor is the ordinary one.
//!
//! # What the kernel cannot tell you, and what replaces the evaluation test
//!
//! Every other definition in this prelude is pinned by REDUCING it at concrete
//! numerals, because `add_declaration` type-checks a `Definition` and does not
//! evaluate it: `Nat → Nat` is `Nat → Nat` whatever the body computes.
//!
//! **An inductive `Prop` admits no such test.** `Nat.Primrec` has no value to
//! reduce; a constructor with a transposed, weakened or simply wrong index
//! type-checks exactly as happily as the intended one, and `axiom_footprint`,
//! the prelude build and the environment-derived coverage assertion are all
//! blind to it. Giving that safeguard up silently would be the
//! checker-that-cannot-fail defect arriving through the door marked "it is a
//! `Prop`, there is nothing to evaluate".
//!
//! It is not given up. **The predicate does not evaluate, but its INDICES do.**
//! Each constructor's conclusion is `Nat.Primrec <a concrete `Nat → Nat`
//! term>`, and that term is an ordinary function this kernel reduces. So the
//! evaluation test is recovered one level in: extract each constructor's index
//! and `def_eq` it at concrete numerals against a hand-computed table. That is
//! what [`primrec_tests`](super::primrec_tests) does, and it discriminates
//! exactly the defects a numeral table discriminates for a definition —
//! `left`/`right` swapped, `zero` returning its argument, `comp` composing in
//! the wrong order, `prec`'s two `Nat.pair` nestings transposed.
//!
//! Two things it adds that no definition needs:
//!
//! - **A closed derivation, built and type-checked.** `comp succ succ` is
//!   assembled from the real constructors and `Kernel::infer`red; its inferred
//!   type must be `Nat.Primrec` at a function that doubles the successor, which
//!   is then evaluated. A constructor whose hypothesis/conclusion shapes do not
//!   compose cannot appear in such a derivation at all, and no per-constructor
//!   check sees that — the mutually-consistent-errors failure, where five
//!   backwards call sites each type-check against an expectation backwards in
//!   the same way.
//! - **An arity/shape assertion per constructor**, so a constructor that
//!   silently lost a hypothesis (`pair` taking one premise instead of two)
//!   fails rather than passing a weaker statement.

use super::NatPrelude;
use super::ops::{NatDev, NatOps};
use crate::BinderInfo;
use crate::KernelError;
use crate::env::Declaration;
use crate::env::ReducibilityHint;
use crate::expr::ExprId;

/// `Nat.Primrec f`, for a function term `f`.
pub(super) fn primrec_ty(d: &mut NatDev<'_>, p: &NatPrelude, f: ExprId) -> ExprId {
    d.const_app(p.primrec, &[f])
}

/// `Nat → Nat`, the carrier the predicate is indexed by.
fn nat_fn(d: &mut NatDev<'_>) -> ExprId {
    let nat = d.nat_ty();
    d.arrow(nat, nat)
}

/// `∀ {_ : ty}, body` — [`NatOps::pi_fv`] with an IMPLICIT binder.
///
/// Mathlib states `Nat.Primrec.pair {f g}` and `Nat.casesOn {motive}`
/// implicitly, and a mirror that made them explicit would be a different
/// statement, not a formatting choice: the drawn rows apply these constructors
/// without supplying the functions.
fn pi_implicit(d: &mut NatDev<'_>, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = d.kernel().abstract_fvars(body, &[fv]);
    let anon = d.anon_name();
    d.kernel().pi(anon, ty, b, BinderInfo::Implicit)
}

/// `fun {_ : ty} => body` — the lambda matching [`pi_implicit`].
fn lam_implicit(d: &mut NatDev<'_>, fv: u64, ty: ExprId, body: ExprId) -> ExprId {
    let b = d.kernel().abstract_fvars(body, &[fv]);
    let anon = d.anon_name();
    d.kernel().lam(anon, ty, b, BinderInfo::Implicit)
}

/// Declare `Nat.casesOn` and the inductive `Nat.Primrec`.
///
/// Definitions and one inductive family only — see this module's doc for why
/// no theorem about either is declared here.
///
/// # Errors
///
/// Returns the trusted kernel gate's typed rejection.
pub(super) fn declare_primrec_all(
    d: &mut NatDev<'_>,
    p: &NatPrelude,
) -> Result<(), KernelError> {
    let p = *p;
    declare_cases_on(d, &p)?;
    declare_primrec(d, &p)
}

/// `Nat.casesOn.{u}` — `Nat.rec` with the induction hypothesis discarded.
fn declare_cases_on(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let u_lvl = d.kernel().level_param(p.cases_on_uparam);
    let sort_u = d.kernel().sort(u_lvl);

    // motive : Nat → Sort u
    let motive_ty = d.kernel().pi(anon, nat, sort_u, BinderInfo::Default);

    let motive_fv = d.fresh_fvar();
    let motive = d.kernel().fvar(motive_fv);
    let t_fv = d.fresh_fvar();
    let t = d.kernel().fvar(t_fv);

    let zero = d.zero();
    let motive_zero = d.apply(motive, &[zero]);

    // succ minor : (n : Nat) → motive n.succ
    let succ_minor_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let body = d.apply(motive, &[sn]);
        d.pi_fv(n_fv, nat, body)
    };

    let motive_t = d.apply(motive, &[t]);

    // ty := Π {motive : Nat → Sort u} (t : Nat), motive 0 →
    //         ((n : Nat) → motive n.succ) → motive t
    let ty = {
        let with_succ = d.arrow(succ_minor_ty, motive_t);
        let with_zero = d.arrow(motive_zero, with_succ);
        let with_t = d.pi_fv(t_fv, nat, with_zero);
        pi_implicit(d, motive_fv, motive_ty, with_t)
    };

    // value := fun motive t z s => Nat.rec.{u} motive z (fun n _ih => s n) t
    let value = {
        let z_fv = d.fresh_fvar();
        let z = d.kernel().fvar(z_fv);
        let s_fv = d.fresh_fvar();
        let s = d.kernel().fvar(s_fv);

        // The step minor DISCARDS its induction hypothesis: that is the whole
        // difference between `casesOn` and `rec`.
        let step = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let ih_ty = {
                let body = d.apply(motive, &[n]);
                body
            };
            let body = d.apply(s, &[n]);
            let ih_fv = d.fresh_fvar();
            let inner = d.lam_fv(ih_fv, ih_ty, body);
            d.lam_fv(n_fv, nat, inner)
        };

        let rec_name = p.rec;
        let rec = d.kernel().const_(rec_name, vec![u_lvl]);
        let body = d.apply(rec, &[motive, z, step, t]);

        let with_s = d.lam_fv(s_fv, succ_minor_ty, body);
        let with_z = d.lam_fv(z_fv, motive_zero, with_s);
        let with_t = d.lam_fv(t_fv, nat, with_z);
        lam_implicit(d, motive_fv, motive_ty, with_t)
    };

    d.kernel().add_declaration(Declaration::Definition {
        name: p.cases_on,
        uparams: vec![p.cases_on_uparam],
        ty,
        value,
        hint: ReducibilityHint::Regular(1),
    })
}

/// The inductive `Nat.Primrec : (Nat → Nat) → Prop`, seven constructors.
fn declare_primrec(d: &mut NatDev<'_>, p: &NatPrelude) -> Result<(), KernelError> {
    let nat = d.nat_ty();
    let anon = d.anon_name();
    let prop = d.kernel().sort_zero();
    let fn_ty = nat_fn(d);

    // family := (Nat → Nat) → Prop, the function argument an INDEX.
    let family_ty = d.kernel().pi(anon, fn_ty, prop, BinderInfo::Default);

    // zero : Nat.Primrec (fun _ => 0)
    let zero_ty = {
        let zero = d.zero();
        let f = d.kernel().lam(anon, nat, zero, BinderInfo::Default);
        primrec_ty(d, p, f)
    };

    // succ : Nat.Primrec Nat.succ
    //
    // `Nat.succ` is the constructor, and it is eta-expanded to a lambda rather
    // than used bare: a constructor constant applied to nothing is not a
    // function term in this kernel's elaboration, and the index slot wants a
    // `Nat → Nat`.
    let succ_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let sn = d.succ(n);
        let f = d.lam_fv(n_fv, nat, sn);
        primrec_ty(d, p, f)
    };

    // left : Nat.Primrec Nat.unpairLeft  (Mathlib: `fun n => n.unpair.1`)
    let left_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.unpair_left, &[n]);
        let f = d.lam_fv(n_fv, nat, body);
        primrec_ty(d, p, f)
    };

    // right : Nat.Primrec Nat.unpairRight  (Mathlib: `fun n => n.unpair.2`)
    let right_ty = {
        let n_fv = d.fresh_fvar();
        let n = d.kernel().fvar(n_fv);
        let body = d.const_app(p.unpair_right, &[n]);
        let f = d.lam_fv(n_fv, nat, body);
        primrec_ty(d, p, f)
    };

    // pair {f g} : Primrec f → Primrec g → Primrec (fun n => Nat.pair (f n) (g n))
    let pair_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);

        let concl = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let fn_ = d.apply(f, &[n]);
            let gn = d.apply(g, &[n]);
            let body = d.const_app(p.pair_fn, &[fn_, gn]);
            let lam = d.lam_fv(n_fv, nat, body);
            primrec_ty(d, p, lam)
        };
        let hf = primrec_ty(d, p, f);
        let hg = primrec_ty(d, p, g);
        let with_hg = d.arrow(hg, concl);
        let with_hf = d.arrow(hf, with_hg);
        let with_g = pi_implicit(d, g_fv, fn_ty, with_hf);
        pi_implicit(d, f_fv, fn_ty, with_g)
    };

    // comp {f g} : Primrec f → Primrec g → Primrec (fun n => f (g n))
    let comp_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);

        let concl = {
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);
            let gn = d.apply(g, &[n]);
            let body = d.apply(f, &[gn]);
            let lam = d.lam_fv(n_fv, nat, body);
            primrec_ty(d, p, lam)
        };
        let hf = primrec_ty(d, p, f);
        let hg = primrec_ty(d, p, g);
        let with_hg = d.arrow(hg, concl);
        let with_hf = d.arrow(hf, with_hg);
        let with_g = pi_implicit(d, g_fv, fn_ty, with_hf);
        pi_implicit(d, f_fv, fn_ty, with_g)
    };

    // prec {f g} : Primrec f → Primrec g →
    //   Primrec (Nat.unpaired fun z n =>
    //     Nat.rec (f z) (fun y IH => g (Nat.pair z (Nat.pair y IH))) n)
    //
    // The two `Nat.pair` nestings are Mathlib's own and are NOT symmetric:
    // `pair z (pair y IH)` pairs the parameter with the pair of the index and
    // the recursive value. Transposing them gives a different, well-typed and
    // wrong constructor, which is why the evaluation test pins this index at
    // an asymmetric `f`/`g`.
    let prec_ty = {
        let f_fv = d.fresh_fvar();
        let f = d.kernel().fvar(f_fv);
        let g_fv = d.fresh_fvar();
        let g = d.kernel().fvar(g_fv);

        let concl = {
            let z_fv = d.fresh_fvar();
            let z = d.kernel().fvar(z_fv);
            let n_fv = d.fresh_fvar();
            let n = d.kernel().fvar(n_fv);

            let motive = d.kernel().lam(anon, nat, nat, BinderInfo::Default);
            let base = d.apply(f, &[z]);
            let step = {
                let y_fv = d.fresh_fvar();
                let y = d.kernel().fvar(y_fv);
                let ih_fv = d.fresh_fvar();
                let ih = d.kernel().fvar(ih_fv);
                let inner_pair = d.const_app(p.pair_fn, &[y, ih]);
                let outer_pair = d.const_app(p.pair_fn, &[z, inner_pair]);
                let body = d.apply(g, &[outer_pair]);
                let with_ih = d.lam_fv(ih_fv, nat, body);
                d.lam_fv(y_fv, nat, with_ih)
            };
            let one = d.level_one();
            let rec_name = p.rec;
            let rec = d.kernel().const_(rec_name, vec![one]);
            let rec_body = d.apply(rec, &[motive, base, step, n]);

            let binary = {
                let inner = d.arrow(nat, nat);
                let with_n = d.lam_fv(n_fv, nat, rec_body);
                let lam = d.lam_fv(z_fv, nat, with_n);
                let _ = inner;
                lam
            };
            let applied = d.const_app(p.unpaired, &[binary]);
            primrec_ty(d, p, applied)
        };
        let hf = primrec_ty(d, p, f);
        let hg = primrec_ty(d, p, g);
        let with_hg = d.arrow(hg, concl);
        let with_hf = d.arrow(hf, with_hg);
        let with_g = pi_implicit(d, g_fv, fn_ty, with_hf);
        pi_implicit(d, f_fv, fn_ty, with_g)
    };

    d.kernel().add_inductive(
        p.primrec,
        &[],
        0,
        family_ty,
        &[
            (p.primrec_zero, zero_ty),
            (p.primrec_succ, succ_ty),
            (p.primrec_left, left_ty),
            (p.primrec_right, right_ty),
            (p.primrec_pair, pair_ty),
            (p.primrec_comp, comp_ty),
            (p.primrec_prec, prec_ty),
        ],
    )
}
