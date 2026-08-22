//! A small, fixed, reviewed substitution of three trusted-declaration
//! blockers by proofs this project's own kernel constructs and checks.
//!
//! `docs/autogenesis/233-adapter-blocker-is-three-theorems.md` measured that
//! `adapter-rejection:trusted-declaration` — the statement adapter's refusal
//! of any stream whose closure carries an axiom, theorem, opaque, or quotient
//! declaration — is 114 of 138 frozen census rows, and that all 114 name
//! exactly four declarations: `congrArg` (56), `congr` (38), `mt` (19), and
//! the genuine axiom `propext` (1).
//!
//! The first three are ordinary consequences of `Eq.rec` (`congrArg`,
//! `congr`) or bare propositional logic (`mt`) — nothing about them requires
//! trusting Mathlib's own proof. This module rebuilds each one from kernel
//! primitives that are themselves never trusted-and-refused (`Eq`, `Eq.rec`,
//! `Eq.refl`, `Not`, `False` are Inductive/Constructor/Recursor/Definition,
//! not Axiom/Theorem/Opaque/Quotient), and hands the *reconstructed*
//! declaration to [`Kernel::add_declaration`] for the same independent check
//! every other admitted declaration receives. The untrusted stream's own
//! `type`/`value` fields for these three names are never read by this module
//! and never influence the declaration it builds.
//!
//! `propext` is a genuine axiom, independent of everything else in the
//! kernel, and is deliberately absent from [`SUBSTITUTABLE_THEOREMS`].
//! Nothing here attempts to derive it, and a stream whose *only* blocker is
//! `propext` is refused exactly as before.
//!
//! Adding a name to [`SUBSTITUTABLE_THEOREMS`] is a deliberate, reviewed
//! source edit — this module never pattern-matches "looks derivable" and
//! never dispatches on anything but an exact, hardcoded name.
//!
//! Every intermediate lambda this module builds closes its own free variable
//! *immediately*, via [`Kernel::abstract_fvars`] followed by [`Kernel::lam`]/
//! [`Kernel::pi`] — the same discipline
//! `bounded_induction_support::build_congr` uses, and for the same reason: a
//! lambda that is applied *internally* (as an `Eq.rec` motive is, while this
//! module is still constructing the surrounding term) must already be a
//! genuine de Bruijn-indexed binder before that application, or ordinary beta
//! reduction cannot see through it. [`Kernel::infer_and_close_scoped_fvars`]
//! defers closing to one final call and is right for a top-level telescope
//! that is never itself applied — it is the wrong tool for a motive, and an
//! earlier version of this module that used it there admitted nothing (every
//! `Eq.rec` application failed to typecheck against its own motive).

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, LevelId, NameId, ReducibilityHint,
};

/// The complete, reviewed set of trusted theorem names this module will
/// substitute a self-derived proof for. `propext` is a genuine axiom and must
/// never be added here.
pub(crate) const SUBSTITUTABLE_THEOREMS: &[&str] = &["congrArg", "congr", "mt"];

/// First free-variable id this module mints. Chosen far above any id an
/// import stream or another producer's search would use — exported
/// declarations never contain `FVar` nodes at all (they are closed terms), so
/// this only has to avoid collision with other *constructors* sharing the
/// same kernel within one process, which currently mint from `9_000_000`.
const FVAR_BASE: u64 = 900_000_000;

/// Why a name in [`SUBSTITUTABLE_THEOREMS`] could not be reconstructed here.
/// This is never a soundness signal — it means this module declines, and the
/// caller falls back to the ordinary trusted-declaration refusal.
#[derive(Debug)]
pub(crate) enum SubstitutionError {
    /// A required ambient declaration (`Eq`, `Eq.rec`, `Not`, `False`, ...) is
    /// absent or occurs more than once under its exact display name.
    RequiredDeclarationUnavailable(&'static str),
    /// A required ambient declaration exists but is not the shape this
    /// reconstruction depends on (e.g. `Eq.rec` is not a two-universe-param
    /// `Recursor`).
    ///
    /// Nothing in this module calls `Kernel::add_declaration` or otherwise
    /// asks the kernel to check anything — it only ever *constructs* a
    /// candidate `(type, value)` pair. The one real check (does this
    /// candidate actually kernel-check?) happens where the candidate is
    /// admitted, in `ImportState::import_theorem`, via the kernel's ordinary
    /// `ImportError::Kernel`, not through this type. If that admission ever
    /// fails for a reconstruction, that is a bug in this module — never a
    /// reason to fall back to the untrusted stream value; it must still
    /// refuse the whole record, and does (see `import_theorem`'s `Err(_)`
    /// arm).
    UnexpectedShape(&'static str),
}

impl std::fmt::Display for SubstitutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::RequiredDeclarationUnavailable(name) => {
                write!(f, "required declaration {name:?} is absent or ambiguous")
            }
            Self::UnexpectedShape(detail) => write!(f, "unexpected shape: {detail}"),
        }
    }
}

fn fresh(counter: &mut u64) -> u64 {
    *counter += 1;
    *counter
}

fn exact_name(kernel: &Kernel, rendered: &'static str) -> Result<NameId, SubstitutionError> {
    let mut matches = kernel
        .environment()
        .iter()
        .filter(|(name, _)| kernel.display_name(**name).to_string() == rendered)
        .map(|(name, _)| *name);
    let first = matches
        .next()
        .ok_or(SubstitutionError::RequiredDeclarationUnavailable(rendered))?;
    if matches.next().is_some() {
        return Err(SubstitutionError::RequiredDeclarationUnavailable(rendered));
    }
    Ok(first)
}

/// The ambient `Eq`/`Eq.refl`/`Eq.rec` primitives, discovered by exact display
/// name and checked rather than assumed — the same discipline
/// `bounded_induction_support::discover_eq_primitives` uses for the same
/// reason: an isolated statement-import kernel keeps only Definitions and
/// Inductives, so there is no borrowed `congrArg`/`congr`/`mt` to lean on, and
/// none of this construction may assume one exists with a particular shape.
struct EqPrimitives {
    eq: NameId,
    eq_refl: NameId,
    eq_rec: NameId,
}

fn discover_eq(kernel: &Kernel) -> Result<EqPrimitives, SubstitutionError> {
    let eq = exact_name(kernel, "Eq")?;
    let eq_refl = exact_name(kernel, "Eq.refl")?;
    let eq_rec = exact_name(kernel, "Eq.rec")?;
    let Some(Declaration::Recursor { uparams, .. }) = kernel.environment().get(eq_rec) else {
        return Err(SubstitutionError::UnexpectedShape(
            "Eq.rec is not a Recursor declaration",
        ));
    };
    if uparams.len() != 2 {
        return Err(SubstitutionError::UnexpectedShape(
            "Eq.rec does not have exactly two universe parameters",
        ));
    }
    Ok(EqPrimitives {
        eq,
        eq_refl,
        eq_rec,
    })
}

fn build_eq(
    kernel: &mut Kernel,
    eq: NameId,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
    y: ExprId,
) -> ExprId {
    let head = kernel.const_(eq, vec![level]);
    let with_carrier = kernel.app(head, carrier);
    let with_x = kernel.app(with_carrier, x);
    kernel.app(with_x, y)
}

fn build_eq_refl(
    kernel: &mut Kernel,
    eq_refl: NameId,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
) -> ExprId {
    let head = kernel.const_(eq_refl, vec![level]);
    let with_carrier = kernel.app(head, carrier);
    kernel.app(with_carrier, x)
}

/// `fun (name : ty) => body[fv]`, closing `fv` immediately via
/// [`Kernel::abstract_fvars`] so the result is a genuine de Bruijn-indexed
/// lambda — safe to apply internally right away, unlike a lambda whose body
/// still refers to its own parameter through a raw free variable.
fn lam_fv(
    kernel: &mut Kernel,
    name: NameId,
    fv: u64,
    ty: ExprId,
    body: ExprId,
    info: BinderInfo,
) -> ExprId {
    let abstracted = kernel.abstract_fvars(body, &[fv]);
    kernel.lam(name, ty, abstracted, info)
}

/// `congrArg f h : Eq result_level result_carrier (f hyp_lhs) (f hyp_rhs)`
/// from `h : Eq hyp_level hyp_carrier hyp_lhs hyp_rhs`, built directly from
/// `Eq.rec` — never a hand-written `congrArg`. `f` may be any function value,
/// including a lambda built on the spot (this is exactly how `congr`'s second
/// rewrite below uses it, with `f := fun k => k b`).
#[allow(clippy::too_many_arguments)]
fn build_congr_arg(
    kernel: &mut Kernel,
    eqp: &EqPrimitives,
    next_fvar: &mut u64,
    f: ExprId,
    hyp_level: LevelId,
    hyp_carrier: ExprId,
    hyp_lhs: ExprId,
    hyp_rhs: ExprId,
    hyp_proof: ExprId,
    result_level: LevelId,
    result_carrier: ExprId,
) -> ExprId {
    let anon = kernel.anon();
    let fa = kernel.app(f, hyp_lhs);
    let x_fv = fresh(next_fvar);
    let x = kernel.fvar(x_fv);
    let fx = kernel.app(f, x);
    let concl = build_eq(kernel, eqp.eq, result_level, result_carrier, fa, fx);
    let hyp_ty = build_eq(kernel, eqp.eq, hyp_level, hyp_carrier, hyp_lhs, x);
    let anon_hyp = kernel.anon();
    let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
    let motive = lam_fv(kernel, anon, x_fv, hyp_carrier, inner, BinderInfo::Default);
    let refl_case = build_eq_refl(kernel, eqp.eq_refl, result_level, result_carrier, fa);
    let zero = kernel.level_zero();
    let rec = kernel.const_(eqp.eq_rec, vec![zero, hyp_level]);
    let with_carrier = kernel.app(rec, hyp_carrier);
    let with_a = kernel.app(with_carrier, hyp_lhs);
    let with_motive = kernel.app(with_a, motive);
    let with_minor = kernel.app(with_motive, refl_case);
    let with_b = kernel.app(with_minor, hyp_rhs);
    kernel.app(with_b, hyp_proof)
}

/// Transitivity of `Eq`, from `p1 : Eq level carrier x y` and
/// `p2 : Eq level carrier y z`, to a proof of `Eq level carrier x z` — again
/// directly from `Eq.rec`, never a borrowed `Eq.trans`.
#[allow(clippy::too_many_arguments)]
fn build_trans(
    kernel: &mut Kernel,
    eqp: &EqPrimitives,
    next_fvar: &mut u64,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
    y: ExprId,
    p1: ExprId,
    z: ExprId,
    p2: ExprId,
) -> ExprId {
    let anon = kernel.anon();
    let z_fv = fresh(next_fvar);
    let zvar = kernel.fvar(z_fv);
    let concl = build_eq(kernel, eqp.eq, level, carrier, x, zvar);
    let hyp_ty = build_eq(kernel, eqp.eq, level, carrier, y, zvar);
    let anon_hyp = kernel.anon();
    let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
    let motive = lam_fv(kernel, anon, z_fv, carrier, inner, BinderInfo::Default);
    let zero = kernel.level_zero();
    let rec = kernel.const_(eqp.eq_rec, vec![zero, level]);
    let with_carrier = kernel.app(rec, carrier);
    let with_a = kernel.app(with_carrier, y);
    let with_motive = kernel.app(with_a, motive);
    let with_minor = kernel.app(with_motive, p1);
    let with_b = kernel.app(with_minor, z);
    kernel.app(with_b, p2)
}

/// Close a telescope of free variables over a paired (value, type),
/// outer-to-inner in `binders`, by abstracting each one (innermost first) out
/// of the accumulated value and type and wrapping both in a matching
/// `Lam`/`Pi`. Each binder's own declared type may still mention any *outer*
/// (not-yet-closed) free variable — a later iteration finds and abstracts it
/// correctly, since [`Kernel::abstract_fvars`] recurses into a `Lam`/`Pi`
/// node's domain as well as its body.
fn close_telescope(
    kernel: &mut Kernel,
    binders: &[(u64, ExprId, BinderInfo)],
    mut value: ExprId,
    mut ty: ExprId,
) -> (ExprId, ExprId) {
    for &(fv, fv_ty, info) in binders.iter().rev() {
        let name = kernel.anon();
        let abstracted_value = kernel.abstract_fvars(value, &[fv]);
        let abstracted_ty = kernel.abstract_fvars(ty, &[fv]);
        value = kernel.lam(name, fv_ty, abstracted_value, info);
        ty = kernel.pi(name, fv_ty, abstracted_ty, info);
    }
    (value, ty)
}

/// `congrArg.{u,v} : {alpha : Sort u} -> {beta : Sort v} -> {a1 a2 : alpha} ->
/// (f : alpha -> beta) -> Eq alpha a1 a2 -> Eq beta (f a1) (f a2)`.
#[allow(clippy::many_single_char_names)]
fn congr_arg_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let v_name = kernel.name_str(anon, "v");
    let u = kernel.level_param(u_name);
    let v = kernel.level_param(v_name);
    let sort_u = kernel.sort(u);
    let sort_v = kernel.sort(v);

    let alpha_fv = fresh(&mut next_fvar);
    let beta_fv = fresh(&mut next_fvar);
    let a1_fv = fresh(&mut next_fvar);
    let a2_fv = fresh(&mut next_fvar);
    let f_fv = fresh(&mut next_fvar);
    let h_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let beta = kernel.fvar(beta_fv);
    let a1 = kernel.fvar(a1_fv);
    let a2 = kernel.fvar(a2_fv);
    let f = kernel.fvar(f_fv);
    let h = kernel.fvar(h_fv);

    let ty_f = kernel.pi(anon, alpha, beta, BinderInfo::Default);
    let ty_h = build_eq(kernel, eqp.eq, u, alpha, a1, a2);

    let value_body = build_congr_arg(
        kernel,
        &eqp,
        &mut next_fvar,
        f,
        u,
        alpha,
        a1,
        a2,
        h,
        v,
        beta,
    );
    let f_a1 = kernel.app(f, a1);
    let f_a2 = kernel.app(f, a2);
    let type_body = build_eq(kernel, eqp.eq, v, beta, f_a1, f_a2);

    let binders = [
        (alpha_fv, sort_u, BinderInfo::Default),
        (beta_fv, sort_v, BinderInfo::Default),
        (a1_fv, alpha, BinderInfo::Default),
        (a2_fv, alpha, BinderInfo::Default),
        (f_fv, ty_f, BinderInfo::Default),
        (h_fv, ty_h, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name, v_name]))
}

/// `congr.{u,v} : {alpha : Sort u} -> {beta : Sort v} -> {f g : alpha -> beta}
/// -> {a b : alpha} -> Eq (alpha -> beta) f g -> Eq alpha a b ->
/// Eq beta (f a) (g b)`, built as `Eq.trans (congrArg f h2) (congrArg
/// (fun k => k b) h1)` — with both `congrArg` steps and the transitivity
/// themselves reconstructed from `Eq.rec` by this module, never by naming a
/// `congrArg`/`congr`/`Eq.trans` declaration.
#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]
fn congr_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let v_name = kernel.name_str(anon, "v");
    let u = kernel.level_param(u_name);
    let v = kernel.level_param(v_name);
    let sort_u = kernel.sort(u);
    let sort_v = kernel.sort(v);

    let alpha_fv = fresh(&mut next_fvar);
    let beta_fv = fresh(&mut next_fvar);
    let f_fv = fresh(&mut next_fvar);
    let g_fv = fresh(&mut next_fvar);
    let a_fv = fresh(&mut next_fvar);
    let b_fv = fresh(&mut next_fvar);
    let h1_fv = fresh(&mut next_fvar);
    let h2_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let beta = kernel.fvar(beta_fv);
    let f = kernel.fvar(f_fv);
    let g = kernel.fvar(g_fv);
    let a = kernel.fvar(a_fv);
    let b = kernel.fvar(b_fv);
    let h1 = kernel.fvar(h1_fv);
    let h2 = kernel.fvar(h2_fv);

    let ty_f = kernel.pi(anon, alpha, beta, BinderInfo::Default);
    // `alpha -> beta : Sort (imax u v)` by the ordinary Pi-formation rule —
    // computed directly from the levels this construction already minted,
    // never by calling `Kernel::infer` on a term that still carries free
    // variables (that needs a populated `LocalContext`, which an open
    // skeleton under construction does not have).
    let arrow_level = kernel.level_imax(u, v);

    let ty_h1 = build_eq(kernel, eqp.eq, arrow_level, ty_f, f, g);
    let ty_h2 = build_eq(kernel, eqp.eq, u, alpha, a, b);

    // c1 : Eq v beta (f a) (f b), from h2 : Eq u alpha a b.
    let c1 = build_congr_arg(kernel, &eqp, &mut next_fvar, f, u, alpha, a, b, h2, v, beta);
    let f_a = kernel.app(f, a);
    let f_b = kernel.app(f, b);

    // apply_b := fun (k : alpha -> beta) => k b
    let k_fv = fresh(&mut next_fvar);
    let k = kernel.fvar(k_fv);
    let k_b = kernel.app(k, b);
    let apply_b_name = kernel.anon();
    let apply_b = lam_fv(kernel, apply_b_name, k_fv, ty_f, k_b, BinderInfo::Default);

    // c2 : Eq v beta (f b) (g b), from h1 : Eq arrow_level (alpha -> beta) f g,
    // i.e. congrArg applied to the function "apply at b".
    let c2 = build_congr_arg(
        kernel,
        &eqp,
        &mut next_fvar,
        apply_b,
        arrow_level,
        ty_f,
        f,
        g,
        h1,
        v,
        beta,
    );
    let g_b = kernel.app(g, b);

    // Eq.trans c1 c2 : Eq v beta (f a) (g b)
    let value_body = build_trans(kernel, &eqp, &mut next_fvar, v, beta, f_a, f_b, c1, g_b, c2);
    let type_body = build_eq(kernel, eqp.eq, v, beta, f_a, g_b);

    let binders = [
        (alpha_fv, sort_u, BinderInfo::Default),
        (beta_fv, sort_v, BinderInfo::Default),
        (f_fv, ty_f, BinderInfo::Default),
        (g_fv, ty_f, BinderInfo::Default),
        (a_fv, alpha, BinderInfo::Default),
        (b_fv, alpha, BinderInfo::Default),
        (h1_fv, ty_h1, BinderInfo::Default),
        (h2_fv, ty_h2, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name, v_name]))
}

/// `mt : {a b : Prop} -> (a -> b) -> Not b -> Not a := fun a b hab hnb ha =>
/// hnb (hab ha)` — bare propositional logic, no axiom and no `Eq` at all.
/// Depends structurally only on `Not` being an unfoldable `Definition` (so
/// `Not b` and `b -> False` are interchangeable to the kernel's own `def_eq`),
/// discovered and checked rather than assumed.
#[allow(clippy::similar_names)]
fn mt_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let not_name = exact_name(kernel, "Not")?;
    match kernel.environment().get(not_name) {
        Some(Declaration::Definition { uparams, hint, .. })
            if uparams.is_empty() && !matches!(hint, ReducibilityHint::Opaque) => {}
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "Not is not a zero-universe unfoldable Definition",
            ));
        }
    }
    // False itself is never referenced by name in the construction below (it
    // only ever appears as `Not`'s own unfolded body), but its presence with
    // the expected shape is exactly what makes `Not`'s unfolding the ordinary
    // `Prop -> Prop` shape this construction assumes nothing further about.
    let false_name = exact_name(kernel, "False")?;
    match kernel.environment().get(false_name) {
        Some(Declaration::Inductive {
            num_params,
            num_indices,
            ctor_names,
            ..
        }) if *num_params == 0 && *num_indices == 0 && ctor_names.is_empty() => {}
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "False is not a zero-constructor Inductive",
            ));
        }
    }

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let a_fv = fresh(&mut next_fvar);
    let b_fv = fresh(&mut next_fvar);
    let hab_fv = fresh(&mut next_fvar);
    let hnb_fv = fresh(&mut next_fvar);
    let ha_fv = fresh(&mut next_fvar);
    let a = kernel.fvar(a_fv);
    let b = kernel.fvar(b_fv);
    let hab = kernel.fvar(hab_fv);
    let hnb = kernel.fvar(hnb_fv);
    let ha = kernel.fvar(ha_fv);

    let not_a = {
        let not_const = kernel.const_(not_name, vec![]);
        kernel.app(not_const, a)
    };
    let not_b = {
        let not_const = kernel.const_(not_name, vec![]);
        kernel.app(not_const, b)
    };
    let ty_hab = kernel.pi(anon, a, b, BinderInfo::Default);

    let hab_ha = kernel.app(hab, ha);
    let hnb_hab_ha = kernel.app(hnb, hab_ha);
    let value_body = lam_fv(kernel, anon, ha_fv, a, hnb_hab_ha, BinderInfo::Default);
    let type_body = not_a;

    let binders = [
        (a_fv, prop, BinderInfo::Default),
        (b_fv, prop, BinderInfo::Default),
        (hab_fv, ty_hab, BinderInfo::Default),
        (hnb_fv, not_b, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![]))
}

/// Attempt to reconstruct `rendered` as a kernel-checked declaration built
/// entirely from this module's own primitives, never from the untrusted
/// stream. Returns `Ok(None)` when `rendered` is not one of
/// [`SUBSTITUTABLE_THEOREMS`] — nothing to do, not a failure. Returns
/// `Err(_)` when it is one of those names but this kernel lacks the shape the
/// reconstruction depends on; the caller must treat that exactly like "not
/// substitutable" (fall back to the ordinary trusted-declaration refusal),
/// never as license to admit the untrusted value instead.
pub(crate) fn reconstruct(
    kernel: &mut Kernel,
    name: NameId,
    rendered: &str,
) -> Result<Option<Declaration>, SubstitutionError> {
    if !SUBSTITUTABLE_THEOREMS.contains(&rendered) {
        return Ok(None);
    }
    let (value, ty, uparams) = match rendered {
        "congrArg" => congr_arg_pair(kernel)?,
        "congr" => congr_pair(kernel)?,
        "mt" => mt_pair(kernel)?,
        _ => unreachable!("checked against SUBSTITUTABLE_THEOREMS above"),
    };
    Ok(Some(Declaration::Theorem {
        name,
        uparams,
        ty,
        value,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ImportLimits, import_ndjson};
    use std::io::Cursor;

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
    fn congr_arg_reconstructs_and_kernel_checks() {
        let mut kernel = fixture_kernel();
        let (value, ty, uparams) = congr_arg_pair(&mut kernel).expect("congrArg reconstructs");
        assert_eq!(uparams.len(), 2);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestCongrArg")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed congrArg must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn congr_reconstructs_and_kernel_checks() {
        let mut kernel = fixture_kernel();
        let (value, ty, uparams) = congr_pair(&mut kernel).expect("congr reconstructs");
        assert_eq!(uparams.len(), 2);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestCongr")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed congr must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn reconstruct_rejects_names_outside_the_fixed_set() {
        let mut kernel = fixture_kernel();
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "propext")
        };
        assert!(matches!(
            reconstruct(&mut kernel, name, "propext"),
            Ok(None)
        ));
    }

    /// A minimal kernel carrying exactly `False : Prop` (an Inductive with no
    /// constructors) and `Not := fun (p : Prop) => p -> False` (an unfoldable
    /// Definition) — the only two ambient declarations `mt_pair` depends on,
    /// built directly rather than through any external fixture.
    fn false_not_kernel() -> Kernel {
        let mut kernel = Kernel::new();
        let root = kernel.anon();
        let zero = kernel.level_zero();
        let prop = kernel.sort(zero);

        let false_name = kernel.name_str(root, "False");
        kernel
            .add_inductive(false_name, &[], 0, prop, &[])
            .expect("False must admit");

        let not_name = kernel.name_str(root, "Not");
        let p_fv = 1_u64;
        let p = kernel.fvar(p_fv);
        let false_const = kernel.const_(false_name, vec![]);
        let arrow = kernel.pi(root, p, false_const, BinderInfo::Default);
        let not_ty = {
            let abstracted = kernel.abstract_fvars(prop, &[p_fv]);
            kernel.pi(root, prop, abstracted, BinderInfo::Default)
        };
        let not_value = {
            let abstracted = kernel.abstract_fvars(arrow, &[p_fv]);
            kernel.lam(root, prop, abstracted, BinderInfo::Default)
        };
        kernel
            .add_declaration(Declaration::Definition {
                name: not_name,
                uparams: vec![],
                ty: not_ty,
                value: not_value,
                hint: ReducibilityHint::Regular(1),
            })
            .expect("Not must admit");
        kernel
    }

    #[test]
    fn mt_reconstructs_and_kernel_checks() {
        let mut kernel = false_not_kernel();
        let (value, ty, uparams) = mt_pair(&mut kernel).expect("mt reconstructs");
        assert_eq!(uparams.len(), 0);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestMt")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed mt must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn mt_declines_when_not_is_missing() {
        let mut kernel = Kernel::new();
        assert!(matches!(
            mt_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Not"))
        ));
    }

    #[test]
    fn congr_arg_declines_when_eq_rec_is_missing() {
        let mut kernel = Kernel::new();
        assert!(matches!(
            congr_arg_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Eq"))
        ));
    }
}
