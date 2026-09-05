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
//! `producers::bounded_induction::build_congr` uses, and for the same reason: a
//! lambda that is applied *internally* (as an `Eq.rec` motive is, while this
//! module is still constructing the surrounding term) must already be a
//! genuine de Bruijn-indexed binder before that application, or ordinary beta
//! reduction cannot see through it. [`Kernel::infer_and_close_scoped_fvars`]
//! defers closing to one final call and is right for a top-level telescope
//! that is never itself applied — it is the wrong tool for a motive, and an
//! earlier version of this module that used it there admitted nothing (every
//! `Eq.rec` application failed to typecheck against its own motive).
//!
//! `Eq.symm` was added the same way (bare `Eq.rec`, no wire type or value
//! ever read) once `docs/autogenesis/236-…` measured that the four-name
//! count above was only the *first-reported* blocker, not the whole closure.
//! The twenty `Nat` order/pred/sub/ble lemmas that closure also names are a
//! different shape of fact — arithmetic about a *specific* stream-supplied
//! `Nat.le`/`Nat.pred`/`Nat.sub`/`Nat.ble`, not a universally valid logical
//! primitive — so they are handled by the sibling
//! [`crate::nat_order_substitution`] module, which admits under the stream's
//! own declared type rather than one this module invents; see that module's
//! own doc comment for why.
//!
//! `eq_of_heq` was added the same way once
//! `docs/autogenesis/236-…`/`237-…` measured it as the single largest
//! *first-reported* blocker (41 of 114 rows) once `congrArg`/`congr`/`mt` no
//! longer shadowed it. `HEq` (heterogeneous equality) is, like `Eq`, a
//! universal logical primitive — an `Inductive` with one constructor
//! `HEq.refl` — never stream-specific data, so this builds both the type and
//! the value itself exactly like `congrArg`/`Eq.symm`, never reading the
//! stream's own `eq_of_heq` record. The construction mirrors Lean 4 core's
//! own `eq_of_heq` verbatim (confirmed by inspecting a real stream's `thm`
//! record for it): generalize over an *independent* type variable `β` and
//! transport across the type-level equality `α = β` via `cast`, because
//! `HEq.rec`'s motive necessarily varies in `β` (unlike `Eq.rec`, which fixes
//! a single carrier). The refl case needs `cast α α h a` to reduce
//! definitionally to `a` for an *arbitrary* proof `h : α = α` (not just
//! `Eq.refl`), which is exactly what `axeyum-lean-kernel`'s K-like reduction
//! (`crates/axeyum-lean-kernel/tests/k_like_reduction.rs`) exists for; the
//! `eq_of_heq_reconstructs_and_kernel_checks` test below is the confirmation
//! that this kernel's own K-like support is strong enough to typecheck it,
//! not an assumption.
//!
//! `cast` itself is referenced directly by name (a `Definition`, never
//! Axiom/Theorem/Opaque/Quotient) rather than rebuilt from `Eq.rec` — the
//! same discipline `nat_order_substitution` uses for the stream's own
//! `Nat.pred`/`Nat.sub`/`Nat.ble`: reusing a non-trusted declaration by name
//! is not "citing the stream", only reusing a *theorem* would be.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, LevelId, NameId, ReducibilityHint,
};

/// The complete, reviewed set of trusted theorem names this module will
/// substitute a self-derived proof for. `propext` is a genuine axiom and must
/// never be added here.
///
/// `if_neg`/`ite_self`/`decide_eq_false` were added once
/// `docs/autogenesis/233-…`'s successor census measured them as 18+15+3 of
/// the frozen census's first-reported blockers once `congrArg`/`congr`/`mt`/
/// `Eq.symm`/`eq_of_heq` no longer shadowed them. All three are ordinary
/// `Decidable.rec` case splits on the *ambient instance* `h : Decidable c`
/// (never assumed to be `isFalse` or `isTrue`) — confirmed against a real
/// stream record (`ite`/`Decidable.decide`/`if_neg` in
/// `26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r015.ndjson`):
/// the `isFalse` branch closes by `Eq.refl` once `ite`/`Decidable.decide`
/// ι-reduces to the else/false arm; the `isTrue` branch is impossible under
/// the hypothesis (`hnc hc : False` / `h hp : False`) and closes via
/// `False.rec`. `ite_self` needs no impossibility at all — both branches of
/// `ite c a a` ι-reduce to `a`, so both minor premises are `Eq.refl`. No
/// `propext` needed anywhere, and this module never reads the stream's own
/// `if_neg`/`ite_self`/`decide_eq_false` value or type.
///
/// `if_pos`/`of_decide_eq_true`/`Or.elim` were added the same census cycle
/// once the successor census measured them as 18/3/15 of the first-reported
/// blockers once the names above no longer shadowed them. `if_pos` is
/// [`if_neg_pair`]'s exact mirror (branches swapped: `isFalse` is now the
/// impossible one, `isTrue` now closes trivially). `of_decide_eq_true` is
/// NOT [`decide_eq_false_pair`]'s mirror in the same simple sense — its
/// *given* hypothesis (`decide p inst = true`) itself mentions the
/// scrutinee `inst`, so it cannot be threaded in externally the way `Not
/// p`/`Not c` are elsewhere in this module; the motive has to quantify over
/// the hypothesis inside the `Decidable.rec` case split, and the impossible
/// `isFalse` branch needs a genuine `Bool.false ≠ Bool.true` discrimination
/// ([`bool_false_ne_true`], built via `Bool.rec` into `Prop` — the same
/// technique `nat_order_substitution::B::false_true_elim` uses inline, here
/// reconstructed against raw `Kernel` calls because this module never reads
/// the stream's own value or type). `Or.elim` is a different shape again: a
/// universal logical primitive over the stream's own `Or`/`Or.rec` (2-param,
/// 0-index, 2-constructor `Inductive` with a zero-universe-param recursor,
/// exactly like `Decidable`), built with a *constant* motive `fun _ => c`
/// rather than a case split — see [`discover_or`]'s and [`or_elim_pair`]'s
/// own doc comments for why neither branch needs a `False.rec` discharge.
///
/// `Or.resolve_right`/`ne_true_of_eq_false`/`dif_neg` were added the next
/// census cycle, once `Nat.lt_irrefl`/`Or.elim`/`if_pos`/`of_decide_eq_true`
/// no longer shadowed them (measured 15/3/18 of the first-reported
/// blockers). `Or.resolve_right` is [`or_elim_pair`]'s own shape specialized
/// rather than generalized: the same `Or.rec` case split with the same
/// constant motive `fun _ => a`, but the `Or.inr` branch is now impossible
/// (its own bound `hb : b` together with the *given* `nb : Not b` gives `nb
/// hb : False`, discharged by `False.rec` exactly like [`if_neg_pair`]'s
/// impossible branch) rather than handed a minor premise directly, and the
/// `Or.inl` branch is `id`. `ne_true_of_eq_false` needs no case split at
/// all: from `h : b = false` and the bound `h2 : b = true`, `Eq.trans
/// (Eq.symm h) h2 : Bool.false = Bool.true` is discharged by
/// [`bool_false_ne_true`] exactly as [`of_decide_eq_true_pair`]'s impossible
/// branch does — the only new plumbing is [`build_eq_symm`], `Eq.symm`'s own
/// construction factored out of [`eq_symm_pair`] so it can be reused inline
/// without declaring a standalone `Eq.symm`. `dif_neg` is the DEPENDENT
/// `if`: the same `Decidable.rec` case split as [`if_neg_pair`], but its
/// branch arguments are themselves functions (`t : c -> α`, `e : Not c ->
/// α`) rather than plain values, and the conclusion targets `e hnc` rather
/// than bare `e` — the isFalse branch's own bound `hnc' : Not c` need not
/// equal the *given* `hnc` syntactically for `Eq.refl (e hnc')` to also
/// prove `Eq α (e hnc') (e hnc)`, because this kernel's definitional PROOF
/// IRRELEVANCE (`tc.rs`'s `proof_irrel_eq`, reached through `def_eq_app`'s
/// pointwise argument check) identifies any two proofs of `Not c : Prop`
/// outright; see [`dif_neg_pair`]'s own doc comment.
pub(crate) const SUBSTITUTABLE_THEOREMS: &[&str] = &[
    "congrArg",
    "congr",
    "mt",
    "Eq.symm",
    "eq_of_heq",
    "if_neg",
    "ite_self",
    "decide_eq_false",
    "if_pos",
    "of_decide_eq_true",
    "Or.elim",
    "Or.resolve_right",
    "ne_true_of_eq_false",
    "dif_neg",
    "dif_pos",
    "Eq.subst",
    "And.left",
];

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

pub(crate) fn exact_name(
    kernel: &Kernel,
    rendered: &'static str,
) -> Result<NameId, SubstitutionError> {
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
/// `producers::bounded_induction::discover_eq_primitives` uses for the same
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

/// `(name : ty) -> body[fv]` — the `Pi` (type-level) counterpart of
/// [`lam_fv`], for a binder whose body is itself a *type* (e.g. one more
/// argument of a motive that returns `Sort _`), not a value.
fn pi_fv(
    kernel: &mut Kernel,
    name: NameId,
    fv: u64,
    ty: ExprId,
    body: ExprId,
    info: BinderInfo,
) -> ExprId {
    let abstracted = kernel.abstract_fvars(body, &[fv]);
    kernel.pi(name, ty, abstracted, info)
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

/// `Eq.symm`'s value at a specific `(level, carrier, x, y, proof)` — the
/// same `Eq.rec` transport [`eq_symm_pair`] wraps into a standalone
/// declaration, factored out so other constructions
/// ([`ne_true_of_eq_false_pair`]) can reuse it inline without declaring an
/// intermediate `Eq.symm`.
#[allow(clippy::too_many_arguments)]
fn build_eq_symm(
    kernel: &mut Kernel,
    eqp: &EqPrimitives,
    next_fvar: &mut u64,
    level: LevelId,
    carrier: ExprId,
    x: ExprId,
    y: ExprId,
    proof: ExprId,
) -> ExprId {
    let anon = kernel.anon();
    // motive := fun (z : carrier) (_ : Eq level carrier x z) => Eq level carrier z x
    let z_fv = fresh(next_fvar);
    let z = kernel.fvar(z_fv);
    let concl = build_eq(kernel, eqp.eq, level, carrier, z, x);
    let hyp_ty = build_eq(kernel, eqp.eq, level, carrier, x, z);
    let anon_hyp = kernel.anon();
    let inner = kernel.lam(anon_hyp, hyp_ty, concl, BinderInfo::Default);
    let motive = lam_fv(kernel, anon, z_fv, carrier, inner, BinderInfo::Default);
    let refl_case = build_eq_refl(kernel, eqp.eq_refl, level, carrier, x);
    let zero = kernel.level_zero();
    let rec = kernel.const_(eqp.eq_rec, vec![zero, level]);
    let with_carrier = kernel.app(rec, carrier);
    let with_x = kernel.app(with_carrier, x);
    let with_motive = kernel.app(with_x, motive);
    let with_minor = kernel.app(with_motive, refl_case);
    let with_y = kernel.app(with_minor, y);
    kernel.app(with_y, proof)
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

/// `Or`/`Or.inl`/`Or.inr`/`Or.rec`, discovered structurally rather than
/// assumed — the `Or.elim` analogue of [`discover_decidable`]. `Or a b :
/// Prop` is a 2-param (`a b : Prop`), 0-index, 2-constructor `Inductive`;
/// like [`discover_decidable`]'s own `Decidable`, `Or.rec` never gets an
/// elimination-universe parameter because a `Prop` with more than one
/// constructor cannot eliminate outside `Prop` — confirmed by this project's
/// own [`axeyum_lean_kernel::prelude`] construction of `Or.elim`, which is
/// the term-for-term recipe this function follows (`or_rec` with a *constant*
/// motive `fun _ => c`, never a case split that varies in the scrutinee, so
/// unlike [`if_neg_pair`]/[`decide_eq_false_pair`] neither branch is
/// "impossible" — both `ha : a -> c` and `hb : b -> c` are used verbatim as
/// the two minor premises).
struct OrPrimitives {
    or_: NameId,
    rec: NameId,
}

fn discover_or(kernel: &Kernel) -> Result<OrPrimitives, SubstitutionError> {
    let or_ = exact_name(kernel, "Or")?;
    match kernel.environment().get(or_) {
        Some(Declaration::Inductive {
            num_params,
            num_indices,
            ctor_names,
            ..
        }) if *num_params == 2 && *num_indices == 0 && ctor_names.len() == 2 => {}
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "Or is not a 2-param, 0-index, 2-constructor Inductive",
            ));
        }
    }
    let inl = exact_name(kernel, "Or.inl")?;
    if !matches!(
        kernel.environment().get(inl),
        Some(Declaration::Constructor { .. })
    ) {
        return Err(SubstitutionError::UnexpectedShape(
            "Or.inl is not a Constructor",
        ));
    }
    let inr = exact_name(kernel, "Or.inr")?;
    if !matches!(
        kernel.environment().get(inr),
        Some(Declaration::Constructor { .. })
    ) {
        return Err(SubstitutionError::UnexpectedShape(
            "Or.inr is not a Constructor",
        ));
    }
    let rec = exact_name(kernel, "Or.rec")?;
    match kernel.environment().get(rec) {
        Some(Declaration::Recursor { uparams, .. }) if uparams.is_empty() => {}
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "Or.rec is not a zero-universe-param Recursor",
            ));
        }
    }
    Ok(OrPrimitives { or_, rec })
}

/// `Or.elim : {a b c : Prop} -> Or a b -> (a -> c) -> (b -> c) -> c`, via
/// `Or.rec` with the constant motive `fun _ => c` — see [`discover_or`]'s
/// doc comment for why neither branch needs a `False.rec` discharge.
#[allow(clippy::many_single_char_names, clippy::similar_names)]
fn or_elim_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let orp = discover_or(kernel)?;
    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let a_fv = fresh(&mut next_fvar);
    let a = kernel.fvar(a_fv);
    let b_fv = fresh(&mut next_fvar);
    let b = kernel.fvar(b_fv);
    let c_fv = fresh(&mut next_fvar);
    let c = kernel.fvar(c_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);
    let ha_fv = fresh(&mut next_fvar);
    let ha = kernel.fvar(ha_fv);
    let hb_fv = fresh(&mut next_fvar);
    let hb = kernel.fvar(hb_fv);

    let or_ab = {
        let head = kernel.const_(orp.or_, vec![]);
        let w1 = kernel.app(head, a);
        kernel.app(w1, b)
    };
    let ac = kernel.pi(anon, a, c, BinderInfo::Default);
    let bc = kernel.pi(anon, b, c, BinderInfo::Default);

    // motive := fun (_ : Or a b) => c
    let motive = {
        let ignore_fv = fresh(&mut next_fvar);
        lam_fv(kernel, anon, ignore_fv, or_ab, c, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(orp.rec, vec![]);
        let w1 = kernel.app(rec, a);
        let w2 = kernel.app(w1, b);
        let w3 = kernel.app(w2, motive);
        let w4 = kernel.app(w3, ha);
        let w5 = kernel.app(w4, hb);
        kernel.app(w5, h)
    };
    let type_body = c;

    let binders = [
        (a_fv, prop, BinderInfo::Implicit),
        (b_fv, prop, BinderInfo::Implicit),
        (c_fv, prop, BinderInfo::Implicit),
        (h_fv, or_ab, BinderInfo::Default),
        (ha_fv, ac, BinderInfo::Default),
        (hb_fv, bc, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![]))
}

/// `Eq.symm.{u} : {alpha : Sort u} -> {a b : alpha} -> Eq alpha a b -> Eq
/// alpha b a`, built directly from `Eq.rec` with motive `fun x _ => Eq alpha
/// x a` — never a hand-written `Eq.symm`.
#[allow(clippy::many_single_char_names)]
fn eq_symm_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);

    let alpha_fv = fresh(&mut next_fvar);
    let a_fv = fresh(&mut next_fvar);
    let b_fv = fresh(&mut next_fvar);
    let h_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let a = kernel.fvar(a_fv);
    let b = kernel.fvar(b_fv);
    let h = kernel.fvar(h_fv);

    let ty_h = build_eq(kernel, eqp.eq, u, alpha, a, b);

    let value_body = build_eq_symm(kernel, &eqp, &mut next_fvar, u, alpha, a, b, h);
    let type_body = build_eq(kernel, eqp.eq, u, alpha, b, a);

    let binders = [
        (alpha_fv, sort_u, BinderInfo::Default),
        (a_fv, alpha, BinderInfo::Default),
        (b_fv, alpha, BinderInfo::Default),
        (h_fv, ty_h, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name]))
}

/// The ambient `HEq`/`HEq.refl`/`HEq.rec`/`cast` primitives `eq_of_heq_pair`
/// depends on, discovered by exact display name and checked rather than
/// assumed, for the same reason [`discover_eq`] does.
struct HeqPrimitives {
    heq: NameId,
    heq_rec: NameId,
    cast: NameId,
}

fn discover_heq(kernel: &Kernel) -> Result<HeqPrimitives, SubstitutionError> {
    let heq = exact_name(kernel, "HEq")?;
    let heq_refl = exact_name(kernel, "HEq.refl")?;
    if !matches!(
        kernel.environment().get(heq_refl),
        Some(Declaration::Constructor { .. })
    ) {
        return Err(SubstitutionError::UnexpectedShape(
            "HEq.refl is not a Constructor",
        ));
    }
    let heq_rec = exact_name(kernel, "HEq.rec")?;
    let Some(Declaration::Recursor { uparams, .. }) = kernel.environment().get(heq_rec) else {
        return Err(SubstitutionError::UnexpectedShape(
            "HEq.rec is not a Recursor declaration",
        ));
    };
    if uparams.len() != 2 {
        return Err(SubstitutionError::UnexpectedShape(
            "HEq.rec does not have exactly two universe parameters",
        ));
    }
    let cast_name = exact_name(kernel, "cast")?;
    match kernel.environment().get(cast_name) {
        Some(Declaration::Definition { uparams, hint, .. })
            if uparams.len() == 1 && !matches!(hint, ReducibilityHint::Opaque) => {}
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "cast is not a one-universe-param unfoldable Definition",
            ));
        }
    }
    Ok(HeqPrimitives {
        heq,
        heq_rec,
        cast: cast_name,
    })
}

/// `eq_of_heq.{u} : {alpha : Sort u} -> {a a' : alpha} -> HEq alpha a alpha
/// a' -> Eq alpha a a'`, built directly from `HEq.rec`/`cast` — mirroring
/// Lean 4 core's own definition verbatim (see this module's doc comment for
/// why the `cast`-across-`β` detour is unavoidable and what it depends on
/// the kernel for).
#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]
fn eq_of_heq_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let heqp = discover_heq(kernel)?;
    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let u = kernel.level_param(u_name);
    let u_plus1 = kernel.level_succ(u);
    let sort_u = kernel.sort(u);
    let zero = kernel.level_zero();

    let alpha_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let a_fv = fresh(&mut next_fvar);
    let a = kernel.fvar(a_fv);
    let ap_fv = fresh(&mut next_fvar);
    let ap = kernel.fvar(ap_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);

    let build_heq = |kernel: &mut Kernel, ty1: ExprId, x1: ExprId, ty2: ExprId, x2: ExprId| {
        let head = kernel.const_(heqp.heq, vec![u]);
        let w1 = kernel.app(head, ty1);
        let w2 = kernel.app(w1, x1);
        let w3 = kernel.app(w2, ty2);
        kernel.app(w3, x2)
    };
    let cast_at = |kernel: &mut Kernel, ty1: ExprId, ty2: ExprId, heq_ty_eq: ExprId, x: ExprId| {
        let head = kernel.const_(heqp.cast, vec![u]);
        let w1 = kernel.app(head, ty1);
        let w2 = kernel.app(w1, ty2);
        let w3 = kernel.app(w2, heq_ty_eq);
        kernel.app(w3, x)
    };

    let ty_h = build_heq(kernel, alpha, a, alpha, ap);

    // motive := fun (beta:Sort u) (b:beta) (_:HEq alpha a beta b) =>
    //   (heq_ty : Eq.{u+1} (Sort u) alpha beta) -> Eq beta (cast alpha beta heq_ty a) b
    let beta_fv = fresh(&mut next_fvar);
    let beta = kernel.fvar(beta_fv);
    let b_fv = fresh(&mut next_fvar);
    let b = kernel.fvar(b_fv);
    let witness_fv = fresh(&mut next_fvar);
    let heq_ty_eq_fv = fresh(&mut next_fvar);
    let heq_ty_eq = kernel.fvar(heq_ty_eq_fv);
    let motive = {
        let cast_app = cast_at(kernel, alpha, beta, heq_ty_eq, a);
        let concl = build_eq(kernel, eqp.eq, u, beta, cast_app, b);
        let heq_ty_eq_ty = build_eq(kernel, eqp.eq, u_plus1, sort_u, alpha, beta);
        let inner = pi_fv(
            kernel,
            anon,
            heq_ty_eq_fv,
            heq_ty_eq_ty,
            concl,
            BinderInfo::Default,
        );
        let witness_ty = build_heq(kernel, alpha, a, beta, b);
        let with_witness = lam_fv(
            kernel,
            anon,
            witness_fv,
            witness_ty,
            inner,
            BinderInfo::Default,
        );
        let with_b = lam_fv(kernel, anon, b_fv, beta, with_witness, BinderInfo::Default);
        lam_fv(kernel, anon, beta_fv, sort_u, with_b, BinderInfo::Default)
    };

    // refl_case : (heq_ty : Eq.{u+1} (Sort u) alpha alpha) -> Eq alpha (cast alpha alpha heq_ty a) a
    let refl_case = {
        let heq_ty_eq2_fv = fresh(&mut next_fvar);
        let heq_ty_eq2 = kernel.fvar(heq_ty_eq2_fv);
        let cast_app = cast_at(kernel, alpha, alpha, heq_ty_eq2, a);
        let refl_proof = build_eq_refl(kernel, eqp.eq_refl, u, alpha, cast_app);
        let heq_ty_eq2_ty = build_eq(kernel, eqp.eq, u_plus1, sort_u, alpha, alpha);
        lam_fv(
            kernel,
            anon,
            heq_ty_eq2_fv,
            heq_ty_eq2_ty,
            refl_proof,
            BinderInfo::Default,
        )
    };

    // this := HEq.rec.{0,u} alpha a motive refl_case alpha ap h
    //   : (heq_ty : Eq.{u+1} (Sort u) alpha alpha) -> Eq alpha (cast alpha alpha heq_ty a) ap
    let this = {
        let rec = kernel.const_(heqp.heq_rec, vec![zero, u]);
        let w1 = kernel.app(rec, alpha);
        let w2 = kernel.app(w1, a);
        let w3 = kernel.app(w2, motive);
        let w4 = kernel.app(w3, refl_case);
        let w5 = kernel.app(w4, alpha);
        let w6 = kernel.app(w5, ap);
        kernel.app(w6, h)
    };
    // eq_of_heq alpha a a' h := this (Eq.refl.{u+1} (Sort u) alpha) : Eq alpha (cast alpha alpha rfl a) a'
    // — independently re-verified below to be def-eq to the intended
    // `Eq alpha a a'` (relying on the kernel's own K-like reduction of
    // `cast alpha alpha rfl a` down to `a`, never assumed here).
    let alpha_self_eq = build_eq_refl(kernel, eqp.eq_refl, u_plus1, sort_u, alpha);
    let value_body = kernel.app(this, alpha_self_eq);
    let type_body = build_eq(kernel, eqp.eq, u, alpha, a, ap);

    let binders = [
        (alpha_fv, sort_u, BinderInfo::Default),
        (a_fv, alpha, BinderInfo::Default),
        (ap_fv, alpha, BinderInfo::Default),
        (h_fv, ty_h, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name]))
}

/// The `Decidable`/`Decidable.isFalse`/`Decidable.isTrue`/`Decidable.rec`
/// primitives `if_neg`/`ite_self`/`decide_eq_false` case-split on, discovered
/// structurally rather than assumed. `Decidable.rec` supports large
/// elimination (its motive may target any `Sort v`, not just `Prop`) exactly
/// like `Nat.rec` — confirmed by cross-checking a real stream's own
/// `Decidable.rec` `Recursor` record (`num_params: 1, num_indices: 0`,
/// exactly one universe parameter).
struct DecidablePrimitives {
    decidable: NameId,
    /// Checked (2-constructor shape) but never referenced by name afterward:
    /// [`if_neg_pair`]/[`ite_self_pair`]/[`decide_eq_false_pair`] build their
    /// `Decidable.rec` minor premises positionally (isFalse first, isTrue
    /// second, matching declaration order), never by constructing an
    /// explicit `Decidable.isFalse`/`Decidable.isTrue` application — the
    /// kernel's own recursor rule handles constructor substitution
    /// symbolically. Kept on the struct as the discovery record, not dead
    /// validation.
    #[allow(dead_code)]
    is_false: NameId,
    #[allow(dead_code)]
    is_true: NameId,
    rec: NameId,
}

fn discover_decidable(kernel: &Kernel) -> Result<DecidablePrimitives, SubstitutionError> {
    let decidable = exact_name(kernel, "Decidable")?;
    match kernel.environment().get(decidable) {
        Some(Declaration::Inductive {
            num_params,
            num_indices,
            ctor_names,
            ..
        }) if *num_params == 1 && *num_indices == 0 && ctor_names.len() == 2 => {}
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "Decidable is not a 1-param, 0-index, 2-constructor Inductive",
            ));
        }
    }
    let is_false = exact_name(kernel, "Decidable.isFalse")?;
    if !matches!(
        kernel.environment().get(is_false),
        Some(Declaration::Constructor { .. })
    ) {
        return Err(SubstitutionError::UnexpectedShape(
            "Decidable.isFalse is not a Constructor",
        ));
    }
    let is_true = exact_name(kernel, "Decidable.isTrue")?;
    if !matches!(
        kernel.environment().get(is_true),
        Some(Declaration::Constructor { .. })
    ) {
        return Err(SubstitutionError::UnexpectedShape(
            "Decidable.isTrue is not a Constructor",
        ));
    }
    let rec = exact_name(kernel, "Decidable.rec")?;
    let Some(Declaration::Recursor { uparams, .. }) = kernel.environment().get(rec) else {
        return Err(SubstitutionError::UnexpectedShape(
            "Decidable.rec is not a Recursor declaration",
        ));
    };
    if uparams.len() != 1 {
        return Err(SubstitutionError::UnexpectedShape(
            "Decidable.rec does not have exactly one universe parameter",
        ));
    }
    Ok(DecidablePrimitives {
        decidable,
        is_false,
        is_true,
        rec,
    })
}

/// `Not`, discovered as a zero-universe-param unfoldable `Definition` —
/// exactly [`mt_pair`]'s own inline check, factored out for reuse by
/// [`if_neg_pair`]/[`decide_eq_false_pair`] so a hypothesis of type `Not c`
/// can be applied directly to a proof of `c` and the kernel unfolds `Not c`
/// to `c -> False` to typecheck the application.
fn discover_not(kernel: &Kernel) -> Result<NameId, SubstitutionError> {
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
    Ok(not_name)
}

/// `False`/`False.rec`, discovered together — the zero-constructor
/// `Inductive` and its large-eliminating `Recursor` (one universe parameter,
/// the target `Sort` of the motive), used by [`if_neg_pair`]/
/// [`decide_eq_false_pair`] to close the impossible `isTrue`/`isTrue` branch
/// from a derived `False`.
struct FalsePrimitives {
    false_: NameId,
    false_rec: NameId,
}

fn discover_false(kernel: &Kernel) -> Result<FalsePrimitives, SubstitutionError> {
    let false_ = exact_name(kernel, "False")?;
    match kernel.environment().get(false_) {
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
    let false_rec = exact_name(kernel, "False.rec")?;
    let Some(Declaration::Recursor { uparams, .. }) = kernel.environment().get(false_rec) else {
        return Err(SubstitutionError::UnexpectedShape(
            "False.rec is not a Recursor declaration",
        ));
    };
    if uparams.len() != 1 {
        return Err(SubstitutionError::UnexpectedShape(
            "False.rec does not have exactly one universe parameter",
        ));
    }
    Ok(FalsePrimitives { false_, false_rec })
}

/// `ite`, discovered as a one-universe-param (`α : Sort u`) unfoldable
/// `Definition` — needed so `ite α c (Decidable.isFalse c hnc) t e` /
/// `ite α c (Decidable.isTrue c hc) t e` ι-reduce to `e`/`t` respectively
/// once the kernel unfolds `ite` and iota-reduces the `Decidable.rec`
/// application inside it on the literal constructor supplied by a
/// [`DecidablePrimitives::rec`] minor premise.
fn discover_ite(kernel: &Kernel) -> Result<NameId, SubstitutionError> {
    let ite_name = exact_name(kernel, "ite")?;
    match kernel.environment().get(ite_name) {
        Some(Declaration::Definition { uparams, hint, .. })
            if uparams.len() == 1 && !matches!(hint, ReducibilityHint::Opaque) =>
        {
            Ok(ite_name)
        }
        _ => Err(SubstitutionError::UnexpectedShape(
            "ite is not a one-universe-param unfoldable Definition",
        )),
    }
}

/// `dite`, discovered as a one-universe-param (`α : Sort u`) unfoldable
/// `Definition` — the DEPENDENT-if analogue of [`discover_ite`]: needed so
/// `dite α c (Decidable.isFalse c hnc') t e` / `dite α c (Decidable.isTrue c
/// hc) t e` ι-reduce to `e hnc'`/`t hc` respectively once the kernel unfolds
/// `dite` and iota-reduces the `Decidable.rec` application inside it on the
/// literal constructor supplied by a [`DecidablePrimitives::rec`] minor
/// premise.
fn discover_dite(kernel: &Kernel) -> Result<NameId, SubstitutionError> {
    let dite_name = exact_name(kernel, "dite")?;
    match kernel.environment().get(dite_name) {
        Some(Declaration::Definition { uparams, hint, .. })
            if uparams.len() == 1 && !matches!(hint, ReducibilityHint::Opaque) =>
        {
            Ok(dite_name)
        }
        _ => Err(SubstitutionError::UnexpectedShape(
            "dite is not a one-universe-param unfoldable Definition",
        )),
    }
}

/// `Decidable.decide`, discovered as a zero-universe-param unfoldable
/// `Definition` — the `decide_eq_false_pair` analogue of [`discover_ite`].
fn discover_decide(kernel: &Kernel) -> Result<NameId, SubstitutionError> {
    let decide_name = exact_name(kernel, "Decidable.decide")?;
    match kernel.environment().get(decide_name) {
        Some(Declaration::Definition { uparams, hint, .. })
            if uparams.is_empty() && !matches!(hint, ReducibilityHint::Opaque) =>
        {
            Ok(decide_name)
        }
        _ => Err(SubstitutionError::UnexpectedShape(
            "Decidable.decide is not a zero-universe-param unfoldable Definition",
        )),
    }
}

/// `Bool`/`Bool.true`/`Bool.false`, discovered together for
/// [`decide_eq_false_pair`] — a zero-param, zero-index, 2-constructor
/// `Inductive` and its two `Constructor`s.
#[allow(clippy::struct_field_names)]
struct BoolPrimitives {
    bool_: NameId,
    true_: NameId,
    false_: NameId,
}

fn discover_bool(kernel: &Kernel) -> Result<BoolPrimitives, SubstitutionError> {
    let bool_ = exact_name(kernel, "Bool")?;
    match kernel.environment().get(bool_) {
        Some(Declaration::Inductive {
            num_params,
            num_indices,
            ctor_names,
            ..
        }) if *num_params == 0 && *num_indices == 0 && ctor_names.len() == 2 => {}
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "Bool is not a 0-param, 0-index, 2-constructor Inductive",
            ));
        }
    }
    let true_ = exact_name(kernel, "Bool.true")?;
    if !matches!(
        kernel.environment().get(true_),
        Some(Declaration::Constructor { .. })
    ) {
        return Err(SubstitutionError::UnexpectedShape(
            "Bool.true is not a Constructor",
        ));
    }
    let false_ = exact_name(kernel, "Bool.false")?;
    if !matches!(
        kernel.environment().get(false_),
        Some(Declaration::Constructor { .. })
    ) {
        return Err(SubstitutionError::UnexpectedShape(
            "Bool.false is not a Constructor",
        ));
    }
    Ok(BoolPrimitives {
        bool_,
        true_,
        false_,
    })
}

/// `Bool.rec`, discovered as a one-universe-param `Recursor` — `Bool` lives
/// in `Sort 1` (never `Prop`), so unlike `Or`/`And`/`Decidable`-into-`Prop`
/// eliminators, large elimination is always available and expected. Needed
/// by [`bool_false_ne_true`]'s discriminator.
fn discover_bool_rec(kernel: &Kernel) -> Result<NameId, SubstitutionError> {
    let bool_rec = exact_name(kernel, "Bool.rec")?;
    match kernel.environment().get(bool_rec) {
        Some(Declaration::Recursor { uparams, .. }) if uparams.len() == 1 => Ok(bool_rec),
        _ => Err(SubstitutionError::UnexpectedShape(
            "Bool.rec is not a one-universe-param Recursor",
        )),
    }
}

/// `True`/`True.intro`, discovered together — the one-constructor `Inductive`
/// and its `Constructor`, needed as the "true" leg of [`bool_false_ne_true`]'s
/// `Bool -> Prop` discriminator (`Bool.rec (fun _ => Prop) True False`).
struct TruePrimitives {
    true_: NameId,
    true_intro: NameId,
}

fn discover_true(kernel: &Kernel) -> Result<TruePrimitives, SubstitutionError> {
    let true_ = exact_name(kernel, "True")?;
    match kernel.environment().get(true_) {
        Some(Declaration::Inductive {
            num_params,
            num_indices,
            ctor_names,
            ..
        }) if *num_params == 0 && *num_indices == 0 && ctor_names.len() == 1 => {}
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "True is not a 0-param, 0-index, 1-constructor Inductive",
            ));
        }
    }
    let true_intro = exact_name(kernel, "True.intro")?;
    if !matches!(
        kernel.environment().get(true_intro),
        Some(Declaration::Constructor { .. })
    ) {
        return Err(SubstitutionError::UnexpectedShape(
            "True.intro is not a Constructor",
        ));
    }
    Ok(TruePrimitives { true_, true_intro })
}

/// `Bool.false = Bool.true -> False`, the discrimination this project's own
/// `nat_order_substitution::B::false_true_elim` builds inline against its own
/// `B` wrapper — reconstructed here term-for-term against raw `Kernel` calls
/// (this module's own style) because [`of_decide_eq_true_pair`]'s impossible
/// branch needs exactly this and has no external hypothesis to fall back on
/// the way [`if_neg_pair`]/[`decide_eq_false_pair`] do. Builds the
/// `Bool -> Prop` discriminator `Bool.rec (fun _ => Prop) True False` and
/// transports `equality` across it from the `True` side, giving a term of
/// `discriminator Bool.true = False` after ι-reduction.
#[allow(clippy::too_many_arguments)]
fn bool_false_ne_true(
    kernel: &mut Kernel,
    next_fvar: &mut u64,
    eqp: &EqPrimitives,
    boolp: &BoolPrimitives,
    bool_rec: NameId,
    truep: &TruePrimitives,
    falsep: &FalsePrimitives,
    equality: ExprId,
) -> ExprId {
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let prop = kernel.sort(zero);
    let bool_ty = kernel.const_(boolp.bool_, vec![]);
    let bool_false = kernel.const_(boolp.false_, vec![]);
    let bool_true = kernel.const_(boolp.true_, vec![]);

    // discriminator : Bool -> Prop := Bool.rec.{1} (fun _ => Prop) True False.
    let discriminator = {
        let ignore_fv = fresh(next_fvar);
        let motive = lam_fv(kernel, anon, ignore_fv, bool_ty, prop, BinderInfo::Default);
        let rec = kernel.const_(bool_rec, vec![one]);
        let true_prop = kernel.const_(truep.true_, vec![]);
        let false_prop = kernel.const_(falsep.false_, vec![]);
        let w1 = kernel.app(rec, motive);
        let w2 = kernel.app(w1, true_prop);
        kernel.app(w2, false_prop)
    };
    // motive := fun (value : Bool) (_ : Eq Bool false value) => discriminator value
    let motive = {
        let value_fv = fresh(next_fvar);
        let value = kernel.fvar(value_fv);
        let eq_ty = build_eq(kernel, eqp.eq, one, bool_ty, bool_false, value);
        let body = kernel.app(discriminator, value);
        let inner = kernel.lam(anon, eq_ty, body, BinderInfo::Default);
        lam_fv(kernel, anon, value_fv, bool_ty, inner, BinderInfo::Default)
    };
    let true_intro = kernel.const_(truep.true_intro, vec![]);
    let eq_rec = kernel.const_(eqp.eq_rec, vec![zero, one]);
    // Eq.rec bool_ty false_value motive true_intro true_value equality :
    // discriminator true_value, which is `False` after ι-reduction.
    let w1 = kernel.app(eq_rec, bool_ty);
    let w2 = kernel.app(w1, bool_false);
    let w3 = kernel.app(w2, motive);
    let w4 = kernel.app(w3, true_intro);
    let w5 = kernel.app(w4, bool_true);
    kernel.app(w5, equality)
}

/// `if_neg.{u} : {c : Prop} -> {h : Decidable c} -> Not c -> {α : Sort u} ->
/// {t e : α} -> Eq α (ite α c h t e) e`, case-splitting on the *ambient*
/// `h : Decidable c` via `Decidable.rec` (never assumed to be `isFalse`) —
/// see [`SUBSTITUTABLE_THEOREMS`]'s doc comment for the branch shapes.
#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]
fn if_neg_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let dp = discover_decidable(kernel)?;
    let ite_name = discover_ite(kernel)?;
    let not_name = discover_not(kernel)?;
    let falsep = discover_false(kernel)?;

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let c_fv = fresh(&mut next_fvar);
    let c = kernel.fvar(c_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);
    let hnc_fv = fresh(&mut next_fvar);
    let hnc = kernel.fvar(hnc_fv);
    let alpha_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let t_fv = fresh(&mut next_fvar);
    let t = kernel.fvar(t_fv);
    let e_fv = fresh(&mut next_fvar);
    let e = kernel.fvar(e_fv);

    let decidable_c = {
        let head = kernel.const_(dp.decidable, vec![]);
        kernel.app(head, c)
    };
    let not_c = {
        let head = kernel.const_(not_name, vec![]);
        kernel.app(head, c)
    };
    let ite_at = |kernel: &mut Kernel, inst: ExprId| -> ExprId {
        let head = kernel.const_(ite_name, vec![u]);
        let w1 = kernel.app(head, alpha);
        let w2 = kernel.app(w1, c);
        let w3 = kernel.app(w2, inst);
        let w4 = kernel.app(w3, t);
        kernel.app(w4, e)
    };

    // motive := fun (h' : Decidable c) => Eq alpha (ite alpha c h' t e) e
    let motive = {
        let hp_fv = fresh(&mut next_fvar);
        let hp = kernel.fvar(hp_fv);
        let ite_app = ite_at(kernel, hp);
        let body = build_eq(kernel, eqp.eq, u, alpha, ite_app, e);
        lam_fv(kernel, anon, hp_fv, decidable_c, body, BinderInfo::Default)
    };

    // isFalse case: `ite alpha c (isFalse hnc') t e` iota-reduces to `e`.
    let minor_false = {
        let hncp_fv = fresh(&mut next_fvar);
        let refl = build_eq_refl(kernel, eqp.eq_refl, u, alpha, e);
        lam_fv(kernel, anon, hncp_fv, not_c, refl, BinderInfo::Default)
    };

    // isTrue case: `ite alpha c (isTrue hc) t e` iota-reduces to `t`, but
    // `hnc hc : False` makes the branch impossible; discharge via False.rec
    // at motive `fun _ => Eq alpha t e`.
    let minor_true = {
        let hc_fv = fresh(&mut next_fvar);
        let hc = kernel.fvar(hc_fv);
        let target_ty = build_eq(kernel, eqp.eq, u, alpha, t, e);
        let false_ty = kernel.const_(falsep.false_, vec![]);
        let false_motive = kernel.lam(anon, false_ty, target_ty, BinderInfo::Default);
        let contradiction = kernel.app(hnc, hc);
        let rec = kernel.const_(falsep.false_rec, vec![zero]);
        let w1 = kernel.app(rec, false_motive);
        let body = kernel.app(w1, contradiction);
        lam_fv(kernel, anon, hc_fv, c, body, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(dp.rec, vec![zero]);
        let w1 = kernel.app(rec, c);
        let w2 = kernel.app(w1, motive);
        let w3 = kernel.app(w2, minor_false);
        let w4 = kernel.app(w3, minor_true);
        kernel.app(w4, h)
    };
    let type_body = {
        let ite_h = ite_at(kernel, h);
        build_eq(kernel, eqp.eq, u, alpha, ite_h, e)
    };

    let binders = [
        (c_fv, prop, BinderInfo::Implicit),
        (h_fv, decidable_c, BinderInfo::InstImplicit),
        (hnc_fv, not_c, BinderInfo::Default),
        (alpha_fv, sort_u, BinderInfo::Implicit),
        (t_fv, alpha, BinderInfo::Implicit),
        (e_fv, alpha, BinderInfo::Implicit),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name]))
}

/// `if_pos.{u} : {c : Prop} -> {h : Decidable c} -> c -> {α : Sort u} -> {t e
/// : α} -> Eq α (ite α c h t e) t` — the mirror image of [`if_neg_pair`],
/// same `Decidable.rec` case split on the ambient `h : Decidable c`, branches
/// swapped: `isTrue` now closes trivially by `Eq.refl` (`ite` ι-reduces to
/// `t`), `isFalse` is now the impossible one (the *given* `hc : c` together
/// with the branch's own bound `hnc' : Not c` gives `hnc' hc : False`).
#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]
fn if_pos_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let dp = discover_decidable(kernel)?;
    let ite_name = discover_ite(kernel)?;
    let falsep = discover_false(kernel)?;

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let c_fv = fresh(&mut next_fvar);
    let c = kernel.fvar(c_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);
    let hc_fv = fresh(&mut next_fvar);
    let hc = kernel.fvar(hc_fv);
    let alpha_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let t_fv = fresh(&mut next_fvar);
    let t = kernel.fvar(t_fv);
    let e_fv = fresh(&mut next_fvar);
    let e = kernel.fvar(e_fv);

    let decidable_c = {
        let head = kernel.const_(dp.decidable, vec![]);
        kernel.app(head, c)
    };
    // `Not` is discovered fresh here rather than threaded in, exactly like
    // `ite_self_pair` does for its own `not_c` — [`if_neg_pair`] threads it
    // because it needs the *given* hypothesis to already carry type `Not c`;
    // here the given hypothesis is `hc : c` and `Not c` is only needed for
    // the impossible branch's own bound variable.
    let not_c = {
        let not_name = discover_not(kernel)?;
        let head = kernel.const_(not_name, vec![]);
        kernel.app(head, c)
    };
    let ite_at = |kernel: &mut Kernel, inst: ExprId| -> ExprId {
        let head = kernel.const_(ite_name, vec![u]);
        let w1 = kernel.app(head, alpha);
        let w2 = kernel.app(w1, c);
        let w3 = kernel.app(w2, inst);
        let w4 = kernel.app(w3, t);
        kernel.app(w4, e)
    };

    // motive := fun (h' : Decidable c) => Eq alpha (ite alpha c h' t e) t
    let motive = {
        let hp_fv = fresh(&mut next_fvar);
        let hp = kernel.fvar(hp_fv);
        let ite_app = ite_at(kernel, hp);
        let body = build_eq(kernel, eqp.eq, u, alpha, ite_app, t);
        lam_fv(kernel, anon, hp_fv, decidable_c, body, BinderInfo::Default)
    };

    // isFalse case: `ite alpha c (isFalse hnc') t e` iota-reduces to `e`, but
    // `hnc' hc : False` (the branch's own bound `hnc'` applied to the given
    // `hc`) makes the branch impossible; discharge via False.rec at motive
    // `fun _ => Eq alpha e t`.
    let minor_false = {
        let hncp_fv = fresh(&mut next_fvar);
        let hncp = kernel.fvar(hncp_fv);
        let target_ty = build_eq(kernel, eqp.eq, u, alpha, e, t);
        let false_ty = kernel.const_(falsep.false_, vec![]);
        let false_motive = kernel.lam(anon, false_ty, target_ty, BinderInfo::Default);
        let contradiction = kernel.app(hncp, hc);
        let rec = kernel.const_(falsep.false_rec, vec![zero]);
        let w1 = kernel.app(rec, false_motive);
        let body = kernel.app(w1, contradiction);
        lam_fv(kernel, anon, hncp_fv, not_c, body, BinderInfo::Default)
    };

    // isTrue case: `ite alpha c (isTrue hc') t e` iota-reduces to `t`.
    let minor_true = {
        let hcp_fv = fresh(&mut next_fvar);
        let refl = build_eq_refl(kernel, eqp.eq_refl, u, alpha, t);
        lam_fv(kernel, anon, hcp_fv, c, refl, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(dp.rec, vec![zero]);
        let w1 = kernel.app(rec, c);
        let w2 = kernel.app(w1, motive);
        let w3 = kernel.app(w2, minor_false);
        let w4 = kernel.app(w3, minor_true);
        kernel.app(w4, h)
    };
    let type_body = {
        let ite_h = ite_at(kernel, h);
        build_eq(kernel, eqp.eq, u, alpha, ite_h, t)
    };

    let binders = [
        (c_fv, prop, BinderInfo::Implicit),
        (h_fv, decidable_c, BinderInfo::InstImplicit),
        (hc_fv, c, BinderInfo::Default),
        (alpha_fv, sort_u, BinderInfo::Implicit),
        (t_fv, alpha, BinderInfo::Implicit),
        (e_fv, alpha, BinderInfo::Implicit),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name]))
}

/// `ite_self.{u} : {α : Sort u} -> {c : Prop} -> {d : Decidable c} -> (a : α)
/// -> Eq α (ite α c d a a) a`. Both `Decidable.rec` branches ι-reduce `ite α c
/// _ a a` to `a` (the then- and else-branch values coincide), so both minor
/// premises are `Eq.refl` — no impossibility, no `False.rec`, needed.
#[allow(clippy::many_single_char_names, clippy::similar_names)]
fn ite_self_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let dp = discover_decidable(kernel)?;
    let ite_name = discover_ite(kernel)?;

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let alpha_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let c_fv = fresh(&mut next_fvar);
    let c = kernel.fvar(c_fv);
    let d_fv = fresh(&mut next_fvar);
    let d = kernel.fvar(d_fv);
    let a_fv = fresh(&mut next_fvar);
    let a = kernel.fvar(a_fv);

    let decidable_c = {
        let head = kernel.const_(dp.decidable, vec![]);
        kernel.app(head, c)
    };
    let ite_at = |kernel: &mut Kernel, inst: ExprId| -> ExprId {
        let head = kernel.const_(ite_name, vec![u]);
        let w1 = kernel.app(head, alpha);
        let w2 = kernel.app(w1, c);
        let w3 = kernel.app(w2, inst);
        let w4 = kernel.app(w3, a);
        kernel.app(w4, a)
    };

    // motive := fun (d' : Decidable c) => Eq alpha (ite alpha c d' a a) a
    let motive = {
        let dp_fv = fresh(&mut next_fvar);
        let dpv = kernel.fvar(dp_fv);
        let ite_app = ite_at(kernel, dpv);
        let body = build_eq(kernel, eqp.eq, u, alpha, ite_app, a);
        lam_fv(kernel, anon, dp_fv, decidable_c, body, BinderInfo::Default)
    };

    let not_c = {
        // Only needed for the isFalse minor premise's own hypothesis type;
        // `Not` is discovered fresh here rather than threaded in, exactly
        // like `if_neg_pair`.
        let not_name = discover_not(kernel)?;
        let head = kernel.const_(not_name, vec![]);
        kernel.app(head, c)
    };
    let minor_false = {
        let hnc_fv = fresh(&mut next_fvar);
        let refl = build_eq_refl(kernel, eqp.eq_refl, u, alpha, a);
        lam_fv(kernel, anon, hnc_fv, not_c, refl, BinderInfo::Default)
    };
    let minor_true = {
        let hc_fv = fresh(&mut next_fvar);
        let refl = build_eq_refl(kernel, eqp.eq_refl, u, alpha, a);
        lam_fv(kernel, anon, hc_fv, c, refl, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(dp.rec, vec![zero]);
        let w1 = kernel.app(rec, c);
        let w2 = kernel.app(w1, motive);
        let w3 = kernel.app(w2, minor_false);
        let w4 = kernel.app(w3, minor_true);
        kernel.app(w4, d)
    };
    let type_body = {
        let ite_d = ite_at(kernel, d);
        build_eq(kernel, eqp.eq, u, alpha, ite_d, a)
    };

    let binders = [
        (alpha_fv, sort_u, BinderInfo::Implicit),
        (c_fv, prop, BinderInfo::Implicit),
        (d_fv, decidable_c, BinderInfo::InstImplicit),
        (a_fv, alpha, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name]))
}

/// `decide_eq_false : {p : Prop} -> {inst : Decidable p} -> Not p ->
/// Eq Bool (Decidable.decide p inst) Bool.false`. Same `Decidable.rec`
/// case-split shape as [`if_neg_pair`], targeting `Decidable.decide` instead
/// of `ite`: `isFalse` closes by `Eq.refl` once `decide` ι-reduces to
/// `Bool.false`; `isTrue` is impossible (`h hp : False`) and closes via
/// `False.rec`. No extra universe parameter — `Bool`/`Prop` are both fixed
/// sorts.
#[allow(clippy::many_single_char_names, clippy::similar_names)]
fn decide_eq_false_pair(
    kernel: &mut Kernel,
) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let dp = discover_decidable(kernel)?;
    let decide_name = discover_decide(kernel)?;
    let not_name = discover_not(kernel)?;
    let falsep = discover_false(kernel)?;
    let boolp = discover_bool(kernel)?;

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let prop = kernel.sort(zero);
    let bool_ty = kernel.const_(boolp.bool_, vec![]);
    let bool_false = kernel.const_(boolp.false_, vec![]);
    let bool_true = kernel.const_(boolp.true_, vec![]);

    let p_fv = fresh(&mut next_fvar);
    let p = kernel.fvar(p_fv);
    let inst_fv = fresh(&mut next_fvar);
    let inst = kernel.fvar(inst_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);

    let decidable_p = {
        let head = kernel.const_(dp.decidable, vec![]);
        kernel.app(head, p)
    };
    let not_p = {
        let head = kernel.const_(not_name, vec![]);
        kernel.app(head, p)
    };
    let decide_at = |kernel: &mut Kernel, i: ExprId| -> ExprId {
        let head = kernel.const_(decide_name, vec![]);
        let w1 = kernel.app(head, p);
        kernel.app(w1, i)
    };

    // motive := fun (inst' : Decidable p) => Eq Bool (decide p inst') false
    let motive = {
        let ip_fv = fresh(&mut next_fvar);
        let ipv = kernel.fvar(ip_fv);
        let decide_app = decide_at(kernel, ipv);
        let body = build_eq(kernel, eqp.eq, one, bool_ty, decide_app, bool_false);
        lam_fv(kernel, anon, ip_fv, decidable_p, body, BinderInfo::Default)
    };

    // isFalse case: `decide p (isFalse hnp)` iota-reduces to `Bool.false`.
    let minor_false = {
        let hnp_fv = fresh(&mut next_fvar);
        let refl = build_eq_refl(kernel, eqp.eq_refl, one, bool_ty, bool_false);
        lam_fv(kernel, anon, hnp_fv, not_p, refl, BinderInfo::Default)
    };

    // isTrue case: `decide p (isTrue hp)` iota-reduces to `Bool.true`, but
    // `h hp : False` makes the branch impossible.
    let minor_true = {
        let hp_fv = fresh(&mut next_fvar);
        let hp = kernel.fvar(hp_fv);
        let target_ty = build_eq(kernel, eqp.eq, one, bool_ty, bool_true, bool_false);
        let false_ty = kernel.const_(falsep.false_, vec![]);
        let false_motive = kernel.lam(anon, false_ty, target_ty, BinderInfo::Default);
        let contradiction = kernel.app(h, hp);
        let rec = kernel.const_(falsep.false_rec, vec![zero]);
        let w1 = kernel.app(rec, false_motive);
        let body = kernel.app(w1, contradiction);
        lam_fv(kernel, anon, hp_fv, p, body, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(dp.rec, vec![zero]);
        let w1 = kernel.app(rec, p);
        let w2 = kernel.app(w1, motive);
        let w3 = kernel.app(w2, minor_false);
        let w4 = kernel.app(w3, minor_true);
        kernel.app(w4, inst)
    };
    let type_body = {
        let decide_inst = decide_at(kernel, inst);
        build_eq(kernel, eqp.eq, one, bool_ty, decide_inst, bool_false)
    };

    let binders = [
        (p_fv, prop, BinderInfo::Implicit),
        (inst_fv, decidable_p, BinderInfo::InstImplicit),
        (h_fv, not_p, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![]))
}

/// `of_decide_eq_true : {p : Prop} -> {inst : Decidable p} -> Eq Bool
/// (Decidable.decide p inst) Bool.true -> p`. Unlike every other name in
/// [`SUBSTITUTABLE_THEOREMS`], the *given* hypothesis (`decide p inst =
/// true`) itself mentions the scrutinee `inst`, so it cannot be threaded in
/// externally the way [`if_neg_pair`]/[`decide_eq_false_pair`] thread `Not
/// c`/`Not p` — the motive must quantify over the hypothesis *inside* the
/// `Decidable.rec` case split (`fun inst' => decide p inst' = true -> p`),
/// exactly the shape
/// [`nat_order_substitution::build_le_of_ble_eq_true`](crate::nat_order_substitution)
/// uses for the same reason. `isFalse` (`hnp : Not p` bound): `decide p
/// (isFalse hnp)` ι-reduces to `Bool.false`, so the branch's own hypothesis
/// has type `Bool.false = Bool.true`, impossible via
/// [`bool_false_ne_true`] then `False.rec` into `p`. `isTrue` (`hp : p`
/// bound): trivial, the branch's hypothesis is discarded and `hp` returned
/// directly.
#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]
fn of_decide_eq_true_pair(
    kernel: &mut Kernel,
) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let dp = discover_decidable(kernel)?;
    let decide_name = discover_decide(kernel)?;
    let not_name = discover_not(kernel)?;
    let falsep = discover_false(kernel)?;
    let boolp = discover_bool(kernel)?;
    let bool_rec = discover_bool_rec(kernel)?;
    let truep = discover_true(kernel)?;

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let prop = kernel.sort(zero);
    let bool_ty = kernel.const_(boolp.bool_, vec![]);
    let bool_false = kernel.const_(boolp.false_, vec![]);
    let bool_true = kernel.const_(boolp.true_, vec![]);

    let p_fv = fresh(&mut next_fvar);
    let p = kernel.fvar(p_fv);
    let inst_fv = fresh(&mut next_fvar);
    let inst = kernel.fvar(inst_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);

    let decidable_p = {
        let head = kernel.const_(dp.decidable, vec![]);
        kernel.app(head, p)
    };
    let not_p = {
        let head = kernel.const_(not_name, vec![]);
        kernel.app(head, p)
    };
    let decide_at = |kernel: &mut Kernel, i: ExprId| -> ExprId {
        let head = kernel.const_(decide_name, vec![]);
        let w1 = kernel.app(head, p);
        kernel.app(w1, i)
    };

    // motive := fun (inst' : Decidable p) => Eq Bool (decide p inst') true -> p
    let motive = {
        let ip_fv = fresh(&mut next_fvar);
        let ipv = kernel.fvar(ip_fv);
        let decide_app = decide_at(kernel, ipv);
        let hyp_ty = build_eq(kernel, eqp.eq, one, bool_ty, decide_app, bool_true);
        let body = kernel.pi(anon, hyp_ty, p, BinderInfo::Default);
        lam_fv(kernel, anon, ip_fv, decidable_p, body, BinderInfo::Default)
    };

    // isFalse case: `decide p (isFalse hnp)` iota-reduces to `Bool.false`, so
    // this branch's own hypothesis has the impossible type
    // `Eq Bool Bool.false Bool.true`.
    let minor_false = {
        let hnp_fv = fresh(&mut next_fvar);
        let heq_fv = fresh(&mut next_fvar);
        let heq = kernel.fvar(heq_fv);
        let heq_ty = build_eq(kernel, eqp.eq, one, bool_ty, bool_false, bool_true);
        let contradiction = bool_false_ne_true(
            kernel,
            &mut next_fvar,
            &eqp,
            &boolp,
            bool_rec,
            &truep,
            &falsep,
            heq,
        );
        let false_ty = kernel.const_(falsep.false_, vec![]);
        let false_motive = kernel.lam(anon, false_ty, p, BinderInfo::Default);
        let rec = kernel.const_(falsep.false_rec, vec![zero]);
        let w1 = kernel.app(rec, false_motive);
        let derived_p = kernel.app(w1, contradiction);
        let inner = lam_fv(kernel, anon, heq_fv, heq_ty, derived_p, BinderInfo::Default);
        lam_fv(kernel, anon, hnp_fv, not_p, inner, BinderInfo::Default)
    };

    // isTrue case: `decide p (isTrue hp)` iota-reduces to `Bool.true`, so
    // this branch's own hypothesis is trivially satisfiable; discard it and
    // return the bound `hp : p` itself.
    let minor_true = {
        let hp_fv = fresh(&mut next_fvar);
        let hp = kernel.fvar(hp_fv);
        let heq_fv = fresh(&mut next_fvar);
        let heq_ty = build_eq(kernel, eqp.eq, one, bool_ty, bool_true, bool_true);
        let inner = lam_fv(kernel, anon, heq_fv, heq_ty, hp, BinderInfo::Default);
        lam_fv(kernel, anon, hp_fv, p, inner, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(dp.rec, vec![zero]);
        let w1 = kernel.app(rec, p);
        let w2 = kernel.app(w1, motive);
        let w3 = kernel.app(w2, minor_false);
        let w4 = kernel.app(w3, minor_true);
        let applied_to_inst = kernel.app(w4, inst);
        kernel.app(applied_to_inst, h)
    };
    let type_body = p;

    let hyp_ty = {
        let decide_inst = decide_at(kernel, inst);
        build_eq(kernel, eqp.eq, one, bool_ty, decide_inst, bool_true)
    };
    let binders = [
        (p_fv, prop, BinderInfo::Implicit),
        (inst_fv, decidable_p, BinderInfo::InstImplicit),
        (h_fv, hyp_ty, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![]))
}

/// `Or.resolve_right : {a b : Prop} -> Or a b -> Not b -> a`, via `Or.rec`
/// with the same constant motive `fun _ => a` [`or_elim_pair`] uses (see
/// [`discover_or`]'s doc comment for why `Or.rec` here has no elimination
/// universe parameter). Unlike `Or.elim`'s two minor premises, which are
/// both handed in directly, here the `Or.inr` branch must be discharged:
/// its own bound `hb : b` together with the *given* `nb : Not b` gives `nb
/// hb : False`, closed via `False.rec` into `a` exactly like
/// [`if_neg_pair`]'s impossible branch. The `Or.inl` branch is `id`.
#[allow(clippy::many_single_char_names, clippy::similar_names)]
fn or_resolve_right_pair(
    kernel: &mut Kernel,
) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let orp = discover_or(kernel)?;
    let not_name = discover_not(kernel)?;
    let falsep = discover_false(kernel)?;

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let a_fv = fresh(&mut next_fvar);
    let a = kernel.fvar(a_fv);
    let b_fv = fresh(&mut next_fvar);
    let b = kernel.fvar(b_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);
    let nb_fv = fresh(&mut next_fvar);
    let nb = kernel.fvar(nb_fv);

    let or_ab = {
        let head = kernel.const_(orp.or_, vec![]);
        let w1 = kernel.app(head, a);
        kernel.app(w1, b)
    };
    let not_b = {
        let head = kernel.const_(not_name, vec![]);
        kernel.app(head, b)
    };

    // motive := fun (_ : Or a b) => a
    let motive = {
        let ignore_fv = fresh(&mut next_fvar);
        lam_fv(kernel, anon, ignore_fv, or_ab, a, BinderInfo::Default)
    };

    // Or.inl branch: ha : a -> a := id.
    let minor_left = {
        let ha_fv = fresh(&mut next_fvar);
        let ha = kernel.fvar(ha_fv);
        lam_fv(kernel, anon, ha_fv, a, ha, BinderInfo::Default)
    };

    // Or.inr branch: hb : b bound; `nb hb : False` makes the branch
    // impossible, discharged via `False.rec` at motive `fun _ => a`.
    let minor_right = {
        let hb_fv = fresh(&mut next_fvar);
        let hb = kernel.fvar(hb_fv);
        let false_ty = kernel.const_(falsep.false_, vec![]);
        let false_motive = kernel.lam(anon, false_ty, a, BinderInfo::Default);
        let contradiction = kernel.app(nb, hb);
        let rec = kernel.const_(falsep.false_rec, vec![zero]);
        let w1 = kernel.app(rec, false_motive);
        let body = kernel.app(w1, contradiction);
        lam_fv(kernel, anon, hb_fv, b, body, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(orp.rec, vec![]);
        let w1 = kernel.app(rec, a);
        let w2 = kernel.app(w1, b);
        let w3 = kernel.app(w2, motive);
        let w4 = kernel.app(w3, minor_left);
        let w5 = kernel.app(w4, minor_right);
        kernel.app(w5, h)
    };
    let type_body = a;

    let binders = [
        (a_fv, prop, BinderInfo::Implicit),
        (b_fv, prop, BinderInfo::Implicit),
        (h_fv, or_ab, BinderInfo::Default),
        (nb_fv, not_b, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![]))
}

/// `ne_true_of_eq_false : {b : Bool} -> Eq Bool b Bool.false ->
/// Not (Eq Bool b Bool.true)` (`Not (Eq Bool b Bool.true)` unfolds to
/// `Eq Bool b Bool.true -> False`, exactly like [`mt_pair`]'s own `Not a`).
/// From the *given* `h : b = false` and the *bound* `h2 : b = true`,
/// `Eq.trans (Eq.symm h) h2 : Eq Bool Bool.false Bool.true`, discharged by
/// [`bool_false_ne_true`] exactly as [`of_decide_eq_true_pair`]'s
/// impossible branch does — the only new plumbing is [`build_eq_symm`].
#[allow(clippy::many_single_char_names, clippy::similar_names)]
fn ne_true_of_eq_false_pair(
    kernel: &mut Kernel,
) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let boolp = discover_bool(kernel)?;
    let bool_rec = discover_bool_rec(kernel)?;
    let truep = discover_true(kernel)?;
    let falsep = discover_false(kernel)?;
    let not_name = discover_not(kernel)?;

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let one = kernel.level_succ(zero);
    let bool_ty = kernel.const_(boolp.bool_, vec![]);
    let bool_false = kernel.const_(boolp.false_, vec![]);
    let bool_true = kernel.const_(boolp.true_, vec![]);

    let b_fv = fresh(&mut next_fvar);
    let b = kernel.fvar(b_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);
    let h2_fv = fresh(&mut next_fvar);
    let h2 = kernel.fvar(h2_fv);

    let h_ty = build_eq(kernel, eqp.eq, one, bool_ty, b, bool_false);
    let h2_ty = build_eq(kernel, eqp.eq, one, bool_ty, b, bool_true);

    let symm_h = build_eq_symm(kernel, &eqp, &mut next_fvar, one, bool_ty, b, bool_false, h);
    let contradiction_eq = build_trans(
        kernel,
        &eqp,
        &mut next_fvar,
        one,
        bool_ty,
        bool_false,
        b,
        symm_h,
        bool_true,
        h2,
    );
    let derived_false = bool_false_ne_true(
        kernel,
        &mut next_fvar,
        &eqp,
        &boolp,
        bool_rec,
        &truep,
        &falsep,
        contradiction_eq,
    );

    let not_b_true = {
        let head = kernel.const_(not_name, vec![]);
        kernel.app(head, h2_ty)
    };
    let value_body = lam_fv(
        kernel,
        anon,
        h2_fv,
        h2_ty,
        derived_false,
        BinderInfo::Default,
    );
    let type_body = not_b_true;

    let binders = [
        (b_fv, bool_ty, BinderInfo::Implicit),
        (h_fv, h_ty, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![]))
}

/// `dif_neg.{u} : {c : Prop} -> {h : Decidable c} -> (hnc : Not c) ->
/// {α : Sort u} -> {t : c -> α} -> {e : Not c -> α} ->
/// Eq α (dite α c h t e) (e hnc)`. The DEPENDENT `if`: the same
/// `Decidable.rec` case split as [`if_neg_pair`] on the *ambient*
/// `h : Decidable c`, but the two branch arguments are themselves functions
/// (`t : c -> α`, `e : Not c -> α`) rather than plain values of `α`, and the
/// conclusion's right-hand side is `e hnc`, not bare `e`.
///
/// The isFalse branch's own bound witness `hnc' : Not c` need not equal the
/// *given* `hnc` syntactically for `Eq.refl (e hnc')` to also prove
/// `Eq α (e hnc') (e hnc)` — `Not c : Prop`, so this kernel's definitional
/// proof irrelevance (`tc.rs`'s `proof_irrel_eq`, reached through
/// `def_eq_app`'s pointwise argument check when it compares `e hnc'`
/// against `e hnc`) identifies `hnc'` and `hnc` outright.
/// `if_neg`/`ite_self`/`decide_eq_false` never needed this because their
/// branch minors are plain values, never applied to the case-split witness.
/// isTrue is impossible exactly as in [`if_neg_pair`].
#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]
fn dif_neg_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let dp = discover_decidable(kernel)?;
    let dite_name = discover_dite(kernel)?;
    let not_name = discover_not(kernel)?;
    let falsep = discover_false(kernel)?;

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let c_fv = fresh(&mut next_fvar);
    let c = kernel.fvar(c_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);
    let hnc_fv = fresh(&mut next_fvar);
    let hnc = kernel.fvar(hnc_fv);
    let alpha_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let t_fv = fresh(&mut next_fvar);
    let t = kernel.fvar(t_fv);
    let e_fv = fresh(&mut next_fvar);
    let e = kernel.fvar(e_fv);

    let decidable_c = {
        let head = kernel.const_(dp.decidable, vec![]);
        kernel.app(head, c)
    };
    let not_c = {
        let head = kernel.const_(not_name, vec![]);
        kernel.app(head, c)
    };
    let ty_t = kernel.pi(anon, c, alpha, BinderInfo::Default);
    let ty_e = kernel.pi(anon, not_c, alpha, BinderInfo::Default);

    let dite_at = |kernel: &mut Kernel, inst: ExprId| -> ExprId {
        let head = kernel.const_(dite_name, vec![u]);
        let w1 = kernel.app(head, alpha);
        let w2 = kernel.app(w1, c);
        let w3 = kernel.app(w2, inst);
        let w4 = kernel.app(w3, t);
        kernel.app(w4, e)
    };

    let e_hnc = kernel.app(e, hnc);

    // motive := fun (h' : Decidable c) => Eq alpha (dite_at h') (e hnc)
    let motive = {
        let hp_fv = fresh(&mut next_fvar);
        let hp = kernel.fvar(hp_fv);
        let dite_app = dite_at(kernel, hp);
        let body = build_eq(kernel, eqp.eq, u, alpha, dite_app, e_hnc);
        lam_fv(kernel, anon, hp_fv, decidable_c, body, BinderInfo::Default)
    };

    // isFalse case: `dite alpha c (isFalse hnc') t e` iota-reduces to
    // `e hnc'`; `Eq.refl (e hnc')` also proves `Eq alpha (e hnc') (e hnc)`
    // because `hnc'` and `hnc` are both proofs of `Not c : Prop`.
    let minor_false = {
        let hncp_fv = fresh(&mut next_fvar);
        let hncp = kernel.fvar(hncp_fv);
        let e_hncp = kernel.app(e, hncp);
        let refl = build_eq_refl(kernel, eqp.eq_refl, u, alpha, e_hncp);
        lam_fv(kernel, anon, hncp_fv, not_c, refl, BinderInfo::Default)
    };

    // isTrue case: `dite alpha c (isTrue hc) t e` iota-reduces to `t hc`,
    // but `hnc hc : False` makes the branch impossible; discharge via
    // `False.rec` at motive `fun _ => Eq alpha (t hc) (e hnc)`.
    let minor_true = {
        let hc_fv = fresh(&mut next_fvar);
        let hc = kernel.fvar(hc_fv);
        let t_hc = kernel.app(t, hc);
        let target_ty = build_eq(kernel, eqp.eq, u, alpha, t_hc, e_hnc);
        let false_ty = kernel.const_(falsep.false_, vec![]);
        let false_motive = kernel.lam(anon, false_ty, target_ty, BinderInfo::Default);
        let contradiction = kernel.app(hnc, hc);
        let rec = kernel.const_(falsep.false_rec, vec![zero]);
        let w1 = kernel.app(rec, false_motive);
        let body = kernel.app(w1, contradiction);
        lam_fv(kernel, anon, hc_fv, c, body, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(dp.rec, vec![zero]);
        let w1 = kernel.app(rec, c);
        let w2 = kernel.app(w1, motive);
        let w3 = kernel.app(w2, minor_false);
        let w4 = kernel.app(w3, minor_true);
        kernel.app(w4, h)
    };
    let type_body = {
        let dite_h = dite_at(kernel, h);
        build_eq(kernel, eqp.eq, u, alpha, dite_h, e_hnc)
    };

    let binders = [
        (c_fv, prop, BinderInfo::Implicit),
        (h_fv, decidable_c, BinderInfo::InstImplicit),
        (hnc_fv, not_c, BinderInfo::Default),
        (alpha_fv, sort_u, BinderInfo::Implicit),
        (t_fv, ty_t, BinderInfo::Implicit),
        (e_fv, ty_e, BinderInfo::Implicit),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name]))
}

/// `dif_pos.{u} : {c : Prop} -> {h : Decidable c} -> (hc : c) ->
/// {α : Sort u} -> {t : c -> α} -> {e : Not c -> α} ->
/// Eq α (dite α c h t e) (t hc)`. [`dif_neg_pair`]'s exact mirror with the
/// two `Decidable.rec` branches swapped: the `isTrue` branch is now the one
/// that closes trivially (`dite α c (isTrue hc') t e` ι-reduces to `t hc'`,
/// and `Eq.refl (t hc')` also proves `Eq α (t hc') (t hc)` because `hc'` and
/// the given `hc` are both proofs of `c : Prop` and this kernel's
/// definitional proof irrelevance identifies them), and the `isFalse` branch
/// is the impossible one (`hnc hc : False`, discharged by `False.rec`).
///
/// Measured 2026-09-05 as the fourth-largest first-reported blocker of the
/// statement-import census (34 of 756 rows, ADR-1662). Its own exported
/// closure carries no axiom: `Not`, `Decidable`, `dite`, `Decidable.casesOn`,
/// `rfl` and `absurd` are all Definitions/Inductives, so nothing here reads
/// the stream's `dif_pos` value or type.
#[allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines
)]
fn dif_pos_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let dp = discover_decidable(kernel)?;
    let dite_name = discover_dite(kernel)?;
    let not_name = discover_not(kernel)?;
    let falsep = discover_false(kernel)?;

    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let c_fv = fresh(&mut next_fvar);
    let c = kernel.fvar(c_fv);
    let h_fv = fresh(&mut next_fvar);
    let h = kernel.fvar(h_fv);
    let hc_fv = fresh(&mut next_fvar);
    let hc = kernel.fvar(hc_fv);
    let alpha_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let t_fv = fresh(&mut next_fvar);
    let t = kernel.fvar(t_fv);
    let e_fv = fresh(&mut next_fvar);
    let e = kernel.fvar(e_fv);

    let decidable_c = {
        let head = kernel.const_(dp.decidable, vec![]);
        kernel.app(head, c)
    };
    let not_c = {
        let head = kernel.const_(not_name, vec![]);
        kernel.app(head, c)
    };
    let ty_t = kernel.pi(anon, c, alpha, BinderInfo::Default);
    let ty_e = kernel.pi(anon, not_c, alpha, BinderInfo::Default);

    let dite_at = |kernel: &mut Kernel, inst: ExprId| -> ExprId {
        let head = kernel.const_(dite_name, vec![u]);
        let w1 = kernel.app(head, alpha);
        let w2 = kernel.app(w1, c);
        let w3 = kernel.app(w2, inst);
        let w4 = kernel.app(w3, t);
        kernel.app(w4, e)
    };

    let t_hc = kernel.app(t, hc);

    // motive := fun (h' : Decidable c) => Eq alpha (dite_at h') (t hc)
    let motive = {
        let hp_fv = fresh(&mut next_fvar);
        let hp = kernel.fvar(hp_fv);
        let dite_app = dite_at(kernel, hp);
        let body = build_eq(kernel, eqp.eq, u, alpha, dite_app, t_hc);
        lam_fv(kernel, anon, hp_fv, decidable_c, body, BinderInfo::Default)
    };

    // isFalse case: `dite alpha c (isFalse hnc) t e` iota-reduces to `e hnc`,
    // but the branch's own `hnc : Not c` applied to the GIVEN `hc : c` gives
    // `False`; discharge via `False.rec` at motive
    // `fun _ => Eq alpha (e hnc) (t hc)`.
    let minor_false = {
        let hnc_fv = fresh(&mut next_fvar);
        let hnc = kernel.fvar(hnc_fv);
        let e_hnc = kernel.app(e, hnc);
        let target_ty = build_eq(kernel, eqp.eq, u, alpha, e_hnc, t_hc);
        let false_ty = kernel.const_(falsep.false_, vec![]);
        let false_motive = kernel.lam(anon, false_ty, target_ty, BinderInfo::Default);
        let contradiction = kernel.app(hnc, hc);
        let rec = kernel.const_(falsep.false_rec, vec![zero]);
        let w1 = kernel.app(rec, false_motive);
        let body = kernel.app(w1, contradiction);
        lam_fv(kernel, anon, hnc_fv, not_c, body, BinderInfo::Default)
    };

    // isTrue case: `dite alpha c (isTrue hc') t e` iota-reduces to `t hc'`;
    // `Eq.refl (t hc')` also proves `Eq alpha (t hc') (t hc)` because `hc'`
    // and `hc` are both proofs of `c : Prop` (definitional proof irrelevance,
    // exactly as in `dif_neg_pair`'s isFalse branch).
    let minor_true = {
        let hcp_fv = fresh(&mut next_fvar);
        let hcp = kernel.fvar(hcp_fv);
        let t_hcp = kernel.app(t, hcp);
        let refl = build_eq_refl(kernel, eqp.eq_refl, u, alpha, t_hcp);
        lam_fv(kernel, anon, hcp_fv, c, refl, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(dp.rec, vec![zero]);
        let w1 = kernel.app(rec, c);
        let w2 = kernel.app(w1, motive);
        let w3 = kernel.app(w2, minor_false);
        let w4 = kernel.app(w3, minor_true);
        kernel.app(w4, h)
    };
    let type_body = {
        let dite_h = dite_at(kernel, h);
        build_eq(kernel, eqp.eq, u, alpha, dite_h, t_hc)
    };

    let binders = [
        (c_fv, prop, BinderInfo::Implicit),
        (h_fv, decidable_c, BinderInfo::InstImplicit),
        (hc_fv, c, BinderInfo::Default),
        (alpha_fv, sort_u, BinderInfo::Implicit),
        (t_fv, ty_t, BinderInfo::Implicit),
        (e_fv, ty_e, BinderInfo::Implicit),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name]))
}

/// `Eq.subst.{u} : {α : Sort u} -> {motive : α -> Prop} -> {a b : α} ->
/// Eq α a b -> motive a -> motive b`, built directly from `Eq.rec` with the
/// motive `fun (x : α) (_ : Eq α a x) => motive x` — never a hand-written
/// `Eq.subst`, and never reading the stream's own `Eq.subst` record.
///
/// Lean 4.30 routes its own `Eq.subst` through the `Eq.ndrec` *Definition*;
/// that indirection is not reproduced here, because a `Definition` in the
/// closure is not a blocker and the shortest independent reconstruction is
/// the `Eq.rec` application `Eq.ndrec` unfolds to anyway. Measured
/// 2026-09-05 as the eighth first-reported blocker of the statement-import
/// census (7 of 756 rows, ADR-1662); its exported closure carries no axiom.
#[allow(clippy::many_single_char_names, clippy::similar_names)]
fn eq_subst_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let eqp = discover_eq(kernel)?;
    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let u_name = kernel.name_str(anon, "u");
    let u = kernel.level_param(u_name);
    let sort_u = kernel.sort(u);
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let alpha_fv = fresh(&mut next_fvar);
    let alpha = kernel.fvar(alpha_fv);
    let motive_fv = fresh(&mut next_fvar);
    let motive = kernel.fvar(motive_fv);
    let a_fv = fresh(&mut next_fvar);
    let a = kernel.fvar(a_fv);
    let b_fv = fresh(&mut next_fvar);
    let b = kernel.fvar(b_fv);
    let h1_fv = fresh(&mut next_fvar);
    let h1 = kernel.fvar(h1_fv);
    let h2_fv = fresh(&mut next_fvar);
    let h2 = kernel.fvar(h2_fv);

    let ty_motive = kernel.pi(anon, alpha, prop, BinderInfo::Default);
    let ty_h1 = build_eq(kernel, eqp.eq, u, alpha, a, b);
    let motive_a = kernel.app(motive, a);
    let motive_b = kernel.app(motive, b);

    // rec_motive := fun (x : α) (_ : Eq α a x) => motive x
    let rec_motive = {
        let x_fv = fresh(&mut next_fvar);
        let x = kernel.fvar(x_fv);
        let motive_x = kernel.app(motive, x);
        let hyp_ty = build_eq(kernel, eqp.eq, u, alpha, a, x);
        let anon_hyp = kernel.anon();
        let inner = kernel.lam(anon_hyp, hyp_ty, motive_x, BinderInfo::Default);
        lam_fv(kernel, anon, x_fv, alpha, inner, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(eqp.eq_rec, vec![zero, u]);
        let w1 = kernel.app(rec, alpha);
        let w2 = kernel.app(w1, a);
        let w3 = kernel.app(w2, rec_motive);
        let w4 = kernel.app(w3, h2);
        let w5 = kernel.app(w4, b);
        kernel.app(w5, h1)
    };
    let type_body = motive_b;

    let binders = [
        (alpha_fv, sort_u, BinderInfo::Implicit),
        (motive_fv, ty_motive, BinderInfo::Implicit),
        (a_fv, alpha, BinderInfo::Implicit),
        (b_fv, alpha, BinderInfo::Implicit),
        (h1_fv, ty_h1, BinderInfo::Default),
        (h2_fv, motive_a, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![u_name]))
}

/// The ambient `And`/`And.intro`/`And.rec` primitives, discovered by exact
/// display name and checked rather than assumed — the same discipline
/// [`discover_or`] uses, and for the same reason. `And` is a 2-parameter,
/// 0-index, single-constructor `Inductive` in `Prop` whose only fields are
/// proofs, so Lean gives it a LARGE-eliminating recursor (`And.rec` carries
/// one universe parameter); [`and_left_pair`] instantiates that parameter at
/// `0`, which is all it needs.
struct AndPrimitives {
    and_: NameId,
    rec: NameId,
}

fn discover_and(kernel: &Kernel) -> Result<AndPrimitives, SubstitutionError> {
    let and_ = exact_name(kernel, "And")?;
    match kernel.environment().get(and_) {
        Some(Declaration::Inductive {
            num_params,
            num_indices,
            ctor_names,
            ..
        }) if *num_params == 2 && *num_indices == 0 && ctor_names.len() == 1 => {}
        _ => {
            return Err(SubstitutionError::UnexpectedShape(
                "And is not a 2-param, 0-index, 1-constructor Inductive",
            ));
        }
    }
    let intro = exact_name(kernel, "And.intro")?;
    if !matches!(
        kernel.environment().get(intro),
        Some(Declaration::Constructor { .. })
    ) {
        return Err(SubstitutionError::UnexpectedShape(
            "And.intro is not a Constructor",
        ));
    }
    let rec = exact_name(kernel, "And.rec")?;
    let Some(Declaration::Recursor { uparams, .. }) = kernel.environment().get(rec) else {
        return Err(SubstitutionError::UnexpectedShape(
            "And.rec is not a Recursor declaration",
        ));
    };
    if uparams.len() != 1 {
        return Err(SubstitutionError::UnexpectedShape(
            "And.rec does not have exactly one universe parameter",
        ));
    }
    Ok(AndPrimitives { and_, rec })
}

/// `And.left : {a b : Prop} -> And a b -> a`, via `And.rec` at universe `0`
/// with the constant motive `fun _ => a` and the minor
/// `fun (left : a) (right : b) => left`.
///
/// Lean 4.30 exports its own `And.left` as a structure PROJECTION
/// (`self.0`); this reconstruction uses the recursor instead, because the
/// recursor is generated and checked by this kernel from the `And` inductive
/// in the same stream, while a projection would have to agree with the
/// stream's own structure metadata. Neither branch of that choice reads the
/// stream's `And.left` value or type. Measured 2026-09-05 as the seventh
/// first-reported blocker of the statement-import census (12 of 756 rows,
/// ADR-1662).
#[allow(clippy::many_single_char_names, clippy::similar_names)]
fn and_left_pair(kernel: &mut Kernel) -> Result<(ExprId, ExprId, Vec<NameId>), SubstitutionError> {
    let andp = discover_and(kernel)?;
    let mut next_fvar = FVAR_BASE;
    let anon = kernel.anon();
    let zero = kernel.level_zero();
    let prop = kernel.sort(zero);

    let a_fv = fresh(&mut next_fvar);
    let a = kernel.fvar(a_fv);
    let b_fv = fresh(&mut next_fvar);
    let b = kernel.fvar(b_fv);
    let self_fv = fresh(&mut next_fvar);
    let self_ = kernel.fvar(self_fv);

    let and_ab = {
        let head = kernel.const_(andp.and_, vec![]);
        let w1 = kernel.app(head, a);
        kernel.app(w1, b)
    };

    // motive := fun (_ : And a b) => a
    let motive = {
        let ignore_fv = fresh(&mut next_fvar);
        lam_fv(kernel, anon, ignore_fv, and_ab, a, BinderInfo::Default)
    };

    // minor := fun (left : a) (right : b) => left
    let minor = {
        let left_fv = fresh(&mut next_fvar);
        let left = kernel.fvar(left_fv);
        let right_fv = fresh(&mut next_fvar);
        let inner = lam_fv(kernel, anon, right_fv, b, left, BinderInfo::Default);
        lam_fv(kernel, anon, left_fv, a, inner, BinderInfo::Default)
    };

    let value_body = {
        let rec = kernel.const_(andp.rec, vec![zero]);
        let w1 = kernel.app(rec, a);
        let w2 = kernel.app(w1, b);
        let w3 = kernel.app(w2, motive);
        let w4 = kernel.app(w3, minor);
        kernel.app(w4, self_)
    };
    let type_body = a;

    let binders = [
        (a_fv, prop, BinderInfo::Implicit),
        (b_fv, prop, BinderInfo::Implicit),
        (self_fv, and_ab, BinderInfo::Default),
    ];
    let (value, ty) = close_telescope(kernel, &binders, value_body, type_body);
    Ok((value, ty, vec![]))
}

/// Attempt to reconstruct `rendered` as a kernel-checked declaration built
/// entirely from this module's own primitives, never from the untrusted
/// stream, **or** (for the twenty names in
/// [`nat_order_substitution::SUBSTITUTABLE_NAT_ORDER_THEOREMS`](crate::nat_order_substitution::SUBSTITUTABLE_NAT_ORDER_THEOREMS))
/// admitted under the stream's own declared type `wire_ty` with a proof this
/// module's sibling constructs — see that module's doc comment for why the
/// two shapes differ. Returns `Ok(None)` when `rendered` is not one of either
/// list — nothing to do, not a failure. Returns `Err(_)` when it is one of
/// these names but this kernel lacks the shape the reconstruction depends on,
/// or (for the `wire_ty`-checked path) the candidate failed to independently
/// type-check against it; the caller must treat both exactly like "not
/// substitutable" (fall back to the ordinary trusted-declaration refusal),
/// never as license to admit the untrusted value instead.
pub(crate) fn reconstruct(
    kernel: &mut Kernel,
    name: NameId,
    rendered: &str,
    wire_ty: ExprId,
) -> Result<Option<Declaration>, SubstitutionError> {
    if SUBSTITUTABLE_THEOREMS.contains(&rendered) {
        let (value, ty, uparams) = match rendered {
            "congrArg" => congr_arg_pair(kernel)?,
            "congr" => congr_pair(kernel)?,
            "mt" => mt_pair(kernel)?,
            "Eq.symm" => eq_symm_pair(kernel)?,
            "eq_of_heq" => eq_of_heq_pair(kernel)?,
            "if_neg" => if_neg_pair(kernel)?,
            "ite_self" => ite_self_pair(kernel)?,
            "decide_eq_false" => decide_eq_false_pair(kernel)?,
            "if_pos" => if_pos_pair(kernel)?,
            "of_decide_eq_true" => of_decide_eq_true_pair(kernel)?,
            "Or.elim" => or_elim_pair(kernel)?,
            "Or.resolve_right" => or_resolve_right_pair(kernel)?,
            "ne_true_of_eq_false" => ne_true_of_eq_false_pair(kernel)?,
            "dif_neg" => dif_neg_pair(kernel)?,
            "dif_pos" => dif_pos_pair(kernel)?,
            "Eq.subst" => eq_subst_pair(kernel)?,
            "And.left" => and_left_pair(kernel)?,
            _ => unreachable!("checked against SUBSTITUTABLE_THEOREMS above"),
        };
        return Ok(Some(Declaration::Theorem {
            name,
            uparams,
            ty,
            value,
        }));
    }
    if let Some(value) = crate::nat_order_substitution::reconstruct(kernel, rendered, wire_ty)? {
        return Ok(Some(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: wire_ty,
            value,
        }));
    }
    if let Some((value, uparams)) =
        crate::nat_no_confusion_substitution::reconstruct(kernel, rendered, wire_ty)?
    {
        return Ok(Some(Declaration::Theorem {
            name,
            uparams,
            ty: wire_ty,
            value,
        }));
    }
    if let Some(value) = crate::nat_le_brecon_substitution::reconstruct(kernel, rendered, wire_ty)?
    {
        return Ok(Some(Declaration::Theorem {
            name,
            uparams: vec![],
            ty: wire_ty,
            value,
        }));
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ImportLimits, import_ndjson};
    use std::io::Cursor;

    const QUOTIENT_FIXTURE: &str =
        include_str!("../../../docs/plan/fixtures/lean4export-v4.30-quotient.ndjson");

    // `pub(super)` so the sibling `c4_admission_tests` module can reuse the
    // same fixture rather than duplicating it.
    pub(super) fn fixture_kernel() -> Kernel {
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
    fn eq_symm_reconstructs_and_kernel_checks() {
        let mut kernel = fixture_kernel();
        let (value, ty, uparams) = eq_symm_pair(&mut kernel).expect("Eq.symm reconstructs");
        assert_eq!(uparams.len(), 1);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestEqSymm")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed Eq.symm must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn eq_symm_declines_when_eq_rec_is_missing() {
        let mut kernel = Kernel::new();
        assert!(matches!(
            eq_symm_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Eq"))
        ));
    }

    #[test]
    fn eq_of_heq_declines_when_heq_is_missing() {
        // The quotient fixture (used above) carries `Eq` but not `HEq`; this
        // must decline cleanly, never panic or fabricate.
        let mut kernel = fixture_kernel();
        assert!(matches!(
            eq_of_heq_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("HEq"))
        ));
    }

    /// The `reconstruct` entry point actually dispatches to
    /// `nat_order_substitution` for one of its twenty names — an
    /// integration test distinct from that module's own unit tests, which
    /// call its `reconstruct` directly rather than through this one.
    #[test]
    fn reconstruct_dispatches_to_nat_order_substitution() {
        use axeyum_lean_kernel::build_nat_prelude;
        let mut kernel = Kernel::new();
        // `Nat.pred_le_pred` (not `Nat.le_refl`) so this integration test
        // actually exercises the `Nat.le_trans` dependency chain, not just
        // the dispatch itself.
        let prelude = build_nat_prelude(&mut kernel).expect("nat prelude must build");
        let wire_ty = kernel
            .environment()
            .get(prelude.pred_le_pred)
            .expect("declared")
            .ty();
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDispatchPredLePred")
        };
        let declaration = reconstruct(&mut kernel, name, "Nat.pred_le_pred", wire_ty)
            .expect("Nat.pred_le_pred reconstructs")
            .expect("Nat.pred_le_pred is substitutable");
        kernel
            .add_declaration(declaration)
            .expect("dispatched reconstruction must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(
            kernel.theorem_dependencies(name).len(),
            0,
            "must not cite the reference kernel's own Nat.le_trans"
        );
    }

    #[test]
    fn reconstruct_rejects_names_outside_the_fixed_set() {
        let mut kernel = fixture_kernel();
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "propext")
        };
        let wire_ty = kernel.sort_zero();
        assert!(matches!(
            reconstruct(&mut kernel, name, "propext", wire_ty),
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

    /// Builds on [`fixture_kernel`] (which already carries a real, universe-
    /// polymorphic `Eq`/`Eq.refl`/`Eq.rec` from a genuine Lean export, never
    /// colliding with anything added here — the quotient fixture has no
    /// `False`/`Not`/`Bool`/`Decidable`) by adding, with raw `Kernel` calls
    /// exactly like `axeyum-lean-kernel::prelude`'s own `build_logic_prelude`
    /// does: `False` (0-ctor `Inductive`), `Not` (`Prop -> Prop` unfoldable
    /// `Definition`), `Bool` (0-param 2-ctor `Inductive` at `Sort 1`),
    /// `Decidable` (1-param 2-ctor `Inductive` at `Sort 1`, mirroring Lean
    /// core's own `isFalse (h : Not p) | isTrue (h : p)`), and the two
    /// `Decidable.rec`-based definitions `if_neg_pair`/`ite_self_pair`/
    /// `decide_eq_false_pair` themselves depend on, `ite` and
    /// `Decidable.decide` — each built term-for-term against a real stream's
    /// own record for it (confirmed 2026-08-22 against
    /// `26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams/r015.ndjson`).
    #[allow(
        clippy::many_single_char_names,
        clippy::similar_names,
        clippy::too_many_lines
    )]
    pub(super) fn decidable_test_kernel() -> Kernel {
        let mut kernel = fixture_kernel();
        let anon = kernel.anon();
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let prop = kernel.sort(zero);
        let sort1 = kernel.sort(one);
        let mut next_fvar = FVAR_BASE;

        // False : Prop, zero constructors.
        let false_name = kernel.name_str(anon, "False");
        kernel
            .add_inductive(false_name, &[], 0, prop, &[])
            .expect("False must admit");

        // Not (a : Prop) : Prop := a -> False.
        let not_name = kernel.name_str(anon, "Not");
        {
            let not_ty = kernel.pi(anon, prop, prop, BinderInfo::Default);
            let not_value = {
                let a_fv = fresh(&mut next_fvar);
                let a = kernel.fvar(a_fv);
                let false_const = kernel.const_(false_name, vec![]);
                let arrow = kernel.pi(anon, a, false_const, BinderInfo::Default);
                lam_fv(&mut kernel, anon, a_fv, prop, arrow, BinderInfo::Default)
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
        }

        // Bool : Sort 1, Bool.false | Bool.true.
        let bool_name = kernel.name_str(anon, "Bool");
        let bool_false = kernel.name_str(bool_name, "false");
        let bool_true = kernel.name_str(bool_name, "true");
        {
            let bool_const = kernel.const_(bool_name, vec![]);
            kernel
                .add_inductive(
                    bool_name,
                    &[],
                    0,
                    sort1,
                    &[(bool_false, bool_const), (bool_true, bool_const)],
                )
                .expect("Bool must admit");
        }

        // Decidable (p : Prop) : Sort 1,
        //   isFalse (p : Prop) (h : Not p) : Decidable p
        //   isTrue  (p : Prop) (h : p)     : Decidable p
        // (each constructor's own telescope re-quantifies the family
        // parameter `p`, exactly like `And.intro`'s in
        // `axeyum-lean-kernel::prelude::build_logic_prelude_uncached`.)
        let decidable_name = kernel.name_str(anon, "Decidable");
        let is_false_name = kernel.name_str(decidable_name, "isFalse");
        let is_true_name = kernel.name_str(decidable_name, "isTrue");
        {
            let decidable_ty = kernel.pi(anon, prop, sort1, BinderInfo::Default);
            let decidable_const = kernel.const_(decidable_name, vec![]);
            let not_const = kernel.const_(not_name, vec![]);
            let is_false_ty = {
                let p0 = kernel.bvar(0);
                let not_p = kernel.app(not_const, p0);
                let p1 = kernel.bvar(1);
                let decidable_p = kernel.app(decidable_const, p1);
                let inner = kernel.pi(anon, not_p, decidable_p, BinderInfo::Default);
                kernel.pi(anon, prop, inner, BinderInfo::Default)
            };
            let is_true_ty = {
                let p0 = kernel.bvar(0);
                let p1 = kernel.bvar(1);
                let decidable_p = kernel.app(decidable_const, p1);
                let inner = kernel.pi(anon, p0, decidable_p, BinderInfo::Default);
                kernel.pi(anon, prop, inner, BinderInfo::Default)
            };
            kernel
                .add_inductive(
                    decidable_name,
                    &[],
                    1,
                    decidable_ty,
                    &[(is_false_name, is_false_ty), (is_true_name, is_true_ty)],
                )
                .expect("Decidable must admit");
        }
        let decidable_rec = kernel.name_str(decidable_name, "rec");

        // ite {alpha : Sort u} (c : Prop) [h : Decidable c] (t e : alpha) : alpha :=
        //   Decidable.rec.{u} c (fun _ => alpha) (fun _ => e) (fun _ => t) h.
        let ite_name = kernel.name_str(anon, "ite");
        {
            let u_name = kernel.name_str(anon, "u");
            let u = kernel.level_param(u_name);
            let sort_u = kernel.sort(u);

            let alpha_fv = fresh(&mut next_fvar);
            let alpha = kernel.fvar(alpha_fv);
            let c_fv = fresh(&mut next_fvar);
            let c = kernel.fvar(c_fv);
            let h_fv = fresh(&mut next_fvar);
            let h = kernel.fvar(h_fv);
            let t_fv = fresh(&mut next_fvar);
            let t = kernel.fvar(t_fv);
            let e_fv = fresh(&mut next_fvar);
            let e = kernel.fvar(e_fv);

            let decidable_c = {
                let d = kernel.const_(decidable_name, vec![]);
                kernel.app(d, c)
            };
            let not_c = {
                let n = kernel.const_(not_name, vec![]);
                kernel.app(n, c)
            };
            let motive = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(
                    &mut kernel,
                    anon,
                    ignore_fv,
                    decidable_c,
                    alpha,
                    BinderInfo::Default,
                )
            };
            let minor_false = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(&mut kernel, anon, ignore_fv, not_c, e, BinderInfo::Default)
            };
            let minor_true = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(&mut kernel, anon, ignore_fv, c, t, BinderInfo::Default)
            };
            let value_body = {
                let rec = kernel.const_(decidable_rec, vec![u]);
                let w1 = kernel.app(rec, c);
                let w2 = kernel.app(w1, motive);
                let w3 = kernel.app(w2, minor_false);
                let w4 = kernel.app(w3, minor_true);
                kernel.app(w4, h)
            };
            let type_body = alpha;
            let binders = [
                (alpha_fv, sort_u, BinderInfo::Implicit),
                (c_fv, prop, BinderInfo::Default),
                (h_fv, decidable_c, BinderInfo::InstImplicit),
                (t_fv, alpha, BinderInfo::Default),
                (e_fv, alpha, BinderInfo::Default),
            ];
            let (ite_value, ite_ty) = close_telescope(&mut kernel, &binders, value_body, type_body);
            kernel
                .add_declaration(Declaration::Definition {
                    name: ite_name,
                    uparams: vec![u_name],
                    ty: ite_ty,
                    value: ite_value,
                    hint: ReducibilityHint::Regular(1),
                })
                .expect("ite must admit");
        }

        // dite {alpha : Sort u} (c : Prop) [h : Decidable c] (t : c -> alpha)
        //   (e : Not c -> alpha) : alpha := Decidable.rec.{u} c (fun _ => alpha) e t h.
        // Unlike `ite`'s `t`/`e` (plain values of `alpha`, wrapped in
        // constant-ignoring minors), `dite`'s `t`/`e` are already functions
        // of exactly the minor-premise domain (`c -> alpha`/`Not c -> alpha`),
        // so the minors are `e`/`t` directly — no extra wrapping lambda.
        let dite_name = kernel.name_str(anon, "dite");
        {
            let u_name = kernel.name_str(anon, "u");
            let u = kernel.level_param(u_name);
            let sort_u = kernel.sort(u);

            let alpha_fv = fresh(&mut next_fvar);
            let alpha = kernel.fvar(alpha_fv);
            let c_fv = fresh(&mut next_fvar);
            let c = kernel.fvar(c_fv);
            let h_fv = fresh(&mut next_fvar);
            let h = kernel.fvar(h_fv);
            let t_fv = fresh(&mut next_fvar);
            let t = kernel.fvar(t_fv);
            let e_fv = fresh(&mut next_fvar);
            let e = kernel.fvar(e_fv);

            let decidable_c = {
                let d = kernel.const_(decidable_name, vec![]);
                kernel.app(d, c)
            };
            let not_c = {
                let n = kernel.const_(not_name, vec![]);
                kernel.app(n, c)
            };
            let ty_t = kernel.pi(anon, c, alpha, BinderInfo::Default);
            let ty_e = kernel.pi(anon, not_c, alpha, BinderInfo::Default);
            let motive = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(
                    &mut kernel,
                    anon,
                    ignore_fv,
                    decidable_c,
                    alpha,
                    BinderInfo::Default,
                )
            };
            let value_body = {
                let rec = kernel.const_(decidable_rec, vec![u]);
                let w1 = kernel.app(rec, c);
                let w2 = kernel.app(w1, motive);
                let w3 = kernel.app(w2, e);
                let w4 = kernel.app(w3, t);
                kernel.app(w4, h)
            };
            let type_body = alpha;
            let binders = [
                (alpha_fv, sort_u, BinderInfo::Implicit),
                (c_fv, prop, BinderInfo::Default),
                (h_fv, decidable_c, BinderInfo::InstImplicit),
                (t_fv, ty_t, BinderInfo::Default),
                (e_fv, ty_e, BinderInfo::Default),
            ];
            let (dite_value, dite_ty) =
                close_telescope(&mut kernel, &binders, value_body, type_body);
            kernel
                .add_declaration(Declaration::Definition {
                    name: dite_name,
                    uparams: vec![u_name],
                    ty: dite_ty,
                    value: dite_value,
                    hint: ReducibilityHint::Regular(1),
                })
                .expect("dite must admit");
        }

        // Decidable.decide (p : Prop) [h : Decidable p] : Bool :=
        //   Decidable.rec.{1} p (fun _ => Bool) (fun _ => Bool.false)
        //     (fun _ => Bool.true) h.
        let decide_name = kernel.name_str(decidable_name, "decide");
        {
            let p_fv = fresh(&mut next_fvar);
            let p = kernel.fvar(p_fv);
            let h_fv = fresh(&mut next_fvar);
            let h = kernel.fvar(h_fv);
            let decidable_p = {
                let d = kernel.const_(decidable_name, vec![]);
                kernel.app(d, p)
            };
            let not_p = {
                let n = kernel.const_(not_name, vec![]);
                kernel.app(n, p)
            };
            let bool_ty_expr = kernel.const_(bool_name, vec![]);
            let bool_false_c = kernel.const_(bool_false, vec![]);
            let bool_true_c = kernel.const_(bool_true, vec![]);
            let motive = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(
                    &mut kernel,
                    anon,
                    ignore_fv,
                    decidable_p,
                    bool_ty_expr,
                    BinderInfo::Default,
                )
            };
            let minor_false = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(
                    &mut kernel,
                    anon,
                    ignore_fv,
                    not_p,
                    bool_false_c,
                    BinderInfo::Default,
                )
            };
            let minor_true = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(
                    &mut kernel,
                    anon,
                    ignore_fv,
                    p,
                    bool_true_c,
                    BinderInfo::Default,
                )
            };
            let value_body = {
                let rec = kernel.const_(decidable_rec, vec![one]);
                let w1 = kernel.app(rec, p);
                let w2 = kernel.app(w1, motive);
                let w3 = kernel.app(w2, minor_false);
                let w4 = kernel.app(w3, minor_true);
                kernel.app(w4, h)
            };
            let type_body = bool_ty_expr;
            let binders = [
                (p_fv, prop, BinderInfo::Default),
                (h_fv, decidable_p, BinderInfo::InstImplicit),
            ];
            let (decide_value, decide_ty) =
                close_telescope(&mut kernel, &binders, value_body, type_body);
            kernel
                .add_declaration(Declaration::Definition {
                    name: decide_name,
                    uparams: vec![],
                    ty: decide_ty,
                    value: decide_value,
                    hint: ReducibilityHint::Regular(1),
                })
                .expect("Decidable.decide must admit");
        }

        // True : Prop, one constructor `intro`. Needed only by
        // `of_decide_eq_true_pair`'s `bool_false_ne_true` discriminator, not
        // by `if_neg`/`ite_self`/`decide_eq_false` — added here anyway so
        // this one fixture covers every `Decidable`-based reconstruction.
        let true_name = kernel.name_str(anon, "True");
        let true_intro_name = kernel.name_str(true_name, "intro");
        {
            let true_const = kernel.const_(true_name, vec![]);
            kernel
                .add_inductive(true_name, &[], 0, prop, &[(true_intro_name, true_const)])
                .expect("True must admit");
        }

        kernel
    }

    #[test]
    fn if_neg_reconstructs_and_kernel_checks() {
        let mut kernel = decidable_test_kernel();
        let (value, ty, uparams) = if_neg_pair(&mut kernel).expect("if_neg reconstructs");
        assert_eq!(uparams.len(), 1);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestIfNeg")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed if_neg must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn if_neg_declines_when_decidable_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            if_neg_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable(
                "Decidable"
            ))
        ));
    }

    #[test]
    fn ite_self_reconstructs_and_kernel_checks() {
        let mut kernel = decidable_test_kernel();
        let (value, ty, uparams) = ite_self_pair(&mut kernel).expect("ite_self reconstructs");
        assert_eq!(uparams.len(), 1);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestIteSelf")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed ite_self must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn ite_self_declines_when_eq_is_missing() {
        // `ite_self_pair` discovers `Eq` first, exactly like every other
        // constructor in this module — mirrors
        // `congr_arg_declines_when_eq_rec_is_missing`.
        let mut kernel = Kernel::new();
        assert!(matches!(
            ite_self_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Eq"))
        ));
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    fn ite_self_declines_when_ite_is_missing() {
        // `decidable_test_kernel` has no removal hook, so build the narrower
        // claim directly: a kernel with `Eq`/`False`/`Not`/`Decidable` but no
        // `ite` (everything `decidable_test_kernel` builds up to, minus its
        // `ite`/`Decidable.decide` steps) declines on `ite` specifically —
        // confirming discovery reaches the SECOND primitive, not just `Eq`.
        let mut kernel = {
            let mut k = fixture_kernel();
            let anon = k.anon();
            let zero = k.level_zero();
            let one = k.level_succ(zero);
            let prop = k.sort(zero);
            let sort1 = k.sort(one);
            let false_name = k.name_str(anon, "False");
            k.add_inductive(false_name, &[], 0, prop, &[])
                .expect("False must admit");
            let not_name = k.name_str(anon, "Not");
            {
                let not_ty = k.pi(anon, prop, prop, BinderInfo::Default);
                let not_value = {
                    let a_fv = FVAR_BASE + 1;
                    let a = k.fvar(a_fv);
                    let false_const = k.const_(false_name, vec![]);
                    let arrow = k.pi(anon, a, false_const, BinderInfo::Default);
                    lam_fv(&mut k, anon, a_fv, prop, arrow, BinderInfo::Default)
                };
                k.add_declaration(Declaration::Definition {
                    name: not_name,
                    uparams: vec![],
                    ty: not_ty,
                    value: not_value,
                    hint: ReducibilityHint::Regular(1),
                })
                .expect("Not must admit");
            }
            let decidable_name = k.name_str(anon, "Decidable");
            let is_false_name = k.name_str(decidable_name, "isFalse");
            let is_true_name = k.name_str(decidable_name, "isTrue");
            let decidable_ty = k.pi(anon, prop, sort1, BinderInfo::Default);
            let decidable_const = k.const_(decidable_name, vec![]);
            let not_const = k.const_(not_name, vec![]);
            let is_false_ty = {
                let p0 = k.bvar(0);
                let not_p = k.app(not_const, p0);
                let p1 = k.bvar(1);
                let decidable_p = k.app(decidable_const, p1);
                let inner = k.pi(anon, not_p, decidable_p, BinderInfo::Default);
                k.pi(anon, prop, inner, BinderInfo::Default)
            };
            let is_true_ty = {
                let p0 = k.bvar(0);
                let p1 = k.bvar(1);
                let decidable_p = k.app(decidable_const, p1);
                let inner = k.pi(anon, p0, decidable_p, BinderInfo::Default);
                k.pi(anon, prop, inner, BinderInfo::Default)
            };
            k.add_inductive(
                decidable_name,
                &[],
                1,
                decidable_ty,
                &[(is_false_name, is_false_ty), (is_true_name, is_true_ty)],
            )
            .expect("Decidable must admit");
            k
        };
        assert!(matches!(
            ite_self_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("ite"))
        ));
    }

    #[test]
    fn decide_eq_false_reconstructs_and_kernel_checks() {
        let mut kernel = decidable_test_kernel();
        let (value, ty, uparams) =
            decide_eq_false_pair(&mut kernel).expect("decide_eq_false reconstructs");
        assert_eq!(uparams.len(), 0);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDecideEqFalse")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed decide_eq_false must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn decide_eq_false_declines_when_decidable_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            decide_eq_false_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable(
                "Decidable"
            ))
        ));
    }

    /// [`SUBSTITUTABLE_THEOREMS`] must dispatch the three new names, exactly
    /// like [`reconstruct_dispatches_to_nat_order_substitution`] confirms for
    /// the sibling module. Mutation target: deleting any one of the three new
    /// match arms in [`reconstruct`] must make exactly this test's assertion
    /// for that name fail (it would fall through to `unreachable!` instead,
    /// panicking rather than returning `Ok`).
    #[test]
    fn reconstruct_dispatches_decidable_case_splits() {
        for rendered in [
            "if_neg",
            "ite_self",
            "decide_eq_false",
            "if_pos",
            "of_decide_eq_true",
            "dif_neg",
        ] {
            let mut kernel = decidable_test_kernel();
            let name = {
                let root = kernel.anon();
                kernel.name_str(root, "TestDispatch")
            };
            let wire_ty = kernel.sort_zero();
            let result = reconstruct(&mut kernel, name, rendered, wire_ty);
            assert!(
                matches!(result, Ok(Some(Declaration::Theorem { .. }))),
                "{rendered}: expected Ok(Some(Theorem)), got {result:?}"
            );
        }
    }

    #[test]
    fn if_pos_reconstructs_and_kernel_checks() {
        let mut kernel = decidable_test_kernel();
        let (value, ty, uparams) = if_pos_pair(&mut kernel).expect("if_pos reconstructs");
        assert_eq!(uparams.len(), 1);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestIfPos")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed if_pos must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn if_pos_declines_when_decidable_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            if_pos_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable(
                "Decidable"
            ))
        ));
    }

    #[test]
    fn of_decide_eq_true_reconstructs_and_kernel_checks() {
        let mut kernel = decidable_test_kernel();
        let (value, ty, uparams) =
            of_decide_eq_true_pair(&mut kernel).expect("of_decide_eq_true reconstructs");
        assert_eq!(uparams.len(), 0);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestOfDecideEqTrue")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed of_decide_eq_true must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn of_decide_eq_true_declines_when_decidable_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            of_decide_eq_true_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable(
                "Decidable"
            ))
        ));
    }

    /// [`of_decide_eq_true_pair`] additionally needs `True`/`True.intro`
    /// (for [`bool_false_ne_true`]'s discriminator), unlike `if_neg`/
    /// `ite_self`/`decide_eq_false` — confirmed here by removing exactly
    /// that one declaration from an otherwise complete fixture. Mutation
    /// target: `discover_true`'s inductive-shape check.
    #[test]
    #[allow(clippy::too_many_lines)]
    fn of_decide_eq_true_declines_when_true_is_missing() {
        // `decidable_test_kernel` minus the trailing `True` construction:
        // everything `if_neg`/`ite_self`/`decide_eq_false` need, nothing
        // `of_decide_eq_true` additionally needs.
        let mut kernel = fixture_kernel();
        let anon = kernel.anon();
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let prop = kernel.sort(zero);
        let sort1 = kernel.sort(one);
        let mut next_fvar = FVAR_BASE + 10_000_000;

        let false_name = kernel.name_str(anon, "False");
        kernel
            .add_inductive(false_name, &[], 0, prop, &[])
            .expect("False must admit");
        let not_name = kernel.name_str(anon, "Not");
        {
            let not_ty = kernel.pi(anon, prop, prop, BinderInfo::Default);
            let not_value = {
                let a_fv = fresh(&mut next_fvar);
                let a = kernel.fvar(a_fv);
                let false_const = kernel.const_(false_name, vec![]);
                let arrow = kernel.pi(anon, a, false_const, BinderInfo::Default);
                lam_fv(&mut kernel, anon, a_fv, prop, arrow, BinderInfo::Default)
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
        }
        let bool_name = kernel.name_str(anon, "Bool");
        let bool_false = kernel.name_str(bool_name, "false");
        let bool_true = kernel.name_str(bool_name, "true");
        {
            let bool_const = kernel.const_(bool_name, vec![]);
            kernel
                .add_inductive(
                    bool_name,
                    &[],
                    0,
                    sort1,
                    &[(bool_false, bool_const), (bool_true, bool_const)],
                )
                .expect("Bool must admit");
        }
        let decidable_name = kernel.name_str(anon, "Decidable");
        let is_false_name = kernel.name_str(decidable_name, "isFalse");
        let is_true_name = kernel.name_str(decidable_name, "isTrue");
        {
            let decidable_ty = kernel.pi(anon, prop, sort1, BinderInfo::Default);
            let not_p = {
                let p1 = kernel.bvar(0);
                let n = kernel.const_(not_name, vec![]);
                kernel.app(n, p1)
            };
            let p_self = kernel.bvar(1);
            let is_false_ty = {
                let dec_p = {
                    let d = kernel.const_(decidable_name, vec![]);
                    kernel.app(d, p_self)
                };
                let inner = kernel.pi(anon, not_p, dec_p, BinderInfo::Default);
                kernel.pi(anon, prop, inner, BinderInfo::Default)
            };
            let is_true_ty = {
                let p1 = kernel.bvar(0);
                let dec_p = {
                    let d = kernel.const_(decidable_name, vec![]);
                    kernel.app(d, p_self)
                };
                let inner = kernel.pi(anon, p1, dec_p, BinderInfo::Default);
                kernel.pi(anon, prop, inner, BinderInfo::Default)
            };
            kernel
                .add_inductive(
                    decidable_name,
                    &[],
                    1,
                    decidable_ty,
                    &[(is_false_name, is_false_ty), (is_true_name, is_true_ty)],
                )
                .expect("Decidable must admit");
        }
        let decide_name = kernel.name_str(decidable_name, "decide");
        {
            let p_fv = fresh(&mut next_fvar);
            let p = kernel.fvar(p_fv);
            let h_fv = fresh(&mut next_fvar);
            let h = kernel.fvar(h_fv);
            let decidable_p = {
                let d = kernel.const_(decidable_name, vec![]);
                kernel.app(d, p)
            };
            let not_p = {
                let n = kernel.const_(not_name, vec![]);
                kernel.app(n, p)
            };
            let bool_ty_expr = kernel.const_(bool_name, vec![]);
            let bool_false_c = kernel.const_(bool_false, vec![]);
            let bool_true_c = kernel.const_(bool_true, vec![]);
            let motive = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(
                    &mut kernel,
                    anon,
                    ignore_fv,
                    decidable_p,
                    bool_ty_expr,
                    BinderInfo::Default,
                )
            };
            let minor_false = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(
                    &mut kernel,
                    anon,
                    ignore_fv,
                    not_p,
                    bool_false_c,
                    BinderInfo::Default,
                )
            };
            let minor_true = {
                let ignore_fv = fresh(&mut next_fvar);
                lam_fv(
                    &mut kernel,
                    anon,
                    ignore_fv,
                    p,
                    bool_true_c,
                    BinderInfo::Default,
                )
            };
            let value_body = {
                let decidable_rec_name = kernel.name_str(decidable_name, "rec");
                let rec = kernel.const_(decidable_rec_name, vec![one]);
                let w1 = kernel.app(rec, p);
                let w2 = kernel.app(w1, motive);
                let w3 = kernel.app(w2, minor_false);
                let w4 = kernel.app(w3, minor_true);
                kernel.app(w4, h)
            };
            let type_body = bool_ty_expr;
            let binders = [
                (p_fv, prop, BinderInfo::Default),
                (h_fv, decidable_p, BinderInfo::InstImplicit),
            ];
            let (decide_value, decide_ty) =
                close_telescope(&mut kernel, &binders, value_body, type_body);
            kernel
                .add_declaration(Declaration::Definition {
                    name: decide_name,
                    uparams: vec![],
                    ty: decide_ty,
                    value: decide_value,
                    hint: ReducibilityHint::Regular(1),
                })
                .expect("Decidable.decide must admit");
        }
        // Deliberately no `True`/`True.intro` here.
        assert!(matches!(
            of_decide_eq_true_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("True"))
        ));
    }

    #[test]
    fn dif_neg_reconstructs_and_kernel_checks() {
        let mut kernel = decidable_test_kernel();
        let (value, ty, uparams) = dif_neg_pair(&mut kernel).expect("dif_neg reconstructs");
        assert_eq!(uparams.len(), 1);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDifNeg")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed dif_neg must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn dif_neg_declines_when_decidable_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            dif_neg_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable(
                "Decidable"
            ))
        ));
    }

    /// [`dif_neg_pair`] additionally needs `dite`, unlike `if_neg`/
    /// `ite_self`/`decide_eq_false`/`if_pos`/`of_decide_eq_true` (which all
    /// case-split on `Decidable` via `ite`/`Decidable.decide` instead).
    /// Mutation target: [`discover_dite`]'s definition-shape check.
    #[test]
    fn dif_neg_declines_when_dite_is_missing() {
        // `decidable_test_kernel` builds `Decidable`/`ite`/`Decidable.decide`
        // but this check only needs `Decidable` present and `dite` absent,
        // so a plain `decidable_test_kernel()` minus the `dite` step would
        // require duplicating that whole fixture; instead confirm directly
        // that `exact_name` finds no `dite` in it once `dite` itself is
        // never declared — using the pre-`dite` fixture shape via
        // `fixture_kernel()` plus `Decidable` alone is not enough, since
        // `discover_decidable` must also succeed first. Build the minimal
        // shape here: `False`/`Not`/`Bool`/`Decidable`, no `ite`/`dite`.
        let mut kernel = fixture_kernel();
        let anon = kernel.anon();
        let zero = kernel.level_zero();
        let one = kernel.level_succ(zero);
        let prop = kernel.sort(zero);
        let sort1 = kernel.sort(one);
        let mut next_fvar = FVAR_BASE + 30_000_000;

        let false_name = kernel.name_str(anon, "False");
        kernel
            .add_inductive(false_name, &[], 0, prop, &[])
            .expect("False must admit");
        let not_name = kernel.name_str(anon, "Not");
        {
            let not_ty = kernel.pi(anon, prop, prop, BinderInfo::Default);
            let not_value = {
                let a_fv = fresh(&mut next_fvar);
                let a = kernel.fvar(a_fv);
                let false_const = kernel.const_(false_name, vec![]);
                let arrow = kernel.pi(anon, a, false_const, BinderInfo::Default);
                lam_fv(&mut kernel, anon, a_fv, prop, arrow, BinderInfo::Default)
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
        }
        let decidable_name = kernel.name_str(anon, "Decidable");
        let is_false_name = kernel.name_str(decidable_name, "isFalse");
        let is_true_name = kernel.name_str(decidable_name, "isTrue");
        {
            let decidable_ty = kernel.pi(anon, prop, sort1, BinderInfo::Default);
            let decidable_const = kernel.const_(decidable_name, vec![]);
            let not_const = kernel.const_(not_name, vec![]);
            let is_false_ty = {
                let p0 = kernel.bvar(0);
                let not_p = kernel.app(not_const, p0);
                let p1 = kernel.bvar(1);
                let decidable_p = kernel.app(decidable_const, p1);
                let inner = kernel.pi(anon, not_p, decidable_p, BinderInfo::Default);
                kernel.pi(anon, prop, inner, BinderInfo::Default)
            };
            let is_true_ty = {
                let p0 = kernel.bvar(0);
                let p1 = kernel.bvar(1);
                let decidable_p = kernel.app(decidable_const, p1);
                let inner = kernel.pi(anon, p0, decidable_p, BinderInfo::Default);
                kernel.pi(anon, prop, inner, BinderInfo::Default)
            };
            kernel
                .add_inductive(
                    decidable_name,
                    &[],
                    1,
                    decidable_ty,
                    &[(is_false_name, is_false_ty), (is_true_name, is_true_ty)],
                )
                .expect("Decidable must admit");
        }
        // Deliberately no `ite`/`dite` here.
        assert!(matches!(
            dif_neg_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("dite"))
        ));
    }

    #[test]
    fn ne_true_of_eq_false_reconstructs_and_kernel_checks() {
        let mut kernel = decidable_test_kernel();
        let (value, ty, uparams) =
            ne_true_of_eq_false_pair(&mut kernel).expect("ne_true_of_eq_false reconstructs");
        assert_eq!(uparams.len(), 0);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestNeTrueOfEqFalse")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed ne_true_of_eq_false must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn ne_true_of_eq_false_declines_when_bool_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            ne_true_of_eq_false_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Bool"))
        ));
    }

    /// [`SUBSTITUTABLE_THEOREMS`] must dispatch `dif_neg`/`ne_true_of_eq_false`
    /// exactly like [`reconstruct_dispatches_decidable_case_splits`] confirms
    /// for the earlier `Decidable`-based names. Mutation target: deleting
    /// either match arm in [`reconstruct`] makes exactly this test's
    /// assertion for that name fail.
    #[test]
    fn reconstruct_dispatches_dif_neg_and_ne_true_of_eq_false() {
        for rendered in ["dif_neg", "ne_true_of_eq_false"] {
            let mut kernel = decidable_test_kernel();
            let name = {
                let root = kernel.anon();
                kernel.name_str(root, "TestDispatch")
            };
            let wire_ty = kernel.sort_zero();
            let result = reconstruct(&mut kernel, name, rendered, wire_ty);
            assert!(
                matches!(result, Ok(Some(Declaration::Theorem { .. }))),
                "{rendered}: expected Ok(Some(Theorem)), got {result:?}"
            );
        }
    }

    #[allow(clippy::similar_names)]
    fn or_test_kernel() -> Kernel {
        let mut kernel = Kernel::new();
        let anon = kernel.anon();
        let zero = kernel.level_zero();
        let prop = kernel.sort(zero);
        let mut next_fvar = FVAR_BASE + 20_000_000;

        // False : Prop, zero constructors, and Not (a : Prop) : Prop := a ->
        // False — needed only by `or_resolve_right_pair`, not `or_elim_pair`,
        // added here anyway so this one fixture covers both `Or`
        // reconstructions.
        let false_name = kernel.name_str(anon, "False");
        kernel
            .add_inductive(false_name, &[], 0, prop, &[])
            .expect("False must admit");
        {
            let not_name = kernel.name_str(anon, "Not");
            let not_ty = kernel.pi(anon, prop, prop, BinderInfo::Default);
            let not_value = {
                let a_fv = fresh(&mut next_fvar);
                let a = kernel.fvar(a_fv);
                let false_const = kernel.const_(false_name, vec![]);
                let arrow = kernel.pi(anon, a, false_const, BinderInfo::Default);
                lam_fv(&mut kernel, anon, a_fv, prop, arrow, BinderInfo::Default)
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
        }

        let or_name = kernel.name_str(anon, "Or");
        let or_inl = kernel.name_str(or_name, "inl");
        let or_inr = kernel.name_str(or_name, "inr");
        let or_const = kernel.const_(or_name, vec![]);

        let or_ty = {
            let inner = kernel.pi(anon, prop, prop, BinderInfo::Default);
            kernel.pi(anon, prop, inner, BinderInfo::Default)
        };
        // Or.inl : Π (a b : Prop) (_ : a), Or a b.
        let inl_ty = {
            let a2 = kernel.bvar(2);
            let b1 = kernel.bvar(1);
            let or_ab = {
                let e = kernel.app(or_const, a2);
                kernel.app(e, b1)
            };
            let a1 = kernel.bvar(1);
            let inner_ha = kernel.pi(anon, a1, or_ab, BinderInfo::Default);
            let inner_b = kernel.pi(anon, prop, inner_ha, BinderInfo::Default);
            kernel.pi(anon, prop, inner_b, BinderInfo::Default)
        };
        // Or.inr : Π (a b : Prop) (_ : b), Or a b.
        let inr_ty = {
            let a2 = kernel.bvar(2);
            let b1 = kernel.bvar(1);
            let or_ab = {
                let e = kernel.app(or_const, a2);
                kernel.app(e, b1)
            };
            let b0 = kernel.bvar(0);
            let inner_hb = kernel.pi(anon, b0, or_ab, BinderInfo::Default);
            let inner_b = kernel.pi(anon, prop, inner_hb, BinderInfo::Default);
            kernel.pi(anon, prop, inner_b, BinderInfo::Default)
        };
        kernel
            .add_inductive(
                or_name,
                &[],
                2,
                or_ty,
                &[(or_inl, inl_ty), (or_inr, inr_ty)],
            )
            .expect("Or must admit");
        kernel
    }

    #[test]
    fn or_elim_reconstructs_and_kernel_checks() {
        let mut kernel = or_test_kernel();
        let (value, ty, uparams) = or_elim_pair(&mut kernel).expect("Or.elim reconstructs");
        assert_eq!(uparams.len(), 0);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestOrElim")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed Or.elim must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn or_elim_declines_when_or_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            or_elim_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Or"))
        ));
    }

    #[test]
    fn reconstruct_dispatches_or_elim() {
        let mut kernel = or_test_kernel();
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDispatchOrElim")
        };
        let wire_ty = kernel.sort_zero();
        let result = reconstruct(&mut kernel, name, "Or.elim", wire_ty);
        assert!(
            matches!(result, Ok(Some(Declaration::Theorem { .. }))),
            "Or.elim: expected Ok(Some(Theorem)), got {result:?}"
        );
    }

    #[test]
    fn or_resolve_right_reconstructs_and_kernel_checks() {
        let mut kernel = or_test_kernel();
        let (value, ty, uparams) =
            or_resolve_right_pair(&mut kernel).expect("Or.resolve_right reconstructs");
        assert_eq!(uparams.len(), 0);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestOrResolveRight")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed Or.resolve_right must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    #[test]
    fn or_resolve_right_declines_when_or_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            or_resolve_right_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Or"))
        ));
    }

    #[test]
    fn reconstruct_dispatches_or_resolve_right() {
        let mut kernel = or_test_kernel();
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDispatchOrResolveRight")
        };
        let wire_ty = kernel.sort_zero();
        let result = reconstruct(&mut kernel, name, "Or.resolve_right", wire_ty);
        assert!(
            matches!(result, Ok(Some(Declaration::Theorem { .. }))),
            "Or.resolve_right: expected Ok(Some(Theorem)), got {result:?}"
        );
    }
}

#[cfg(test)]
mod real_stream_eq_of_heq_tests {
    //! Not run by default (reads the frozen census archive, host-local under
    //! `/nas3`, not part of this repository). Run explicitly with
    //! `cargo test -p axeyum-lean-import --lib trusted_substitution::real_stream_eq_of_heq_tests -- --ignored --nocapture`,
    //! optionally overriding the directory with
    //! `AXEYUM_EQ_OF_HEQ_PROBE_DIR`. This is the independent, real-kernel
    //! confirmation that this crate's K-like reduction support is strong
    //! enough for `eq_of_heq_pair`'s refl case (see this module's doc
    //! comment) — not merely that it compiles.
    use super::*;
    use crate::{ImportLimits, import_ndjson};
    use std::fs::File;
    use std::io::BufReader;

    const DEFAULT_DIR: &str = "/nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams";

    #[test]
    #[ignore = "reads the frozen census archive under /nas3, not part of this repository"]
    fn probe_real_archive() {
        let dir =
            std::env::var("AXEYUM_EQ_OF_HEQ_PROBE_DIR").unwrap_or_else(|_| DEFAULT_DIR.into());
        let mut entries: Vec<_> = std::fs::read_dir(&dir)
            .unwrap_or_else(|e| panic!("read_dir {dir}: {e}"))
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| p.extension().is_some_and(|ext| ext == "ndjson"))
            .take(20)
            .collect();
        entries.sort();
        assert!(!entries.is_empty(), "no .ndjson files found under {dir}");

        let mut present = 0u32;
        let mut ok = 0u32;
        let mut failed = Vec::new();
        for path in &entries {
            let file = File::open(path).unwrap_or_else(|e| panic!("open {path:?}: {e}"));
            let reader = BufReader::new(file);
            let Ok(completed) = import_ndjson(reader, ImportLimits::default()) else {
                continue;
            };
            let (mut kernel, _report) = completed.into_parts();
            let has_eq_of_heq = kernel.environment().iter().any(|(name, decl)| {
                matches!(decl, Declaration::Theorem { .. })
                    && kernel.display_name(*name).to_string() == "eq_of_heq"
            });
            if !has_eq_of_heq {
                continue;
            }
            present += 1;
            match eq_of_heq_pair(&mut kernel) {
                Ok((value, ty, uparams)) => {
                    let name = {
                        let root = kernel.anon();
                        kernel.name_str(root, "ProbeReconstructEqOfHeq")
                    };
                    match kernel.add_declaration(Declaration::Theorem {
                        name,
                        uparams,
                        ty,
                        value,
                    }) {
                        Ok(()) => {
                            let footprint = kernel.axiom_footprint(name);
                            assert!(
                                footprint.is_empty(),
                                "{path:?}: nonempty axiom footprint {footprint:?}"
                            );
                            let deps = kernel.theorem_dependencies(name);
                            assert!(
                                deps.is_empty(),
                                "{path:?}: cites another theorem: {:?}",
                                deps.iter()
                                    .map(|&n| kernel.display_name(n).to_string())
                                    .collect::<Vec<_>>()
                            );
                            ok += 1;
                        }
                        Err(e) => failed.push(format!("{path:?}: admission failed: {e:?}")),
                    }
                }
                Err(e) => failed.push(format!("{path:?}: {e}")),
            }
        }
        println!("files examined: {}", entries.len());
        println!("eq_of_heq: present={present} ok={ok}");
        for e in &failed {
            println!("    decline: {e}");
        }
        assert!(present > 0, "no examined stream carried eq_of_heq");
        assert_eq!(
            ok, present,
            "eq_of_heq_pair must succeed on every present row"
        );
    }
}

/// Tests for the three C4 admission substitutions added 2026-09-05
/// (`dif_pos`, `Eq.subst`, `And.left`) — see ADR-1667 and the census artifact
/// `artifacts/measurements/statement-import-blocker-census-2026-09-05.json`.
///
/// Every one carries BOTH a positive control (the reconstruction is admitted
/// by [`Kernel::add_declaration`] at the type this module built, with an
/// empty axiom footprint and no cited theorem) and a NEGATIVE control (the
/// same reconstructed VALUE offered at a deliberately wrong type is REFUSED
/// by the kernel). The negative controls call `add_declaration` directly with
/// a hand-swapped type, so no Rust-side guard in this module participates —
/// the kernel is the only thing that can reject them, which is the point.
#[cfg(test)]
mod c4_admission_tests {
    use super::tests::{decidable_test_kernel, fixture_kernel};
    use super::*;

    /// `fixture_kernel()` plus a two-parameter, single-constructor `And` in
    /// `Prop` whose fields are both proofs — the shape Lean 4.30 exports, and
    /// the shape [`discover_and`] checks for.
    fn and_test_kernel() -> Kernel {
        let mut kernel = fixture_kernel();
        let anon = kernel.anon();
        let zero = kernel.level_zero();
        let prop = kernel.sort(zero);

        let and_name = kernel.name_str(anon, "And");
        let and_intro = kernel.name_str(and_name, "intro");
        let and_const = kernel.const_(and_name, vec![]);

        let and_ty = {
            let inner = kernel.pi(anon, prop, prop, BinderInfo::Default);
            kernel.pi(anon, prop, inner, BinderInfo::Default)
        };
        // And.intro : Pi (a b : Prop) (_ : a) (_ : b), And a b.
        let intro_ty = {
            let a3 = kernel.bvar(3);
            let b2 = kernel.bvar(2);
            let and_ab = {
                let e = kernel.app(and_const, a3);
                kernel.app(e, b2)
            };
            let b1 = kernel.bvar(1);
            let right_field = kernel.pi(anon, b1, and_ab, BinderInfo::Default);
            let a1 = kernel.bvar(1);
            let left_field = kernel.pi(anon, a1, right_field, BinderInfo::Default);
            let second_param = kernel.pi(anon, prop, left_field, BinderInfo::Default);
            kernel.pi(anon, prop, second_param, BinderInfo::Default)
        };
        kernel
            .add_inductive(and_name, &[], 2, and_ty, &[(and_intro, intro_ty)])
            .expect("And must admit");
        kernel
    }

    // ---------------------------------------------------------------- dif_pos

    #[test]
    fn dif_pos_reconstructs_and_kernel_checks() {
        let mut kernel = decidable_test_kernel();
        let (value, ty, uparams) = dif_pos_pair(&mut kernel).expect("dif_pos reconstructs");
        assert_eq!(uparams.len(), 1);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDifPos")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed dif_pos must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    /// NEGATIVE control: `dif_pos`'s value proves `dite c h t e = t hc`;
    /// offering it at `dif_neg`'s type (`dite c h t e = e hnc`) is a
    /// WRONG-DIRECTION substitution of exactly the kind a mirrored
    /// construction produces by copy-paste. Both types are real, well-formed,
    /// and differ only in which branch the right-hand side names, so nothing
    /// but the kernel's own conversion check can tell them apart.
    #[test]
    fn dif_pos_value_at_dif_negs_type_is_refused_by_the_kernel() {
        let mut kernel = decidable_test_kernel();
        let (value, _pos_ty, uparams) = dif_pos_pair(&mut kernel).expect("dif_pos reconstructs");
        let (_neg_value, neg_ty, _) = dif_neg_pair(&mut kernel).expect("dif_neg reconstructs");
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDifPosWrongType")
        };
        let outcome = kernel.add_declaration(Declaration::Theorem {
            name,
            uparams,
            ty: neg_ty,
            value,
        });
        assert!(
            outcome.is_err(),
            "the kernel must refuse dif_pos's value at dif_neg's type, got {outcome:?}"
        );
    }

    #[test]
    fn dif_pos_declines_when_decidable_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            dif_pos_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable(
                "Decidable"
            ))
        ));
    }

    #[test]
    fn reconstruct_dispatches_dif_pos() {
        let mut kernel = decidable_test_kernel();
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDispatchDifPos")
        };
        let wire_ty = kernel.sort_zero();
        let result = reconstruct(&mut kernel, name, "dif_pos", wire_ty);
        assert!(
            matches!(result, Ok(Some(Declaration::Theorem { .. }))),
            "dif_pos: expected Ok(Some(Theorem)), got {result:?}"
        );
    }

    // --------------------------------------------------------------- Eq.subst

    #[test]
    fn eq_subst_reconstructs_and_kernel_checks() {
        let mut kernel = fixture_kernel();
        let (value, ty, uparams) = eq_subst_pair(&mut kernel).expect("Eq.subst reconstructs");
        assert_eq!(uparams.len(), 1);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestEqSubst")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed Eq.subst must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    /// NEGATIVE control: `Eq.subst`'s value transports along `h₁ : a = b` in
    /// the FORWARD direction (`motive a -> motive b`). Offering that same
    /// value at the type whose two `motive` applications are exchanged
    /// (`motive b -> motive a`, built here by hand from the same pieces) is
    /// the backwards-transport bug. It is a real, inhabited, well-formed
    /// proposition, so only the kernel's conversion check refuses it.
    #[test]
    fn eq_subst_value_at_the_reversed_type_is_refused_by_the_kernel() {
        let mut kernel = fixture_kernel();
        let (value, _forward_ty, uparams) = eq_subst_pair(&mut kernel).expect("Eq.subst builds");

        // Rebuild `Eq.subst`'s telescope with hypothesis and conclusion
        // exchanged: {α} {motive} {a b} -> Eq α a b -> motive b -> motive a.
        let eqp = discover_eq(&kernel).expect("Eq primitives");
        let mut next_fvar = FVAR_BASE + 70_000_000;
        let anon = kernel.anon();
        let u_name = kernel.name_str(anon, "u");
        let u = kernel.level_param(u_name);
        let sort_u = kernel.sort(u);
        let zero = kernel.level_zero();
        let prop = kernel.sort(zero);

        let alpha_fv = fresh(&mut next_fvar);
        let alpha = kernel.fvar(alpha_fv);
        let motive_fv = fresh(&mut next_fvar);
        let motive = kernel.fvar(motive_fv);
        let a_fv = fresh(&mut next_fvar);
        let a = kernel.fvar(a_fv);
        let b_fv = fresh(&mut next_fvar);
        let b = kernel.fvar(b_fv);
        let h1_fv = fresh(&mut next_fvar);
        let h2_fv = fresh(&mut next_fvar);

        let ty_motive = kernel.pi(anon, alpha, prop, BinderInfo::Default);
        let ty_h1 = build_eq(&mut kernel, eqp.eq, u, alpha, a, b);
        let motive_a = kernel.app(motive, a);
        let motive_b = kernel.app(motive, b);
        let binders = [
            (alpha_fv, sort_u, BinderInfo::Implicit),
            (motive_fv, ty_motive, BinderInfo::Implicit),
            (a_fv, alpha, BinderInfo::Implicit),
            (b_fv, alpha, BinderInfo::Implicit),
            (h1_fv, ty_h1, BinderInfo::Default),
            // hypothesis `motive b`, conclusion `motive a` — reversed.
            (h2_fv, motive_b, BinderInfo::Default),
        ];
        let (_ignored_value, reversed_ty) =
            close_telescope(&mut kernel, &binders, motive_a, motive_a);

        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestEqSubstReversed")
        };
        let outcome = kernel.add_declaration(Declaration::Theorem {
            name,
            uparams,
            ty: reversed_ty,
            value,
        });
        assert!(
            outcome.is_err(),
            "the kernel must refuse Eq.subst's value at the reversed type, got {outcome:?}"
        );
    }

    #[test]
    fn eq_subst_declines_when_eq_is_missing() {
        let mut kernel = Kernel::new();
        assert!(matches!(
            eq_subst_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("Eq"))
        ));
    }

    #[test]
    fn reconstruct_dispatches_eq_subst() {
        let mut kernel = fixture_kernel();
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDispatchEqSubst")
        };
        let wire_ty = kernel.sort_zero();
        let result = reconstruct(&mut kernel, name, "Eq.subst", wire_ty);
        assert!(
            matches!(result, Ok(Some(Declaration::Theorem { .. }))),
            "Eq.subst: expected Ok(Some(Theorem)), got {result:?}"
        );
    }

    // --------------------------------------------------------------- And.left

    #[test]
    fn and_left_reconstructs_and_kernel_checks() {
        let mut kernel = and_test_kernel();
        let (value, ty, uparams) = and_left_pair(&mut kernel).expect("And.left reconstructs");
        assert_eq!(uparams.len(), 0);
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestAndLeft")
        };
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams,
                ty,
                value,
            })
            .expect("reconstructed And.left must kernel-check");
        assert_eq!(kernel.axiom_footprint(name).len(), 0);
        assert_eq!(kernel.theorem_dependencies(name).len(), 0);
    }

    /// NEGATIVE control: `And.left`'s value returns the FIRST field, so
    /// offering it at `And.right`'s type (`{a b : Prop} -> And a b -> b`,
    /// built here by hand) is the projection-index bug. `a` and `b` are two
    /// distinct bound `Prop`s, so nothing but the kernel can tell the two
    /// types apart — a Rust-side name check would not even look.
    #[test]
    fn and_left_value_at_and_rights_type_is_refused_by_the_kernel() {
        let mut kernel = and_test_kernel();
        let (value, _left_ty, uparams) = and_left_pair(&mut kernel).expect("And.left builds");

        let andp = discover_and(&kernel).expect("And primitives");
        let mut next_fvar = FVAR_BASE + 80_000_000;
        let zero = kernel.level_zero();
        let prop = kernel.sort(zero);
        let a_fv = fresh(&mut next_fvar);
        let a = kernel.fvar(a_fv);
        let b_fv = fresh(&mut next_fvar);
        let b = kernel.fvar(b_fv);
        let self_fv = fresh(&mut next_fvar);
        let and_ab = {
            let head = kernel.const_(andp.and_, vec![]);
            let w1 = kernel.app(head, a);
            kernel.app(w1, b)
        };
        let binders = [
            (a_fv, prop, BinderInfo::Implicit),
            (b_fv, prop, BinderInfo::Implicit),
            (self_fv, and_ab, BinderInfo::Default),
        ];
        // conclusion `b`, not `a` — this is `And.right`'s statement.
        let (_ignored_value, right_ty) = close_telescope(&mut kernel, &binders, b, b);

        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestAndLeftWrongField")
        };
        let outcome = kernel.add_declaration(Declaration::Theorem {
            name,
            uparams,
            ty: right_ty,
            value,
        });
        assert!(
            outcome.is_err(),
            "the kernel must refuse And.left's value at And.right's type, got {outcome:?}"
        );
    }

    #[test]
    fn and_left_declines_when_and_is_missing() {
        let mut kernel = fixture_kernel();
        assert!(matches!(
            and_left_pair(&mut kernel),
            Err(SubstitutionError::RequiredDeclarationUnavailable("And"))
        ));
    }

    // ---------------------------------------------------- eq_self (NOT done)

    /// `eq_self` is the LARGEST first-reported blocker of the 2026-09-05
    /// statement-import census (97 of 756 rows) and ADR-1662 grouped it with
    /// the six constructive names. That grouping is wrong, and this test is
    /// the measurement that says so rather than a comment claiming it:
    /// `eq_self : (a = a) = True` is an equality between two `Prop`s, and
    /// Lean 4.30 proves it through `eq_true`, which is `propext` applied to
    /// an `Iff`. `propext` is a genuine AXIOM and this kernel is
    /// intuitionistic (`crates/axeyum-lean-kernel/src/prelude.rs`: no
    /// `Classical.em`, no `propext`, no `funext`), so there is no
    /// reconstruction of `eq_self` that does not first enlarge the trusted
    /// surface by an axiom — which is exactly the decision ADR-1662 held
    /// back, and which this lane does not take.
    ///
    /// Read from the pinned Lean 4.30 export of the real declaration, so it
    /// fails if a Mathlib pin move ever makes `eq_self` axiom-free (which
    /// would be the signal to revisit), and it fails if anyone adds `eq_self`
    /// to [`SUBSTITUTABLE_THEOREMS`] without taking the `propext` decision.
    #[test]
    fn eq_self_is_propext_dependent_and_therefore_not_substituted() {
        use crate::{ImportLimits, import_ndjson};
        use std::io::Cursor;

        const EQ_SELF_FIXTURE: &str =
            include_str!("../../../docs/plan/fixtures/lean4export-v4.30-eq-self.ndjson");

        assert!(
            !SUBSTITUTABLE_THEOREMS.contains(&"eq_self"),
            "eq_self must not be substituted while this kernel has no propext"
        );

        let completed = import_ndjson(
            Cursor::new(EQ_SELF_FIXTURE.as_bytes()),
            ImportLimits::default(),
        )
        .expect("pinned eq_self fixture must import");
        let kernel = completed.into_parts().0;
        let eq_self = kernel
            .environment()
            .iter()
            .find(|(name, _)| kernel.display_name(**name).to_string() == "eq_self")
            .map(|(name, _)| *name)
            .expect("the fixture must carry eq_self");
        let footprint: Vec<String> = kernel
            .axiom_footprint(eq_self)
            .into_iter()
            .map(|n| kernel.display_name(n).to_string())
            .collect();
        assert!(
            footprint.iter().any(|n| n == "propext"),
            "eq_self's own Lean 4.30 closure must reach propext; measured footprint {footprint:?}"
        );
    }

    #[test]
    fn reconstruct_dispatches_and_left() {
        let mut kernel = and_test_kernel();
        let name = {
            let root = kernel.anon();
            kernel.name_str(root, "TestDispatchAndLeft")
        };
        let wire_ty = kernel.sort_zero();
        let result = reconstruct(&mut kernel, name, "And.left", wire_ty);
        assert!(
            matches!(result, Ok(Some(Declaration::Theorem { .. }))),
            "And.left: expected Ok(Some(Theorem)), got {result:?}"
        );
    }
}
