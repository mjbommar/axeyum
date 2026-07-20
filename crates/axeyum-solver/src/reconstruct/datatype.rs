//! Axiom-free Lean reconstruction for algebraic datatype field rules.

use std::collections::BTreeMap;

use axeyum_ir::{
    ConstructorId, DatatypeId, Op as IrOp, Sort as IrSort, TermArena, TermId,
    TermNode as IrTermNode,
};
use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, LevelId, NameId, RecField};

use super::{
    LEAN_MODULE_THEOREM, ReconstructCtx, ReconstructError, fresh_axiom, require_infers_false,
};

// ===========================================================================
// QF_DT **is-tester** fold — axiom-free Lean-kernel reconstruction (route A).
//
// The is-tester fold is `is_C (C x) = true` and `is_C (K x) = false` for K ≠ C
// (the SMT-LIB datatype-tester semantics). The selector route already models an
// SMT datatype constructor as a kernel inductive constructor, so the
// read-over-construct projection is ι-reduction (`Eq.refl`); this is its
// **is-tester twin**.
//
// A pure is-tester contradiction is a single redex `is_C (cⱼ x…)` asserted with
// a polarity that disagrees with the fold:
//
//   - `¬is_C (C x)` — a TRUE-fold contradiction (`is_C (C x)` ι-reduces to
//     `Bool.true`, but the assertion says it is not true); or
//   - `is_C (K x)` with `K ≠ C` — a FALSE-fold contradiction (`is_C (K x)`
//     ι-reduces to `Bool.false`, but the assertion says it is true).
//
// We model the whole datatype as ONE kernel inductive carrying every
// constructor ([`axeyum_lean_kernel::Kernel::add_datatype_family`]); the is-tester is the recursor
// application [`axeyum_lean_kernel::Kernel::datatype_tester`] eliminating into the **computational
// `Bool`**, so `is_C (cⱼ x…)` ι-reduces (kernel `whnf`/`def_eq`) to a concrete
// `Bool.true`/`Bool.false`. The is-tester predicate "`is_C(arg)` holds" is the
// Bool equality `Eq Bool (is_C arg) Bool.true`, and:
//
//   - the input assertion `is_C(arg)` / `¬is_C(arg)` is the ONLY assumed axiom
//     (the honest encoding of the input); and
//   - the fold itself is discharged BY ι — `Eq.refl Bool true` (true fold) closes
//     the negated hypothesis directly, while the false fold uses the
//     `Bool.true ≠ Bool.false` discriminator (a `Bool.rec` motive `D` with
//     `D false = True`, `D true = False`, transported along the hypothesis),
//     which is itself axiom-free (no `noConfusion` axiom, just `Bool.rec` ι).
//
// The final term `infer`s to `False` (gated by [`require_infers_false`]); a wrong
// fold makes ι fail to reduce and the kernel rejects — never a wrong `False`.
// ===========================================================================

/// A pure is-tester contradiction located in `assertions`: a tester redex
/// `is_C(cⱼ x…)` whose asserted polarity disagrees with the constructor fold.
struct TesterContradiction {
    /// The datatype of the tester's constructors.
    datatype: DatatypeId,
    /// The **tested** constructor `C` of `is_C`.
    tested: ConstructorId,
    /// The **builder** constructor `cⱼ` of the argument `cⱼ(x…)`.
    builder: ConstructorId,
    /// The builder's field argument terms (modeled as opaque carrier atoms).
    fields: Vec<TermId>,
    /// `true` when the assertion is the positive tester atom `is_C(cⱼ x…)`
    /// (a FALSE-fold contradiction needs `tested != builder`); `false` when it is
    /// the negated atom `¬is_C(cⱼ x…)` (a TRUE-fold contradiction needs
    /// `tested == builder`).
    asserted_positive: bool,
}

/// Find the first pure is-tester contradiction in `assertions`: an assertion that
/// is `is_C(cⱼ x…)` or `¬is_C(cⱼ x…)` (a tester directly over a constructor
/// application) whose polarity disagrees with the `tested == builder` fold.
/// Returns [`None`] when no such redex is present (e.g. a select-over-construct
/// proof, or a tester over a non-constructor argument).
fn find_tester_contradiction(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<TesterContradiction> {
    for &assertion in assertions {
        let (atom, positive) = match arena.node(assertion) {
            IrTermNode::App {
                op: IrOp::BoolNot,
                args,
            } => (args[0], false),
            _ => (assertion, true),
        };
        let IrTermNode::App {
            op: IrOp::DtTest(tested),
            args,
        } = arena.node(atom)
        else {
            continue;
        };
        let tested = *tested;
        let arg = args[0];
        let IrTermNode::App {
            op: IrOp::DtConstruct { constructor, .. },
            args: fields,
        } = arena.node(arg)
        else {
            continue;
        };
        let builder = *constructor;
        let folds_true = builder == tested;
        // A contradiction iff the asserted polarity disagrees with the fold:
        // positive assertion ⇒ needs the fold to be FALSE; negative ⇒ TRUE.
        if positive != folds_true {
            return Some(TesterContradiction {
                datatype: arena.constructor_datatype(tested),
                tested,
                builder,
                fields: fields.to_vec(),
                asserted_positive: positive,
            });
        }
    }
    None
}

/// **Reconstruct a pure `QF_DT` is-tester contradiction to a Lean module** whose
/// `axeyum_refutation : False` is kernel-checked and **axiom-free over the fold**
/// — the is-tester fold `is_C (C x) = true` / `is_C (K x) = false` is discharged
/// by ι-reduction (`Eq.refl`), not assumed. The only added axiom is the input
/// tester assertion itself (the honest encoding of the input constraint).
///
/// Returns [`None`] when `assertions` carry no pure is-tester contradiction
/// (the caller then falls back to the general datatype reconstructor).
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if the datatype family fails to admit or
/// the assembled `False` term does not `infer`/`def_eq` to `False` (a defensive
/// gate; a sound fold always discharges).
pub(super) fn reconstruct_qf_dt_tester_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Result<String, ReconstructError>> {
    let c = find_tester_contradiction(arena, assertions)?;
    Some(build_tester_refutation_module(arena, &c))
}

// ===========================================================================
// QF_DT **constructor DISTINCTNESS** — axiom-free Lean-kernel reconstruction
// (slice 2, the Lean mirror of the Carcara `prove_qf_dt_distinct_alethe_carcara`).
//
// An asserted constructor equality `C x… = D y…` between two **distinct**
// constructors `C ≠ D` of the *same* datatype family is UNSAT — distinct
// constructors of an inductive are never equal. We discharge it by COMPOSING
// the slice-1 is-tester primitives, with **no `noConfusion`** and **no new
// axiom** beyond the honest encoding of the input equality:
//
//   1. register the family `D` carrying every constructor
//      ([`axeyum_lean_kernel::Kernel::add_datatype_family`], reused from the tester path);
//   2. apply the is-tester for the RIGHT constructor `D`
//      ([`axeyum_lean_kernel::Kernel::datatype_tester`]): `is_D (C x…)` ι-reduces to `Bool.false`,
//      `is_D (D y…)` ι-reduces to `Bool.true`;
//   3. from the input hypothesis `h : Eq Dty (C x…) (D y…)`, transport by
//      congruence (`Eq.rec` with motive `fun z _ => Eq Bool (is_D (C x…)) (is_D z)`,
//      refl case `Eq.refl Bool (is_D (C x…))`) to `Eq Bool (is_D (C x…)) (is_D (D y…))`,
//      which is `def_eq` to `Eq Bool Bool.false Bool.true` after ι on both sides;
//   4. feed that to the EXISTING `Bool.true ≠ Bool.false` discriminator
//      ([`build_bool_true_ne_false`]): its `lhs = is_D (C x…)` ι-reduces to
//      `Bool.false`, the proof witnesses `lhs = Bool.true`, and the `Bool.rec`
//      motive `D false = True, D true = False` transported along it yields `False`.
//
// Every step is ι-reduction + `Eq.rec` — axiom-free, exactly like slice 1's
// false-fold. The final term `infer`s to `False` (gated by [`require_infers_false`]);
// a non-distinct or ill-typed equality makes ι fail and the kernel rejects —
// never a wrong `False`.
// ===========================================================================

/// A pure constructor-distinctness contradiction located in `assertions`: an
/// asserted equality `C x… = D y…` whose two constructors `C ≠ D` are **distinct**
/// constructors of the same datatype family.
struct DistinctContradiction {
    /// The shared datatype of `C` and `D`.
    datatype: DatatypeId,
    /// The left-hand-side (builder) constructor `C`.
    lhs_ctor: ConstructorId,
    /// The left-hand-side field argument terms (modeled as opaque carrier atoms).
    lhs_fields: Vec<TermId>,
    /// The right-hand-side (builder) constructor `D` — used as the tested
    /// constructor `is_D`, so the congruence yields `false = true`.
    rhs_ctor: ConstructorId,
    /// The right-hand-side field argument terms (modeled as opaque carrier atoms).
    rhs_fields: Vec<TermId>,
}

/// Find the first asserted equality `C x… = D y…` between **distinct**
/// constructors `C ≠ D` of the same datatype. Returns [`None`] when no such
/// equality is present (e.g. a same-constructor equality `C x = C y`, which is an
/// injectivity obligation handled by a separate slice, or a non-constructor
/// equality).
fn find_distinct_constructor_contradiction(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<DistinctContradiction> {
    for &assertion in assertions {
        let IrTermNode::App { op: IrOp::Eq, args } = arena.node(assertion) else {
            continue;
        };
        let &[lhs, rhs] = &args[..] else {
            continue;
        };
        let IrTermNode::App {
            op:
                IrOp::DtConstruct {
                    constructor: lhs_ctor,
                    ..
                },
            args: lhs_fields,
        } = arena.node(lhs)
        else {
            continue;
        };
        let IrTermNode::App {
            op:
                IrOp::DtConstruct {
                    constructor: rhs_ctor,
                    ..
                },
            args: rhs_fields,
        } = arena.node(rhs)
        else {
            continue;
        };
        let (lhs_ctor, rhs_ctor) = (*lhs_ctor, *rhs_ctor);
        // SAME constructor ⇒ this is an injectivity obligation, NOT distinctness;
        // decline so the distinctness reconstructor never emits a wrong `False`.
        if lhs_ctor == rhs_ctor {
            continue;
        }
        // Distinct constructors must share the same datatype (the SMT equality is
        // sort-homogeneous; guard defensively anyway).
        let datatype = arena.constructor_datatype(lhs_ctor);
        if arena.constructor_datatype(rhs_ctor) != datatype {
            continue;
        }
        return Some(DistinctContradiction {
            datatype,
            lhs_ctor,
            lhs_fields: lhs_fields.to_vec(),
            rhs_ctor,
            rhs_fields: rhs_fields.to_vec(),
        });
    }
    None
}

/// **Reconstruct a pure `QF_DT` constructor-distinctness contradiction to a Lean
/// module** whose `axeyum_refutation : False` is kernel-checked and **axiom-free
/// over the fold** — distinctness is discharged by composing the is-tester ι-fold
/// with a congruence transport and the `Bool.true ≠ Bool.false` discriminator, not
/// assumed (no `noConfusion`). The only added axiom is the input equality itself.
///
/// Returns [`None`] when `assertions` carry no distinct-constructor equality (the
/// caller then falls back to the general datatype reconstructor).
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if the datatype family fails to admit or
/// the assembled `False` term does not `infer`/`def_eq` to `False` (a defensive
/// gate; a sound distinctness refutation always discharges).
pub(super) fn reconstruct_qf_dt_distinct_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Result<String, ReconstructError>> {
    let c = find_distinct_constructor_contradiction(arena, assertions)?;
    Some(build_distinct_refutation_module(arena, &c))
}

/// Assemble the kernel `False` term for a [`DistinctContradiction`] and render the
/// Lean module. Mirrors [`build_tester_refutation_module`]: same family registry,
/// same `datatype_tester`, same `build_bool_true_ne_false` discriminator — the only
/// new piece is the `Eq.rec` congruence transport built by [`build_congr_is_d`].
fn build_distinct_refutation_module(
    arena: &TermArena,
    c: &DistinctContradiction,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();

    // 1. Declare the kernel family `D` carrying EVERY constructor of the datatype
    //    (declaration order), reusing the tester path's family registry.
    let dt_name = arena.datatype_name(c.datatype).to_owned();
    let ctor_ids = arena.datatype_constructors(c.datatype).to_vec();
    let ctor_decls: Vec<(String, usize)> = ctor_ids
        .iter()
        .enumerate()
        .map(|(j, &cid)| (format!("c{j}"), arena.constructor_fields(cid).len()))
        .collect();
    let family = ctx.datatype_family(&dt_name, &ctor_decls)?;

    let lhs_pos = constructor_position(&ctor_ids, c.lhs_ctor)?;
    let rhs_pos = constructor_position(&ctor_ids, c.rhs_ctor)?;

    // 2. Build the two constructor applications `C(x…)` and `D(y…)`. Each field is a
    //    fresh opaque carrier atom (distinctness is field-independent — only the
    //    constructor head drives the is-tester ι).
    let lhs_con = build_opaque_construct(&mut ctx, family.ctors[lhs_pos], c.lhs_fields.len())?;
    let rhs_con = build_opaque_construct(&mut ctx, family.ctors[rhs_pos], c.rhs_fields.len())?;

    // 3. The is-tester for the RIGHT constructor `D`: `is_D (C x…)` ι-reduces to
    //    `Bool.false`, `is_D (D y…)` ι-reduces to `Bool.true`.
    let alpha = ctx.alpha;
    let is_d = ctx.kernel.datatype_tester(
        &family,
        ctx.prelude.bool_,
        ctx.prelude.bool_true,
        ctx.prelude.bool_false,
        alpha,
        rhs_pos,
    );
    // `is_d (C x…)` ι→ Bool.false (the discriminator `lhs`); `is_d (D y…)` ι→
    // Bool.true (the congruence's right side — built inside `build_congr_is_d`).
    let is_d_lhs = ctx.kernel.app(is_d, lhs_con);

    // 4. Input hypothesis `h : Eq Dty (C x…) (D y…)` (the ONLY added axiom). The
    //    datatype carrier in the kernel is the family inductive `Dty := D`.
    let dty = ctx.kernel.const_(family.ind, vec![]);
    let one = ctx.one;
    let eq_prop = mk_eq_at(&mut ctx, dty, one, lhs_con, rhs_con);
    let h = fresh_axiom(&mut ctx, eq_prop, "assume")?;

    // 5. Congruence transport `congrArg is_D h : Eq Bool (is_D (C x…)) (is_D (D y…))`,
    //    which is `def_eq` to `Eq Bool Bool.false Bool.true`.
    let congr = build_congr_is_d(&mut ctx, dty, is_d, lhs_con, rhs_con, h);

    // 6. The existing `Bool.true ≠ Bool.false` discriminator: `lhs = is_D (C x…)`
    //    ι-reduces to `Bool.false`, `congr : Eq Bool lhs Bool.true` ⇒ `False`.
    let false_term = build_bool_true_ne_false(&mut ctx, is_d_lhs, congr);

    require_infers_false(&mut ctx, false_term)?;
    // Render the datatype family AND the computational `Bool` as real Lean
    // `inductive`s so an external Lean regenerates their recursors *with* ι — the
    // congruence `Eq.rec` only collapses to `false = true` if Lean can compute
    // `is_D (cⱼ x…)` by ι.
    let bool_ind = ctx.prelude.bool_;
    let false_const = {
        let n = ctx.prelude().false_;
        ctx.kernel_mut().const_(n, vec![])
    };
    Ok(ctx.kernel().render_lean_module_with_inductives(
        LEAN_MODULE_THEOREM,
        false_const,
        false_term,
        &[family.ind, bool_ind],
    ))
}

/// Position of constructor `cid` in `ctor_ids` (declaration order), or a
/// [`ReconstructError::KernelRejected`] if it is not a constructor of the datatype.
fn constructor_position(
    ctor_ids: &[ConstructorId],
    cid: ConstructorId,
) -> Result<usize, ReconstructError> {
    ctor_ids
        .iter()
        .position(|&c| c == cid)
        .ok_or_else(|| ReconstructError::KernelRejected {
            rule: "datatype_distinct".to_owned(),
            detail: "constructor not in datatype".to_owned(),
        })
}

/// Build a constructor application `ctor a₀ … a_{arity-1}` whose `arity` field
/// arguments are fresh opaque carrier atoms of sort `α` (distinctness is
/// field-independent, so the exact field values are irrelevant — only the
/// constructor head drives the is-tester ι).
fn build_opaque_construct(
    ctx: &mut ReconstructCtx,
    ctor: NameId,
    arity: usize,
) -> Result<ExprId, ReconstructError> {
    let mut con = ctx.kernel.const_(ctor, vec![]);
    for i in 0..arity {
        let atom_name = ctx.fresh_name(&format!("fld_{i}"));
        let alpha = ctx.alpha;
        ctx.kernel
            .add_declaration(Declaration::Axiom {
                name: atom_name,
                uparams: vec![],
                ty: alpha,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "datatype_distinct".to_owned(),
                detail: format!("field carrier atom did not admit: {e:?}"),
            })?;
        let a = ctx.kernel.const_(atom_name, vec![]);
        con = ctx.kernel.app(con, a);
    }
    Ok(con)
}

/// Build `Eq.{u} ty l r` for an arbitrary carrier type `ty : Sort u`.
fn mk_eq_at(ctx: &mut ReconstructCtx, ty: ExprId, u: LevelId, l: ExprId, r: ExprId) -> ExprId {
    let eq = ctx.kernel.const_(ctx.prelude.eq, vec![u]);
    let e = ctx.kernel.app(eq, ty);
    let e = ctx.kernel.app(e, l);
    ctx.kernel.app(e, r)
}

/// Build the congruence transport `congrArg is_D h` as an `Eq.rec`:
/// given `h : Eq dty lhs_con rhs_con` (both `dty`-typed constructor applications)
/// and the is-tester `is_d : dty → Bool`, produce a proof of
/// `Eq Bool (is_d lhs_con) (is_d rhs_con)`.
///
/// Transport motive `fun (z : dty) (_ : Eq dty lhs_con z) => Eq Bool (is_d lhs_con) (is_d z)`,
/// refl case `Eq.refl Bool (is_d lhs_con)` (the `z := lhs_con` instance is
/// `Eq Bool (is_d lhs_con) (is_d lhs_con)`), then `Eq.rec … rhs_con h` lands at
/// `Eq Bool (is_d lhs_con) (is_d rhs_con)`. Pure `Eq.rec` — axiom-free, the exact
/// `congrArg` derivation.
fn build_congr_is_d(
    ctx: &mut ReconstructCtx,
    dty: ExprId,
    is_d: ExprId,
    lhs_con: ExprId,
    rhs_con: ExprId,
    h: ExprId,
) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let bool_const = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    let is_d_lhs = ctx.kernel.app(is_d, lhs_con);

    // motive := fun (z : dty) (_ : Eq dty lhs_con z) => Eq Bool (is_d lhs_con) (is_d z).
    let transport_motive = {
        // Under binders (z : dty) (_ : Eq dty lhs_con z): `z` is bvar 1.
        let z_var = ctx.kernel.bvar(1);
        let is_d_z = ctx.kernel.app(is_d, z_var);
        let body = mk_eq_at(ctx, bool_const, one, is_d_lhs, is_d_z);
        // inner Pi binder type: Eq dty lhs_con z, with `z` as bvar 0 at this depth.
        let z0 = ctx.kernel.bvar(0);
        let eq_lhs_z = mk_eq_at(ctx, dty, one, lhs_con, z0);
        let inner = ctx.kernel.lam(anon, eq_lhs_z, body, BinderInfo::Default);
        ctx.kernel.lam(anon, dty, inner, BinderInfo::Default)
    };
    // refl_case : Eq Bool (is_d lhs_con) (is_d lhs_con) — `Eq.refl Bool (is_d lhs_con)`.
    let refl = ctx.kernel.const_(ctx.prelude.eq_refl, vec![ctx.one]);
    let refl_case = {
        let e = ctx.kernel.app(refl, bool_const);
        ctx.kernel.app(e, is_d_lhs)
    };
    // Eq.rec.{v,u} dty lhs_con transport_motive refl_case rhs_con h
    //   : Eq Bool (is_d lhs_con) (is_d rhs_con).
    // motive `fun z _ => Eq Bool …` eliminates into `Prop` ⇒ v = 0; the equands of
    // `h` are `dty : Sort 1` ⇒ u = 1 (= `ctx.one`).
    let v = ctx.kernel.level_zero();
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![v, one]);
    let e = ctx.kernel.app(rec_eq, dty);
    let e = ctx.kernel.app(e, lhs_con);
    let e = ctx.kernel.app(e, transport_motive);
    let e = ctx.kernel.app(e, refl_case);
    let e = ctx.kernel.app(e, rhs_con);
    ctx.kernel.app(e, h)
}

// ===========================================================================
// QF_DT **constructor INJECTIVITY** — axiom-free Lean-kernel reconstruction
// (slice 3, the Lean mirror of the Carcara `prove_qf_dt_injective_alethe_carcara`).
//
// An asserted same-constructor equality `C x… = C y…` together with a conflicting
// field disequality `¬(x_i = y_i)` is UNSAT: constructors are injective, so
// `C x… = C y…` forces `x_i = y_i`, contradicting the disequality. We discharge
// it through the **SELECTOR** route (the field-projection analogue of slice-2's
// is-tester discriminator) — **no `noConfusion`** and **no new axiom** beyond the
// honest encoding of the two input assertions:
//
//   1. register the family `D` carrying every constructor
//      ([`axeyum_lean_kernel::Kernel::add_datatype_family`], reused from the tester/distinct paths);
//   2. build the `i`-th field SELECTOR for `C` over the family
//      ([`axeyum_lean_kernel::Kernel::datatype_family_selector`]): `sel_i (C x…)` ι-reduces to `x_i`,
//      `sel_i (C y…)` ι-reduces to `y_i` (the same-constructor major is always
//      `C`-headed, so the family recursor's other minors never reduce);
//   3. from the input hypothesis `h : Eq D (C x…) (C y…)`, transport by
//      congruence ([`build_congr_sel`], an `Eq.rec` with motive
//      `fun z _ => Eq α (sel_i (C x…)) (sel_i z)`, refl case
//      `Eq.refl α (sel_i (C x…))`) to `Eq α (sel_i (C x…)) (sel_i (C y…))`, which
//      is `def_eq` to `Eq α x_i y_i` after ι on both sides;
//   4. resolve against the input field disequality `hne : Eq α x_i y_i → False`
//      (with an inline `Eq.symm` when the diseq is asserted in the `y_i = x_i`
//      order) ⇒ `False`.
//
// Every step is ι-reduction + `Eq.rec` + a function application — axiom-free,
// exactly the selector twin of slice-2's distinctness. The final term `infer`s to
// `False` (gated by [`require_infers_false`]); a different-constructor equality is
// DECLINED (distinctness's job) and a same-constructor equality without a
// conflicting field diseq is DECLINED — never a wrong `False`.
// ===========================================================================

/// A pure constructor-injectivity contradiction located in `assertions`: an
/// asserted same-constructor equality `C x… = C y…` with a conflicting field
/// disequality `¬(x_i = y_i)` on field `i`.
struct InjectiveContradiction {
    /// The datatype of the constructor `C`.
    datatype: DatatypeId,
    /// The (shared) constructor `C` of both equands.
    ctor: ConstructorId,
    /// The left-hand-side field argument terms (modeled as opaque carrier atoms).
    lhs_fields: Vec<TermId>,
    /// The right-hand-side field argument terms (modeled as opaque carrier atoms).
    rhs_fields: Vec<TermId>,
    /// The index `i` of the conflicting field.
    field: usize,
    /// `true` when the disequality is asserted in the `x_i = y_i` order
    /// (`¬(x_i = y_i)`), `false` when reversed (`¬(y_i = x_i)`). Drives whether the
    /// congruence proof is fed to `hne` directly or via an inline `Eq.symm`.
    forward: bool,
}

/// Find the first asserted same-constructor equality `C x… = C y…` with a
/// conflicting field disequality `¬(x_i = y_i)` (in either field order) on some
/// field `i`. Returns [`None`] when no such pair is present — a
/// DISTINCT-constructor equality `C x = D y` is declined (distinctness's job), and
/// a same-constructor equality without a conflicting field diseq is declined (no
/// wrong `False`).
fn find_injectivity_contradiction(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<InjectiveContradiction> {
    for &assertion in assertions {
        let IrTermNode::App { op: IrOp::Eq, args } = arena.node(assertion) else {
            continue;
        };
        let &[lhs, rhs] = &args[..] else {
            continue;
        };
        let IrTermNode::App {
            op:
                IrOp::DtConstruct {
                    constructor: lhs_ctor,
                    ..
                },
            args: lhs_fields,
        } = arena.node(lhs)
        else {
            continue;
        };
        let IrTermNode::App {
            op:
                IrOp::DtConstruct {
                    constructor: rhs_ctor,
                    ..
                },
            args: rhs_fields,
        } = arena.node(rhs)
        else {
            continue;
        };
        let (lhs_ctor, rhs_ctor) = (*lhs_ctor, *rhs_ctor);
        // DIFFERENT constructor ⇒ this is a DISTINCTNESS obligation, NOT injectivity;
        // decline so the injectivity reconstructor never overlaps the distinct path.
        if lhs_ctor != rhs_ctor {
            continue;
        }
        let lhs_fields = lhs_fields.to_vec();
        let rhs_fields = rhs_fields.to_vec();
        // Locate a field index with an asserted conflicting `¬(x_i = y_i)`.
        if let Some((field, forward)) =
            find_conflicting_field_diseq(arena, assertions, &lhs_fields, &rhs_fields)
        {
            return Some(InjectiveContradiction {
                datatype: arena.constructor_datatype(lhs_ctor),
                ctor: lhs_ctor,
                lhs_fields,
                rhs_fields,
                field,
                forward,
            });
        }
    }
    None
}

/// Find the first field index `i` for which `assertions` contains a disequality
/// `¬(x_i = y_i)` (returns `forward = true`) or `¬(y_i = x_i)` (`forward = false`),
/// where `x_i = lhs_fields[i]` and `y_i = rhs_fields[i]`. Returns [`None`] if no
/// field disequality is asserted.
fn find_conflicting_field_diseq(
    arena: &TermArena,
    assertions: &[TermId],
    lhs_fields: &[TermId],
    rhs_fields: &[TermId],
) -> Option<(usize, bool)> {
    for (i, (&x_i, &y_i)) in lhs_fields.iter().zip(rhs_fields).enumerate() {
        for &assertion in assertions {
            let IrTermNode::App {
                op: IrOp::BoolNot,
                args: not_args,
            } = arena.node(assertion)
            else {
                continue;
            };
            let &[inner] = &not_args[..] else {
                continue;
            };
            let IrTermNode::App {
                op: IrOp::Eq,
                args: eq_args,
            } = arena.node(inner)
            else {
                continue;
            };
            let &[p, q] = &eq_args[..] else {
                continue;
            };
            if p == x_i && q == y_i {
                return Some((i, true));
            }
            if p == y_i && q == x_i {
                return Some((i, false));
            }
        }
    }
    None
}

/// **Reconstruct a pure `QF_DT` constructor-injectivity contradiction to a Lean
/// module** whose `axeyum_refutation : False` is kernel-checked and **axiom-free
/// over the projection** — injectivity is discharged by composing the
/// selector-over-construct ι-fold with a congruence transport and the input field
/// disequality, not assumed (no `noConfusion`). The only added axioms are the two
/// input assertions themselves (the same-constructor equality and the field
/// disequality).
///
/// Returns [`None`] when `assertions` carry no same-constructor equality with a
/// conflicting field disequality (the caller then falls back to the general
/// datatype reconstructor).
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if the datatype family fails to admit or
/// the assembled `False` term does not `infer`/`def_eq` to `False` (a defensive
/// gate; a sound injectivity refutation always discharges).
pub(super) fn reconstruct_qf_dt_injective_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Result<String, ReconstructError>> {
    let c = find_injectivity_contradiction(arena, assertions)?;
    Some(build_injective_refutation_module(arena, &c))
}

/// Assemble the kernel `False` term for an [`InjectiveContradiction`] and render the
/// Lean module. Mirrors [`build_distinct_refutation_module`]: same family registry,
/// but uses the field SELECTOR ([`axeyum_lean_kernel::Kernel::datatype_family_selector`]) and the
/// selector congruence ([`build_congr_sel`]), resolving against the input field
/// disequality rather than the `Bool` discriminator.
fn build_injective_refutation_module(
    arena: &TermArena,
    c: &InjectiveContradiction,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();

    // 1. Declare the kernel family `D` carrying EVERY constructor of the datatype
    //    (declaration order), reusing the tester/distinct path's family registry.
    let dt_name = arena.datatype_name(c.datatype).to_owned();
    let ctor_ids = arena.datatype_constructors(c.datatype).to_vec();
    let ctor_decls: Vec<(String, usize)> = ctor_ids
        .iter()
        .enumerate()
        .map(|(j, &cid)| (format!("c{j}"), arena.constructor_fields(cid).len()))
        .collect();
    let family = ctx.datatype_family(&dt_name, &ctor_decls)?;

    let ctor_pos = constructor_position(&ctor_ids, c.ctor)?;

    // 2. Build `C(x…)` and `C(y…)`, keeping the per-field carrier atoms so the i-th
    //    field atoms `x_i`, `y_i` can be referenced by the input field disequality.
    let (lhs_con, lhs_atoms) =
        build_opaque_construct_with_fields(&mut ctx, family.ctors[ctor_pos], c.lhs_fields.len())?;
    let (rhs_con, rhs_atoms) =
        build_opaque_construct_with_fields(&mut ctx, family.ctors[ctor_pos], c.rhs_fields.len())?;
    let x_i = lhs_atoms[c.field];
    let y_i = rhs_atoms[c.field];

    // 3. The i-th field selector for `C`: `sel_i (C x…)` ι→ `x_i`, `sel_i (C y…)`
    //    ι→ `y_i`. The other-constructor minors take a fresh `α` default inhabitant
    //    (they only type the recursor; they never reduce on a `C`-headed major).
    let alpha = ctx.alpha;
    let one = ctx.one;
    let default = {
        let n = ctx.fresh_name("dflt");
        ctx.kernel
            .add_declaration(Declaration::Axiom {
                name: n,
                uparams: vec![],
                ty: alpha,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "datatype_injective".to_owned(),
                detail: format!("selector default inhabitant did not admit: {e:?}"),
            })?;
        ctx.kernel.const_(n, vec![])
    };
    let sel_i = ctx
        .kernel
        .datatype_family_selector(&family, alpha, one, ctor_pos, c.field, default);

    // 4. Input hypothesis `h : Eq D (C x…) (C y…)` (an honest input axiom).
    let dty = ctx.kernel.const_(family.ind, vec![]);
    let eq_prop = mk_eq_at(&mut ctx, dty, one, lhs_con, rhs_con);
    let h = fresh_axiom(&mut ctx, eq_prop, "assume")?;

    // 5. Selector congruence `congrArg sel_i h : Eq α (sel_i (C x…)) (sel_i (C y…))`,
    //    which is `def_eq` to `Eq α x_i y_i` after ι on both sides.
    let congr = build_congr_sel(&mut ctx, dty, sel_i, lhs_con, rhs_con, h);

    // 6. Input field disequality `hne : Not (Eq α P Q) = (Eq α P Q → False)` (the
    //    second honest input axiom), with `(P, Q)` in the ASSERTED order. Feed it
    //    the congruence proof (re-oriented by `Eq.symm` when the diseq is reversed).
    let (p_atom, q_atom) = if c.forward { (x_i, y_i) } else { (y_i, x_i) };
    let diseq_eq = mk_eq_at(&mut ctx, alpha, one, p_atom, q_atom);
    let diseq_not = ctx.mk_not(diseq_eq);
    let hne = fresh_axiom(&mut ctx, diseq_not, "assume")?;
    let eq_proof = if c.forward {
        congr
    } else {
        // `congr : Eq α x_i y_i`; the diseq is over `(y_i, x_i)`, so symmetrize.
        build_eq_symm(&mut ctx, alpha, one, x_i, y_i, congr)
    };
    let false_term = ctx.kernel.app(hne, eq_proof);

    require_infers_false(&mut ctx, false_term)?;
    // Render the datatype family AND the computational `Bool` as real Lean
    // `inductive`s so an external Lean regenerates their recursors *with* ι — the
    // selector congruence `Eq.rec` only collapses to `x_i = y_i` if Lean can
    // compute `sel_i (C z…)` by ι. (`Bool` is listed for parity with the other
    // datatype routes; injectivity itself never folds into `Bool`.)
    let bool_ind = ctx.prelude.bool_;
    let false_const = {
        let n = ctx.prelude().false_;
        ctx.kernel_mut().const_(n, vec![])
    };
    Ok(ctx.kernel().render_lean_module_with_inductives(
        LEAN_MODULE_THEOREM,
        false_const,
        false_term,
        &[family.ind, bool_ind],
    ))
}

/// Build a constructor application `ctor a₀ … a_{arity-1}` whose `arity` field
/// arguments are fresh opaque carrier atoms of sort `α`, **returning the atoms**
/// alongside the application so a caller (injectivity) can reference the i-th
/// field. The selector analogue of [`build_opaque_construct`], which discards them.
fn build_opaque_construct_with_fields(
    ctx: &mut ReconstructCtx,
    ctor: NameId,
    arity: usize,
) -> Result<(ExprId, Vec<ExprId>), ReconstructError> {
    let mut con = ctx.kernel.const_(ctor, vec![]);
    let mut atoms = Vec::with_capacity(arity);
    for i in 0..arity {
        let atom_name = ctx.fresh_name(&format!("fld_{i}"));
        let alpha = ctx.alpha;
        ctx.kernel
            .add_declaration(Declaration::Axiom {
                name: atom_name,
                uparams: vec![],
                ty: alpha,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "datatype_injective".to_owned(),
                detail: format!("field carrier atom did not admit: {e:?}"),
            })?;
        let a = ctx.kernel.const_(atom_name, vec![]);
        atoms.push(a);
        con = ctx.kernel.app(con, a);
    }
    Ok((con, atoms))
}

/// Build the selector congruence transport `congrArg sel_i h` as an `Eq.rec`:
/// given `h : Eq dty lhs_con rhs_con` (both `dty`-typed constructor applications)
/// and the field selector `sel_i : dty → α`, produce a proof of
/// `Eq α (sel_i lhs_con) (sel_i rhs_con)`.
///
/// Transport motive `fun (z : dty) (_ : Eq dty lhs_con z) => Eq α (sel_i lhs_con) (sel_i z)`,
/// refl case `Eq.refl α (sel_i lhs_con)`, then `Eq.rec … rhs_con h` lands at
/// `Eq α (sel_i lhs_con) (sel_i rhs_con)`. The selector twin of [`build_congr_is_d`]
/// (the `Bool` codomain is replaced by the carrier `α`). Pure `Eq.rec` — axiom-free.
fn build_congr_sel(
    ctx: &mut ReconstructCtx,
    dty: ExprId,
    sel_i: ExprId,
    lhs_con: ExprId,
    rhs_con: ExprId,
    h: ExprId,
) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let alpha = ctx.alpha;
    let sel_lhs = ctx.kernel.app(sel_i, lhs_con);

    // motive := fun (z : dty) (_ : Eq dty lhs_con z) => Eq α (sel_i lhs_con) (sel_i z).
    let transport_motive = {
        let z_var = ctx.kernel.bvar(1);
        let sel_z = ctx.kernel.app(sel_i, z_var);
        let body = mk_eq_at(ctx, alpha, one, sel_lhs, sel_z);
        let z0 = ctx.kernel.bvar(0);
        let eq_lhs_z = mk_eq_at(ctx, dty, one, lhs_con, z0);
        let inner = ctx.kernel.lam(anon, eq_lhs_z, body, BinderInfo::Default);
        ctx.kernel.lam(anon, dty, inner, BinderInfo::Default)
    };
    // refl_case : Eq α (sel_i lhs_con) (sel_i lhs_con) — `Eq.refl α (sel_i lhs_con)`.
    let refl = ctx.kernel.const_(ctx.prelude.eq_refl, vec![one]);
    let refl_case = {
        let e = ctx.kernel.app(refl, alpha);
        ctx.kernel.app(e, sel_lhs)
    };
    // Eq.rec.{v,u} dty lhs_con transport_motive refl_case rhs_con h
    //   : Eq α (sel_i lhs_con) (sel_i rhs_con).
    // motive `fun z _ => Eq α …` eliminates into `Prop` ⇒ v = 0; the equands of `h`
    // are `dty : Sort 1` ⇒ u = 1 (= `ctx.one`).
    let v = ctx.kernel.level_zero();
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![v, one]);
    let e = ctx.kernel.app(rec_eq, dty);
    let e = ctx.kernel.app(e, lhs_con);
    let e = ctx.kernel.app(e, transport_motive);
    let e = ctx.kernel.app(e, refl_case);
    let e = ctx.kernel.app(e, rhs_con);
    ctx.kernel.app(e, h)
}

/// Build `Eq.symm` of `h : Eq α a b` as an `Eq.rec`, producing `Eq α b a`:
/// motive `fun (x : α) (_ : Eq α a x) => Eq α x a`, refl case `Eq.refl α a`, then
/// `Eq.rec … b h : Eq α b a`. Pure `Eq.rec` — axiom-free. Used to re-orient the
/// selector congruence when the input field disequality is asserted as `¬(y_i = x_i)`.
fn build_eq_symm(
    ctx: &mut ReconstructCtx,
    ty: ExprId,
    u: LevelId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let anon = ctx.kernel.anon();
    // motive := fun (x : α) (_ : Eq α a x) => Eq α x a.
    let transport_motive = {
        let x_var = ctx.kernel.bvar(1);
        let body = mk_eq_at(ctx, ty, u, x_var, a);
        let x0 = ctx.kernel.bvar(0);
        let eq_a_x = mk_eq_at(ctx, ty, u, a, x0);
        let inner = ctx.kernel.lam(anon, eq_a_x, body, BinderInfo::Default);
        ctx.kernel.lam(anon, ty, inner, BinderInfo::Default)
    };
    // refl_case : Eq α a a — `Eq.refl α a`.
    let refl = ctx.kernel.const_(ctx.prelude.eq_refl, vec![u]);
    let refl_case = {
        let e = ctx.kernel.app(refl, ty);
        ctx.kernel.app(e, a)
    };
    let v = ctx.kernel.level_zero();
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![v, u]);
    let e = ctx.kernel.app(rec_eq, ty);
    let e = ctx.kernel.app(e, a);
    let e = ctx.kernel.app(e, transport_motive);
    let e = ctx.kernel.app(e, refl_case);
    let e = ctx.kernel.app(e, b);
    ctx.kernel.app(e, h)
}

// ===========================================================================
// Datatype ACYCLICITY (occurs-check) — the LAST QF_DT field axiom, discharged
// axiom-free by a SIZE argument (the Lean mirror of the structural occurs-check;
// completes the datatype field-axiom Lean chain alongside is-tester /
// distinctness / injectivity).
//
// A single-level containment cycle `x = C(… x …)` over a recursive datatype `D`
// (e.g. `IntList = nil | cons(head : α, tail : D)`, cycle `x = cons(h, x)`) is
// UNSAT: inductive values are well-founded, so no value strictly contains
// itself. We discharge it WITHOUT well-founded recursion, by a SIZE measure:
//
//   1. model `D` as a *recursive* kernel inductive
//      ([`axeyum_lean_kernel::Kernel::add_recursive_datatype_family`]) — the `tail : D` field is the
//      inductive's own sort, so `cons` is a genuine recursive constructor and the
//      recursor carries an induction hypothesis;
//   2. define `size : D → Nat` ([`axeyum_lean_kernel::Kernel::recursive_datatype_size`]) by the
//      recursor into the computational `Nat`: `size nil` ι→ `Nat.zero`,
//      `size (cons h t)` ι→ `Nat.succ (size t)` (one `Nat.succ` per recursive
//      field);
//   3. from the cycle hypothesis `hx : Eq D x (cons h x)`, transport by
//      congruence ([`build_congr_size`], an `Eq.rec`) to
//      `Eq Nat (size x) (size (cons h x))`, which is `def_eq` to
//      `Eq Nat (size x) (Nat.succ (size x))` after ι on the right;
//   4. apply `nat_ne_succ (size x)` ([`build_nat_ne_succ`]) — the proof, BY
//      INDUCTION on `Nat`, that `n ≠ Nat.succ n` — to that equality ⇒ `False`.
//
// Every step is ι-reduction + `Eq.rec` + `Nat.rec` (eliminating into `Prop` for
// the induction, into `Prop`/`Nat` for the base-case discriminator / predecessor
// selector). NO assumed acyclicity axiom, NO `noConfusion`, NO well-founded
// fixpoint — only the recursors of `D` and `Nat`, which the kernel generates and
// type-checks. The only added axioms are the carrier atoms and the single input
// cycle equality `hx` (the honest encoding of the input constraint). The final
// term `infer`s to `False` (gated by [`require_infers_false`]); a non-cycle
// assertion is DECLINED (no wrong `False`).
// ===========================================================================

/// A single-level datatype **containment cycle** `x = C(… x …)` located in
/// `assertions`: an asserted equality (in either orientation) between a
/// datatype-sorted term `x` and a constructor application `C(args…)` whose
/// immediate arguments include `x` itself.
struct AcyclicCycle {
    /// The datatype `D` of the cycle.
    datatype: DatatypeId,
    /// The constructor `C` of the self-containing side. The kernel refutation
    /// models the cyclic value `x` as a single opaque atom of `D` and rebuilds
    /// `C(… x …)` from the constructor's field shapes, so the concrete `x`/arg
    /// `TermId`s are needed only during detection, not in the refutation.
    ctor: ConstructorId,
    /// `true` when the equality is asserted as `x = C(…)`, `false` when reversed
    /// (`C(…) = x`). Drives whether the size congruence is fed directly or
    /// re-oriented by `Eq.symm`.
    forward: bool,
}

/// Find the first asserted single-level cycle `x = C(… x …)` (in either
/// orientation) over a recursive datatype, or [`None`] when no such equality is
/// present. Declines if the self-containing constructor has **more than one**
/// field of *this* datatype (the size measure's single-recursive-field shape) or
/// any field of a *different* datatype (out of scope, kept sound by declining).
fn find_acyclicity_cycle(arena: &TermArena, assertions: &[TermId]) -> Option<AcyclicCycle> {
    for &assertion in assertions {
        let IrTermNode::App { op: IrOp::Eq, args } = arena.node(assertion) else {
            continue;
        };
        let &[lhs, rhs] = &args[..] else {
            continue;
        };
        // Try both orientations: `x = C(… x …)` (forward) and `C(… x …) = x`.
        for (forward, var, con) in [(true, lhs, rhs), (false, rhs, lhs)] {
            let IrTermNode::App {
                op: IrOp::DtConstruct { constructor, .. },
                args: con_args,
            } = arena.node(con)
            else {
                continue;
            };
            // `var` must be a NON-constructor datatype term that occurs as an
            // immediate argument of the constructor (a single-level cycle).
            if matches!(
                arena.node(var),
                IrTermNode::App {
                    op: IrOp::DtConstruct { .. },
                    ..
                }
            ) {
                continue;
            }
            if !matches!(arena.sort_of(var), IrSort::Datatype(_)) {
                continue;
            }
            let con_args = con_args.to_vec();
            if !con_args.contains(&var) {
                continue;
            }
            let ctor = *constructor;
            let datatype = arena.constructor_datatype(ctor);
            // The self-containing constructor must fit the size measure's shape:
            // every datatype-typed field must be exactly THIS datatype, and at
            // most one such recursive field (decline otherwise — keeps it sound).
            let mut recursive_fields = 0usize;
            let mut declined = false;
            for (_, field_sort) in arena.constructor_fields(ctor) {
                if let IrSort::Datatype(fdt) = field_sort {
                    if *fdt == datatype {
                        recursive_fields += 1;
                    } else {
                        declined = true; // a field of a different datatype: out of scope
                    }
                }
            }
            if declined || recursive_fields != 1 {
                continue;
            }
            return Some(AcyclicCycle {
                datatype,
                ctor,
                forward,
            });
        }
    }
    None
}

/// **Reconstruct a pure `QF_DT` acyclicity cycle to a Lean module** whose
/// `axeyum_refutation : False` is kernel-checked and **axiom-free over the
/// occurs-check** — acyclicity is discharged by the SIZE argument (a `Nat`-valued
/// recursor measure + the `n ≠ Nat.succ n` induction), not assumed (no acyclicity
/// axiom, no well-founded recursion). The only added axioms are the carrier atoms
/// and the input cycle equality itself.
///
/// Returns [`None`] when `assertions` carry no single-level cycle (the caller then
/// falls back to the general datatype reconstructor).
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if the recursive datatype family fails to
/// admit or the assembled `False` term does not `infer`/`def_eq` to `False` (a
/// defensive gate; a sound acyclicity refutation always discharges).
pub(super) fn reconstruct_qf_dt_acyclic_to_lean_module(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Result<String, ReconstructError>> {
    // A multi-step containment cycle `x₀ ⊐ x₁ ⊐ … ⊐ x_{k-1} ⊐ x₀` (k ≥ 2) is
    // discharged by the CHAINED size argument (`size x₀ = Nat.succ^k (size x₀)`,
    // refuted by `n ≠ Nat.succ^k n`); a single-level cycle (k = 1) keeps the
    // dedicated one-step path. Try the multi-step chain first, then fall back.
    if let Some(chain) = find_acyclicity_chain(arena, assertions) {
        return Some(build_acyclic_chain_refutation_module(arena, &chain));
    }
    let c = find_acyclicity_cycle(arena, assertions)?;
    Some(build_acyclic_refutation_module(arena, &c))
}

/// Assemble the kernel `False` term for an [`AcyclicCycle`] and render the Lean
/// module: build the recursive family `D`, the size measure `size : D → Nat`, the
/// cycle hypothesis `hx : Eq D x (C … x …)`, the size congruence
/// `Eq Nat (size x) (Nat.succ (size x))`, and the `n ≠ Nat.succ n` refutation.
fn build_acyclic_refutation_module(
    arena: &TermArena,
    c: &AcyclicCycle,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();

    // 1. Declare the kernel RECURSIVE family `D` carrying every constructor, each
    //    field shaped Carrier (non-datatype) or Recursive (this datatype).
    let ctor_ids = arena.datatype_constructors(c.datatype).to_vec();
    let ctor_shapes: Vec<(String, Vec<RecField>)> = ctor_ids
        .iter()
        .enumerate()
        .map(|(j, &cid)| {
            let shapes = arena
                .constructor_fields(cid)
                .iter()
                .map(|(_, sort)| match sort {
                    IrSort::Datatype(fdt) if *fdt == c.datatype => RecField::Recursive,
                    _ => RecField::Carrier,
                })
                .collect();
            (format!("c{j}"), shapes)
        })
        .collect();
    let family = ctx.recursive_datatype_family(&ctor_shapes)?;
    let ctor_pos = recursive_constructor_position(&ctor_ids, c.ctor)?;

    // 2. The cyclic value `x` is a single opaque atom of the datatype sort `D`;
    //    the constructor application `C(… x …)` reuses that same atom for the
    //    recursive argument and fresh carrier atoms for the non-recursive fields.
    let dty = ctx.kernel.const_(family.ind, vec![]);
    let x_atom = build_datatype_atom(&mut ctx, dty)?;
    let shapes = &family.fields[ctor_pos];
    let con = build_cycle_construct(&mut ctx, family.ctors[ctor_pos], shapes, x_atom)?;

    // 3. The size measure `size : D → Nat` and the two size applications
    //    `size x` and `size (C … x …)`; the latter ι→ `Nat.succ (size x)`.
    let alpha = ctx.alpha;
    let (nat, nat_zero, nat_succ) = (ctx.prelude.nat, ctx.prelude.nat_zero, ctx.prelude.nat_succ);
    let size = ctx
        .kernel
        .recursive_datatype_size(&family, alpha, nat, nat_zero, nat_succ);
    let size_x = ctx.kernel.app(size, x_atom);

    // 4. Input cycle hypothesis `hx : Eq D x (C … x …)` (the ONLY non-atom axiom),
    //    asserted in the input orientation.
    let one = ctx.one;
    let (eq_lhs, eq_rhs) = if c.forward {
        (x_atom, con)
    } else {
        (con, x_atom)
    };
    let eq_prop = mk_eq_at(&mut ctx, dty, one, eq_lhs, eq_rhs);
    let hx = fresh_axiom(&mut ctx, eq_prop, "assume")?;

    // 5. Size congruence `congrArg size hx`. With the hypothesis in the `x = C…`
    //    orientation this is `Eq Nat (size x) (size (C … x …))`, def_eq to
    //    `Eq Nat (size x) (Nat.succ (size x))`. When reversed, symmetrize first so
    //    the congruence's left side is `size x`.
    let nat_const = ctx.kernel.const_(nat, vec![]);
    let size_cong = if c.forward {
        build_congr_size(&mut ctx, dty, size, x_atom, con, hx)
    } else {
        // hx : Eq D (C…) x; flip to Eq D x (C…), then congruence on size.
        let hx_flipped = build_eq_symm(&mut ctx, dty, one, con, x_atom, hx);
        build_congr_size(&mut ctx, dty, size, x_atom, con, hx_flipped)
    };

    // 6. `nat_ne_succ (size x) size_cong : False` — the `n ≠ Nat.succ n` induction
    //    applied to `n := size x` and the size congruence `Eq Nat (size x)
    //    (Nat.succ (size x))` (def_eq to the induction's hypothesis type).
    let nat_ne_succ = build_nat_ne_succ(&mut ctx);
    let applied_n = ctx.kernel.app(nat_ne_succ, size_x);
    let false_term = ctx.kernel.app(applied_n, size_cong);

    require_infers_false(&mut ctx, false_term)?;
    let _ = nat_const;
    // Render the datatype family, the computational `Bool`, AND `Nat` as real Lean
    // `inductive`s so an external Lean regenerates their recursors *with* ι — the
    // size congruence and the `n ≠ succ n` induction only collapse if Lean can
    // compute `size (C … x …)` ι→ `Nat.succ (size x)`, `pred (succ k)` ι→ `k`, and
    // the discriminator `d zero`/`d (succ _)`. (`Bool` is listed for parity with
    // the other datatype routes; acyclicity itself never folds into `Bool`.)
    let bool_ind = ctx.prelude.bool_;
    let nat_ind = ctx.prelude.nat;
    let false_const = {
        let n = ctx.prelude().false_;
        ctx.kernel_mut().const_(n, vec![])
    };
    Ok(ctx.kernel().render_lean_module_with_inductives(
        LEAN_MODULE_THEOREM,
        false_const,
        false_term,
        &[family.ind, bool_ind, nat_ind],
    ))
}

// ===========================================================================
// Datatype ACYCLICITY — MULTI-STEP containment cycles (k ≥ 2), the chained size
// argument generalizing the single-level cycle above to full generality.
//
// A length-`k` containment cycle
//   x₀ = C₁(… x₁ …) ∧ x₁ = C₂(… x₂ …) ∧ … ∧ x_{k-1} = C_k(… x₀ …)
// (the structural cycle detector gives this path) is UNSAT for the same reason:
// the value `x₀` would strictly contain itself after `k` constructor descents.
// We discharge it WITHOUT any acyclicity axiom by CHAINING the size argument:
//
//   1. the recursive family `D` + `size : D → Nat` are as in the single-step
//      case, with `size (Cᵢ(… xⱼ …))` ι→ `Nat.succ (size xⱼ)` at the cycle's
//      recursive field;
//   2. each cycle equality `hᵢ : Eq D xᵢ Cᵢ₊₁(… x_{i+1} …)` gives, by
//      `congrArg size`, `cᵢ : Eq Nat (size xᵢ) (Nat.succ (size x_{i+1}))`
//      (def_eq after ι on the constructor side);
//   3. chain the `cᵢ` by `Eq.trans`, wrapping `congrArg Nat.succ^j` so the
//      middle terms line up, to reach
//        Eq Nat (size x₀) (Nat.succ^k (size x₀));
//   4. apply `nat_ne_succ_pow k (size x₀)` — the proof, BY INDUCTION on `Nat`,
//      that `n ≠ Nat.succ^k n` for `k ≥ 1` (the SAME discriminator / predecessor
//      machinery as `n ≠ Nat.succ n`, with `Nat.succ^k` for `Nat.succ`) — to
//      close it to `False`.
//
// Every step is ι-reduction + `Eq.rec` (`congrArg`/`Eq.trans`) + `Nat.rec`; the
// only added axioms are the carrier atoms (one opaque `D` atom per cycle
// variable `xᵢ`, fresh `α` atoms for the non-recursive fields) and the `k` input
// cycle equalities. The k = 1 special case stays on the dedicated single-step
// path; this handles k ≥ 2 (mutual recursion and longer chains).
// ===========================================================================

/// One link of a [`AcyclicChain`]: an asserted equality `xᵢ = Cᵢ₊₁(… x_{i+1} …)`
/// (in either orientation) whose constructor `Cᵢ₊₁` strictly contains the next
/// cycle variable `x_{i+1}` at its single recursive field.
struct AcyclicChainLink {
    /// The constructor `Cᵢ₊₁` of this link's containing side.
    ctor: ConstructorId,
    /// `true` when the equality is asserted as `xᵢ = Cᵢ₊₁(…)`, `false` when
    /// reversed (`Cᵢ₊₁(…) = xᵢ`). Drives whether the size congruence is fed
    /// directly or re-oriented by `Eq.symm`.
    forward: bool,
}

/// A length-`k` (k ≥ 2) containment cycle `x₀ ⊐ x₁ ⊐ … ⊐ x_{k-1} ⊐ x₀` located in
/// `assertions`. The cyclic values are modeled as `k` distinct opaque `D` atoms
/// in the kernel refutation, so only the datatype, the per-link constructor, and
/// the orientation are needed (the concrete `TermId`s drive detection only).
struct AcyclicChain {
    /// The datatype `D` shared by every cycle variable.
    datatype: DatatypeId,
    /// The `k` links, in cycle order: link `i` is `xᵢ = Cᵢ₊₁(… x_{i+1} …)`.
    links: Vec<AcyclicChainLink>,
}

/// A directed strict-containment edge `var → next` derived from one asserted
/// equality `var = C(… next …)`: `var` is a non-constructor datatype term, `C`
/// has exactly one recursive field of this datatype holding the non-constructor
/// datatype term `next`.
struct ContainmentEdge {
    var: TermId,
    next: TermId,
    ctor: ConstructorId,
    datatype: DatatypeId,
    forward: bool,
}

/// Whether `term` is a constructor application.
fn is_constructor_app(arena: &TermArena, term: TermId) -> bool {
    matches!(
        arena.node(term),
        IrTermNode::App {
            op: IrOp::DtConstruct { .. },
            ..
        }
    )
}

/// Extract a single strict-containment edge from one asserted equality, in the
/// given orientation: `var = con` where `var` is a non-constructor datatype term
/// and `con = C(… next …)` has exactly one recursive (this-datatype) field whose
/// argument `next` is itself a non-constructor datatype term. Declines (returns
/// [`None`]) otherwise — keeping the route sound by only emitting genuine edges.
fn containment_edge(
    arena: &TermArena,
    var: TermId,
    con: TermId,
    forward: bool,
) -> Option<ContainmentEdge> {
    let IrTermNode::App {
        op: IrOp::DtConstruct { constructor, .. },
        args: con_args,
    } = arena.node(con)
    else {
        return None;
    };
    // `var` must be a non-constructor datatype term (a cycle node, not a value).
    if is_constructor_app(arena, var) || !matches!(arena.sort_of(var), IrSort::Datatype(_)) {
        return None;
    }
    let ctor = *constructor;
    let con_args = con_args.to_vec();
    let datatype = arena.constructor_datatype(ctor);
    // Identify the single recursive field of THIS datatype and the term it holds;
    // decline on any other-datatype field or a recursive-field count ≠ 1.
    let mut next: Option<TermId> = None;
    for ((_, field_sort), &arg) in arena.constructor_fields(ctor).iter().zip(&con_args) {
        if let IrSort::Datatype(fdt) = field_sort {
            if *fdt == datatype {
                if next.is_some() {
                    return None; // more than one recursive field — out of shape
                }
                next = Some(arg);
            } else {
                return None; // a field of a different datatype — out of scope
            }
        }
    }
    let next = next?;
    // The recursive field must hold a non-constructor datatype term (the next
    // cycle node); a constructor there would be a different (nested) shape.
    if is_constructor_app(arena, next) {
        return None;
    }
    Some(ContainmentEdge {
        var,
        next,
        ctor,
        datatype,
        forward,
    })
}

/// Find a MULTI-step (k ≥ 2) containment cycle among `assertions`, or [`None`].
///
/// Builds the strict-containment graph (edge `var → next` per asserted
/// `var = C(… next …)`, [`containment_edge`]) and runs a DFS for a directed
/// cycle of length ≥ 2. The returned [`AcyclicChain`] lists the cycle's links in
/// order. Single-level self-cycles (`var → var`, k = 1) are intentionally NOT
/// returned here — they keep the dedicated [`find_acyclicity_cycle`] path.
fn find_acyclicity_chain(arena: &TermArena, assertions: &[TermId]) -> Option<AcyclicChain> {
    // Collect every containment edge (both orientations of each equality).
    let mut edges: Vec<ContainmentEdge> = Vec::new();
    for &assertion in assertions {
        let IrTermNode::App { op: IrOp::Eq, args } = arena.node(assertion) else {
            continue;
        };
        let &[lhs, rhs] = &args[..] else {
            continue;
        };
        for (forward, var, con) in [(true, lhs, rhs), (false, rhs, lhs)] {
            if let Some(edge) = containment_edge(arena, var, con, forward) {
                edges.push(edge);
            }
        }
    }
    if edges.is_empty() {
        return None;
    }
    // Adjacency by source `var`: for each node, the edges leaving it. Iterate in
    // a deterministic (insertion) order so the cycle found is stable.
    let mut nodes: Vec<TermId> = Vec::new();
    let mut node_index: BTreeMap<TermId, usize> = BTreeMap::new();
    let intern = |t: TermId, nodes: &mut Vec<TermId>, idx: &mut BTreeMap<TermId, usize>| {
        *idx.entry(t).or_insert_with(|| {
            nodes.push(t);
            nodes.len() - 1
        })
    };
    let mut adj: Vec<Vec<usize>> = Vec::new();
    for (e_idx, e) in edges.iter().enumerate() {
        let vi = intern(e.var, &mut nodes, &mut node_index);
        let ni = intern(e.next, &mut nodes, &mut node_index);
        while adj.len() <= vi.max(ni) {
            adj.push(Vec::new());
        }
        adj[vi].push(e_idx);
        let _ = ni;
    }

    // Iterative three-colour DFS that records the edge path, so on a back-edge we
    // can reconstruct the cycle's links.
    let n = nodes.len();
    let mut color = vec![0u8; n]; // 0 white, 1 grey/on-path, 2 black
    // For each grey node, the edge index by which we entered it (parent edge).
    let mut parent_edge = vec![usize::MAX; n];
    for start in 0..n {
        if color[start] != 0 {
            continue;
        }
        // Stack of (node, edge_index_into_adj[node]) for explicit DFS.
        let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
        color[start] = 1;
        while let Some(&(node, ei)) = stack.last() {
            if ei >= adj[node].len() {
                color[node] = 2;
                stack.pop();
                continue;
            }
            stack.last_mut().unwrap().1 += 1;
            let edge_idx = adj[node][ei];
            let to = node_index[&edges[edge_idx].next];
            match color[to] {
                1 => {
                    // Back-edge `node → to`: a cycle. Walk parent edges from `node`
                    // back to `to` to collect the cycle's edge indices in order.
                    if let Some(chain) =
                        collect_cycle(&edges, &parent_edge, &nodes, node, to, edge_idx)
                    {
                        return Some(chain);
                    }
                }
                0 => {
                    color[to] = 1;
                    parent_edge[to] = edge_idx;
                    stack.push((to, 0));
                }
                _ => {}
            }
        }
    }
    None
}

/// Reconstruct the cycle's ordered links from a discovered back-edge
/// `from → back` (edge `closing_edge`). Walks `parent_edge` from `from` up to
/// `back`, collecting edge indices, then orders them `back → … → from → back`.
/// Returns [`None`] for a degenerate length-1 cycle (handled by the single-step
/// path) or any datatype mismatch among the links (kept sound by declining).
fn collect_cycle(
    edges: &[ContainmentEdge],
    parent_edge: &[usize],
    nodes: &[TermId],
    from: usize,
    back: usize,
    closing_edge: usize,
) -> Option<AcyclicChain> {
    // Collect the back-path edges from `from` up to (but not including) `back`.
    let mut path_edges: Vec<usize> = vec![closing_edge];
    let mut cur = from;
    while cur != back {
        let pe = parent_edge[cur];
        if pe == usize::MAX {
            return None; // no parent — not a closed cycle through `back`
        }
        path_edges.push(pe);
        // Step to the source node of the parent edge.
        cur = nodes
            .iter()
            .position(|&t| t == edges[pe].var)
            .expect("edge source is an interned node");
    }
    // `path_edges` is closing_edge (from→back) then parents back→…→from; the cycle
    // in order x₀ ⊐ x₁ ⊐ … is the reverse, starting at `back`.
    path_edges.reverse();
    if path_edges.len() < 2 {
        return None; // length-1 self-cycle: the single-step path covers it.
    }
    let datatype = edges[path_edges[0]].datatype;
    let mut links = Vec::with_capacity(path_edges.len());
    for &ei in &path_edges {
        if edges[ei].datatype != datatype {
            return None; // mixed datatypes in one cycle — out of scope, decline.
        }
        links.push(AcyclicChainLink {
            ctor: edges[ei].ctor,
            forward: edges[ei].forward,
        });
    }
    Some(AcyclicChain { datatype, links })
}

/// Assemble the kernel `False` term for an [`AcyclicChain`] (k ≥ 2) and render the
/// Lean module: build the recursive family `D`, the size measure, `k` opaque `D`
/// atoms `x₀ … x_{k-1}`, the `k` cycle hypotheses, chain their size congruences by
/// `Eq.trans` to `Eq Nat (size x₀) (Nat.succ^k (size x₀))`, and refute with
/// `nat_ne_succ_pow k`.
fn build_acyclic_chain_refutation_module(
    arena: &TermArena,
    chain: &AcyclicChain,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();
    let k = chain.links.len();

    // 1. Declare the recursive family `D` (every constructor, fields Carrier/Rec).
    let ctor_ids = arena.datatype_constructors(chain.datatype).to_vec();
    let ctor_shapes: Vec<(String, Vec<RecField>)> = ctor_ids
        .iter()
        .enumerate()
        .map(|(j, &cid)| {
            let shapes = arena
                .constructor_fields(cid)
                .iter()
                .map(|(_, sort)| match sort {
                    IrSort::Datatype(fdt) if *fdt == chain.datatype => RecField::Recursive,
                    _ => RecField::Carrier,
                })
                .collect();
            (format!("c{j}"), shapes)
        })
        .collect();
    let family = ctx.recursive_datatype_family(&ctor_shapes)?;

    // 2. The size measure `size : D → Nat`.
    let dty = ctx.kernel.const_(family.ind, vec![]);
    let alpha = ctx.alpha;
    let (nat, nat_zero, nat_succ) = (ctx.prelude.nat, ctx.prelude.nat_zero, ctx.prelude.nat_succ);
    let size = ctx
        .kernel
        .recursive_datatype_size(&family, alpha, nat, nat_zero, nat_succ);

    // 3. One opaque `D` atom per cycle variable x₀ … x_{k-1}.
    let mut x_atoms = Vec::with_capacity(k);
    for _ in 0..k {
        x_atoms.push(build_datatype_atom(&mut ctx, dty)?);
    }
    let size_x: Vec<ExprId> = x_atoms.iter().map(|&x| ctx.kernel.app(size, x)).collect();

    // 4./5. For each link i: hypothesis hᵢ : xᵢ = Cᵢ₊₁(… x_{i+1} …), then
    //   cᵢ := congrArg size hᵢ : Eq Nat (size xᵢ) (size con_i)
    //       def_eq Eq Nat (size xᵢ) (Nat.succ (size x_{i+1})).
    let one = ctx.one;
    let mut link_congrs = Vec::with_capacity(k);
    for (i, link) in chain.links.iter().enumerate() {
        let next = (i + 1) % k;
        let pos = recursive_constructor_position(&ctor_ids, link.ctor)?;
        let shapes = family.fields[pos].clone();
        let con = build_cycle_construct(&mut ctx, family.ctors[pos], &shapes, x_atoms[next])?;
        let (eq_lhs, eq_rhs) = if link.forward {
            (x_atoms[i], con)
        } else {
            (con, x_atoms[i])
        };
        let eq_prop = mk_eq_at(&mut ctx, dty, one, eq_lhs, eq_rhs);
        let hx = fresh_axiom(&mut ctx, eq_prop, "assume")?;
        let congr = if link.forward {
            build_congr_size(&mut ctx, dty, size, x_atoms[i], con, hx)
        } else {
            let hx_flipped = build_eq_symm(&mut ctx, dty, one, con, x_atoms[i], hx);
            build_congr_size(&mut ctx, dty, size, x_atoms[i], con, hx_flipped)
        };
        // congr : Eq Nat (size xᵢ) (size con) def_eq Eq Nat (size xᵢ)
        //         (Nat.succ (size x_{next})).
        link_congrs.push(congr);
    }

    // 6. Chain by Eq.trans, wrapping `congrArg Nat.succ^j` so the middle terms line
    //    up. `acc : Eq Nat (size x₀) (Nat.succ^{rhs_pow} (size x_{cur_idx}))`.
    let nat_const = ctx.kernel.const_(nat, vec![]);
    let succ_const = ctx.kernel.const_(nat_succ, vec![]);

    // acc starts as link 0: Eq Nat (size x₀) (Nat.succ (size x₁)).
    let mut acc = link_congrs[0];
    // rhs_pow tracks the number of `succ`s currently wrapping `size x_{cur_idx}`.
    let mut cur_idx = 1 % k;
    let mut rhs_pow = 1usize;
    for &link_congr in link_congrs.iter().skip(1) {
        // link_congr : Eq Nat (size x_{cur_idx}) (Nat.succ (size x_{next_idx})).
        let next_idx = (cur_idx + 1) % k;
        // congrArg (Nat.succ^{rhs_pow}) link_congr :
        //   Eq Nat (Nat.succ^{rhs_pow} (size x_{cur_idx}))
        //          (Nat.succ^{rhs_pow} (Nat.succ (size x_{next_idx}))).
        let link_rhs = succ_pow_apply(&mut ctx, nat_succ, 1, size_x[next_idx]);
        let wrapped = build_congr_succ_pow(
            &mut ctx,
            succ_const,
            nat_const,
            rhs_pow,
            size_x[cur_idx],
            link_rhs,
            link_congr,
        );
        // Eq.trans acc wrapped : Eq Nat (size x₀)
        //   (Nat.succ^{rhs_pow} (Nat.succ (size x_{next_idx})))
        //   = Eq Nat (size x₀) (Nat.succ^{rhs_pow+1} (size x_{next_idx})).
        let mid = succ_pow_apply(&mut ctx, nat_succ, rhs_pow, size_x[cur_idx]);
        let new_pow = rhs_pow + 1;
        let rhs = succ_pow_apply(&mut ctx, nat_succ, new_pow, size_x[next_idx]);
        acc = build_eq_trans_nat(&mut ctx, nat_const, size_x[0], mid, rhs, acc, wrapped);
        cur_idx = next_idx;
        rhs_pow = new_pow;
    }
    // After the loop cur_idx == 0 and rhs_pow == k:
    //   acc : Eq Nat (size x₀) (Nat.succ^k (size x₀)).
    debug_assert_eq!(cur_idx, 0);
    debug_assert_eq!(rhs_pow, k);

    // 7. nat_ne_succ_pow k applied to (size x₀) and acc : False.
    let nat_ne_succ_pow = build_nat_ne_succ_pow(&mut ctx, k);
    let applied_n = ctx.kernel.app(nat_ne_succ_pow, size_x[0]);
    let false_term = ctx.kernel.app(applied_n, acc);

    require_infers_false(&mut ctx, false_term)?;
    let _ = nat_const;
    let bool_ind = ctx.prelude.bool_;
    let nat_ind = ctx.prelude.nat;
    let false_const = {
        let n = ctx.prelude().false_;
        ctx.kernel_mut().const_(n, vec![])
    };
    Ok(ctx.kernel().render_lean_module_with_inductives(
        LEAN_MODULE_THEOREM,
        false_const,
        false_term,
        &[family.ind, bool_ind, nat_ind],
    ))
}

/// Apply `Nat.succ` `j` times to `base`, returning `Nat.succ^j base`.
fn succ_pow_apply(ctx: &mut ReconstructCtx, nat_succ: NameId, j: usize, base: ExprId) -> ExprId {
    let mut e = base;
    for _ in 0..j {
        let s = ctx.kernel.const_(nat_succ, vec![]);
        e = ctx.kernel.app(s, e);
    }
    e
}

/// Build `congrArg (Nat.succ^pow) h` as nested `congrArg Nat.succ` `Eq.rec`s:
/// given `h : Eq Nat a b`, produce `Eq Nat (Nat.succ^pow a) (Nat.succ^pow b)`.
/// `a`/`b` are the equands of `h`; `pow` is the number of `Nat.succ` wraps. Pure
/// `Eq.rec` — axiom-free.
fn build_congr_succ_pow(
    ctx: &mut ReconstructCtx,
    succ: ExprId,
    nat_const: ExprId,
    pow: usize,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let mut proof = h;
    let mut left = a;
    let mut right = b;
    for _ in 0..pow {
        proof = build_congr_unary(ctx, nat_const, succ, left, right, proof);
        let new_left = ctx.kernel.app(succ, left);
        let new_right = ctx.kernel.app(succ, right);
        left = new_left;
        right = new_right;
    }
    let _ = (left, right);
    proof
}

/// Build `congrArg f h` for a unary `f : Nat → Nat` as an `Eq.rec`: given
/// `h : Eq Nat a b`, produce `Eq Nat (f a) (f b)`. The `Nat → Nat` analogue of
/// [`build_congr_size`] (`size : D → Nat`) specialised to a same-sort function.
fn build_congr_unary(
    ctx: &mut ReconstructCtx,
    nat_const: ExprId,
    f: ExprId,
    a: ExprId,
    b: ExprId,
    h: ExprId,
) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let f_a = ctx.kernel.app(f, a);
    // motive := fun (z : Nat) (_ : Eq Nat a z) => Eq Nat (f a) (f z).
    let transport_motive = {
        let z1 = ctx.kernel.bvar(1);
        let f_z = ctx.kernel.app(f, z1);
        let body = mk_eq_at(ctx, nat_const, one, f_a, f_z);
        let z0 = ctx.kernel.bvar(0);
        let eq_a_z = mk_eq_at(ctx, nat_const, one, a, z0);
        let inner = ctx.kernel.lam(anon, eq_a_z, body, BinderInfo::Default);
        ctx.kernel.lam(anon, nat_const, inner, BinderInfo::Default)
    };
    let refl = ctx.kernel.const_(ctx.prelude.eq_refl, vec![one]);
    let refl_case = {
        let e = ctx.kernel.app(refl, nat_const);
        ctx.kernel.app(e, f_a)
    };
    let v = ctx.kernel.level_zero();
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![v, one]);
    let e = ctx.kernel.app(rec_eq, nat_const);
    let e = ctx.kernel.app(e, a);
    let e = ctx.kernel.app(e, transport_motive);
    let e = ctx.kernel.app(e, refl_case);
    let e = ctx.kernel.app(e, b);
    ctx.kernel.app(e, h)
}

/// Build `Eq.trans` over `Nat`: given `h1 : Eq Nat a b` and `h2 : Eq Nat b c`,
/// produce `Eq Nat a c`. An `Eq.rec` transport of `h1` along `h2` (motive
/// `fun (z) (_ : Eq Nat b z) => Eq Nat a z`, refl case `h1`). Pure `Eq.rec` —
/// axiom-free. Specialised to `Nat` (the chained size argument's codomain).
fn build_eq_trans_nat(
    ctx: &mut ReconstructCtx,
    nat_const: ExprId,
    a: ExprId,
    b: ExprId,
    c: ExprId,
    h1: ExprId,
    h2: ExprId,
) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    // motive := fun (z : Nat) (_ : Eq Nat b z) => Eq Nat a z.
    let transport_motive = {
        let z1 = ctx.kernel.bvar(1);
        let body = mk_eq_at(ctx, nat_const, one, a, z1);
        let z0 = ctx.kernel.bvar(0);
        let eq_b_z = mk_eq_at(ctx, nat_const, one, b, z0);
        let inner = ctx.kernel.lam(anon, eq_b_z, body, BinderInfo::Default);
        ctx.kernel.lam(anon, nat_const, inner, BinderInfo::Default)
    };
    // refl case : Eq Nat a b — exactly `h1` (the `z := b` instance is `Eq Nat a b`).
    let refl_case = h1;
    let v = ctx.kernel.level_zero();
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![v, one]);
    let e = ctx.kernel.app(rec_eq, nat_const);
    let e = ctx.kernel.app(e, b);
    let e = ctx.kernel.app(e, transport_motive);
    let e = ctx.kernel.app(e, refl_case);
    let e = ctx.kernel.app(e, c);
    ctx.kernel.app(e, h2)
}

/// Position of constructor `cid` in `ctor_ids` (declaration order), or a
/// [`ReconstructError::KernelRejected`] if it is not a constructor of the
/// datatype.
fn recursive_constructor_position(
    ctor_ids: &[ConstructorId],
    cid: ConstructorId,
) -> Result<usize, ReconstructError> {
    ctor_ids
        .iter()
        .position(|&c| c == cid)
        .ok_or_else(|| ReconstructError::KernelRejected {
            rule: "datatype_acyclic".to_owned(),
            detail: "constructor not in datatype".to_owned(),
        })
}

/// Declare a fresh opaque atom of the datatype sort `dty` (the cyclic value `x`).
fn build_datatype_atom(ctx: &mut ReconstructCtx, dty: ExprId) -> Result<ExprId, ReconstructError> {
    let atom_name = ctx.fresh_name("dtatom");
    ctx.kernel
        .add_declaration(Declaration::Axiom {
            name: atom_name,
            uparams: vec![],
            ty: dty,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "datatype_acyclic".to_owned(),
            detail: format!("datatype atom did not admit: {e:?}"),
        })?;
    Ok(ctx.kernel.const_(atom_name, vec![]))
}

/// Build the self-containing constructor application `C(… x …)`: the single
/// recursive field is the cyclic atom `x_atom`, every carrier field a fresh
/// opaque `α` atom.
fn build_cycle_construct(
    ctx: &mut ReconstructCtx,
    ctor: NameId,
    shapes: &[RecField],
    x_atom: ExprId,
) -> Result<ExprId, ReconstructError> {
    let mut con = ctx.kernel.const_(ctor, vec![]);
    for (i, shape) in shapes.iter().enumerate() {
        let arg = match shape {
            RecField::Recursive => x_atom,
            RecField::Carrier => {
                let atom_name = ctx.fresh_name(&format!("fld_{i}"));
                let alpha = ctx.alpha;
                ctx.kernel
                    .add_declaration(Declaration::Axiom {
                        name: atom_name,
                        uparams: vec![],
                        ty: alpha,
                    })
                    .map_err(|e| ReconstructError::KernelRejected {
                        rule: "datatype_acyclic".to_owned(),
                        detail: format!("field carrier atom did not admit: {e:?}"),
                    })?;
                ctx.kernel.const_(atom_name, vec![])
            }
        };
        con = ctx.kernel.app(con, arg);
    }
    Ok(con)
}

/// Build the size congruence transport `congrArg size h` as an `Eq.rec`: given
/// `h : Eq dty x con` and the size measure `size : dty → Nat`, produce a proof of
/// `Eq Nat (size x) (size con)`. The `Nat` twin of [`build_congr_sel`] (the
/// carrier codomain `α` replaced by `Nat`). Pure `Eq.rec` — axiom-free.
fn build_congr_size(
    ctx: &mut ReconstructCtx,
    dty: ExprId,
    size: ExprId,
    x: ExprId,
    con: ExprId,
    h: ExprId,
) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);
    let size_x = ctx.kernel.app(size, x);

    // motive := fun (z : dty) (_ : Eq dty x z) => Eq Nat (size x) (size z).
    let transport_motive = {
        let z_var = ctx.kernel.bvar(1);
        let size_z = ctx.kernel.app(size, z_var);
        let body = mk_eq_at(ctx, nat_const, one, size_x, size_z);
        let z0 = ctx.kernel.bvar(0);
        let eq_x_z = mk_eq_at(ctx, dty, one, x, z0);
        let inner = ctx.kernel.lam(anon, eq_x_z, body, BinderInfo::Default);
        ctx.kernel.lam(anon, dty, inner, BinderInfo::Default)
    };
    // refl_case : Eq Nat (size x) (size x) — `Eq.refl Nat (size x)`.
    let refl = ctx.kernel.const_(ctx.prelude.eq_refl, vec![one]);
    let refl_case = {
        let e = ctx.kernel.app(refl, nat_const);
        ctx.kernel.app(e, size_x)
    };
    // Eq.rec.{0,1} dty x transport_motive refl_case con h
    //   : Eq Nat (size x) (size con). The motive eliminates into `Prop` ⇒ v = 0;
    // the equands of `h` are `dty : Sort 1` ⇒ u = 1.
    let v = ctx.kernel.level_zero();
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![v, one]);
    let e = ctx.kernel.app(rec_eq, dty);
    let e = ctx.kernel.app(e, x);
    let e = ctx.kernel.app(e, transport_motive);
    let e = ctx.kernel.app(e, refl_case);
    let e = ctx.kernel.app(e, con);
    ctx.kernel.app(e, h)
}

/// Build the proof `nat_ne_succ : Π (n : Nat), Eq Nat n (Nat.succ n) → False` — the
/// fact that `n ≠ Nat.succ n` — **by induction on `Nat`** (`Nat.rec` into `Prop`,
/// elimination universe `v = 0`), axiom-free:
///
/// - **motive** `P := λ (n : Nat) => Eq Nat n (Nat.succ n) → False` (`Nat → Prop`);
/// - **base** `m_zero : P Nat.zero`, i.e. `Eq Nat zero (succ zero) → False`: an
///   `Eq.rec` transport of `True.intro` along the hypothesis through the
///   discriminator `d := Nat.rec (λ _ => Prop) True (λ _ _ => False)` (so
///   `d zero ι→ True`, `d (succ _) ι→ False`) lands `False`;
/// - **step** `m_succ : Π (k : Nat) (ih : P k), P (succ k)`: from
///   `h : Eq Nat (succ k) (succ (succ k))`, the predecessor selector
///   `pred := Nat.rec (λ _ => Nat) zero (λ m _ => m)` and `congrArg pred h` give
///   `Eq Nat k (succ k)` (ι on both `pred (succ _)`), which `ih` turns into
///   `False`.
pub(super) fn build_nat_ne_succ(ctx: &mut ReconstructCtx) -> ExprId {
    // motive `P := λ (n : Nat) => Eq Nat n (Nat.succ n) → False` (`Nat → Prop`).
    let motive = build_nat_ne_succ_motive(ctx);
    let m_zero = build_nat_ne_succ_m_zero(ctx);
    let m_succ = build_nat_ne_succ_m_succ(ctx);
    // `Nat.rec.{0} P m_zero m_succ` : Π (n : Nat), P n.
    let z = ctx.kernel.level_zero();
    let rec0 = ctx.kernel.const_(ctx.prelude.nat_rec, vec![z]);
    let e = ctx.kernel.app(rec0, motive);
    let e = ctx.kernel.app(e, m_zero);
    ctx.kernel.app(e, m_succ)
}

/// The induction motive `P := λ (n : Nat) => Eq Nat n (Nat.succ n) → False`
/// (`Nat → Prop`) of the `n ≠ Nat.succ n` proof.
fn build_nat_ne_succ_motive(ctx: &mut ReconstructCtx) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);
    let succ_const = ctx.kernel.const_(ctx.prelude.nat_succ, vec![]);
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    // Under the binder `n` (BVar 0): `Eq Nat n (Nat.succ n) → False`.
    let n0 = ctx.kernel.bvar(0);
    let succ_n = ctx.kernel.app(succ_const, n0);
    let n0b = ctx.kernel.bvar(0);
    let eq_n = mk_eq_at(ctx, nat_const, one, n0b, succ_n);
    let arrow = ctx.kernel.pi(anon, eq_n, false_const, BinderInfo::Default);
    ctx.kernel.lam(anon, nat_const, arrow, BinderInfo::Default)
}

/// The `zero`-base discriminator `d := Nat.rec.{1} (λ _ => Prop) True
/// (λ _ _ => False)` : `d Nat.zero` ι→ `True`, `d (Nat.succ _)` ι→ `False`.
pub(super) fn build_nat_discriminator(ctx: &mut ReconstructCtx) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let prop = ctx.kernel.sort_zero();
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);
    let true_const = ctx.kernel.const_(ctx.prelude.true_, vec![]);
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let rec1 = ctx.kernel.const_(ctx.prelude.nat_rec, vec![one]);
    let d_motive = ctx.kernel.lam(anon, nat_const, prop, BinderInfo::Default);
    // m_zero := True ;  m_succ := λ (k : Nat) (ih : Prop), False.
    let m_succ = {
        let inner = ctx.kernel.lam(anon, prop, false_const, BinderInfo::Default);
        ctx.kernel.lam(anon, nat_const, inner, BinderInfo::Default)
    };
    let e = ctx.kernel.app(rec1, d_motive);
    let e = ctx.kernel.app(e, true_const);
    ctx.kernel.app(e, m_succ)
}

/// The predecessor selector `pred := Nat.rec.{1} (λ _ => Nat) Nat.zero
/// (λ (m : Nat) (ih : Nat) => m)` : `pred (Nat.succ m)` ι→ `m`.
pub(super) fn build_nat_pred(ctx: &mut ReconstructCtx) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);
    let zero_const = ctx.kernel.const_(ctx.prelude.nat_zero, vec![]);
    let rec1 = ctx.kernel.const_(ctx.prelude.nat_rec, vec![one]);
    let p_motive = ctx
        .kernel
        .lam(anon, nat_const, nat_const, BinderInfo::Default);
    // m_succ := λ (m : Nat) (ih : Nat), m   (m is BVar 1 under the ih binder).
    let m_succ_p = {
        let m1 = ctx.kernel.bvar(1);
        let inner = ctx.kernel.lam(anon, nat_const, m1, BinderInfo::Default);
        ctx.kernel.lam(anon, nat_const, inner, BinderInfo::Default)
    };
    let e = ctx.kernel.app(rec1, p_motive);
    let e = ctx.kernel.app(e, zero_const);
    ctx.kernel.app(e, m_succ_p)
}

/// The base-case minor `m_zero : P Nat.zero` = `Eq Nat zero (succ zero) → False`:
/// `λ (h : Eq Nat zero (succ zero)), Eq.rec.{0,1} Nat zero
///  (λ (m : Nat)(_ : Eq Nat zero m) => d m) (True.intro : d zero) (succ zero) h`,
/// where `d zero` `def_eq` `True` and `d (succ zero)` `def_eq` `False` (the
/// discriminator ι), so the transport lands `False`.
pub(super) fn build_nat_ne_succ_m_zero(ctx: &mut ReconstructCtx) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let z = ctx.kernel.level_zero();
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);
    let zero_const = ctx.kernel.const_(ctx.prelude.nat_zero, vec![]);
    let succ_const = ctx.kernel.const_(ctx.prelude.nat_succ, vec![]);
    let succ_zero = ctx.kernel.app(succ_const, zero_const);
    let discr = build_nat_discriminator(ctx);

    let hyp_ty = mk_eq_at(ctx, nat_const, one, zero_const, succ_zero);
    // transport motive: λ (m : Nat) (_ : Eq Nat zero m) => d m.
    let t_motive = {
        let m1 = ctx.kernel.bvar(1);
        let d_m = ctx.kernel.app(discr, m1);
        let m0 = ctx.kernel.bvar(0);
        let eq_zero_m = mk_eq_at(ctx, nat_const, one, zero_const, m0);
        let inner = ctx.kernel.lam(anon, eq_zero_m, d_m, BinderInfo::Default);
        ctx.kernel.lam(anon, nat_const, inner, BinderInfo::Default)
    };
    // refl case `True.intro : d zero` (d zero def_eq True).
    let refl_case = ctx.kernel.const_(ctx.prelude.true_intro, vec![]);
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![z, one]);
    let body = {
        let e = ctx.kernel.app(rec_eq, nat_const);
        let e = ctx.kernel.app(e, zero_const);
        let e = ctx.kernel.app(e, t_motive);
        let e = ctx.kernel.app(e, refl_case);
        let e = ctx.kernel.app(e, succ_zero);
        let h = ctx.kernel.bvar(0);
        ctx.kernel.app(e, h)
    };
    ctx.kernel.lam(anon, hyp_ty, body, BinderInfo::Default)
}

/// The step minor `m_succ : Π (k : Nat) (ih : P k), P (succ k)`:
/// `λ (k : Nat) (ih : Eq Nat k (succ k) → False)
///  (h : Eq Nat (succ k) (succ (succ k))), ih (congrArg pred h)`,
/// where `congrArg pred h : Eq Nat (pred (succ k)) (pred (succ (succ k)))` is
/// `def_eq` `Eq Nat k (succ k)` (ι on both `pred (succ _)`), which `ih` turns into
/// `False`.
pub(super) fn build_nat_ne_succ_m_succ(ctx: &mut ReconstructCtx) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);
    let succ_const = ctx.kernel.const_(ctx.prelude.nat_succ, vec![]);
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let pred = build_nat_pred(ctx);
    // The CLOSED predecessor-congruence lemma, applied (below) to the open `succ k`
    // terms — closed, so no de-Bruijn capture.
    let congr_pred = build_congr_pred_lemma(ctx, pred);

    // Build inside three binders: k(BVar 2), ih(BVar 1), h(BVar 0).
    // hyp type of `h`: Eq Nat (succ k) (succ (succ k)) (under k, ih ⇒ k = BVar 1).
    let k_for_h = ctx.kernel.bvar(1);
    let succ_k_h = ctx.kernel.app(succ_const, k_for_h);
    let succ_succ_k_h = ctx.kernel.app(succ_const, succ_k_h);
    let h_ty = mk_eq_at(ctx, nat_const, one, succ_k_h, succ_succ_k_h);

    // congr_pred (succ k) (succ (succ k)) h
    //   : Eq Nat (pred (succ k)) (pred (succ (succ k))), def_eq Eq Nat k (succ k).
    // Under k(BVar 2), ih(BVar 1), h(BVar 0): k = BVar 2, h = BVar 0.
    let k_under_h = ctx.kernel.bvar(2);
    let succ_k = ctx.kernel.app(succ_const, k_under_h);
    let succ_succ_k = ctx.kernel.app(succ_const, succ_k);
    let h_var = ctx.kernel.bvar(0);
    let congr = {
        let e = ctx.kernel.app(congr_pred, succ_k);
        let e = ctx.kernel.app(e, succ_succ_k);
        ctx.kernel.app(e, h_var)
    };
    // ih (congr) : False   (ih is BVar 1, congr def_eq Eq Nat k (succ k)).
    let ih_var = ctx.kernel.bvar(1);
    let applied = ctx.kernel.app(ih_var, congr);

    // Bind h, then ih, then k.
    let lam_h = ctx.kernel.lam(anon, h_ty, applied, BinderInfo::Default);
    // ih type: Eq Nat k (succ k) → False  (under k ⇒ k = BVar 0).
    let k_for_ih = ctx.kernel.bvar(0);
    let succ_k_ih = ctx.kernel.app(succ_const, k_for_ih);
    let k_for_ih2 = ctx.kernel.bvar(0);
    let eq_k = mk_eq_at(ctx, nat_const, one, k_for_ih2, succ_k_ih);
    let ih_ty = ctx.kernel.pi(anon, eq_k, false_const, BinderInfo::Default);
    let lam_ih = ctx.kernel.lam(anon, ih_ty, lam_h, BinderInfo::Default);
    ctx.kernel.lam(anon, nat_const, lam_ih, BinderInfo::Default)
}

/// Build the **closed** predecessor-congruence lemma
/// `congr_pred : Π (a b : Nat) (h : Eq Nat a b), Eq Nat (pred a) (pred b)` as a
/// lambda whose body is an `Eq.rec` transport over the supplied `pred : Nat → Nat`.
/// Because the lemma is closed (all `Nat`/`Eq` references are bound by its own
/// `a`/`b`/`h` binders), it can be *applied* to open terms — e.g. `succ k` for the
/// outer-bound `k` in the `n ≠ succ n` step — without manual de-Bruijn lifting (a
/// `congrArg` over open terms would otherwise capture). Pure `Eq.rec` — axiom-free.
///
/// De Bruijn layout (outer→inner): `a` (`BVar 2`), `b` (`BVar 1`), `h` (`BVar 0`).
/// The transport motive adds two further binders `z` (`BVar 1` there) and `_`
/// (`BVar 0`).
fn build_congr_pred_lemma(ctx: &mut ReconstructCtx, pred: ExprId) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let v = ctx.kernel.level_zero();
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);

    // Inside the three binders a(BVar 2), b(BVar 1), h(BVar 0):
    //   pred_a := pred a  (a = BVar 2).
    let a_outer = ctx.kernel.bvar(2);
    let pred_a = ctx.kernel.app(pred, a_outer);
    // motive := fun (z : Nat) (_ : Eq Nat a z) => Eq Nat (pred a) (pred z).
    //   Under z(BVar 1 here), _(BVar 0 here): the outer `a` is now BVar (2 + 2) = 4
    //   inside the inner-most binder; `pred a`/`pred z` are rebuilt at that depth.
    let transport_motive = {
        // body under z, _: Eq Nat (pred a) (pred z). a = BVar 4 (2 outer + 2 motive),
        // z = BVar 1.
        let a_in_body = ctx.kernel.bvar(4);
        let pred_a_body = ctx.kernel.app(pred, a_in_body);
        let z_in_body = ctx.kernel.bvar(1);
        let pred_z = ctx.kernel.app(pred, z_in_body);
        let body = mk_eq_at(ctx, nat_const, one, pred_a_body, pred_z);
        // inner binder type Eq Nat a z, under z (one motive binder): a = BVar 3, z = BVar 0.
        let a_in_dom = ctx.kernel.bvar(3);
        let z0 = ctx.kernel.bvar(0);
        let eq_a_z = mk_eq_at(ctx, nat_const, one, a_in_dom, z0);
        let inner = ctx.kernel.lam(anon, eq_a_z, body, BinderInfo::Default);
        ctx.kernel.lam(anon, nat_const, inner, BinderInfo::Default)
    };
    // refl_case : Eq Nat (pred a) (pred a) — `Eq.refl Nat (pred a)`.
    let refl = ctx.kernel.const_(ctx.prelude.eq_refl, vec![one]);
    let refl_case = {
        let e = ctx.kernel.app(refl, nat_const);
        ctx.kernel.app(e, pred_a)
    };
    // Eq.rec.{0,1} Nat a motive refl_case b h : Eq Nat (pred a) (pred b).
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![v, one]);
    let body = {
        let a_arg = ctx.kernel.bvar(2);
        let b_arg = ctx.kernel.bvar(1);
        let h_arg = ctx.kernel.bvar(0);
        let e = ctx.kernel.app(rec_eq, nat_const);
        let e = ctx.kernel.app(e, a_arg);
        let e = ctx.kernel.app(e, transport_motive);
        let e = ctx.kernel.app(e, refl_case);
        let e = ctx.kernel.app(e, b_arg);
        ctx.kernel.app(e, h_arg)
    };
    // Wrap binders h, b, a (innermost-to-outermost).
    let h_ty = {
        // h : Eq Nat a b, under a(BVar 1), b(BVar 0).
        let a1 = ctx.kernel.bvar(1);
        let b0 = ctx.kernel.bvar(0);
        mk_eq_at(ctx, nat_const, one, a1, b0)
    };
    let lam_h = ctx.kernel.lam(anon, h_ty, body, BinderInfo::Default);
    let lam_b = ctx.kernel.lam(anon, nat_const, lam_h, BinderInfo::Default);
    ctx.kernel.lam(anon, nat_const, lam_b, BinderInfo::Default)
}

/// Build `Nat.succ^k n` (k applications of `Nat.succ` to `n`); `k == 0` returns
/// `n` unchanged.
fn nat_succ_pow(ctx: &mut ReconstructCtx, n: ExprId, k: usize) -> ExprId {
    let succ_const = ctx.kernel.const_(ctx.prelude.nat_succ, vec![]);
    let mut e = n;
    for _ in 0..k {
        e = ctx.kernel.app(succ_const, e);
    }
    e
}

/// Build the proof `nat_ne_succ_pow k : Π (n : Nat), Eq Nat n (Nat.succ^k n) → False`
/// — the fact that `n ≠ Nat.succ^k n` for `k ≥ 1` — **by induction on `Nat`**, the
/// chained generalization of [`build_nat_ne_succ`] (the `k = 1` case). The proof is
/// structurally identical to `nat_ne_succ` with `Nat.succ^k` in place of
/// `Nat.succ`; the SAME discriminator and predecessor selector serve:
///
/// - **motive** `P := λ (n : Nat) => Eq Nat n (Nat.succ^k n) → False`;
/// - **base** `P Nat.zero`: `Nat.succ^k Nat.zero` is `succ`-headed (k ≥ 1) so the
///   `zero ≠ succ` discriminator `d` gives `d (succ^k zero)` ι→ `False`, and
///   transporting `True.intro : d zero` along the hypothesis lands `False`;
/// - **step** `Π (k_var) (ih), P (succ k_var)`: `Nat.succ^k (succ k_var)` is
///   `succ (Nat.succ^k k_var)`, so from `h : Eq Nat (succ k_var)
///   (succ (Nat.succ^k k_var))`, `congrArg pred h` is `def_eq`
///   `Eq Nat k_var (Nat.succ^k k_var) = P k_var`'s hypothesis, which `ih` refutes.
///
/// Panics-free for `k ≥ 1`; `k == 0` would build the (true) `n ≠ n → False`, never
/// requested by the chained acyclicity route (a cycle has `k ≥ 1` constructors).
pub(super) fn build_nat_ne_succ_pow(ctx: &mut ReconstructCtx, k: usize) -> ExprId {
    let motive = build_nat_ne_succ_pow_motive(ctx, k);
    let m_zero = build_nat_ne_succ_pow_m_zero(ctx, k);
    let m_succ = build_nat_ne_succ_pow_m_succ(ctx, k);
    // `Nat.rec.{0} P m_zero m_succ` : Π (n : Nat), P n.
    let z = ctx.kernel.level_zero();
    let rec0 = ctx.kernel.const_(ctx.prelude.nat_rec, vec![z]);
    let e = ctx.kernel.app(rec0, motive);
    let e = ctx.kernel.app(e, m_zero);
    ctx.kernel.app(e, m_succ)
}

/// The induction motive `P := λ (n : Nat) => Eq Nat n (Nat.succ^k n) → False` of
/// the `n ≠ Nat.succ^k n` proof.
fn build_nat_ne_succ_pow_motive(ctx: &mut ReconstructCtx, k: usize) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    // Under the binder `n` (BVar 0): `Eq Nat n (Nat.succ^k n) → False`.
    let n0 = ctx.kernel.bvar(0);
    let succ_k_n = nat_succ_pow(ctx, n0, k);
    let n0b = ctx.kernel.bvar(0);
    let eq_n = mk_eq_at(ctx, nat_const, one, n0b, succ_k_n);
    let arrow = ctx.kernel.pi(anon, eq_n, false_const, BinderInfo::Default);
    ctx.kernel.lam(anon, nat_const, arrow, BinderInfo::Default)
}

/// The base-case minor `m_zero : P Nat.zero` = `Eq Nat zero (succ^k zero) → False`:
/// `λ (h : Eq Nat zero (succ^k zero)), Eq.rec.{0,1} Nat zero
///  (λ (m : Nat)(_ : Eq Nat zero m) => d m) (True.intro : d zero) (succ^k zero) h`,
/// where (for `k ≥ 1`) `d zero` `def_eq` `True` and `d (succ^k zero)` `def_eq`
/// `False`, so the transport lands `False`.
pub(super) fn build_nat_ne_succ_pow_m_zero(ctx: &mut ReconstructCtx, k: usize) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let z = ctx.kernel.level_zero();
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);
    let zero_const = ctx.kernel.const_(ctx.prelude.nat_zero, vec![]);
    let succ_k_zero = nat_succ_pow(ctx, zero_const, k);
    let discr = build_nat_discriminator(ctx);

    let hyp_ty = mk_eq_at(ctx, nat_const, one, zero_const, succ_k_zero);
    // transport motive: λ (m : Nat) (_ : Eq Nat zero m) => d m.
    let t_motive = {
        let m1 = ctx.kernel.bvar(1);
        let d_m = ctx.kernel.app(discr, m1);
        let m0 = ctx.kernel.bvar(0);
        let eq_zero_m = mk_eq_at(ctx, nat_const, one, zero_const, m0);
        let inner = ctx.kernel.lam(anon, eq_zero_m, d_m, BinderInfo::Default);
        ctx.kernel.lam(anon, nat_const, inner, BinderInfo::Default)
    };
    let refl_case = ctx.kernel.const_(ctx.prelude.true_intro, vec![]);
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![z, one]);
    let body = {
        let e = ctx.kernel.app(rec_eq, nat_const);
        let e = ctx.kernel.app(e, zero_const);
        let e = ctx.kernel.app(e, t_motive);
        let e = ctx.kernel.app(e, refl_case);
        let e = ctx.kernel.app(e, succ_k_zero);
        let h = ctx.kernel.bvar(0);
        ctx.kernel.app(e, h)
    };
    ctx.kernel.lam(anon, hyp_ty, body, BinderInfo::Default)
}

/// The step minor `m_succ : Π (k_var : Nat) (ih : P k_var), P (succ k_var)`:
/// `λ (k_var : Nat) (ih : Eq Nat k_var (succ^k k_var) → False)
///  (h : Eq Nat (succ k_var) (succ^k (succ k_var))), ih (congrArg pred h)`.
/// Since `succ^k (succ k_var) = succ (succ^k k_var)`, `congrArg pred h` is `def_eq`
/// `Eq Nat k_var (succ^k k_var)` (ι: `pred (succ k_var)` ι→ `k_var`,
/// `pred (succ (succ^k k_var))` ι→ `succ^k k_var`), which `ih` turns into `False`.
pub(super) fn build_nat_ne_succ_pow_m_succ(ctx: &mut ReconstructCtx, k: usize) -> ExprId {
    let anon = ctx.kernel.anon();
    let one = ctx.one;
    let nat_const = ctx.kernel.const_(ctx.prelude.nat, vec![]);
    let succ_const = ctx.kernel.const_(ctx.prelude.nat_succ, vec![]);
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);
    let pred = build_nat_pred(ctx);
    let congr_pred = build_congr_pred_lemma(ctx, pred);

    // Build inside three binders: k_var(BVar 2), ih(BVar 1), h(BVar 0).
    // hyp type of `h`: Eq Nat (succ k_var) (succ^k (succ k_var))
    //   (under k_var, ih ⇒ k_var = BVar 1).
    let k_for_h = ctx.kernel.bvar(1);
    let succ_k_h = ctx.kernel.app(succ_const, k_for_h);
    let succ_pow_succ_k_h = nat_succ_pow(ctx, succ_k_h, k);
    let h_ty = mk_eq_at(ctx, nat_const, one, succ_k_h, succ_pow_succ_k_h);

    // congr_pred (succ k_var) (succ^k (succ k_var)) h
    //   : Eq Nat (pred (succ k_var)) (pred (succ^k (succ k_var)))
    //   def_eq Eq Nat k_var (succ^k k_var).
    // Under k_var(BVar 2), ih(BVar 1), h(BVar 0): k_var = BVar 2, h = BVar 0.
    let k_under_h = ctx.kernel.bvar(2);
    let succ_k = ctx.kernel.app(succ_const, k_under_h);
    let succ_pow_succ_k = nat_succ_pow(ctx, succ_k, k);
    let h_var = ctx.kernel.bvar(0);
    let congr = {
        let e = ctx.kernel.app(congr_pred, succ_k);
        let e = ctx.kernel.app(e, succ_pow_succ_k);
        ctx.kernel.app(e, h_var)
    };
    // ih (congr) : False.
    let ih_var = ctx.kernel.bvar(1);
    let applied = ctx.kernel.app(ih_var, congr);

    // Bind h, then ih, then k_var.
    let lam_h = ctx.kernel.lam(anon, h_ty, applied, BinderInfo::Default);
    // ih type: Eq Nat k_var (succ^k k_var) → False  (under k_var ⇒ k_var = BVar 0).
    let k_for_ih = ctx.kernel.bvar(0);
    let succ_pow_k_ih = nat_succ_pow(ctx, k_for_ih, k);
    let k_for_ih2 = ctx.kernel.bvar(0);
    let eq_k = mk_eq_at(ctx, nat_const, one, k_for_ih2, succ_pow_k_ih);
    let ih_ty = ctx.kernel.pi(anon, eq_k, false_const, BinderInfo::Default);
    let lam_ih = ctx.kernel.lam(anon, ih_ty, lam_h, BinderInfo::Default);
    ctx.kernel.lam(anon, nat_const, lam_ih, BinderInfo::Default)
}

/// Assemble the kernel `False` term for a [`TesterContradiction`] and render the
/// Lean module. Split out so the entry point stays a thin Option wrapper.
fn build_tester_refutation_module(
    arena: &TermArena,
    c: &TesterContradiction,
) -> Result<String, ReconstructError> {
    let mut ctx = ReconstructCtx::new();

    // 1. Declare the kernel family `D` carrying EVERY constructor of the datatype
    //    (in declaration order), so the recursor can distinguish them.
    let dt_name = arena.datatype_name(c.datatype).to_owned();
    let ctor_ids = arena.datatype_constructors(c.datatype).to_vec();
    // Constructor LEAF names `c0, c1, …` (kept positional + Lean-identifier-safe;
    // `datatype_family` namespaces them under the family inductive so Lean's
    // regenerated constructor/recursor names match).
    let ctor_decls: Vec<(String, usize)> = ctor_ids
        .iter()
        .enumerate()
        .map(|(j, &cid)| (format!("c{j}"), arena.constructor_fields(cid).len()))
        .collect();
    let family = ctx.datatype_family(&dt_name, &ctor_decls)?;

    // 2. Build the constructor application `cⱼ(x…)`: model each field as a fresh
    //    opaque carrier atom `α` (the fold is field-independent, so the exact
    //    field value is irrelevant — only the constructor head drives ι).
    let builder_pos = ctor_ids
        .iter()
        .position(|&cid| cid == c.builder)
        .ok_or_else(|| ReconstructError::KernelRejected {
            rule: "datatype_tester".to_owned(),
            detail: "builder constructor not in datatype".to_owned(),
        })?;
    let tested_pos = ctor_ids
        .iter()
        .position(|&cid| cid == c.tested)
        .ok_or_else(|| ReconstructError::KernelRejected {
            rule: "datatype_tester".to_owned(),
            detail: "tested constructor not in datatype".to_owned(),
        })?;
    let mut con = ctx.kernel.const_(family.ctors[builder_pos], vec![]);
    for (i, _field) in c.fields.iter().enumerate() {
        let atom_name = ctx.fresh_name(&format!("fld_{i}"));
        let alpha = ctx.alpha;
        ctx.kernel
            .add_declaration(Declaration::Axiom {
                name: atom_name,
                uparams: vec![],
                ty: alpha,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "datatype_tester".to_owned(),
                detail: format!("field carrier atom did not admit: {e:?}"),
            })?;
        let a = ctx.kernel.const_(atom_name, vec![]);
        con = ctx.kernel.app(con, a);
    }

    // 3. The is-tester `is_C : D → Bool` and the fold `is_C(cⱼ x…)`.
    let alpha = ctx.alpha;
    let tester = ctx.kernel.datatype_tester(
        &family,
        ctx.prelude.bool_,
        ctx.prelude.bool_true,
        ctx.prelude.bool_false,
        alpha,
        tested_pos,
    );
    let folded = ctx.kernel.app(tester, con);
    let bool_true = ctx.kernel.const_(ctx.prelude.bool_true, vec![]);

    // The is-tester predicate atom "is_C(arg) holds" := Eq Bool (is_C arg) true.
    let pred = ctx.mk_eq_bool(folded, bool_true);

    let false_term = if c.asserted_positive {
        // FALSE fold: assertion `is_C(K x)` ⇒ axiom `h : Eq Bool (is_C(K x)) true`.
        // But `is_C(K x)` ι-reduces to `Bool.false`, so `h` proves `false = true`
        // (def_eq). The `Bool.true ≠ Bool.false` discriminator yields `False`.
        let h = fresh_axiom(&mut ctx, pred, "assume")?;
        build_bool_true_ne_false(&mut ctx, folded, h)
    } else {
        // TRUE fold: assertion `¬is_C(C x)` ⇒ axiom `h : ¬(Eq Bool (is_C(C x)) true)`.
        // `is_C(C x)` ι-reduces to `Bool.true`, so `Eq.refl Bool true` proves the
        // predicate; applying `h` to it gives `False`.
        let not_pred = ctx.mk_not(pred);
        let h = fresh_axiom(&mut ctx, not_pred, "assume")?;
        let refl = ctx.mk_eq_refl_bool(bool_true);
        ctx.kernel.app(h, refl)
    };

    require_infers_false(&mut ctx, false_term)?;
    // Render the datatype family AND the computational `Bool` as **real Lean
    // `inductive`s** so an external Lean regenerates their recursors *with* ι — the
    // is-tester fold `Eq.refl Bool (true/false)` only type-checks if Lean can
    // compute `is_C (cⱼ x…)` by ι. Everything else (the logical prelude, the input
    // hypothesis axiom) renders as before.
    let bool_ind = ctx.prelude.bool_;
    let false_const = {
        let n = ctx.prelude().false_;
        ctx.kernel_mut().const_(n, vec![])
    };
    Ok(ctx.kernel().render_lean_module_with_inductives(
        LEAN_MODULE_THEOREM,
        false_const,
        false_term,
        &[family.ind, bool_ind],
    ))
}

/// Given `lhs` (a `Bool` term that ι-reduces to `Bool.false`) and a proof
/// `h : Eq Bool lhs Bool.true`, build a proof of `False` using the
/// `Bool.true ≠ Bool.false` discriminator — **axiom-free**, by `Bool.rec` ι.
///
/// The discriminator motive is `D := λ (b : Bool), Bool.rec (λ _ => Prop) False
/// True b`, so `D Bool.false` ι-reduces to `True` and `D Bool.true` to `False`.
/// Transporting `True.intro : D lhs` (`lhs` `def_eq` `Bool.false`, so `D lhs`
/// `def_eq` `True`) along `h` to `D Bool.true` (`def_eq` `False`) is the refutation.
fn build_bool_true_ne_false(ctx: &mut ReconstructCtx, lhs: ExprId, h: ExprId) -> ExprId {
    let anon = ctx.kernel.anon();
    let bool_const = ctx.kernel.const_(ctx.prelude.bool_, vec![]);
    let prop = ctx.kernel.sort_zero();
    let true_const = ctx.kernel.const_(ctx.prelude.true_, vec![]);
    let false_const = ctx.kernel.const_(ctx.prelude.false_, vec![]);

    // discr := λ (b : Bool), Bool.rec.{1} (motive := λ _ => Prop) False True b.
    //   minor for Bool.true  = False ;  minor for Bool.false = True.
    // The motive `λ _ => Prop` maps `Bool → Sort 1` (since `Prop : Sort 1`), so the
    // (large) elimination universe is `1`.
    let z = ctx.kernel.level_zero();
    let one = ctx.kernel.level_succ(z);
    let rec = ctx.kernel.const_(ctx.prelude.bool_rec, vec![one]);
    let motive = ctx.kernel.lam(anon, bool_const, prop, BinderInfo::Default);
    let discr = {
        let e = ctx.kernel.app(rec, motive);
        let e = ctx.kernel.app(e, false_const); // minor for Bool.true
        let e = ctx.kernel.app(e, true_const); // minor for Bool.false
        let b = ctx.kernel.bvar(0);
        let body = ctx.kernel.app(e, b);
        ctx.kernel.lam(anon, bool_const, body, BinderInfo::Default)
    };

    // The Eq.rec transport motive `fun (x : Bool) (_ : Eq Bool lhs x) => discr x`.
    // `discr lhs` def_eq `True`, so the refl case is `True.intro : discr lhs`.
    let bool_true = ctx.kernel.const_(ctx.prelude.bool_true, vec![]);
    let transport_motive = {
        // Under binders (x : Bool) (_ : Eq Bool lhs x): apply `discr` to `x`(=bvar 1).
        let x = ctx.kernel.bvar(1);
        let discr_x = ctx.kernel.app(discr, x);
        // inner Pi binder type: Eq Bool lhs x. `lhs` is closed (no bound vars here),
        // `x` is bvar 0 at this binder depth.
        let eq = ctx.kernel.const_(ctx.prelude.eq, vec![ctx.one]);
        let x0 = ctx.kernel.bvar(0);
        let eq_lhs_x = {
            let e = ctx.kernel.app(eq, bool_const);
            let e = ctx.kernel.app(e, lhs);
            ctx.kernel.app(e, x0)
        };
        let inner = ctx.kernel.lam(anon, eq_lhs_x, discr_x, BinderInfo::Default);
        ctx.kernel.lam(anon, bool_const, inner, BinderInfo::Default)
    };
    // refl_case : discr lhs  (def_eq True) — `True.intro`.
    let refl_case = ctx.kernel.const_(ctx.prelude.true_intro, vec![]);
    // Eq.rec.{0,1} Bool lhs transport_motive refl_case Bool.true h : discr Bool.true
    //   = False (def_eq).
    let rec_eq = ctx.kernel.const_(ctx.prelude.eq_rec, vec![z, ctx.one]);
    let e = ctx.kernel.app(rec_eq, bool_const);
    let e = ctx.kernel.app(e, lhs);
    let e = ctx.kernel.app(e, transport_motive);
    let e = ctx.kernel.app(e, refl_case);
    let e = ctx.kernel.app(e, bool_true);
    ctx.kernel.app(e, h)
}
