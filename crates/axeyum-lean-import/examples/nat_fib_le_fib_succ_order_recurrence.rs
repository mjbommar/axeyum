//! `bounded-iterate-recurrence-v3`'s own arity/head gate (`recurrence_proof`'s
//! `target_arguments.len() != 3` check, reproduced independently in
//! `probe_bounded_iterate_recurrence_order_boundary.rs`) rejects
//! `F:ml430-nat-fib-le-fib-succ-d1ef4a3d` (`fib n <= fib (n+1)`) before any
//! `Eq`-only combinator runs: the goal body is `LE.le`-headed at spine arity
//! 4, not `Eq`-headed at arity 3. Doc 262's sixth amendment names the missing
//! capability precisely: "an order-relation combinator vocabulary --
//! order-congruence and monotonicity over the transition function ... Not a
//! parameterization of existing code; new vocabulary."
//!
//! **What this file establishes, measured against the real frozen export
//! (`sha256:d1af65c0c4…`):**
//!
//! 1. The order vocabulary itself IS the smallest true version and IS
//!    buildable here, with no new capability beyond what the isolated
//!    per-goal kernel already carries (`Nat`/`Nat.le`/`Nat.rec`/
//!    `Nat.le.rec`, all present):
//!      - `zeroLe : forall a, 0 <= a`, via `Nat.rec` (base `Nat.le.refl 0`,
//!        step `Nat.le.step` applied to the IH -- generic in `a`).
//!      - `succLeSucc : forall n m, n <= m -> succ n <= succ m`, via
//!        `Nat.le.rec` (induction on the ORDER PROOF itself -- `Nat.le`'s
//!        own recursor).
//!      - `leAddLeft : forall a b, b <= a + b`, composed from the two above
//!        by induction on `b` (matching `Nat.add`'s own right-recursion:
//!        `a+0` is definitionally `a`, `a+succ b'` is definitionally
//!        `succ (a+b')` -- both verified by direct `def_eq` probe against
//!        this exact kernel, not assumed).
//!
//!    All three are registered here as real `Theorem`s and independently
//!    re-type-checked by `Kernel::add_declaration`, axiom-free,
//!    theorem-dependency-free.
//!
//! 2. Composing that vocabulary with `Nat.fib`'s own recursive structure
//!    needs one more ingredient: the fib_add_two-shaped bridge `fib (succ
//!    (succ n)) = fib n + fib (succ n)` (or even just its one-step
//!    building block, `iterate (succ n) x = transition (iterate n x)`),
//!    exactly the identity `bounded-iterate-recurrence-v3` proves for the
//!    SIBLING fact `F:ml430-nat-fib-add-two-b86e0c82`. That identity is
//!    NOT definitionally true here (`Kernel::def_eq` returns `false` for
//!    it against symbolic `n`, measured directly below and in a standalone
//!    probe before this file was written), so closing it needs a genuine
//!    `Eq`-typed inductive proof, exactly as
//!    `nat_fib_iterate_recurrence.rs::iterator_successor_helper` builds one
//!    via `Nat.rec` + `Eq.rec`.
//!
//! 3. **This fact's own minimal-closure export does not declare `Eq` at
//!    all.** Measured two ways: zero occurrences of the string `"Eq"` in
//!    the raw ndjson, and zero matches for `Eq` among the isolated
//!    kernel's 52 declarations (`{Constructor:10, Definition:31,
//!    Inductive:9, Recursor:9}` per doc 262's fifth amendment, plus a
//!    handful more this goal's own closure adds -- still zero `Theorem`,
//!    zero `Eq`). The goal `fib n <= fib (n+1)` is purely `LE.le`-headed,
//!    so Lean's minimal dependency closure for STATING it never pulls in
//!    propositional equality -- exactly the phenomenon doc 262's
//!    `002e7956d` era already flagged for order goals in general ("many
//!    pure-order goals' minimal import closure never declares Eq --
//!    confirmed on 6 of the 12 real targets"), now confirmed for THIS
//!    specific fact.
//!
//! **So the precise blocker is not the order vocabulary** (built, checked,
//! present below) **and not a missing combinator shape** (the goal after
//! case-split reduces to a plain `le_add_left`-shaped step, exactly as
//! predicted) -- **it is that the one non-order ingredient the proof needs
//! (`Eq`, to bridge `fib` across a successor step) is absent from this
//! fact's own isolated kernel**, and no order-only combinator can
//! substitute: `Nat.le`'s recursor can only produce further `Nat.le`-typed
//! conclusions from `Nat.le`-typed premises, never bridge a
//! non-definitional equality. `run()` builds and verifies the vocabulary,
//! then checks for `Eq` and reports this precisely instead of attempting a
//! proof it cannot complete.
//!
//! This producer is deliberately NOT wired into `bounded_induction.rs`'s
//! shared search/budget (`002e7956d` reverted a broad order-side residual
//! mechanism there for exhausting `MAX_RESIDUAL_LEMMAS` for zero admits --
//! this file never touches that budget or that module, single-target by
//! construction exactly like `nat_fib_iterate_recurrence.rs`). Nothing here
//! is registered in `operations.json`: the goal is not closed.

use std::env;
use std::fs;
use std::io::Cursor;

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, canonical_expression_sha256, import_ndjson,
};
use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, NameId};
use sha2::{Digest, Sha256};

const DEFAULT_STREAM: &str = "/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-premise-composition-probe-v1/nat-fib-le-fib-succ.ndjson";
const STREAM_SHA256: &str = "d1af65c0c4e0273c90f9deb0299219a78e5ccbaedec7eda99536a7397c09cc10";
const TARGET: &str = "Axeyum.Autogenesis.Statement.natFibLeFibSucc";
const POLICY_VERSION: &str = "nat-fib-le-fib-succ-order-recurrence-v1";

#[derive(Debug)]
struct FibShape {
    nat: ExprId,
    product: ExprId,
    transition: ExprId,
    initial: ExprId,
    iterate: ExprId,
    successor: ExprId,
    fst: ExprId,
    snd: ExprId,
}

/// Order primitives discovered from the isolated kernel's own `Nat.le`
/// declarations -- discovered by NAME here (this is a single-target
/// producer, unlike `bounded_induction.rs`'s structural `detect_le_shape`),
/// but every subsequent proof step is checked by the same independent
/// `Kernel::add_declaration`/`infer` route regardless of how the pieces were
/// found.
#[derive(Debug)]
struct OrderPrimitives {
    le: ExprId,
    le_refl: ExprId,
    le_step: ExprId,
    le_rec_name: NameId,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-fib-le-fib-succ-order-recurrence: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let stream_path = env::args()
        .nth(1)
        .unwrap_or_else(|| DEFAULT_STREAM.to_owned());
    let stream = fs::read(&stream_path).map_err(|error| error.to_string())?;
    if hex_sha256(&stream) != STREAM_SHA256 {
        return Err("nat-fib-le-fib-succ stream identity changed".to_owned());
    }
    let completed = import_ndjson(Cursor::new(&stream), ImportLimits::default())
        .map_err(|error| format!("source import failed: {error:?}"))?;
    let (mut kernel, report) = completed.into_parts();
    if report.lean_version != "4.30.0"
        || report.lean_githash != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        || !report.axioms.is_empty()
    {
        return Err("source authority changed".to_owned());
    }

    let shape = inspect_fib_shape(&mut kernel)?;
    let order = inspect_order_primitives(&mut kernel)?;

    let target = exact_name(&kernel, TARGET)?;
    let goal = match kernel.environment().get(target) {
        Some(Declaration::Definition { uparams, value, .. }) if uparams.is_empty() => *value,
        _ => return Err("target is not a monomorphic statement definition".to_owned()),
    };

    // The narrow order vocabulary itself: register each combinator as a real,
    // independently kernel-checked `Theorem` in THIS kernel, over nothing but
    // `Nat`/`Nat.le`/`Nat.rec`/`Nat.le.rec` -- proving the vocabulary is
    // buildable here, whatever happens next.
    let zero_le_closed = build_zero_le(&mut kernel, &shape, &order)?;
    register_lemma(
        &mut kernel,
        "zeroLe",
        zero_le_closed,
        "forall a, 0 <= a (via Nat.rec)",
    )?;
    let succ_le_succ_closed = build_succ_le_succ(&mut kernel, &shape, &order)?;
    register_lemma(
        &mut kernel,
        "succLeSucc",
        succ_le_succ_closed,
        "forall n m, n <= m -> succ n <= succ m (via Nat.le.rec)",
    )?;
    let le_add_left_closed = {
        let add_head = extract_add_head(&mut kernel, goal)?;
        build_le_add_left(
            &mut kernel,
            &shape,
            add_head,
            zero_le_closed,
            succ_le_succ_closed,
        )?
    };
    register_lemma(
        &mut kernel,
        "leAddLeft",
        le_add_left_closed,
        "forall a b, b <= a + b (via Nat.rec, composed from zeroLe/succLeSucc)",
    )?;
    println!(
        "order vocabulary built and independently kernel-checked: zeroLe, succLeSucc, leAddLeft (all axiom-free, all Theorem-dependency-free)"
    );

    // The bridge this vocabulary needs to reach `fib_le_fib_succ`: a
    // `Nat.iterate`-unfold recurrence identity, exactly like the one
    // `bounded-iterate-recurrence-v3` already proved for the SIBLING fact
    // `F:ml430-nat-fib-add-two-b86e0c82`. That mechanism is propositional
    // (`iterate (succ n) x` is NOT definitionally `transition (iterate n
    // x)` -- verified directly against this exact kernel below) and
    // requires `Eq`/`Eq.rec`/`Eq.refl`. Check whether this fact's own
    // minimal-closure export declares them before attempting to build it.
    let has_eq = kernel
        .environment()
        .iter()
        .any(|(&name, _)| kernel.display_name(name).to_string() == "Eq");
    if !has_eq {
        let bridge_defeq = {
            let n_id = u64::MAX - 90_001;
            let n = kernel.fvar(n_id);
            let x_id = u64::MAX - 90_002;
            let x = kernel.fvar(x_id);
            let succ_n = kernel.app(shape.successor, n);
            let lhs = iterate(&mut kernel, &shape, succ_n, x);
            let iter_n = iterate(&mut kernel, &shape, n, x);
            let rhs = kernel.app(shape.transition, iter_n);
            kernel.def_eq(lhs, rhs)
        };
        println!("Eq declared in this kernel's environment: false");
        println!(
            "def_eq(iterate(succ n, x), transition(iterate(n, x))) for symbolic n: {bridge_defeq}"
        );
        println!(
            "BLOCKED: fib_le_fib_succ needs the Nat.iterate-unfold recurrence bridge \
             (propositional, requires Eq/Eq.rec/Eq.refl to prove) to relate fib at n \
             and n+1; the isolated per-goal kernel for F:ml430-nat-fib-le-fib-succ-d1ef4a3d \
             does not declare Eq at all (0 occurrences in the raw export -- the goal is \
             purely LE.le-headed, so Lean's minimal dependency closure never pulls in \
             propositional equality). No order-only combinator can substitute: the bridge \
             fact is not definitionally true (measured above), so it needs a genuine \
             inductive PROOF, and Nat.le's own recursor can only produce further \
             Nat.le-typed conclusions from Nat.le-typed premises, never bridge an equality."
        );
        return Ok(());
    }

    let theorem = nested_name(&mut kernel, &["Axeyum", "Autogenesis", "NatFibLeFibSucc"]);
    let proof = build_order_proof(&mut kernel, &shape, &order, goal)?;
    kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .map_err(|error| format!("order-recurrence proof rejected: {error:?}"))?;

    let axioms = rendered_names(&kernel, &kernel.axiom_footprint(theorem));
    let theorem_dependencies = rendered_names(&kernel, &kernel.theorem_dependencies(theorem));
    let closure = kernel.declaration_dependency_closure(theorem);
    if !axioms.is_empty() || !theorem_dependencies.is_empty() || closure.contains(&target) {
        return Err("accepted theorem dependency audit failed".to_owned());
    }
    let theorem_content_sha256 = canonical_declaration_sha256(&kernel, theorem)?;
    let goal_sha256 = canonical_expression_sha256(&kernel, goal)?;
    let theorem_type = kernel
        .environment()
        .get(theorem)
        .ok_or("accepted theorem disappeared")?
        .ty();
    if theorem_type != goal {
        return Err("accepted theorem type changed".to_owned());
    }

    println!("policy_version={POLICY_VERSION}");
    println!("stream_sha256={}", hex_sha256(&stream));
    println!("theorem={}", kernel.display_name(theorem));
    println!("axioms={axioms:?}");
    println!("theorem_dependencies(non-prelude)={theorem_dependencies:?}");
    println!("theorem_content_sha256={theorem_content_sha256}");
    println!("goal_sha256={goal_sha256}");
    println!("AUTOGENESIS_NAT_FIB_LE_FIB_SUCC_OK");
    Ok(())
}

/// Register a closed, already-built term as a real `Theorem` in `kernel`
/// (independently re-type-checked by `add_declaration`), then assert its
/// axiom footprint and theorem-dependency closure are both empty -- the
/// same audit `run` performs on the final goal.
fn register_lemma(
    kernel: &mut Kernel,
    short_name: &str,
    value: ExprId,
    description: &str,
) -> Result<(), String> {
    let ty = kernel
        .infer(value)
        .map_err(|error| format!("{short_name} failed to infer: {error:?}"))?;
    let name = nested_name(kernel, &["Axeyum", "Autogenesis", "NatOrder", short_name]);
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|error| format!("{short_name} rejected: {error:?}"))?;
    let axioms = rendered_names(kernel, &kernel.axiom_footprint(name));
    let theorem_dependencies = rendered_names(kernel, &kernel.theorem_dependencies(name));
    if !axioms.is_empty() || !theorem_dependencies.is_empty() {
        return Err(format!(
            "{short_name} carries a non-empty trusted surface: axioms={axioms:?} theorem_dependencies={theorem_dependencies:?}"
        ));
    }
    println!("  {short_name}: {description} -- axiom-free, checked");
    Ok(())
}

/// Extract the partially-applied `HAdd.hAdd <types> <inst>` function from
/// the goal's own `fib (n + 1)` subterm, exactly as `build_order_proof`
/// does -- factored out so `run` can build `leAddLeft` before deciding
/// whether the `Eq`-dependent recurrence bridge is available.
fn extract_add_head(kernel: &mut Kernel, goal: ExprId) -> Result<ExprId, String> {
    let ExprNode::Pi(_, _, body, _) = kernel.expr_node(goal).clone() else {
        return Err("goal has no pointwise binder".to_owned());
    };
    let probe_id = u64::MAX - 91_000;
    let probe_n = kernel.fvar(probe_id);
    let body_n = kernel.instantiate(body, &[probe_n]);
    let (_, le_args) = app_spine(kernel, body_n);
    if le_args.len() != 4 {
        return Err("goal body is not a 4-arg LE.le application".to_owned());
    }
    let (_, rhs_fib_args) = app_spine(kernel, le_args[3]);
    if rhs_fib_args.len() != 1 {
        return Err("goal RHS is not a unary fib application".to_owned());
    }
    let (add_bare_head, add_args) = app_spine(kernel, rhs_fib_args[0]);
    if add_args.len() != 6 {
        return Err("goal RHS argument spine changed (n+1)".to_owned());
    }
    Ok(apply(kernel, add_bare_head, &add_args[0..4]))
}

// ---------------------------------------------------------------------------
// Order proof assembly
// ---------------------------------------------------------------------------

fn build_order_proof(
    kernel: &mut Kernel,
    shape: &FibShape,
    order: &OrderPrimitives,
    goal: ExprId,
) -> Result<ExprId, String> {
    let ExprNode::Pi(name, domain, body, info) = kernel.expr_node(goal).clone() else {
        return Err("goal has no pointwise binder".to_owned());
    };
    let probe_id = u64::MAX - 71_000;
    let probe_n = kernel.fvar(probe_id);
    let body_n = kernel.instantiate(body, &[probe_n]);
    let (le_bare_head, le_args) = app_spine(kernel, body_n);
    if le_args.len() != 4 {
        return Err("goal body is not a 4-arg LE.le application".to_owned());
    }
    let le_partial = apply(kernel, le_bare_head, &le_args[0..2]);
    let (fib_bare_head, fib_args) = app_spine(kernel, le_args[2]);
    if fib_args.len() != 1 {
        return Err("goal LHS is not a unary fib application".to_owned());
    }
    let fib_const = fib_bare_head;
    let (_, rhs_fib_args) = app_spine(kernel, le_args[3]);
    if rhs_fib_args.len() != 1 {
        return Err("goal RHS is not a unary fib application".to_owned());
    }
    let (add_bare_head, add_args) = app_spine(kernel, rhs_fib_args[0]);
    if add_args.len() != 6 {
        return Err("goal RHS argument spine changed (n+1)".to_owned());
    }
    let add_head = apply(kernel, add_bare_head, &add_args[0..4]);
    let one = add_args[5];

    let helper_id = u64::MAX - 72_000;
    let (helper, _helper_goal) = iterator_successor_helper(kernel, shape, helper_id)?;

    let zero = order_zero(kernel, order)?;

    let zero_le_closed = build_zero_le(kernel, shape, order)?;
    let succ_le_succ_closed = build_succ_le_succ(kernel, shape, order)?;
    let le_add_left_closed =
        build_le_add_left(kernel, shape, add_head, zero_le_closed, succ_le_succ_closed)?;

    // motive := fun n => le_partial (fib n) (fib (n+1))
    let mv_id = u64::MAX - 73_000;
    let mv = kernel.fvar(mv_id);
    let motive_body = motive_at(kernel, le_partial, fib_const, add_head, one, mv)?;
    let motive_body = kernel.abstract_fvars(motive_body, &[mv_id]);
    let anon = kernel.anon();
    let motive = kernel.lam(anon, shape.nat, motive_body, BinderInfo::Default);

    // base: zero_le applied at (fib (0+1))
    let zero_plus_one = apply(kernel, add_head, &[zero, one]);
    let fib_zero_plus_one = kernel.app(fib_const, zero_plus_one);
    let base = kernel.app(zero_le_closed, fib_zero_plus_one);

    // step: fun k (_ih : motive k) => <recurrence + le_add_left + transport>
    let k_id = u64::MAX - 74_000;
    let ih_id = u64::MAX - 74_001;
    let k = kernel.fvar(k_id);
    let (recur_target_lhs, recur_target_rhs, recur_proof) =
        fib_add_two_step(kernel, shape, helper, add_head, fib_const, k)?;

    let succ_k = kernel.app(shape.successor, k);
    let fib_k = kernel.app(fib_const, k);
    let fib_succ_k = kernel.app(fib_const, succ_k);
    let le_before = apply(kernel, le_add_left_closed, &[fib_k, fib_succ_k]);

    let recur_symm = equality_symm(
        kernel,
        shape.nat,
        recur_target_lhs,
        recur_target_rhs,
        recur_proof,
    )?;
    let z_id = u64::MAX - 74_002;
    let z = kernel.fvar(z_id);
    let pred_body = apply(kernel, order.le, &[fib_succ_k, z]);
    let pred_body = kernel.abstract_fvars(pred_body, &[z_id]);
    let anon2 = kernel.anon();
    let predicate = kernel.lam(anon2, shape.nat, pred_body, BinderInfo::Default);
    let step_core = transport_equality(
        kernel,
        shape.nat,
        recur_target_rhs,
        recur_target_lhs,
        recur_symm,
        predicate,
        le_before,
    )?;

    let ih_ty = motive_at(kernel, le_partial, fib_const, add_head, one, k)?;
    let step_body = kernel.abstract_fvars(step_core, &[ih_id]);
    let anon3 = kernel.anon();
    let step_inner = kernel.lam(anon3, ih_ty, step_body, BinderInfo::Default);
    let step_inner = kernel.abstract_fvars(step_inner, &[k_id]);
    let anon4 = kernel.anon();
    let step = kernel.lam(anon4, shape.nat, step_inner, BinderInfo::Default);

    let zero_level = kernel.level_zero();
    let rec_name = exact_name(kernel, "Nat.rec")?;
    let rec_c = kernel.const_(rec_name, vec![zero_level]);
    let full = apply(kernel, rec_c, &[motive, base, step, probe_n]);
    let full = kernel.abstract_fvars(full, &[probe_id]);
    Ok(kernel.lam(name, domain, full, info))
}

/// `le_partial (fib n) (fib (n+add_one))`, the goal's own body shape
/// instantiated at `n`.
#[allow(clippy::unnecessary_wraps)]
fn motive_at(
    kernel: &mut Kernel,
    le_partial: ExprId,
    fib_const: ExprId,
    add_head: ExprId,
    one: ExprId,
    n: ExprId,
) -> Result<ExprId, String> {
    let fib_n = kernel.app(fib_const, n);
    let n_plus_one = apply(kernel, add_head, &[n, one]);
    let fib_n_plus_one = kernel.app(fib_const, n_plus_one);
    Ok(apply(kernel, le_partial, &[fib_n, fib_n_plus_one]))
}

/// `zero_le := fun a => @Nat.rec (fun _ => Nat.le 0 a) (Nat.le.refl 0)
///   (fun a' ih => Nat.le.step 0 a' ih) a` -- closed, generic over `a`.
#[allow(clippy::similar_names)]
fn build_zero_le(
    kernel: &mut Kernel,
    shape: &FibShape,
    order: &OrderPrimitives,
) -> Result<ExprId, String> {
    let zero = order_zero(kernel, order)?;
    let a_id = u64::MAX - 75_000;
    let mv_id = u64::MAX - 75_001;
    let ap_id = u64::MAX - 75_002;
    let ih_id = u64::MAX - 75_003;
    let a = kernel.fvar(a_id);
    let mv = kernel.fvar(mv_id);

    let motive_body = apply(kernel, order.le, &[zero, mv]);
    let motive_body = kernel.abstract_fvars(motive_body, &[mv_id]);
    let anon1 = kernel.anon();
    let motive = kernel.lam(anon1, shape.nat, motive_body, BinderInfo::Default);

    let base = kernel.app(order.le_refl, zero);

    let ap = kernel.fvar(ap_id);
    let ih = kernel.fvar(ih_id);
    let step_body = apply(kernel, order.le_step, &[zero, ap, ih]);
    let step_body = kernel.abstract_fvars(step_body, &[ih_id]);
    let ih_ty = apply(kernel, order.le, &[zero, ap]);
    let anon2 = kernel.anon();
    let step_inner = kernel.lam(anon2, ih_ty, step_body, BinderInfo::Default);
    let step_inner = kernel.abstract_fvars(step_inner, &[ap_id]);
    let anon3 = kernel.anon();
    let step = kernel.lam(anon3, shape.nat, step_inner, BinderInfo::Default);

    let zero_level = kernel.level_zero();
    let rec_name = exact_name(kernel, "Nat.rec")?;
    let rec_c = kernel.const_(rec_name, vec![zero_level]);
    let applied = apply(kernel, rec_c, &[motive, base, step, a]);
    let closed = kernel.abstract_fvars(applied, &[a_id]);
    let anon4 = kernel.anon();
    Ok(kernel.lam(anon4, shape.nat, closed, BinderInfo::Default))
}

/// `succ_le_succ := fun n m (h : Nat.le n m) => @Nat.le.rec n
///   (fun m _ => Nat.le (succ n) (succ m)) (Nat.le.refl (succ n))
///   (fun m' h' ih => Nat.le.step (succ n) (succ m') ih) m h` -- closed,
/// generic over `n`, `m`, `h`.
#[allow(clippy::unnecessary_wraps, clippy::similar_names)]
fn build_succ_le_succ(
    kernel: &mut Kernel,
    shape: &FibShape,
    order: &OrderPrimitives,
) -> Result<ExprId, String> {
    let n_id = u64::MAX - 76_000;
    let m_id = u64::MAX - 76_001;
    let h_id = u64::MAX - 76_002;
    let mv_id = u64::MAX - 76_003;
    let mvh_id = u64::MAX - 76_004;
    let pred_id = u64::MAX - 76_005;
    let pred_hyp_id = u64::MAX - 76_006;
    let ih_id = u64::MAX - 76_007;

    let n = kernel.fvar(n_id);
    let m = kernel.fvar(m_id);
    let h = kernel.fvar(h_id);
    let succ_n = kernel.app(shape.successor, n);

    let mv = kernel.fvar(mv_id);
    let motive_body = {
        let succ_mv = kernel.app(shape.successor, mv);
        apply(kernel, order.le, &[succ_n, succ_mv])
    };
    let motive_body = kernel.abstract_fvars(motive_body, &[mvh_id]);
    let le_n_mv = apply(kernel, order.le, &[n, mv]);
    let anon1 = kernel.anon();
    let motive_inner = kernel.lam(anon1, le_n_mv, motive_body, BinderInfo::Default);
    let motive_inner = kernel.abstract_fvars(motive_inner, &[mv_id]);
    let anon2 = kernel.anon();
    let motive = kernel.lam(anon2, shape.nat, motive_inner, BinderInfo::Default);

    let base = kernel.app(order.le_refl, succ_n);

    let pred = kernel.fvar(pred_id);
    let _pred_hyp = kernel.fvar(pred_hyp_id);
    let ih = kernel.fvar(ih_id);
    let succ_pred = kernel.app(shape.successor, pred);
    let step_body = apply(kernel, order.le_step, &[succ_n, succ_pred, ih]);
    let step_body = kernel.abstract_fvars(step_body, &[ih_id]);
    let ih_ty = apply(kernel, order.le, &[succ_n, succ_pred]);
    let anon3 = kernel.anon();
    let step_l3 = kernel.lam(anon3, ih_ty, step_body, BinderInfo::Default);
    let step_l3 = kernel.abstract_fvars(step_l3, &[pred_hyp_id]);
    let pred_hyp_ty = apply(kernel, order.le, &[n, pred]);
    let anon4 = kernel.anon();
    let step_l2 = kernel.lam(anon4, pred_hyp_ty, step_l3, BinderInfo::Default);
    let step_l2 = kernel.abstract_fvars(step_l2, &[pred_id]);
    let anon5 = kernel.anon();
    let step = kernel.lam(anon5, shape.nat, step_l2, BinderInfo::Default);

    let le_rec_c = kernel.const_(order.le_rec_name, vec![]);
    let applied = apply(kernel, le_rec_c, &[n, motive, base, step, m, h]);
    let h_full_ty = apply(kernel, order.le, &[n, m]);
    let closed = kernel.abstract_fvars(applied, &[h_id]);
    let anon6 = kernel.anon();
    let closed = kernel.lam(anon6, h_full_ty, closed, BinderInfo::Default);
    let closed = kernel.abstract_fvars(closed, &[m_id]);
    let anon7 = kernel.anon();
    let closed = kernel.lam(anon7, shape.nat, closed, BinderInfo::Default);
    let closed = kernel.abstract_fvars(closed, &[n_id]);
    let anon8 = kernel.anon();
    Ok(kernel.lam(anon8, shape.nat, closed, BinderInfo::Default))
}

/// `le_add_left := fun a b => @Nat.rec (fun b => Nat.le b (a+b)) (zero_le a)
///   (fun b' ih => succ_le_succ b' (a+b') ih) b` -- closed, generic over
/// `a`, `b`.
fn build_le_add_left(
    kernel: &mut Kernel,
    shape: &FibShape,
    add_head: ExprId,
    zero_le_closed: ExprId,
    succ_le_succ_closed: ExprId,
) -> Result<ExprId, String> {
    let a_id = u64::MAX - 77_000;
    let b_id = u64::MAX - 77_001;
    let mv_id = u64::MAX - 77_002;
    let bpred_id = u64::MAX - 77_003;
    let ih_id = u64::MAX - 77_004;

    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);

    let mv = kernel.fvar(mv_id);
    let order = order_le_only(kernel)?;
    let motive_body = {
        let a_plus_mv = apply(kernel, add_head, &[a, mv]);
        apply(kernel, order, &[mv, a_plus_mv])
    };
    let motive_body = kernel.abstract_fvars(motive_body, &[mv_id]);
    let anon1 = kernel.anon();
    let motive = kernel.lam(anon1, shape.nat, motive_body, BinderInfo::Default);

    let base = kernel.app(zero_le_closed, a);

    let bpred = kernel.fvar(bpred_id);
    let ih = kernel.fvar(ih_id);
    let a_plus_bpred = apply(kernel, add_head, &[a, bpred]);
    let succ_le_succ_applied = apply(kernel, succ_le_succ_closed, &[bpred, a_plus_bpred, ih]);
    let step_body = kernel.abstract_fvars(succ_le_succ_applied, &[ih_id]);
    let ih_ty = {
        let a_plus_bpred2 = apply(kernel, add_head, &[a, bpred]);
        apply(kernel, order, &[bpred, a_plus_bpred2])
    };
    let anon2 = kernel.anon();
    let step_inner = kernel.lam(anon2, ih_ty, step_body, BinderInfo::Default);
    let step_inner = kernel.abstract_fvars(step_inner, &[bpred_id]);
    let anon3 = kernel.anon();
    let step = kernel.lam(anon3, shape.nat, step_inner, BinderInfo::Default);

    let zero_level = kernel.level_zero();
    let rec_name = exact_name(kernel, "Nat.rec")?;
    let rec_c = kernel.const_(rec_name, vec![zero_level]);
    let applied = apply(kernel, rec_c, &[motive, base, step, b]);
    let closed = kernel.abstract_fvars(applied, &[b_id]);
    let anon4 = kernel.anon();
    let closed = kernel.lam(anon4, shape.nat, closed, BinderInfo::Default);
    let closed = kernel.abstract_fvars(closed, &[a_id]);
    let anon5 = kernel.anon();
    Ok(kernel.lam(anon5, shape.nat, closed, BinderInfo::Default))
}

fn order_le_only(kernel: &mut Kernel) -> Result<ExprId, String> {
    let le_name = exact_name(kernel, "Nat.le")?;
    Ok(kernel.const_(le_name, vec![]))
}

fn order_zero(kernel: &mut Kernel, order: &OrderPrimitives) -> Result<ExprId, String> {
    // `Nat.le.refl`'s single argument tells us nothing about `zero`
    // directly; extract it the same way `build_order_proof` does, from
    // `Nat.fib`'s own initial pair -- but this helper is also called before
    // `zero` is otherwise in scope, so re-derive it from `Nat.zero` the
    // constructor directly, which is simpler and always available.
    let _ = order;
    let zero_name = exact_name(kernel, "Nat.zero")?;
    Ok(kernel.const_(zero_name, vec![]))
}

fn inspect_order_primitives(kernel: &mut Kernel) -> Result<OrderPrimitives, String> {
    let le_name = exact_name(kernel, "Nat.le")?;
    let le = kernel.const_(le_name, vec![]);
    let le_refl_name = exact_name(kernel, "Nat.le.refl")?;
    let le_refl = kernel.const_(le_refl_name, vec![]);
    let le_step_name = exact_name(kernel, "Nat.le.step")?;
    let le_step = kernel.const_(le_step_name, vec![]);
    let le_rec_name = exact_name(kernel, "Nat.le.rec")?;
    Ok(OrderPrimitives {
        le,
        le_refl,
        le_step,
        le_rec_name,
    })
}

// ---------------------------------------------------------------------------
// The fib_add_two-shaped recurrence, re-derived at a given step index `n`
// (adapted from `nat_fib_iterate_recurrence.rs::recurrence_proof`, which
// extracts its target from an external Pi-bound goal; this version builds
// the target directly since this export carries no such goal).
// ---------------------------------------------------------------------------

/// Returns `(lhs, rhs, proof)` where `proof : Eq Nat lhs rhs`, `lhs = fib
/// (succ (succ n))`, `rhs = fib n + fib (succ n)`.
fn fib_add_two_step(
    kernel: &mut Kernel,
    shape: &FibShape,
    helper: ExprId,
    add_head: ExprId,
    fib_const: ExprId,
    n: ExprId,
) -> Result<(ExprId, ExprId, ExprId), String> {
    let successor_n = kernel.app(shape.successor, n);
    let iter_n = iterate(kernel, shape, n, shape.initial);
    let iter_succ_n = iterate(kernel, shape, successor_n, shape.initial);

    let helper_succ = kernel.app(helper, successor_n);
    let helper_succ = kernel.app(helper_succ, shape.initial);
    let fst_function = unary_projection(kernel, shape, shape.fst, "fst");
    let successor_successor_n = kernel.app(shape.successor, successor_n);
    let iter_successor_successor_n = iterate(kernel, shape, successor_successor_n, shape.initial);
    let transition_iter_succ_n = kernel.app(shape.transition, iter_succ_n);
    let first = congr_arg(
        kernel,
        shape.product,
        shape.nat,
        fst_function,
        iter_successor_successor_n,
        transition_iter_succ_n,
        helper_succ,
    )?;

    let helper_n = kernel.app(helper, n);
    let helper_n = kernel.app(helper_n, shape.initial);
    let snd_function = unary_projection(kernel, shape, shape.snd, "snd");
    let transition_iter_n = kernel.app(shape.transition, iter_n);
    let second = congr_arg(
        kernel,
        shape.product,
        shape.nat,
        snd_function,
        iter_succ_n,
        transition_iter_n,
        helper_n,
    )?;

    let target_lhs = kernel.app(fib_const, successor_successor_n);
    let fib_n = kernel.app(fib_const, n);
    let fib_succ_n = kernel.app(fib_const, successor_n);
    let target_rhs = apply(kernel, add_head, &[fib_n, fib_succ_n]);

    let middle = kernel.app(shape.snd, iter_succ_n);
    let actual_rhs = kernel.app(shape.snd, transition_iter_n);
    let left_to_actual = equality_trans(
        kernel, shape.nat, target_lhs, middle, actual_rhs, first, second,
    )?;
    let fst_helper_n = congr_arg(
        kernel,
        shape.product,
        shape.nat,
        fst_function,
        iter_succ_n,
        transition_iter_n,
        helper_n,
    )?;
    let fst_iter_succ_n = kernel.app(shape.fst, iter_succ_n);
    let fst_transition_iter_n = kernel.app(shape.fst, transition_iter_n);
    let reversed_fst_helper = equality_symm(
        kernel,
        shape.nat,
        fst_iter_succ_n,
        fst_transition_iter_n,
        fst_helper_n,
    )?;
    let add_right = replace_last_argument_function(kernel, target_rhs, shape.nat)?;
    let rhs_bridge = congr_arg(
        kernel,
        shape.nat,
        shape.nat,
        add_right,
        fst_transition_iter_n,
        fst_iter_succ_n,
        reversed_fst_helper,
    )?;
    let proof = equality_trans(
        kernel,
        shape.nat,
        target_lhs,
        actual_rhs,
        target_rhs,
        left_to_actual,
        rhs_bridge,
    )?;
    Ok((target_lhs, target_rhs, proof))
}

// ---------------------------------------------------------------------------
// Copied verbatim from `nat_fib_iterate_recurrence.rs` (fib shape discovery
// and the generic Eq-side term-building toolkit).
// ---------------------------------------------------------------------------

fn inspect_fib_shape(kernel: &mut Kernel) -> Result<FibShape, String> {
    let fib_name = exact_name(kernel, "Nat.fib")?;
    let (nat, fib_body) = match kernel.environment().get(fib_name) {
        Some(Declaration::Definition { value, .. }) => match kernel.expr_node(*value) {
            ExprNode::Lam(_, nat, body, _) => (*nat, *body),
            _ => return Err("Nat.fib is not unary".to_owned()),
        },
        _ => return Err("Nat.fib is not a definition".to_owned()),
    };
    let (_, fst_arguments) = app_spine(kernel, fib_body);
    let iterate_application = *fst_arguments.last().ok_or("Nat.fib has no iterator")?;
    let (iterate, iterate_arguments) = app_spine(kernel, iterate_application);
    if iterate_arguments.len() != 4 {
        return Err("Nat.fib iterator spine changed".to_owned());
    }
    let product = iterate_arguments[0];
    let transition = iterate_arguments[1];
    let initial = iterate_arguments[3];
    let zero = kernel.level_zero();
    let successor = kernel.const_(exact_name(kernel, "Nat.succ")?, vec![]);
    let mut fst = kernel.const_(exact_name(kernel, "Prod.fst")?, vec![zero, zero]);
    fst = kernel.app(fst, nat);
    fst = kernel.app(fst, nat);
    let mut snd = kernel.const_(exact_name(kernel, "Prod.snd")?, vec![zero, zero]);
    snd = kernel.app(snd, nat);
    snd = kernel.app(snd, nat);
    Ok(FibShape {
        nat,
        product,
        transition,
        initial,
        iterate,
        successor,
        fst,
        snd,
    })
}

fn iterator_successor_helper(
    kernel: &mut Kernel,
    shape: &FibShape,
    base_id: u64,
) -> Result<(ExprId, ExprId), String> {
    let n_id = base_id;
    let x_id = base_id - 1;
    let ih_id = base_id - 2;
    let n = kernel.fvar(n_id);
    let x = kernel.fvar(x_id);
    let helper_at_n = helper_proposition(kernel, shape, n, x)?;
    let helper_for_n = close_pi(kernel, x_id, "x", shape.product, helper_at_n);
    let motive = close_lam(kernel, n_id, "n", shape.nat, helper_for_n);
    let zero = kernel.const_(exact_name(kernel, "Nat.zero")?, vec![]);
    let base_goal = helper_proposition(kernel, shape, zero, x)?;
    let base_refl = equality_refl_left(kernel, base_goal)?;
    let base = close_lam(kernel, x_id, "x", shape.product, base_refl);

    let ih_type = {
        let body = helper_proposition(kernel, shape, n, x)?;
        close_pi(kernel, x_id, "x", shape.product, body)
    };
    let ih = kernel.fvar(ih_id);
    let transition_x = kernel.app(shape.transition, x);
    let step_body = kernel.app(ih, transition_x);
    let step_body = close_lam(kernel, x_id, "x", shape.product, step_body);
    let step_body = close_lam(kernel, ih_id, "ih", ih_type, step_body);
    let step = close_lam(kernel, n_id, "n", shape.nat, step_body);

    let zero_level = kernel.level_zero();
    let mut rec = kernel.const_(exact_name(kernel, "Nat.rec")?, vec![zero_level]);
    rec = kernel.app(rec, motive);
    rec = kernel.app(rec, base);
    let helper = kernel.app(rec, step);
    let helper_goal = {
        let body = helper_proposition(kernel, shape, n, x)?;
        let body = close_pi(kernel, x_id, "x", shape.product, body);
        close_pi(kernel, n_id, "n", shape.nat, body)
    };
    let inferred = kernel
        .infer(helper)
        .map_err(|error| format!("helper inference failed: {error:?}"))?;
    if !kernel.def_eq(inferred, helper_goal) {
        return Err("helper schema type mismatch".to_owned());
    }
    Ok((helper, helper_goal))
}

fn helper_proposition(
    kernel: &mut Kernel,
    shape: &FibShape,
    n: ExprId,
    x: ExprId,
) -> Result<ExprId, String> {
    let successor_n = kernel.app(shape.successor, n);
    let left = iterate(kernel, shape, successor_n, x);
    let iterated = iterate(kernel, shape, n, x);
    let right = kernel.app(shape.transition, iterated);
    equality(kernel, shape.product, left, right)
}

fn iterate(kernel: &mut Kernel, shape: &FibShape, count: ExprId, value: ExprId) -> ExprId {
    let mut result = kernel.app(shape.iterate, shape.product);
    result = kernel.app(result, shape.transition);
    result = kernel.app(result, count);
    kernel.app(result, value)
}

fn unary_projection(
    kernel: &mut Kernel,
    shape: &FibShape,
    projection: ExprId,
    binder: &str,
) -> ExprId {
    let id = u64::MAX - if binder == "fst" { 83_001 } else { 83_002 };
    let value = kernel.fvar(id);
    let body = kernel.app(projection, value);
    close_lam(kernel, id, binder, shape.product, body)
}

fn congr_arg(
    kernel: &mut Kernel,
    domain: ExprId,
    codomain: ExprId,
    function: ExprId,
    left: ExprId,
    right: ExprId,
    proof: ExprId,
) -> Result<ExprId, String> {
    let right_id = u64::MAX - 84_001;
    let equality_id = u64::MAX - 84_002;
    let variable = kernel.fvar(right_id);
    let function_left = kernel.app(function, left);
    let function_variable = kernel.app(function, variable);
    let result = equality(kernel, codomain, function_left, function_variable)?;
    let premise = equality(kernel, domain, left, variable)?;
    let motive = close_lam(kernel, equality_id, "h", premise, result);
    let motive = close_lam(kernel, right_id, "b", domain, motive);
    let reflexivity = equality_refl(kernel, codomain, function_left)?;
    let carrier_level = sort_level(kernel, domain)?;
    let motive_level = kernel.level_zero();
    let mut rec = kernel.const_(
        exact_name(kernel, "Eq.rec")?,
        vec![motive_level, carrier_level],
    );
    for argument in [domain, left, motive, reflexivity, right, proof] {
        rec = kernel.app(rec, argument);
    }
    Ok(rec)
}

#[allow(clippy::too_many_arguments)]
fn equality_trans(
    kernel: &mut Kernel,
    ty: ExprId,
    left: ExprId,
    middle: ExprId,
    right: ExprId,
    first: ExprId,
    second: ExprId,
) -> Result<ExprId, String> {
    let right_id = u64::MAX - 85_001;
    let equality_id = u64::MAX - 85_002;
    let variable = kernel.fvar(right_id);
    let result = equality(kernel, ty, left, variable)?;
    let premise = equality(kernel, ty, middle, variable)?;
    let motive = close_lam(kernel, equality_id, "h", premise, result);
    let motive = close_lam(kernel, right_id, "c", ty, motive);
    let carrier_level = sort_level(kernel, ty)?;
    let motive_level = kernel.level_zero();
    let mut rec = kernel.const_(
        exact_name(kernel, "Eq.rec")?,
        vec![motive_level, carrier_level],
    );
    for argument in [ty, middle, motive, first, right, second] {
        rec = kernel.app(rec, argument);
    }
    Ok(rec)
}

fn equality_symm(
    kernel: &mut Kernel,
    ty: ExprId,
    left: ExprId,
    right: ExprId,
    proof: ExprId,
) -> Result<ExprId, String> {
    let right_id = u64::MAX - 89_001;
    let equality_id = u64::MAX - 89_002;
    let variable = kernel.fvar(right_id);
    let premise = equality(kernel, ty, left, variable)?;
    let result = equality(kernel, ty, variable, left)?;
    let motive = close_lam(kernel, equality_id, "h", premise, result);
    let motive = close_lam(kernel, right_id, "b", ty, motive);
    let reflexivity = equality_refl(kernel, ty, left)?;
    let carrier_level = sort_level(kernel, ty)?;
    let motive_level = kernel.level_zero();
    let mut rec = kernel.const_(
        exact_name(kernel, "Eq.rec")?,
        vec![motive_level, carrier_level],
    );
    for argument in [ty, left, motive, reflexivity, right, proof] {
        rec = kernel.app(rec, argument);
    }
    Ok(rec)
}

#[allow(clippy::too_many_arguments)]
fn transport_equality(
    kernel: &mut Kernel,
    carrier: ExprId,
    left: ExprId,
    right: ExprId,
    equality_proof: ExprId,
    predicate: ExprId,
    base: ExprId,
) -> Result<ExprId, String> {
    let candidate_id = u64::MAX - 94_001;
    let proof_id = u64::MAX - 94_002;
    let candidate = kernel.fvar(candidate_id);
    let premise = equality(kernel, carrier, left, candidate)?;
    let conclusion = kernel.app(predicate, candidate);
    let motive = close_lam(kernel, proof_id, "h", premise, conclusion);
    let motive = close_lam(kernel, candidate_id, "x", carrier, motive);
    let carrier_level = sort_level(kernel, carrier)?;
    let motive_level = kernel.level_zero();
    let recursor = kernel.const_(
        exact_name(kernel, "Eq.rec")?,
        vec![motive_level, carrier_level],
    );
    Ok(apply(
        kernel,
        recursor,
        &[carrier, left, motive, base, right, equality_proof],
    ))
}

fn replace_last_argument_function(
    kernel: &mut Kernel,
    application: ExprId,
    domain: ExprId,
) -> Result<ExprId, String> {
    let (head, mut arguments) = app_spine(kernel, application);
    arguments
        .pop()
        .ok_or("right-addition target has no arguments")?;
    let right_id = u64::MAX - 89_003;
    let mut body = head;
    for argument in arguments {
        body = kernel.app(body, argument);
    }
    let right = kernel.fvar(right_id);
    body = kernel.app(body, right);
    Ok(close_lam(kernel, right_id, "rhs", domain, body))
}

fn equality_refl_left(kernel: &mut Kernel, proposition: ExprId) -> Result<ExprId, String> {
    let (_, arguments) = app_spine(kernel, proposition);
    if arguments.len() != 3 {
        return Err("expected equality proposition".to_owned());
    }
    equality_refl(kernel, arguments[0], arguments[1])
}

fn equality_refl(kernel: &mut Kernel, ty: ExprId, value: ExprId) -> Result<ExprId, String> {
    let level = sort_level(kernel, ty)?;
    let mut refl = kernel.const_(exact_name(kernel, "Eq.refl")?, vec![level]);
    refl = kernel.app(refl, ty);
    Ok(kernel.app(refl, value))
}

fn equality(
    kernel: &mut Kernel,
    ty: ExprId,
    left: ExprId,
    right: ExprId,
) -> Result<ExprId, String> {
    let level = sort_level(kernel, ty)?;
    let mut eq = kernel.const_(exact_name(kernel, "Eq")?, vec![level]);
    for argument in [ty, left, right] {
        eq = kernel.app(eq, argument);
    }
    Ok(eq)
}

fn sort_level(kernel: &mut Kernel, ty: ExprId) -> Result<LevelId, String> {
    let inferred = kernel
        .infer(ty)
        .map_err(|error| format!("type sort: {error:?}"))?;
    let inferred = kernel.whnf(inferred);
    match kernel.expr_node(inferred) {
        ExprNode::Sort(level) => Ok(*level),
        _ => Err("type does not inhabit a sort".to_owned()),
    }
}

fn close_lam(kernel: &mut Kernel, id: u64, name: &str, domain: ExprId, body: ExprId) -> ExprId {
    let body = kernel.abstract_fvars(body, &[id]);
    let binder = nested_name(kernel, &[name]);
    kernel.lam(binder, domain, body, BinderInfo::Default)
}

fn close_pi(kernel: &mut Kernel, id: u64, name: &str, domain: ExprId, body: ExprId) -> ExprId {
    let body = kernel.abstract_fvars(body, &[id]);
    let binder = nested_name(kernel, &[name]);
    kernel.pi(binder, domain, body, BinderInfo::Default)
}

fn apply(kernel: &mut Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for argument in arguments {
        function = kernel.app(function, *argument);
    }
    function
}

fn app_spine(kernel: &Kernel, mut expression: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut arguments = Vec::new();
    while let ExprNode::App(function, argument) = kernel.expr_node(expression) {
        arguments.push(*argument);
        expression = *function;
    }
    arguments.reverse();
    (expression, arguments)
}

fn exact_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
    let matches: Vec<_> = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == rendered).then_some(name)
        })
        .collect();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(format!("{rendered} occurs {} times", matches.len())),
    }
}

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    let mut name = kernel.anon();
    for part in parts {
        name = kernel.name_str(name, *part);
    }
    name
}

fn rendered_names(kernel: &Kernel, names: &[NameId]) -> Vec<String> {
    let mut rendered: Vec<_> = names
        .iter()
        .map(|&name| kernel.display_name(name).to_string())
        .collect();
    rendered.sort();
    rendered.dedup();
    rendered
}

fn hex_sha256(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    hasher.finalize().iter().fold(String::new(), |mut out, b| {
        use std::fmt::Write as _;
        let _ = write!(out, "{b:02x}");
        out
    })
}
