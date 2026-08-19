//! Execute the preregistered two-template iterator-recurrence proof operation.

use std::env;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    ImportLimits, canonical_declaration_sha256, canonical_expression_sha256, import_ndjson,
};
use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, NameId};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const TARGET: &str = "Axeyum.Autogenesis.Coverage.r080";
const TARGET_FACT: &str = "F:ml430-nat-fib-add-two-b86e0c82";
const STREAM_SHA256: &str = "00578e949d71154cf5d9e79005b2a1c8f7fe73d9885ae96b0dd5cb6744c30501";
const POLICY_VERSION: &str = "nat-fib-iterate-recurrence-v1";
const MAX_PLAN_TEMPLATES: usize = 2;
const MAX_KERNEL_SUBMISSIONS: usize = 2;

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

#[derive(Debug)]
struct SearchResult {
    theorem: NameId,
    plan_rank: usize,
    submissions: usize,
    direct_rejection: String,
    helper_schema_sha256: String,
    proof_sha256: String,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("nat-fib-iterate-recurrence: {error}");
        std::process::exit(1);
    }
}

#[allow(clippy::too_many_lines)]
fn run() -> Result<(), String> {
    let arguments = parse_arguments()?;
    let stream = fs::read(&arguments.stream).map_err(|error| error.to_string())?;
    if hex_sha256(&stream) != STREAM_SHA256 {
        return Err("r080 stream identity changed".to_owned());
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
    let target = exact_name(&kernel, TARGET)?;
    let goal = match kernel.environment().get(target) {
        Some(Declaration::Definition { uparams, value, .. }) if uparams.is_empty() => *value,
        _ => return Err("target is not a monomorphic statement definition".to_owned()),
    };
    let shape = inspect_fib_shape(&mut kernel)?;
    if arguments.preflight {
        let (_, helper_goal) = iterator_successor_helper(&mut kernel, &shape)?;
        let helper_schema_sha256 = canonical_expression_sha256(&kernel, helper_goal)?;
        println!(
            "AUTOGENESIS_NAT_FIB_ITERATE_PREFLIGHT_OK|{helper_schema_sha256}|target_submissions=0|target_outcomes=0"
        );
        return Ok(());
    }
    let output_path = arguments
        .output
        .as_ref()
        .ok_or("missing --output outside preflight mode")?;
    let theorem = nested_name(&mut kernel, &["Axeyum", "Autogenesis", "NatFibAddTwo"]);
    let search = execute_two_template_search(&mut kernel, goal, theorem, &shape)?;
    if search.plan_rank > MAX_PLAN_TEMPLATES || search.submissions > MAX_KERNEL_SUBMISSIONS {
        return Err("frozen search budget changed".to_owned());
    }
    let axioms = rendered_names(&kernel, &kernel.axiom_footprint(search.theorem));
    let theorem_dependencies =
        rendered_names(&kernel, &kernel.theorem_dependencies(search.theorem));
    let closure = kernel.declaration_dependency_closure(search.theorem);
    if !axioms.is_empty() || !theorem_dependencies.is_empty() || closure.contains(&target) {
        return Err("accepted theorem dependency audit failed".to_owned());
    }
    let theorem_content_sha256 = canonical_declaration_sha256(&kernel, search.theorem)?;
    let goal_sha256 = canonical_expression_sha256(&kernel, goal)?;
    let theorem_type = kernel
        .environment()
        .get(search.theorem)
        .ok_or("accepted theorem disappeared")?
        .ty();
    if theorem_type != goal {
        return Err("accepted theorem type changed".to_owned());
    }
    let mut output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-nat-fib-iterate-recurrence-control",
        "state": "candidate-checked-no-receipt-evaluation-or-ledger-credit",
        "policy_version": POLICY_VERSION,
        "source": {
            "artifact_file": "r080.ndjson",
            "stream_sha256": STREAM_SHA256,
            "lean_version": report.lean_version,
            "lean_githash": report.lean_githash,
            "target_definition": TARGET,
            "fact_id": TARGET_FACT,
            "goal_sha256": goal_sha256,
        },
        "search": {
            "operation": "bounded-iterate-recurrence-v1",
            "plan_templates": MAX_PLAN_TEMPLATES,
            "accepted_plan_rank": search.plan_rank,
            "kernel_submissions": search.submissions,
            "executor_invocations": 1,
            "retries": 0,
            "direct_normalization_rejection": search.direct_rejection,
            "helper_schemas_constructed": 1,
            "helper_schema_sha256": search.helper_schema_sha256,
        },
        "candidate": {
            "name": "Axeyum.Autogenesis.NatFibAddTwo",
            "theorem_content_sha256": theorem_content_sha256,
            "proof_sha256": search.proof_sha256,
            "kernel_accepted": true,
            "axiom_footprint": axioms,
            "theorem_dependencies": theorem_dependencies,
            "source_target_dependency": false,
        },
        "authority": {
            "partitions_inspected": ["train"],
            "held_out_inspected": false,
            "proof_bodies_inspected": false,
            "semantic_theorem_receipts_issued": 0,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        },
        "limitations": "The bounded operation produced an independently accepted candidate. A semantic theorem receipt and separate admission transaction are still required before evaluation or ledger credit.",
    });
    let digest = canonical_digest(&output)?;
    output["observation_sha256"] = json!(digest);
    let mut rendered = serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?;
    rendered.push('\n');
    fs::write(output_path, rendered).map_err(|error| error.to_string())?;
    println!(
        "AUTOGENESIS_NAT_FIB_ITERATE_RECURRENCE_OK|{digest}|fact={TARGET_FACT}|plan={}|submissions={}|axioms=0|theorem_dependencies=0|receipts=0|evaluation=0|held_out=0|ledger_writes=0",
        search.plan_rank, search.submissions
    );
    Ok(())
}

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

fn execute_two_template_search(
    kernel: &mut Kernel,
    goal: ExprId,
    theorem: NameId,
    shape: &FibShape,
) -> Result<SearchResult, String> {
    let direct = direct_reflexivity(kernel, goal)?;
    let direct_rejection = match kernel.add_declaration(Declaration::Theorem {
        name: theorem,
        uparams: vec![],
        ty: goal,
        value: direct,
    }) {
        Ok(()) => {
            return Ok(SearchResult {
                theorem,
                plan_rank: 1,
                submissions: 1,
                direct_rejection: String::new(),
                helper_schema_sha256: String::new(),
                proof_sha256: canonical_expression_sha256(kernel, direct)?,
            });
        }
        Err(error) => format!("{error:?}"),
    };
    let (helper, helper_goal) = iterator_successor_helper(kernel, shape)?;
    let helper_schema_sha256 = canonical_expression_sha256(kernel, helper_goal)?;
    let proof = recurrence_proof(kernel, goal, shape, helper)?;
    let proof_sha256 = canonical_expression_sha256(kernel, proof)?;
    kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .map_err(|error| format!("recurrence plan rejected: {error:?}"))?;
    Ok(SearchResult {
        theorem,
        plan_rank: 2,
        submissions: 2,
        direct_rejection,
        helper_schema_sha256,
        proof_sha256,
    })
}

fn iterator_successor_helper(
    kernel: &mut Kernel,
    shape: &FibShape,
) -> Result<(ExprId, ExprId), String> {
    let n_id = u64::MAX - 81_000;
    let x_id = u64::MAX - 81_001;
    let ih_id = u64::MAX - 81_002;
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

fn recurrence_proof(
    kernel: &mut Kernel,
    goal: ExprId,
    shape: &FibShape,
    helper: ExprId,
) -> Result<ExprId, String> {
    let ExprNode::Pi(name, domain, body, info) = kernel.expr_node(goal).clone() else {
        return Err("target has no pointwise binder".to_owned());
    };
    let n_id = u64::MAX - 82_000;
    let n = kernel.fvar(n_id);
    let target = kernel.instantiate(body, &[n]);
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
    let (_, target_arguments) = app_spine(kernel, target);
    if target_arguments.len() != 3 {
        return Err("target body is not equality".to_owned());
    }
    let middle = kernel.app(shape.snd, iter_succ_n);
    let proof = equality_trans(
        kernel,
        shape.nat,
        target_arguments[1],
        middle,
        target_arguments[2],
        first,
        second,
    )?;
    let proof = kernel.abstract_fvars(proof, &[n_id]);
    Ok(kernel.lam(name, domain, proof, info))
}

fn iterate(kernel: &mut Kernel, shape: &FibShape, count: ExprId, value: ExprId) -> ExprId {
    let mut result = shape.iterate;
    for argument in [shape.product, shape.transition, count, value] {
        result = kernel.app(result, argument);
    }
    result
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
    let zero = kernel.level_zero();
    let mut rec = kernel.const_(exact_name(kernel, "Eq.rec")?, vec![zero, zero]);
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
    let zero = kernel.level_zero();
    let mut rec = kernel.const_(exact_name(kernel, "Eq.rec")?, vec![zero, zero]);
    for argument in [ty, middle, motive, first, right, second] {
        rec = kernel.app(rec, argument);
    }
    Ok(rec)
}

fn direct_reflexivity(kernel: &mut Kernel, goal: ExprId) -> Result<ExprId, String> {
    let ExprNode::Pi(name, domain, body, info) = kernel.expr_node(goal).clone() else {
        return Err("direct template requires one binder".to_owned());
    };
    let (_, arguments) = app_spine(kernel, body);
    if arguments.len() != 3 {
        return Err("direct template requires equality".to_owned());
    }
    let proof = equality_refl(kernel, arguments[0], arguments[1])?;
    Ok(kernel.lam(name, domain, proof, info))
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

struct Arguments {
    stream: PathBuf,
    output: Option<PathBuf>,
    preflight: bool,
}

fn parse_arguments() -> Result<Arguments, String> {
    let mut stream = None;
    let mut output = None;
    let mut preflight = false;
    let mut arguments = env::args().skip(1);
    while let Some(flag) = arguments.next() {
        if flag == "--preflight" {
            if preflight {
                return Err("duplicate --preflight".to_owned());
            }
            preflight = true;
            continue;
        }
        let value = arguments
            .next()
            .ok_or_else(|| format!("{flag} requires a value"))?;
        let slot = match flag.as_str() {
            "--stream" => &mut stream,
            "--output" => &mut output,
            _ => return Err(format!("unknown argument {flag}")),
        };
        if slot.replace(PathBuf::from(value)).is_some() {
            return Err(format!("duplicate {flag}"));
        }
    }
    Ok(Arguments {
        stream: stream.ok_or("missing --stream")?,
        output,
        preflight,
    })
}

fn canonical_digest(value: &Value) -> Result<String, String> {
    serde_json::to_vec(value)
        .map(|bytes| hex_sha256(&bytes))
        .map_err(|error| error.to_string())
}

fn hex_sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut output = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write;
        write!(output, "{byte:02x}").expect("writing to String cannot fail");
    }
    output
}
