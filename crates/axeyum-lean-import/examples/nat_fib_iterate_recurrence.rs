//! Execute the preregistered two-template iterator-recurrence proof operation.

use std::env;
use std::fs;
use std::io::Cursor;
use std::path::PathBuf;

use axeyum_lean_import::{
    CHECKED_SEMANTIC_THEOREM_RECEIPT_VERSION, CheckedTheoremAuthority, ImportLimits,
    canonical_declaration_sha256, canonical_expression_sha256, compose_checked_theorem_slice,
    import_ndjson, issue_checked_semantic_theorem_receipt, verify_checked_semantic_theorem_receipt,
    verify_checked_theorem_composition,
};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, KernelError, LevelId, NameId,
    build_nat_prelude,
};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

const TARGET: &str = "Axeyum.Autogenesis.Coverage.r080";
const TARGET_FACT: &str = "F:ml430-nat-fib-add-two-b86e0c82";
const STREAM_SHA256: &str = "00578e949d71154cf5d9e79005b2a1c8f7fe73d9885ae96b0dd5cb6744c30501";
const POLICY_VERSION: &str = "nat-fib-iterate-recurrence-v3";
const MAX_PLAN_TEMPLATES: usize = 2;
const MAX_KERNEL_SUBMISSIONS: usize = 2;
const CANDIDATE_OBSERVATION_SHA256: &str =
    "920ef21dffc17402180725f940220e26a02db02cdf7ff636779d9cdfe6680969";
const CANDIDATE_PROOF_SHA256: &str =
    "b5965831fd4654e708b03bd3145f9124f02fc57aaa04bc16ded8287b6cee50f2";
const CANDIDATE_THEOREM_SHA256: &str =
    "ad53b80748ad1d3f0a0958277774e36a621ce25f5f1441b6882085349886537a";
const GOAL_SHA256: &str = "5433b34c4a138d615c488e4c7dfbee5dac8dc253e14680e114f40a55cf5eb16d";

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
    if let Some(candidate) = &arguments.receipt_candidate {
        let output = arguments
            .output
            .as_ref()
            .ok_or("receipt mode requires --output")?;
        return run_checked_receipt(&stream, candidate, output);
    }
    if arguments.native_composition {
        return run_native_composition(&stream);
    }
    if arguments.native_coprime_control {
        return run_native_coprime_control(&stream);
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
    if arguments.composition_control {
        return run_composition_control(&mut kernel, &shape);
    }
    if arguments.preflight {
        let (_, helper_goal) = iterator_successor_helper(&mut kernel, &shape)?;
        let helper_schema_sha256 = canonical_expression_sha256(&kernel, helper_goal)?;
        println!(
            "AUTOGENESIS_NAT_FIB_ITERATE_PREFLIGHT_OK|{helper_schema_sha256}|target_submissions=0|target_outcomes=0"
        );
        return Ok(());
    }
    let target = exact_name(&kernel, TARGET)?;
    let goal = match kernel.environment().get(target) {
        Some(Declaration::Definition { uparams, value, .. }) if uparams.is_empty() => *value,
        _ => return Err("target is not a monomorphic statement definition".to_owned()),
    };
    if arguments.stage_control {
        return run_recurrence_stage_control(&mut kernel, goal, &shape);
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
            "operation": "bounded-iterate-recurrence-v3",
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

fn run_native_composition(stream: &[u8]) -> Result<(), String> {
    let (source, theorem) = reconstruct_fixed_candidate(stream)?;
    let theorem_name = source.display_name(theorem).to_string();
    let fib = exact_name(&source, "Nat.fib")?;
    let fib_declaration_sha256 = canonical_declaration_sha256(&source, fib)?;
    let mut native = Kernel::new();
    build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude failed to build: {error:?}"))?;
    let caller_declarations = native.environment().len();
    let completed = compose_checked_theorem_slice(&source, &native, &[&theorem_name])
        .map_err(|error| format!("native theorem composition declined: {error:?}"))?;
    verify_checked_theorem_composition(&source, &native, completed.kernel(), completed.receipt())
        .map_err(|error| format!("native theorem composition did not replay: {error:?}"))?;
    if native.environment().len() != caller_declarations {
        return Err("native theorem composition mutated its caller".to_owned());
    }
    let names = completed
        .kernel()
        .environment()
        .iter()
        .map(|(&name, _)| completed.kernel().display_name(name).to_string())
        .collect::<Vec<_>>();
    if !names.iter().any(|name| name == "Nat.fib")
        || !names.iter().any(|name| name == &theorem_name)
        || completed
            .receipt()
            .added_theorems
            .iter()
            .any(|row| !row.axiom_footprint.is_empty())
    {
        return Err("native theorem composition assurance failed".to_owned());
    }
    let completed_theorem = exact_name(completed.kernel(), &theorem_name)?;
    let footprint = rendered_names(
        completed.kernel(),
        &completed.kernel().axiom_footprint(completed_theorem),
    );
    let theorem_dependencies = rendered_names(
        completed.kernel(),
        &completed.kernel().theorem_dependencies(completed_theorem),
    );
    if !footprint.is_empty() || !theorem_dependencies.is_empty() {
        return Err("native theorem dependency audit failed".to_owned());
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-nat-fib-recurrence-native-composition",
            "source_stream_sha256": STREAM_SHA256,
            "nat_fib_declaration_sha256": fib_declaration_sha256,
            "root": theorem_name,
            "source_closure": completed.receipt().source_closure.len(),
            "reused_declarations": completed.receipt().reused_declarations.len(),
            "added_definitions": completed.receipt().added_definitions.iter().map(|row| &row.name).collect::<Vec<_>>(),
            "added_singleton_inductives": completed.receipt().added_singleton_inductives.iter().map(|row| &row.family).collect::<Vec<_>>(),
            "added_theorems": completed.receipt().added_theorems.iter().map(|row| &row.name).collect::<Vec<_>>(),
            "target_theorem_axiom_footprint": footprint,
            "target_theorem_dependencies": theorem_dependencies,
            "caller_declarations_before": caller_declarations,
            "caller_declarations_after": native.environment().len(),
            "completed_declarations": completed.kernel().environment().len(),
            "receipt_sha256": completed.receipt().receipt_sha256,
            "proof_search_invocations": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn run_native_coprime_control(stream: &[u8]) -> Result<(), String> {
    let (source, theorem) = reconstruct_fixed_candidate(stream)?;
    let theorem_name = source.display_name(theorem).to_string();
    let mut native = Kernel::new();
    build_nat_prelude(&mut native)
        .map_err(|error| format!("native Nat prelude failed to build: {error:?}"))?;
    let completed = compose_checked_theorem_slice(&source, &native, &[&theorem_name])
        .map_err(|error| format!("native theorem composition declined: {error:?}"))?;
    verify_checked_theorem_composition(&source, &native, completed.kernel(), completed.receipt())
        .map_err(|error| format!("native theorem composition did not replay: {error:?}"))?;
    let mut kernel = completed.kernel().clone();
    let (target, goal, proof) = admit_native_fib_coprime(&mut kernel, &theorem_name)?;
    let footprint = rendered_names(&kernel, &kernel.axiom_footprint(target));
    let dependencies = rendered_names(&kernel, &kernel.theorem_dependencies(target));
    let expected_dependencies = [
        "Axeyum.Autogenesis.NatFibAddTwo",
        "Nat.add_comm",
        "Nat.dvd_add_iff_right",
        "Nat.dvd_gcd",
        "Nat.eq_one_of_dvd_one",
        "Nat.gcd_dvd_left",
        "Nat.gcd_dvd_right",
        "Nat.gcd_zero_left",
    ];
    if !footprint.is_empty()
        || dependencies
            != expected_dependencies
                .into_iter()
                .map(str::to_owned)
                .collect::<Vec<_>>()
    {
        return Err(format!(
            "native Fibonacci coprimality dependency audit failed: footprint={footprint:?}; dependencies={dependencies:?}"
        ));
    }
    let goal_sha256 = canonical_expression_sha256(&kernel, goal)?;
    let proof_sha256 = canonical_expression_sha256(&kernel, proof)?;
    let theorem_declaration_sha256 = canonical_declaration_sha256(&kernel, target)?;
    let mut replay = completed.kernel().clone();
    let (replay_target, replay_goal, replay_proof) =
        admit_native_fib_coprime(&mut replay, &theorem_name)?;
    if canonical_expression_sha256(&replay, replay_goal)? != goal_sha256
        || canonical_expression_sha256(&replay, replay_proof)? != proof_sha256
        || canonical_declaration_sha256(&replay, replay_target)? != theorem_declaration_sha256
        || replay.axiom_footprint(replay_target) != kernel.axiom_footprint(target)
        || rendered_names(&replay, &replay.theorem_dependencies(replay_target)) != dependencies
    {
        return Err("native Fibonacci coprimality replay changed".to_owned());
    }
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema_version": 1,
            "kind": "axeyum-native-fibonacci-coprimality-control",
            "source_stream_sha256": STREAM_SHA256,
            "composition_receipt_sha256": completed.receipt().receipt_sha256,
            "target": "Axeyum.Autogenesis.NatFibCoprimeSucc",
            "goal_sha256": goal_sha256,
            "proof_sha256": proof_sha256,
            "theorem_declaration_sha256": theorem_declaration_sha256,
            "axiom_footprint": footprint,
            "direct_theorem_dependencies": dependencies,
            "fresh_reconstructions": 2,
            "kernel_submissions": 2,
            "proof_search_invocations": 0,
            "ledger_writes": 0,
        }))
        .map_err(|error| error.to_string())?
    );
    Ok(())
}

fn admit_native_fib_coprime(
    kernel: &mut Kernel,
    recurrence_name: &str,
) -> Result<(NameId, ExprId, ExprId), String> {
    let goal = native_fib_coprime_goal(kernel)?;
    let proof = native_fib_coprime_proof(kernel, goal, recurrence_name)?;
    require_inferred_type(kernel, proof, goal, "native Fibonacci coprimality")?;
    let target = nested_name(kernel, &["Axeyum", "Autogenesis", "NatFibCoprimeSucc"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .map_err(|error| format!("native Fibonacci coprimality rejected: {error:?}"))?;
    Ok((target, goal, proof))
}

fn native_fib_coprime_goal(kernel: &mut Kernel) -> Result<ExprId, String> {
    let nat = constant(kernel, "Nat")?;
    let fib = constant(kernel, "Nat.fib")?;
    let successor = constant(kernel, "Nat.succ")?;
    let gcd = constant(kernel, "Nat.gcd")?;
    let zero = constant(kernel, "Nat.zero")?;
    let one = kernel.app(successor, zero);
    let n_id = u64::MAX - 92_001;
    let n = kernel.fvar(n_id);
    let fib_n = kernel.app(fib, n);
    let successor_n = kernel.app(successor, n);
    let fib_successor_n = kernel.app(fib, successor_n);
    let gcd_neighbors = apply(kernel, gcd, &[fib_n, fib_successor_n]);
    let body = equality(kernel, nat, gcd_neighbors, one)?;
    Ok(close_pi(kernel, n_id, "n", nat, body))
}

#[allow(clippy::too_many_lines)]
fn native_fib_coprime_proof(
    kernel: &mut Kernel,
    goal: ExprId,
    recurrence_name: &str,
) -> Result<ExprId, String> {
    let ExprNode::Pi(name, nat, body, info) = kernel.expr_node(goal).clone() else {
        return Err("native coprimality goal has no Nat binder".to_owned());
    };
    let fib = constant(kernel, "Nat.fib")?;
    let successor = constant(kernel, "Nat.succ")?;
    let add = constant(kernel, "Nat.add")?;
    let gcd = constant(kernel, "Nat.gcd")?;
    let dvd = constant(kernel, "Nat.dvd")?;
    let zero = constant(kernel, "Nat.zero")?;
    let one = kernel.app(successor, zero);

    let motive_id = u64::MAX - 92_010;
    let motive_n = kernel.fvar(motive_id);
    let motive_body = kernel.instantiate(body, &[motive_n]);
    let motive = close_lam(kernel, motive_id, "n", nat, motive_body);

    let fib_one = kernel.app(fib, one);
    let base = apply_named(kernel, "Nat.gcd_zero_left", &[fib_one])?;
    let base_goal = kernel.instantiate(body, &[zero]);
    let base_type = kernel
        .infer(base)
        .map_err(|error| format!("native coprimality base inference failed: {error:?}"))?;
    if !kernel.def_eq(base_type, base_goal) {
        return Err(format!(
            "native coprimality base mismatch: expected {}; inferred {}",
            kernel.render_lean(base_goal),
            kernel.render_lean(base_type)
        ));
    }

    let n_id = u64::MAX - 92_020;
    let ih_id = u64::MAX - 92_021;
    let n = kernel.fvar(n_id);
    let successor_n = kernel.app(successor, n);
    let successor_successor_n = kernel.app(successor, successor_n);
    let induction_hypothesis_type = kernel.instantiate(body, &[n]);
    let induction_hypothesis = kernel.fvar(ih_id);
    let a = kernel.app(fib, n);
    let b = kernel.app(fib, successor_n);
    let c = kernel.app(fib, successor_successor_n);
    let sum_ab = apply(kernel, add, &[a, b]);
    let sum_ba = apply(kernel, add, &[b, a]);

    let recurrence = apply_named(kernel, recurrence_name, &[n])?;
    let commutativity = apply_named(kernel, "Nat.add_comm", &[a, b])?;
    let c_eq_sum_ba = equality_trans(kernel, nat, c, sum_ab, sum_ba, recurrence, commutativity)?;
    let argument_id = u64::MAX - 92_022;
    let argument = kernel.fvar(argument_id);
    let gcd_at_b = apply(kernel, gcd, &[b, argument]);
    let gcd_function = close_lam(kernel, argument_id, "x", nat, gcd_at_b);
    let gcd_b_c = apply(kernel, gcd, &[b, c]);
    let common = apply(kernel, gcd, &[b, sum_ba]);
    let gcd_bridge = congr_arg(kernel, nat, nat, gcd_function, c, sum_ba, c_eq_sum_ba)?;

    let common_divides_b = apply_named(kernel, "Nat.gcd_dvd_left", &[b, sum_ba])?;
    let common_divides_sum = apply_named(kernel, "Nat.gcd_dvd_right", &[b, sum_ba])?;
    let common_divides_a_type = apply(kernel, dvd, &[common, a]);
    let common_divides_sum_type = apply(kernel, dvd, &[common, sum_ba]);
    let add_characterization = apply_named(
        kernel,
        "Nat.dvd_add_iff_right",
        &[common, b, a, common_divides_b],
    )?;
    let sum_to_a = iff_reverse(
        kernel,
        common_divides_a_type,
        common_divides_sum_type,
        add_characterization,
    )?;
    let common_divides_a = kernel.app(sum_to_a, common_divides_sum);
    let common_divides_previous_gcd = apply_named(
        kernel,
        "Nat.dvd_gcd",
        &[common, a, b, common_divides_a, common_divides_b],
    )?;
    let previous_gcd = apply(kernel, gcd, &[a, b]);
    let divides_predicate_id = u64::MAX - 92_023;
    let candidate = kernel.fvar(divides_predicate_id);
    let divides_candidate = apply(kernel, dvd, &[common, candidate]);
    let divides_predicate = close_lam(kernel, divides_predicate_id, "x", nat, divides_candidate);
    let common_divides_one = transport_equality(
        kernel,
        nat,
        previous_gcd,
        one,
        induction_hypothesis,
        divides_predicate,
        common_divides_previous_gcd,
    )?;
    let common_is_one = apply_named(
        kernel,
        "Nat.eq_one_of_dvd_one",
        &[common, common_divides_one],
    )?;
    let step_body = equality_trans(kernel, nat, gcd_b_c, common, one, gcd_bridge, common_is_one)?;
    let step_body = close_lam(kernel, ih_id, "ih", induction_hypothesis_type, step_body);
    let step = close_lam(kernel, n_id, "n", nat, step_body);

    let zero_level = kernel.level_zero();
    let mut induction = kernel.const_(exact_name(kernel, "Nat.rec")?, vec![zero_level]);
    for argument in [motive, base, step] {
        induction = kernel.app(induction, argument);
    }
    let inferred = kernel
        .infer(induction)
        .map_err(|error| format!("native coprimality induction inference failed: {error:?}"))?;
    if !kernel.def_eq(inferred, goal) {
        return Err(format!(
            "native coprimality induction mismatch: expected {}; inferred {}",
            kernel.render_lean(goal),
            kernel.render_lean(inferred)
        ));
    }
    let _ = (name, info);
    Ok(induction)
}

fn constant(kernel: &mut Kernel, name: &str) -> Result<ExprId, String> {
    Ok(kernel.const_(exact_name(kernel, name)?, vec![]))
}

fn apply(kernel: &mut Kernel, mut function: ExprId, arguments: &[ExprId]) -> ExprId {
    for &argument in arguments {
        function = kernel.app(function, argument);
    }
    function
}

fn apply_named(kernel: &mut Kernel, name: &str, arguments: &[ExprId]) -> Result<ExprId, String> {
    let function = constant(kernel, name)?;
    Ok(apply(kernel, function, arguments))
}

fn iff_reverse(
    kernel: &mut Kernel,
    left: ExprId,
    right: ExprId,
    proof: ExprId,
) -> Result<ExprId, String> {
    let iff = apply_named(kernel, "Iff", &[left, right])?;
    let anonymous = kernel.anon();
    let target = kernel.pi(anonymous, right, left, BinderInfo::Default);
    let proof_id = u64::MAX - 93_001;
    let motive = close_lam(kernel, proof_id, "h", iff, target);
    let forward_type = kernel.pi(anonymous, left, right, BinderInfo::Default);
    let forward_id = u64::MAX - 93_002;
    let reverse_id = u64::MAX - 93_003;
    let reverse = kernel.fvar(reverse_id);
    let minor = close_lam(kernel, reverse_id, "reverse", target, reverse);
    let minor = close_lam(kernel, forward_id, "forward", forward_type, minor);
    let zero = kernel.level_zero();
    let recursor = kernel.const_(exact_name(kernel, "Iff.rec")?, vec![zero]);
    Ok(apply(
        kernel,
        recursor,
        &[left, right, motive, minor, proof],
    ))
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

#[allow(clippy::too_many_lines)]
fn run_checked_receipt(
    stream: &[u8],
    candidate_path: &PathBuf,
    output_path: &PathBuf,
) -> Result<(), String> {
    let candidate: Value =
        serde_json::from_slice(&fs::read(candidate_path).map_err(|error| error.to_string())?)
            .map_err(|error| error.to_string())?;
    let mut unsigned = candidate.clone();
    let claimed = unsigned
        .as_object_mut()
        .and_then(|value| value.remove("observation_sha256"))
        .and_then(|value| value.as_str().map(str::to_owned));
    if claimed.as_deref() != Some(CANDIDATE_OBSERVATION_SHA256)
        || canonical_digest(&unsigned)? != CANDIDATE_OBSERVATION_SHA256
        || candidate
            .pointer("/candidate/proof_sha256")
            .and_then(Value::as_str)
            != Some(CANDIDATE_PROOF_SHA256)
        || candidate
            .pointer("/candidate/theorem_content_sha256")
            .and_then(Value::as_str)
            != Some(CANDIDATE_THEOREM_SHA256)
        || candidate
            .pointer("/source/goal_sha256")
            .and_then(Value::as_str)
            != Some(GOAL_SHA256)
        || candidate
            .pointer("/authority/evaluation_credit")
            .and_then(Value::as_u64)
            != Some(0)
        || candidate
            .pointer("/authority/ledger_writes")
            .and_then(Value::as_u64)
            != Some(0)
    {
        return Err("sealed candidate authority changed".to_owned());
    }
    let authority = CheckedTheoremAuthority {
        policy_version: "nat-fib-add-two-checked-theorem-receipt-v1".to_owned(),
        source_artifact_sha256: STREAM_SHA256.to_owned(),
        target_definition: TARGET.to_owned(),
        fact_id: TARGET_FACT.to_owned(),
        goal_sha256: GOAL_SHA256.to_owned(),
        candidate_observation_sha256: CANDIDATE_OBSERVATION_SHA256.to_owned(),
        expected_proof_sha256: CANDIDATE_PROOF_SHA256.to_owned(),
        expected_theorem_content_sha256: CANDIDATE_THEOREM_SHA256.to_owned(),
        operation: "bounded-iterate-recurrence-v3".to_owned(),
        max_plan_templates: MAX_PLAN_TEMPLATES,
        max_kernel_submissions: MAX_KERNEL_SUBMISSIONS,
        max_executor_invocations: 1,
        max_retries: 0,
    };
    let (mut first_kernel, first_theorem) = reconstruct_fixed_candidate(stream)?;
    let receipt =
        issue_checked_semantic_theorem_receipt(&mut first_kernel, first_theorem, &authority)
            .map_err(|error| error.to_string())?;
    let (mut replay_kernel, replay_theorem) = reconstruct_fixed_candidate(stream)?;
    verify_checked_semantic_theorem_receipt(
        &receipt,
        &mut replay_kernel,
        replay_theorem,
        &authority,
    )
    .map_err(|error| error.to_string())?;
    let replayed =
        issue_checked_semantic_theorem_receipt(&mut replay_kernel, replay_theorem, &authority)
            .map_err(|error| error.to_string())?;
    if receipt != replayed
        || receipt.schema_version != CHECKED_SEMANTIC_THEOREM_RECEIPT_VERSION
        || !receipt.has_valid_digest()
    {
        return Err("fresh-kernel theorem receipt replay changed".to_owned());
    }
    let receipt_json: Value = serde_json::from_str(
        &receipt
            .to_pretty_json()
            .map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())?;
    let mut output = json!({
        "schema_version": 1,
        "kind": "axeyum-autogenesis-nat-fib-checked-theorem-receipt",
        "state": "semantic-theorem-receipt-issued-no-evaluation-or-ledger-credit",
        "source": {
            "artifact_file": "r080.ndjson",
            "stream_sha256": STREAM_SHA256,
            "target_definition": TARGET,
            "fact_id": TARGET_FACT,
            "goal_sha256": GOAL_SHA256,
        },
        "candidate_observation_sha256": CANDIDATE_OBSERVATION_SHA256,
        "semantic_theorem_receipt": receipt_json,
        "assurance": {
            "fresh_imports": 2,
            "fixed_plan_reconstructions": 2,
            "search_invocations": 0,
            "target_theorem_submissions": 2,
            "receipt_reissued_exactly": true,
            "axiom_footprint": [],
            "direct_theorem_dependencies": [],
        },
        "authority": {
            "held_out_inspected": false,
            "proof_bodies_inspected": false,
            "semantic_theorem_receipts_issued": 1,
            "evaluation_credit": 0,
            "ledger_writes": 0,
        },
        "limitations": "This independently replays and receipts the fixed accepted candidate. The fact remains open until a separate crash-safe admission transaction succeeds.",
    });
    let digest = canonical_digest(&output)?;
    output["observation_sha256"] = json!(digest);
    let mut rendered = serde_json::to_string_pretty(&output).map_err(|error| error.to_string())?;
    rendered.push('\n');
    fs::write(output_path, rendered).map_err(|error| error.to_string())?;
    println!(
        "AUTOGENESIS_NAT_FIB_CHECKED_RECEIPT_OK|{digest}|receipt={}|fresh_imports=2|search=0|axioms=0|theorem_dependencies=0|evaluation=0|ledger_writes=0",
        receipt.receipt_sha256
    );
    Ok(())
}

fn reconstruct_fixed_candidate(stream: &[u8]) -> Result<(Kernel, NameId), String> {
    let completed = import_ndjson(Cursor::new(stream), ImportLimits::default())
        .map_err(|error| format!("receipt source import failed: {error:?}"))?;
    let (mut kernel, report) = completed.into_parts();
    if report.lean_version != "4.30.0"
        || report.lean_githash != "d024af099ca4bf2c86f649261ebf59565dc8c622"
        || !report.axioms.is_empty()
    {
        return Err("receipt source authority changed".to_owned());
    }
    let target = exact_name(&kernel, TARGET)?;
    let goal = match kernel.environment().get(target) {
        Some(Declaration::Definition { uparams, value, .. }) if uparams.is_empty() => *value,
        _ => return Err("receipt target is not a monomorphic statement definition".to_owned()),
    };
    if canonical_expression_sha256(&kernel, goal)? != GOAL_SHA256 {
        return Err("receipt goal identity changed".to_owned());
    }
    let shape = inspect_fib_shape(&mut kernel)?;
    let (helper, _) = iterator_successor_helper(&mut kernel, &shape)?;
    let proof = recurrence_proof(&mut kernel, goal, &shape, helper)?;
    let theorem = nested_name(&mut kernel, &["Axeyum", "Autogenesis", "NatFibAddTwo"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: theorem,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .map_err(|error| format!("fixed receipt reconstruction rejected: {error:?}"))?;
    Ok((kernel, theorem))
}

fn run_composition_control(kernel: &mut Kernel, shape: &FibShape) -> Result<(), String> {
    let recursor = exact_name(kernel, "Eq.rec")?;
    let recursor_type = kernel
        .environment()
        .get(recursor)
        .ok_or("Eq.rec disappeared")?
        .ty();
    println!("Eq.rec : {}", kernel.render_lean(recursor_type));
    let a_id = u64::MAX - 86_001;
    let b_id = u64::MAX - 86_002;
    let c_id = u64::MAX - 86_003;
    let first_id = u64::MAX - 86_004;
    let second_id = u64::MAX - 86_005;
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);
    let c = kernel.fvar(c_id);
    let first_type = equality(kernel, shape.nat, a, b)?;
    let second_type = equality(kernel, shape.nat, b, c)?;
    let first = kernel.fvar(first_id);
    let second = kernel.fvar(second_id);
    let transitivity = equality_trans(kernel, shape.nat, a, b, c, first, second)?;
    let transitivity = close_lam(kernel, second_id, "hbc", second_type, transitivity);
    let transitivity = close_lam(kernel, first_id, "hab", first_type, transitivity);
    let transitivity = close_lam(kernel, c_id, "c", shape.nat, transitivity);
    let transitivity = close_lam(kernel, b_id, "b", shape.nat, transitivity);
    let transitivity = close_lam(kernel, a_id, "a", shape.nat, transitivity);
    let transitivity_goal = generic_transitivity_goal(kernel, shape)?;
    println!("transitivity proof: {}", kernel.render_lean(transitivity));
    require_inferred_type(
        kernel,
        transitivity,
        transitivity_goal,
        "equality transitivity",
    )?;

    let right_id = u64::MAX - 87_001;
    let proof_id = u64::MAX - 87_002;
    let right = kernel.fvar(right_id);
    let proof_type = equality(kernel, shape.nat, a, right)?;
    let proof = kernel.fvar(proof_id);
    let successor_a = kernel.app(shape.successor, a);
    let successor_right = kernel.app(shape.successor, right);
    let congruence = congr_arg(
        kernel,
        shape.nat,
        shape.nat,
        shape.successor,
        a,
        right,
        proof,
    )?;
    let congruence = close_lam(kernel, proof_id, "h", proof_type, congruence);
    let congruence = close_lam(kernel, right_id, "b", shape.nat, congruence);
    let congruence = close_lam(kernel, a_id, "a", shape.nat, congruence);
    let congruence_goal = {
        let result = equality(kernel, shape.nat, successor_a, successor_right)?;
        let result = close_pi(kernel, proof_id, "h", proof_type, result);
        let result = close_pi(kernel, right_id, "b", shape.nat, result);
        close_pi(kernel, a_id, "a", shape.nat, result)
    };
    require_inferred_type(kernel, congruence, congruence_goal, "successor congruence")?;

    let transitivity_name = nested_name(kernel, &["Axeyum", "Control", "EqTrans"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: transitivity_name,
            uparams: vec![],
            ty: transitivity_goal,
            value: transitivity,
        })
        .map_err(|error| format!("transitivity control rejected: {error:?}"))?;
    let congruence_name = nested_name(kernel, &["Axeyum", "Control", "SuccCongr"]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: congruence_name,
            uparams: vec![],
            ty: congruence_goal,
            value: congruence,
        })
        .map_err(|error| format!("congruence control rejected: {error:?}"))?;
    for theorem in [transitivity_name, congruence_name] {
        if !kernel.axiom_footprint(theorem).is_empty()
            || !kernel.theorem_dependencies(theorem).is_empty()
        {
            return Err("composition control dependency audit failed".to_owned());
        }
    }
    println!(
        "AUTOGENESIS_EQREC_COMPOSITION_CONTROL_OK|eq_rec={}|trans={}|congr={}|target_submissions=0|target_outcomes=0|axioms=0|theorem_dependencies=0",
        canonical_expression_sha256(kernel, recursor_type)?,
        canonical_declaration_sha256(kernel, transitivity_name)?,
        canonical_declaration_sha256(kernel, congruence_name)?,
    );
    Ok(())
}

fn generic_transitivity_goal(kernel: &mut Kernel, shape: &FibShape) -> Result<ExprId, String> {
    let a_id = u64::MAX - 86_001;
    let b_id = u64::MAX - 86_002;
    let c_id = u64::MAX - 86_003;
    let first_id = u64::MAX - 86_004;
    let second_id = u64::MAX - 86_005;
    let a = kernel.fvar(a_id);
    let b = kernel.fvar(b_id);
    let c = kernel.fvar(c_id);
    let first_type = equality(kernel, shape.nat, a, b)?;
    let second_type = equality(kernel, shape.nat, b, c)?;
    let result = equality(kernel, shape.nat, a, c)?;
    let result = close_pi(kernel, second_id, "hbc", second_type, result);
    let result = close_pi(kernel, first_id, "hab", first_type, result);
    let result = close_pi(kernel, c_id, "c", shape.nat, result);
    let result = close_pi(kernel, b_id, "b", shape.nat, result);
    Ok(close_pi(kernel, a_id, "a", shape.nat, result))
}

fn require_inferred_type(
    kernel: &mut Kernel,
    proof: ExprId,
    expected: ExprId,
    label: &str,
) -> Result<(), String> {
    let inferred = kernel.infer(proof).map_err(|error| match error {
        KernelError::TypeMismatch {
            expected: wanted,
            got,
        } => format!(
            "{label} inference failed: expected {}; got {}; theorem goal {}",
            kernel.render_lean(wanted),
            kernel.render_lean(got),
            kernel.render_lean(expected)
        ),
        other => format!(
            "{label} inference failed: {other:?}; theorem goal {}",
            kernel.render_lean(expected)
        ),
    })?;
    if !kernel.def_eq(inferred, expected) {
        return Err(format!(
            "{label} type mismatch; expected {}; inferred {}",
            kernel.render_lean(expected),
            kernel.render_lean(inferred)
        ));
    }
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
    let actual_rhs = kernel.app(shape.snd, transition_iter_n);
    let left_to_actual = equality_trans(
        kernel,
        shape.nat,
        target_arguments[1],
        middle,
        actual_rhs,
        first,
        second,
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
    let add_right = replace_last_argument_function(kernel, target_arguments[2], shape.nat)?;
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
        target_arguments[1],
        actual_rhs,
        target_arguments[2],
        left_to_actual,
        rhs_bridge,
    )?;
    let proof = kernel.abstract_fvars(proof, &[n_id]);
    Ok(kernel.lam(name, domain, proof, info))
}

#[allow(clippy::too_many_lines)]
fn run_recurrence_stage_control(
    kernel: &mut Kernel,
    goal: ExprId,
    shape: &FibShape,
) -> Result<(), String> {
    let (helper, _) = iterator_successor_helper(kernel, shape)?;
    let ExprNode::Pi(name, domain, body, info) = kernel.expr_node(goal).clone() else {
        return Err("stage control target has no pointwise binder".to_owned());
    };
    let n_id = u64::MAX - 88_000;
    let n = kernel.fvar(n_id);
    let target = kernel.instantiate(body, &[n]);
    let (_, target_arguments) = app_spine(kernel, target);
    if target_arguments.len() != 3 {
        return Err("stage control target body is not equality".to_owned());
    }
    let successor_n = kernel.app(shape.successor, n);
    let successor_successor_n = kernel.app(shape.successor, successor_n);
    let iter_n = iterate(kernel, shape, n, shape.initial);
    let iter_succ_n = iterate(kernel, shape, successor_n, shape.initial);
    let iter_successor_successor_n = iterate(kernel, shape, successor_successor_n, shape.initial);

    let helper_n = kernel.app(helper, n);
    let helper_n = kernel.app(helper_n, shape.initial);
    let helper_n_expected = helper_proposition(kernel, shape, n, shape.initial)?;
    let helper_succ = kernel.app(helper, successor_n);
    let helper_succ = kernel.app(helper_succ, shape.initial);
    let helper_succ_expected = helper_proposition(kernel, shape, successor_n, shape.initial)?;

    let fst_function = unary_projection(kernel, shape, shape.fst, "fst");
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
    let middle = kernel.app(shape.snd, iter_succ_n);
    let first_expected = equality(kernel, shape.nat, target_arguments[1], middle)?;

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
    let actual_rhs = kernel.app(shape.snd, transition_iter_n);
    let second_expected = equality(kernel, shape.nat, middle, actual_rhs)?;
    let left_to_actual = equality_trans(
        kernel,
        shape.nat,
        target_arguments[1],
        middle,
        actual_rhs,
        first,
        second,
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
    let fst_helper_expected = equality(kernel, shape.nat, fst_iter_succ_n, fst_transition_iter_n)?;
    let reversed_fst_helper = equality_symm(
        kernel,
        shape.nat,
        fst_iter_succ_n,
        fst_transition_iter_n,
        fst_helper_n,
    )?;
    let reversed_fst_expected =
        equality(kernel, shape.nat, fst_transition_iter_n, fst_iter_succ_n)?;
    let add_right = replace_last_argument_function(kernel, target_arguments[2], shape.nat)?;
    let rhs_bridge = congr_arg(
        kernel,
        shape.nat,
        shape.nat,
        add_right,
        fst_transition_iter_n,
        fst_iter_succ_n,
        reversed_fst_helper,
    )?;
    let rhs_bridge_expected = equality(kernel, shape.nat, actual_rhs, target_arguments[2])?;
    let combined = equality_trans(
        kernel,
        shape.nat,
        target_arguments[1],
        actual_rhs,
        target_arguments[2],
        left_to_actual,
        rhs_bridge,
    )?;

    let stages = [
        ("helper-n", helper_n, helper_n_expected),
        ("helper-succ", helper_succ, helper_succ_expected),
        ("fst-congruence", first, first_expected),
        ("snd-congruence", second, second_expected),
        ("fst-helper", fst_helper_n, fst_helper_expected),
        (
            "fst-helper-symm",
            reversed_fst_helper,
            reversed_fst_expected,
        ),
        ("rhs-bridge", rhs_bridge, rhs_bridge_expected),
        ("transitivity", combined, target),
    ];
    let mut failures = Vec::new();
    for (label, proof, expected) in stages {
        if !report_recurrence_stage(kernel, label, proof, expected, n_id, name, domain, info)? {
            failures.push(label);
        }
    }
    println!(
        "AUTOGENESIS_NAT_FIB_STAGE_CONTROL_OK|failures={}|target_submissions=0|target_outcomes=0|receipts=0|evaluation=0|ledger_writes=0",
        if failures.is_empty() {
            "none".to_owned()
        } else {
            failures.join(",")
        }
    );
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn report_recurrence_stage(
    kernel: &mut Kernel,
    label: &str,
    proof: ExprId,
    expected: ExprId,
    n_id: u64,
    binder: NameId,
    domain: ExprId,
    info: BinderInfo,
) -> Result<bool, String> {
    let closed_proof_body = kernel.abstract_fvars(proof, &[n_id]);
    let closed_proof = kernel.lam(binder, domain, closed_proof_body, info);
    let closed_expected_body = kernel.abstract_fvars(expected, &[n_id]);
    let closed_expected = kernel.pi(binder, domain, closed_expected_body, info);
    let proof_sha256 = canonical_expression_sha256(kernel, closed_proof)?;
    let expected_sha256 = canonical_expression_sha256(kernel, closed_expected)?;
    match kernel.infer(closed_proof) {
        Ok(inferred) => {
            let inferred_sha256 = canonical_expression_sha256(kernel, inferred)?;
            let matches = kernel.def_eq(inferred, closed_expected);
            println!(
                "STAGE|{label}|inferred=1|matches={}|proof={proof_sha256}|expected={expected_sha256}|actual={inferred_sha256}|expected_type={}|actual_type={}",
                usize::from(matches),
                kernel.render_lean(closed_expected),
                kernel.render_lean(inferred),
            );
            Ok(matches)
        }
        Err(KernelError::TypeMismatch {
            expected: wanted,
            got,
        }) => {
            println!(
                "STAGE|{label}|inferred=0|matches=0|proof={proof_sha256}|expected={expected_sha256}|error_expected={}|error_got={}|expected_type={}",
                kernel.render_lean(wanted),
                kernel.render_lean(got),
                kernel.render_lean(closed_expected),
            );
            Ok(false)
        }
        Err(error) => Err(format!("{label} inference failed: {error:?}")),
    }
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

#[allow(clippy::struct_excessive_bools)]
struct Arguments {
    stream: PathBuf,
    output: Option<PathBuf>,
    preflight: bool,
    composition_control: bool,
    stage_control: bool,
    receipt_candidate: Option<PathBuf>,
    native_composition: bool,
    native_coprime_control: bool,
}

fn parse_arguments() -> Result<Arguments, String> {
    let mut stream = None;
    let mut output = None;
    let mut preflight = false;
    let mut composition_control = false;
    let mut stage_control = false;
    let mut receipt_candidate = None;
    let mut native_composition = false;
    let mut native_coprime_control = false;
    let mut arguments = env::args().skip(1);
    while let Some(flag) = arguments.next() {
        if flag == "--preflight" {
            if preflight {
                return Err("duplicate --preflight".to_owned());
            }
            preflight = true;
            continue;
        }
        if flag == "--composition-control" {
            if composition_control {
                return Err("duplicate --composition-control".to_owned());
            }
            composition_control = true;
            continue;
        }
        if flag == "--stage-control" {
            if stage_control {
                return Err("duplicate --stage-control".to_owned());
            }
            stage_control = true;
            continue;
        }
        if flag == "--receipt-candidate" {
            let value = arguments
                .next()
                .ok_or("--receipt-candidate requires a value")?;
            if receipt_candidate.replace(PathBuf::from(value)).is_some() {
                return Err("duplicate --receipt-candidate".to_owned());
            }
            continue;
        }
        if flag == "--native-composition" {
            if native_composition {
                return Err("duplicate --native-composition".to_owned());
            }
            native_composition = true;
            continue;
        }
        if flag == "--native-coprime-control" {
            if native_coprime_control {
                return Err("duplicate --native-coprime-control".to_owned());
            }
            native_coprime_control = true;
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
    if usize::from(preflight)
        + usize::from(composition_control)
        + usize::from(stage_control)
        + usize::from(receipt_candidate.is_some())
        + usize::from(native_composition)
        + usize::from(native_coprime_control)
        > 1
    {
        return Err("preflight modes are mutually exclusive".to_owned());
    }
    Ok(Arguments {
        stream: stream.ok_or("missing --stream")?,
        output,
        preflight,
        composition_control,
        stage_control,
        receipt_candidate,
        native_composition,
        native_coprime_control,
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

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_lean_kernel::build_logic_prelude;

    #[test]
    fn eq_rec_universes_are_motive_then_carrier() {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
        let nat = kernel.const_(logic.nat, vec![]);
        let carrier_level = sort_level(&mut kernel, nat).expect("Nat inhabits a sort");
        let motive_level = kernel.level_zero();

        let correct = kernel.const_(logic.eq_rec, vec![motive_level, carrier_level]);
        let correct_at_nat = kernel.app(correct, nat);
        kernel
            .infer(correct_at_nat)
            .expect("Eq.rec.{0,1} accepts a Type carrier");

        let reversed = kernel.const_(logic.eq_rec, vec![carrier_level, motive_level]);
        let reversed_at_nat = kernel.app(reversed, nat);
        let error = kernel
            .infer(reversed_at_nat)
            .expect_err("Eq.rec.{1,0} requires a Prop carrier");
        assert!(matches!(error, KernelError::TypeMismatch { .. }));
    }

    #[test]
    fn local_nat_equality_transitivity_is_inferred_without_dependencies() {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel).expect("logic prelude builds");
        let nat = kernel.const_(logic.nat, vec![]);
        let a_id = u64::MAX - 90_001;
        let b_id = u64::MAX - 90_002;
        let c_id = u64::MAX - 90_003;
        let first_id = u64::MAX - 90_004;
        let second_id = u64::MAX - 90_005;
        let a = kernel.fvar(a_id);
        let b = kernel.fvar(b_id);
        let c = kernel.fvar(c_id);
        let first_type = equality(&mut kernel, nat, a, b).expect("first equality");
        let second_type = equality(&mut kernel, nat, b, c).expect("second equality");
        let first = kernel.fvar(first_id);
        let second = kernel.fvar(second_id);
        let proof = equality_trans(&mut kernel, nat, a, b, c, first, second)
            .expect("transitivity term builds");
        let proof = close_lam(&mut kernel, second_id, "hbc", second_type, proof);
        let proof = close_lam(&mut kernel, first_id, "hab", first_type, proof);
        let proof = close_lam(&mut kernel, c_id, "c", nat, proof);
        let proof = close_lam(&mut kernel, b_id, "b", nat, proof);
        let proof = close_lam(&mut kernel, a_id, "a", nat, proof);
        let inferred = kernel.infer(proof).expect("transitivity proof infers");

        let result = equality(&mut kernel, nat, a, c).expect("result equality");
        let goal = close_pi(&mut kernel, second_id, "hbc", second_type, result);
        let goal = close_pi(&mut kernel, first_id, "hab", first_type, goal);
        let goal = close_pi(&mut kernel, c_id, "c", nat, goal);
        let goal = close_pi(&mut kernel, b_id, "b", nat, goal);
        let goal = close_pi(&mut kernel, a_id, "a", nat, goal);
        assert!(kernel.def_eq(inferred, goal));
    }
}
