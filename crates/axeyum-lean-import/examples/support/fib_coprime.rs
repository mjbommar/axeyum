//! Shared bounded Fibonacci-neighbor coprimality proof-term constructor.

use axeyum_lean_kernel::{BinderInfo, Declaration, ExprId, ExprNode, Kernel, LevelId, NameId};

pub(crate) fn admit(
    kernel: &mut Kernel,
    target: NameId,
    goal: ExprId,
    recurrence_name: &str,
) -> Result<(NameId, ExprId, ExprId), String> {
    admit_with_mode(kernel, target, goal, recurrence_name, false)
}

pub(crate) fn admit_target_native(
    kernel: &mut Kernel,
    target: NameId,
    goal: ExprId,
    recurrence_name: &str,
) -> Result<(NameId, ExprId, ExprId), String> {
    admit_with_mode(kernel, target, goal, recurrence_name, true)
}

fn admit_with_mode(
    kernel: &mut Kernel,
    target: NameId,
    goal: ExprId,
    recurrence_name: &str,
    target_native: bool,
) -> Result<(NameId, ExprId, ExprId), String> {
    let proof = proof(kernel, goal, recurrence_name, target_native)?;
    require_inferred_type(kernel, proof, goal, "Fibonacci coprimality")?;
    kernel
        .add_declaration(Declaration::Theorem {
            name: target,
            uparams: vec![],
            ty: goal,
            value: proof,
        })
        .map_err(|error| format!("Fibonacci coprimality rejected: {error:?}"))?;
    Ok((target, goal, proof))
}

#[allow(clippy::too_many_lines)]
fn proof(
    kernel: &mut Kernel,
    goal: ExprId,
    recurrence_name: &str,
    target_native: bool,
) -> Result<ExprId, String> {
    let ExprNode::Pi(name, nat, body, info) = kernel.expr_node(goal).clone() else {
        return Err("Fibonacci coprimality goal has no Nat binder".to_owned());
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
    let gcd_zero_left = if target_native {
        "Axeyum.Autogenesis.nat_gcd_zero_left"
    } else {
        "Nat.gcd_zero_left"
    };
    let base = apply_named(kernel, gcd_zero_left, &[fib_one])?;
    let base_goal = kernel.instantiate(body, &[zero]);
    let base_type = kernel
        .infer(base)
        .map_err(|error| format!("Fibonacci coprimality base inference failed: {error:?}"))?;
    if !kernel.def_eq(base_type, base_goal) {
        return Err(format!(
            "Fibonacci coprimality base mismatch: expected {}; inferred {}",
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

    let gcd_dvd_left = if target_native {
        "Axeyum.Autogenesis.gcdDvdLeftOfficialV1"
    } else {
        "Nat.gcd_dvd_left"
    };
    let gcd_dvd_right = if target_native {
        "Axeyum.Autogenesis.gcdDvdRightOfficialV1"
    } else {
        "Nat.gcd_dvd_right"
    };
    let common_divides_b = apply_named(kernel, gcd_dvd_left, &[b, sum_ba])?;
    let common_divides_sum = apply_named(kernel, gcd_dvd_right, &[b, sum_ba])?;
    let common_divides_a = if target_native {
        apply_named(
            kernel,
            "Axeyum.Autogenesis.dvdAddCancelAllNatClosedV1",
            &[common, b, a, common_divides_b, common_divides_sum],
        )?
    } else {
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
        kernel.app(sum_to_a, common_divides_sum)
    };
    let dvd_gcd = if target_native {
        "Axeyum.Autogenesis.dvdGcdOfficialV1"
    } else {
        "Nat.dvd_gcd"
    };
    let common_divides_previous_gcd = apply_named(
        kernel,
        dvd_gcd,
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
    let eq_one = if target_native {
        "Axeyum.Autogenesis.eqOneOfDvdOneOfficialV1"
    } else {
        "Nat.eq_one_of_dvd_one"
    };
    let common_is_one = apply_named(kernel, eq_one, &[common, common_divides_one])?;
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
        .map_err(|error| format!("Fibonacci coprimality induction inference failed: {error:?}"))?;
    if !kernel.def_eq(inferred, goal) {
        return Err(format!(
            "Fibonacci coprimality induction mismatch: expected {}; inferred {}",
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

#[allow(clippy::too_many_arguments)]
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

fn nested_name(kernel: &mut Kernel, parts: &[&str]) -> NameId {
    let mut name = kernel.anon();
    for part in parts {
        name = kernel.name_str(name, *part);
    }
    name
}

fn exact_name(kernel: &Kernel, rendered: &str) -> Result<NameId, String> {
    let matches = kernel
        .environment()
        .iter()
        .filter_map(|(&name, _)| {
            (kernel.display_name(name).to_string() == rendered).then_some(name)
        })
        .collect::<Vec<_>>();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(format!("{rendered} occurs {} times", matches.len())),
    }
}

fn require_inferred_type(
    kernel: &mut Kernel,
    proof: ExprId,
    expected: ExprId,
    label: &str,
) -> Result<(), String> {
    let inferred = kernel
        .infer(proof)
        .map_err(|error| format!("{label} inference failed: {error:?}"))?;
    if !kernel.def_eq(inferred, expected) {
        return Err(format!(
            "{label} mismatch: expected {}; inferred {}",
            kernel.render_lean(expected),
            kernel.render_lean(inferred)
        ));
    }
    Ok(())
}
