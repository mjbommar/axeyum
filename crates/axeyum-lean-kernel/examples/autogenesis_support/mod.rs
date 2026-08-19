//! Shared, fixture-local interpreters for Autogenesis proposal artifacts.
//!
//! This is deliberately below a public proof-plan IR: it exercises one small
//! grammar without adding a crate API or claiming the Phase-3 design decision.

use std::collections::BTreeSet;
use std::fs;
use std::path::Path;

use axeyum_lean_kernel::{ExprId, ExprNode, Kernel, NameId, NatDev, NatOps, NatPrelude};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum InductionStep {
    ExactHypothesis,
    SuccessorCongruenceHypothesis,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InductionPlan {
    pub rank: usize,
    pub target_binder: usize,
    pub step: InductionStep,
}

pub fn parse_induction_plans(
    path: &Path,
    bundle_sha256: &str,
    catalog_sha256: &str,
    phase: &str,
) -> Result<Vec<InductionPlan>, String> {
    let text = fs::read_to_string(path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let mut lines = text.lines();
    let header = lines.next().ok_or("induction plan file is empty")?;
    let header_fields: Vec<&str> = header.split('\t').collect();
    if header_fields
        != [
            "AXEYUM_INDUCTION_PLANS_V1",
            bundle_sha256,
            catalog_sha256,
            phase,
        ]
    {
        return Err(
            "induction plan header does not match the registered bundle/catalog/phase".to_owned(),
        );
    }
    let mut plans = Vec::new();
    let mut identities = BTreeSet::new();
    for (index, line) in lines.enumerate() {
        let fields: Vec<&str> = line.split('\t').collect();
        if fields.len() != 4 {
            return Err(format!(
                "induction plan row {} has {} fields",
                index + 1,
                fields.len()
            ));
        }
        let rank = fields[0]
            .parse::<usize>()
            .map_err(|_| format!("induction plan row {} has invalid rank", index + 1))?;
        if rank != index + 1 {
            return Err(format!(
                "induction plan rank {rank} is not the expected {}",
                index + 1
            ));
        }
        let target_binder = fields[1]
            .parse::<usize>()
            .map_err(|_| format!("induction plan rank {rank} has invalid target binder"))?;
        if fields[2] != "definitional-reflexivity" {
            return Err(format!(
                "induction plan rank {rank} has unregistered base operation {:?}",
                fields[2]
            ));
        }
        let step = match fields[3] {
            "exact-induction-hypothesis" => InductionStep::ExactHypothesis,
            "successor-congruence-induction-hypothesis" => {
                InductionStep::SuccessorCongruenceHypothesis
            }
            other => {
                return Err(format!(
                    "induction plan rank {rank} has unregistered step operation {other:?}"
                ));
            }
        };
        if !identities.insert((target_binder, step)) {
            return Err(format!("induction plan rank {rank} is a duplicate"));
        }
        plans.push(InductionPlan {
            rank,
            target_binder,
            step,
        });
    }
    if plans.is_empty() {
        return Err("induction plan file contains no proposals".to_owned());
    }
    Ok(plans)
}

pub fn intern_dotted(kernel: &mut Kernel, rendered: &str) -> Result<NameId, String> {
    if rendered.is_empty() || rendered.split('.').any(str::is_empty) {
        return Err(format!("invalid dotted declaration name {rendered:?}"));
    }
    let mut name = kernel.anon();
    for component in rendered.split('.') {
        name = kernel.name_str(name, component);
    }
    Ok(name)
}

#[derive(Debug, Clone, Copy)]
struct UnaryNatEquality {
    body: ExprId,
    left: ExprId,
    right: ExprId,
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

fn unary_nat_equality(
    kernel: &mut Kernel,
    prelude: &NatPrelude,
    target: NameId,
) -> Result<UnaryNatEquality, String> {
    let target_type = kernel
        .environment()
        .get(target)
        .ok_or("target declaration is absent")?
        .ty();
    let (domain, body) = match kernel.expr_node(target_type) {
        ExprNode::Pi(_, domain, body, _) => (*domain, *body),
        _ => return Err("induction fixture currently requires one Nat binder".to_owned()),
    };
    if matches!(kernel.expr_node(body), ExprNode::Pi(..)) {
        return Err("induction fixture currently requires exactly one binder".to_owned());
    }
    let nat = kernel.const_(prelude.nat, vec![]);
    if !kernel.def_eq(domain, nat) {
        return Err("induction target binder is not Nat".to_owned());
    }
    let (head, arguments) = app_spine(kernel, body);
    let is_eq =
        matches!(kernel.expr_node(head), ExprNode::Const(name, _) if *name == prelude.logic.eq);
    if !is_eq || arguments.len() != 3 || !kernel.def_eq(arguments[0], nat) {
        return Err(
            "induction fixture currently requires Nat equality after the binder".to_owned(),
        );
    }
    Ok(UnaryNatEquality {
        body,
        left: arguments[1],
        right: arguments[2],
    })
}

fn try_induction_plan(
    kernel: &mut Kernel,
    prelude: &NatPrelude,
    shape: UnaryNatEquality,
    candidate: NameId,
    plan: InductionPlan,
) -> Result<(), String> {
    if plan.target_binder != 0 {
        return Err("induction target binder is outside the one-binder goal".to_owned());
    }
    let mut development = NatDev::new(kernel, *prelude);
    development
        .theorem(candidate, 1, &|d, variables| {
            let value = variables[0];
            let motive = |d: &mut NatDev<'_>, item| d.kernel().instantiate(shape.body, &[item]);
            let statement = motive(d, value);
            let proof = d.induct(
                &motive,
                &|d| {
                    let zero = d.zero();
                    let left = d.kernel().instantiate(shape.left, &[zero]);
                    d.refl(left)
                },
                &|d, item, hypothesis| match plan.step {
                    InductionStep::ExactHypothesis => hypothesis,
                    InductionStep::SuccessorCongruenceHypothesis => {
                        let left = d.kernel().instantiate(shape.left, &[item]);
                        let right = d.kernel().instantiate(shape.right, &[item]);
                        d.congr(left, right, hypothesis, &|d, expression| d.succ(expression))
                    }
                },
                value,
            );
            (statement, proof)
        })
        .map(|_| ())
        .map_err(|error| development.explain(&error))
}

fn candidate_is_creditable(
    kernel: &mut Kernel,
    candidate: NameId,
    target: NameId,
    denied: &BTreeSet<String>,
) -> Result<bool, String> {
    let closure: BTreeSet<String> = kernel
        .declaration_dependency_closure(candidate)
        .into_iter()
        .map(|name| kernel.display_name(name).to_string())
        .collect();
    if !denied.is_disjoint(&closure) || !kernel.axiom_footprint(candidate).is_empty() {
        return Ok(false);
    }
    let candidate_type = kernel
        .environment()
        .get(candidate)
        .ok_or("candidate disappeared after admission")?
        .ty();
    let target_type = kernel
        .environment()
        .get(target)
        .ok_or("target disappeared during admission")?
        .ty();
    Ok(kernel.def_eq(candidate_type, target_type)
        && kernel.render_lean(candidate_type) == kernel.render_lean(target_type))
}

pub struct InductionSearch {
    pub kernel: Kernel,
    pub candidate: Option<NameId>,
    pub attempted: usize,
    pub accepted_rank: Option<usize>,
}

pub fn search_induction(
    kernel: Kernel,
    prelude: &NatPrelude,
    target: NameId,
    candidate_name: &str,
    plans: &[InductionPlan],
    budget: usize,
) -> Result<InductionSearch, String> {
    if budget == 0 {
        return Err("induction budget must be positive".to_owned());
    }
    let denied = BTreeSet::from(["Nat.mul_one".to_owned(), "Nat.zero_add".to_owned()]);
    let mut shape_kernel = kernel.clone();
    let shape = unary_nat_equality(&mut shape_kernel, prelude, target)?;
    let mut attempted = 0;
    for plan in plans.iter().take(budget) {
        attempted += 1;
        let mut trial = kernel.clone();
        let trial_name =
            intern_dotted(&mut trial, &format!("{candidate_name}.trial{}", plan.rank))?;
        if try_induction_plan(&mut trial, prelude, shape, trial_name, *plan).is_err()
            || !candidate_is_creditable(&mut trial, trial_name, target, &denied)?
        {
            continue;
        }

        let mut accepted = kernel.clone();
        let candidate = intern_dotted(&mut accepted, candidate_name)?;
        try_induction_plan(&mut accepted, prelude, shape, candidate, *plan)?;
        if !candidate_is_creditable(&mut accepted, candidate, target, &denied)? {
            return Err(
                "trial passed but exact induction candidate failed the same audit".to_owned(),
            );
        }
        return Ok(InductionSearch {
            kernel: accepted,
            candidate: Some(candidate),
            attempted,
            accepted_rank: Some(plan.rank),
        });
    }
    Ok(InductionSearch {
        kernel,
        candidate: None,
        attempted,
        accepted_rank: None,
    })
}

#[cfg(test)]
mod tests {
    use super::{InductionPlan, InductionStep, search_induction};
    use axeyum_lean_kernel::{Kernel, build_nat_prelude};

    fn plans() -> [InductionPlan; 2] {
        [
            InductionPlan {
                rank: 1,
                target_binder: 0,
                step: InductionStep::ExactHypothesis,
            },
            InductionPlan {
                rank: 2,
                target_binder: 0,
                step: InductionStep::SuccessorCongruenceHypothesis,
            },
        ]
    }

    #[test]
    fn structural_search_is_not_specific_to_zero_add() {
        let mut kernel = Kernel::new();
        let prelude = build_nat_prelude(&mut kernel).expect("Nat prelude");
        let result = search_induction(
            kernel,
            &prelude,
            prelude.add_zero,
            "Autogenesis.Control.add_zero",
            &plans(),
            2,
        )
        .expect("search runs");
        assert!(result.candidate.is_some());
        assert_eq!(result.accepted_rank, Some(2));
    }

    #[test]
    fn exact_hypothesis_step_remains_a_real_alternative() {
        let mut kernel = Kernel::new();
        let prelude = build_nat_prelude(&mut kernel).expect("Nat prelude");
        let result = search_induction(
            kernel,
            &prelude,
            prelude.zero_mul,
            "Autogenesis.Control.zero_mul",
            &plans(),
            2,
        )
        .expect("search runs");
        assert!(result.candidate.is_some());
        assert_eq!(result.accepted_rank, Some(1));
    }
}
