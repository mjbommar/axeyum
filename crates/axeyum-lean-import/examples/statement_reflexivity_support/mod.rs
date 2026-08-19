//! Untrusted, bounded reflexivity proposal logic shared with adversarial tests.

use axeyum_lean_kernel::{BinderInfo, ExprId, ExprNode, Kernel, NameId};

pub const MAX_BINDERS: usize = 8;
pub const MAX_CONSTRUCTED_NODES: usize = 16;

#[derive(Debug)]
pub struct Candidate {
    pub proof: ExprId,
    pub binders: usize,
    pub constructed_nodes: usize,
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
        .filter_map(|(name, _)| {
            (kernel.display_name(*name).to_string() == rendered).then_some(*name)
        })
        .collect();
    match matches.as_slice() {
        [name] => Ok(*name),
        _ => Err(format!(
            "required declaration {rendered:?} occurs {} times",
            matches.len()
        )),
    }
}

pub fn propose_reflexivity(kernel: &mut Kernel, goal: ExprId) -> Result<Candidate, String> {
    let mut binders: Vec<(NameId, ExprId, BinderInfo)> = Vec::new();
    let mut cursor = goal;
    while let ExprNode::Pi(name, ty, body, info) = kernel.expr_node(cursor) {
        if binders.len() == MAX_BINDERS {
            return Err(format!("binder budget exceeded: maximum {MAX_BINDERS}"));
        }
        binders.push((*name, *ty, *info));
        cursor = *body;
    }

    let (head, arguments) = app_spine(kernel, cursor);
    let ExprNode::Const(eq_name, levels) = kernel.expr_node(head) else {
        return Err("terminal goal is not constant-headed equality".to_owned());
    };
    if kernel.display_name(*eq_name).to_string() != "Eq" || arguments.len() != 3 {
        return Err("terminal goal is not an exact Eq application".to_owned());
    }
    let levels = levels.clone();
    let eq_refl_name = exact_name(kernel, "Eq.refl")?;
    let mut proof = kernel.const_(eq_refl_name, levels);
    proof = kernel.app(proof, arguments[0]);
    proof = kernel.app(proof, arguments[1]);
    for (name, ty, info) in binders.iter().rev() {
        proof = kernel.lam(*name, *ty, proof, *info);
    }
    let constructed_nodes = 3 + binders.len();
    if constructed_nodes > MAX_CONSTRUCTED_NODES {
        return Err(format!(
            "construction budget exceeded: {constructed_nodes} > {MAX_CONSTRUCTED_NODES}"
        ));
    }
    Ok(Candidate {
        proof,
        binders: binders.len(),
        constructed_nodes,
    })
}
