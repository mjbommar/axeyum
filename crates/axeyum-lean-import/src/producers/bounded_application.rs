//! Untrusted bounded application search over an explicit candidate set.
//!
//! This is the connective producer between deterministic lemma retrieval and
//! kernel admission. It never scans the environment, guesses names, or grants
//! applicability: the caller supplies exact declarations, this module builds a
//! small type-directed application closure, and the kernel still has to admit
//! the returned term.

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, LocalContext, LocalDecl, NameId,
};

/// Maximum leading goal binders introduced by the search.
pub const MAX_BINDERS: usize = 8;
/// Maximum application layers explored after introducing goal binders.
pub const MAX_APPLICATION_DEPTH: usize = 8;
/// Maximum distinct terms retained in the bounded closure.
pub const MAX_TERMS: usize = 128;

const FVAR_BASE: u64 = 9_100_000;

/// A candidate term awaiting independent kernel admission.
#[derive(Debug, Clone, Copy)]
pub struct Candidate {
    /// Proposed proof term in the caller's kernel.
    pub proof: ExprId,
    /// Goal binders introduced while constructing the term.
    pub binders_used: usize,
    /// Application-closure rounds consumed before finding the proof.
    pub application_depth: usize,
    /// Distinct candidate terms considered.
    pub terms_considered: usize,
}

/// Typed reason the bounded search declined.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclineReason {
    /// The goal has more leading binders than the fixed budget.
    BinderBudgetExceeded,
    /// No supplied declaration is usable as a zero-universe candidate.
    NoUsableCandidates,
    /// The bounded type-directed closure contains no proof of the goal.
    NoTypedApplication,
}

impl std::fmt::Display for DeclineReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BinderBudgetExceeded => write!(f, "goal exceeds the {MAX_BINDERS}-binder budget"),
            Self::NoUsableCandidates => {
                write!(f, "no supplied zero-universe declaration is usable")
            }
            Self::NoTypedApplication => write!(
                f,
                "no proof found within {MAX_APPLICATION_DEPTH} application layers and {MAX_TERMS} terms"
            ),
        }
    }
}

impl std::error::Error for DeclineReason {}

#[derive(Debug, Clone, Copy)]
struct Binder {
    name: NameId,
    ty: ExprId,
    info: BinderInfo,
    fvar: u64,
}

#[derive(Debug, Clone, Copy)]
struct TypedTerm {
    term: ExprId,
    ty: ExprId,
    depth: usize,
}

fn local_context(binders: &[Binder]) -> LocalContext {
    let mut context = LocalContext::new();
    for binder in binders {
        context.push(LocalDecl {
            fvar: binder.fvar,
            name: binder.name,
            ty: binder.ty,
            info: binder.info,
        });
    }
    context
}

fn close_binders(kernel: &mut Kernel, binders: &[Binder], mut proof: ExprId) -> ExprId {
    for binder in binders.iter().rev() {
        let body = kernel.abstract_fvars(proof, &[binder.fvar]);
        proof = kernel.lam(binder.name, binder.ty, body, binder.info);
    }
    proof
}

fn introduce_binders(
    kernel: &mut Kernel,
    goal: ExprId,
) -> Result<(Vec<Binder>, ExprId), DeclineReason> {
    let mut binders = Vec::new();
    let mut terminal = goal;
    loop {
        let reduced = kernel.whnf(terminal);
        let ExprNode::Pi(name, ty, body, info) = kernel.expr_node(reduced).clone() else {
            return Ok((binders, reduced));
        };
        if binders.len() == MAX_BINDERS {
            return Err(DeclineReason::BinderBudgetExceeded);
        }
        let fvar = FVAR_BASE + binders.len() as u64;
        let value = kernel.fvar(fvar);
        terminal = kernel.instantiate(body, &[value]);
        binders.push(Binder {
            name,
            ty,
            info,
            fvar,
        });
    }
}

/// Search the bounded type-directed application closure of `declarations`.
///
/// The declaration list is the caller's retrieval boundary. The target
/// theorem should not be present; this function does not inspect or infer a
/// target name from a bare goal type.
///
/// # Errors
///
/// Returns a typed decline when the fixed binder/application/term budget does
/// not contain a proof. A decline is not a kernel error and proves nothing.
pub fn propose_bounded_application(
    kernel: &mut Kernel,
    goal: ExprId,
    declarations: &[NameId],
) -> Result<Candidate, DeclineReason> {
    let (binders, terminal) = introduce_binders(kernel, goal)?;

    let mut context = local_context(&binders);
    // Retrieval order is part of the bounded search policy: when the term cap
    // is reached, earlier declarations receive application opportunities
    // first. Preserve the caller's deterministic ranking while removing
    // duplicates stably. Sorting by rendered name here used to erase the
    // ranker's only priority signal and made the 128-term budget alphabetical.
    let mut names = Vec::with_capacity(declarations.len());
    for &name in declarations {
        if !names.contains(&name) {
            names.push(name);
        }
    }
    let mut terms = Vec::new();
    for name in names {
        let Some(declaration) = kernel.environment().get(name) else {
            continue;
        };
        if !declaration.uparams().is_empty()
            || !matches!(
                declaration,
                Declaration::Definition { .. } | Declaration::Theorem { .. }
            )
        {
            continue;
        }
        let term = kernel.const_(name, vec![]);
        let Ok(ty) = kernel.infer_in(term, &mut context) else {
            continue;
        };
        terms.push(TypedTerm { term, ty, depth: 0 });
    }
    if terms.is_empty() {
        return Err(DeclineReason::NoUsableCandidates);
    }
    for binder in &binders {
        terms.push(TypedTerm {
            term: kernel.fvar(binder.fvar),
            ty: binder.ty,
            depth: 0,
        });
    }

    for depth in 0..=MAX_APPLICATION_DEPTH {
        for candidate in &terms {
            if candidate.depth <= depth && kernel.def_eq(candidate.ty, terminal) {
                return Ok(Candidate {
                    proof: close_binders(kernel, &binders, candidate.term),
                    binders_used: binders.len(),
                    application_depth: candidate.depth,
                    terms_considered: terms.len(),
                });
            }
        }
        if depth == MAX_APPLICATION_DEPTH || terms.len() >= MAX_TERMS {
            break;
        }
        let snapshot = terms.clone();
        let mut additions = Vec::new();
        'functions: for function in &snapshot {
            let function_type = kernel.whnf(function.ty);
            let ExprNode::Pi(_, domain, _, _) = kernel.expr_node(function_type).clone() else {
                continue;
            };
            for argument in &snapshot {
                if !kernel.def_eq(argument.ty, domain) {
                    continue;
                }
                let term = kernel.app(function.term, argument.term);
                if terms.iter().any(|known| known.term == term)
                    || additions.iter().any(|known: &TypedTerm| known.term == term)
                {
                    continue;
                }
                let Ok(ty) = kernel.infer_in(term, &mut context) else {
                    continue;
                };
                additions.push(TypedTerm {
                    term,
                    ty,
                    depth: depth + 1,
                });
                if terms.len() + additions.len() >= MAX_TERMS {
                    break 'functions;
                }
            }
        }
        if additions.is_empty() {
            break;
        }
        terms.extend(additions);
    }
    Err(DeclineReason::NoTypedApplication)
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_lean_kernel::{Kernel, build_nat_prelude};

    #[test]
    fn composes_fibonacci_monotonicity_from_retrieved_candidates() {
        let mut kernel = Kernel::new();
        let p = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
        let goal = kernel
            .environment()
            .get(p.fib_mono)
            .expect("fib_mono must exist")
            .ty();
        let candidate = propose_bounded_application(
            &mut kernel,
            goal,
            &[p.monotone_of_le_succ, p.fib, p.fib_le_succ],
        )
        .expect("bounded application must find the generic composition");
        let root = kernel.anon();
        let name = kernel.name_str(root, "BoundedApplicationFibMono");
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty: goal,
                value: candidate.proof,
            })
            .expect("kernel must independently accept the candidate");
        assert!(kernel.axiom_footprint(name).is_empty());
        let dependencies = kernel.theorem_dependencies(name);
        assert!(dependencies.contains(&p.monotone_of_le_succ));
        assert!(dependencies.contains(&p.fib_le_succ));
        assert!(!dependencies.contains(&p.fib_mono));
    }

    #[test]
    fn declines_when_the_adjacent_step_candidate_is_missing() {
        let mut kernel = Kernel::new();
        let p = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
        let goal = kernel
            .environment()
            .get(p.fib_mono)
            .expect("fib_mono must exist")
            .ty();
        assert_eq!(
            propose_bounded_application(&mut kernel, goal, &[p.monotone_of_le_succ, p.fib])
                .expect_err("missing adjacent-step evidence must decline"),
            DeclineReason::NoTypedApplication
        );
    }

    #[test]
    fn ranked_input_order_is_stable_under_duplicate_candidates() {
        let mut kernel = Kernel::new();
        let p = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
        let goal = kernel
            .environment()
            .get(p.fib_mono)
            .expect("fib_mono must exist")
            .ty();
        let baseline = propose_bounded_application(
            &mut kernel,
            goal,
            &[p.monotone_of_le_succ, p.fib, p.fib_le_succ],
        )
        .expect("ranked candidates must close");
        let repeated = propose_bounded_application(
            &mut kernel,
            goal,
            &[
                p.monotone_of_le_succ,
                p.monotone_of_le_succ,
                p.fib,
                p.fib_le_succ,
                p.fib,
            ],
        )
        .expect("stable duplicate removal must preserve the same search");
        assert_eq!(baseline.proof, repeated.proof);
        assert_eq!(baseline.application_depth, repeated.application_depth);
        assert_eq!(baseline.terms_considered, repeated.terms_considered);
    }

    #[test]
    fn composes_modulus_zero_from_divisibility_reflexivity() {
        let mut kernel = Kernel::new();
        let p = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
        let nat = kernel.const_(p.nat, vec![]);
        let zero = kernel.const_(p.zero, vec![]);
        let n_fv = 9_200_000_u64;
        let n = kernel.fvar(n_fv);
        let relation = kernel.const_(p.mod_eq, vec![]);
        let at_modulus = kernel.app(relation, n);
        let at_value = kernel.app(at_modulus, n);
        let body = kernel.app(at_value, zero);
        let anon = kernel.anon();
        let abstracted = kernel.abstract_fvars(body, &[n_fv]);
        let goal = kernel.pi(anon, nat, abstracted, BinderInfo::Default);
        let candidate =
            propose_bounded_application(&mut kernel, goal, &[p.mod_eq_zero_of_dvd, p.dvd_refl])
                .expect("typed application closure must compose the divisibility witness");
        let name = kernel.name_str(anon, "BoundedApplicationModulusZero");
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams: vec![],
                ty: goal,
                value: candidate.proof,
            })
            .expect("kernel must independently accept the relation candidate");
        assert!(kernel.axiom_footprint(name).is_empty());
        let dependencies = kernel.theorem_dependencies(name);
        assert!(dependencies.contains(&p.mod_eq_zero_of_dvd));
        assert!(dependencies.contains(&p.dvd_refl));
    }
}
