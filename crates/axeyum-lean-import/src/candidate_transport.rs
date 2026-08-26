//! Checked transport of one native theorem candidate into another kernel.
//!
//! Retrieval produces declaration names, but a name is not an executable
//! premise until the corresponding theorem has been checked in the goal's
//! kernel. This module turns exactly one retrieved source root into such a
//! premise. Existing compatible target theorems are reused; missing roots go
//! through theorem composition. In both cases the candidate must be a theorem
//! with an empty kernel-measured axiom footprint.

use axeyum_lean_kernel::{Declaration, Kernel, NameId};

use crate::{
    CheckedTheoremCompositionError, CheckedTheoremCompositionReceipt, ReusedDeclarationReceipt,
    checked_reused_declaration_compatibility, compose_checked_theorem_slice,
};

/// How the checked candidate became available in the target kernel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CandidateTransportReceipt {
    /// A same-name target theorem already existed and passed compatibility.
    Reused(ReusedDeclarationReceipt),
    /// The source theorem closure was independently admitted into a clone.
    Added(CheckedTheoremCompositionReceipt),
}

/// One target kernel in which the requested candidate is now executable.
#[derive(Debug)]
pub struct CompletedCandidateTransport {
    kernel: Kernel,
    candidate: NameId,
    receipt: CandidateTransportReceipt,
}

impl CompletedCandidateTransport {
    /// Borrow the independently checked completed target.
    #[must_use]
    pub fn kernel(&self) -> &Kernel {
        &self.kernel
    }

    /// Candidate handle belonging to the completed target.
    #[must_use]
    pub fn candidate(&self) -> NameId {
        self.candidate
    }

    /// Checked reuse or admission evidence.
    #[must_use]
    pub fn receipt(&self) -> &CandidateTransportReceipt {
        &self.receipt
    }

    /// Transfer ownership while preserving the matching handle and receipt.
    #[must_use]
    pub fn into_parts(self) -> (Kernel, NameId, CandidateTransportReceipt) {
        (self.kernel, self.candidate, self.receipt)
    }
}

/// Make one exact source theorem root executable in a private target clone.
///
/// This function never searches for a theorem and never changes either input.
/// The caller supplies one exact root selected elsewhere. A same-name target
/// declaration is accepted only after the existing composition compatibility
/// check, theorem-kind check, and empty-footprint check. A missing declaration
/// goes through [`compose_checked_theorem_slice`].
///
/// # Errors
///
/// Returns the existing typed theorem-composition error when the root is
/// absent, incompatible, unsupported, assumption-bearing, or cannot be
/// independently admitted.
pub fn transport_checked_theorem_candidate(
    source: &Kernel,
    target: &Kernel,
    root: &str,
) -> Result<CompletedCandidateTransport, CheckedTheoremCompositionError> {
    let target_candidate = exact_name(target, root);
    let (kernel, receipt) = if let Some(candidate) = target_candidate {
        let reused = checked_reused_declaration_compatibility(source, target, root)?;
        require_axiom_free_theorem(target, candidate, root)?;
        (target.clone(), CandidateTransportReceipt::Reused(reused))
    } else {
        let completed = compose_checked_theorem_slice(source, target, &[root])?;
        let receipt = completed.receipt().clone();
        let (kernel, _) = completed.into_parts();
        (kernel, CandidateTransportReceipt::Added(receipt))
    };
    let candidate = exact_name(&kernel, root).ok_or_else(|| {
        CheckedTheoremCompositionError::Identity(format!(
            "transported theorem is absent from completed target: {root}"
        ))
    })?;
    require_axiom_free_theorem(&kernel, candidate, root)?;
    Ok(CompletedCandidateTransport {
        kernel,
        candidate,
        receipt,
    })
}

fn exact_name(kernel: &Kernel, expected: &str) -> Option<NameId> {
    let mut matches = kernel.environment().iter().filter_map(|(&name, _)| {
        (kernel.display_name(name).to_string() == expected).then_some(name)
    });
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn require_axiom_free_theorem(
    kernel: &Kernel,
    candidate: NameId,
    rendered: &str,
) -> Result<(), CheckedTheoremCompositionError> {
    if !matches!(
        kernel.environment().get(candidate),
        Some(Declaration::Theorem { .. })
    ) {
        return Err(CheckedTheoremCompositionError::RootIsNotTheorem(
            rendered.to_owned(),
        ));
    }
    let footprint = kernel.axiom_footprint(candidate);
    if !footprint.is_empty() {
        return Err(
            CheckedTheoremCompositionError::TargetTheoremLeafAxiomFootprint {
                name: rendered.to_owned(),
                footprint: footprint
                    .into_iter()
                    .map(|name| kernel.display_name(name).to_string())
                    .collect(),
            },
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_lean_kernel::{Kernel, build_logic_prelude, build_nat_prelude};

    #[test]
    fn transports_missing_native_theorem_without_axioms() {
        let mut source = Kernel::new();
        let nat = build_nat_prelude(&mut source).expect("source Nat prelude must build");
        let mut target = Kernel::new();
        build_logic_prelude(&mut target).expect("target logic prelude must build");

        let completed =
            transport_checked_theorem_candidate(&source, &target, "Nat.mod_eq_add_left")
                .expect("candidate closure must transport");
        assert!(matches!(
            completed.receipt(),
            CandidateTransportReceipt::Added(_)
        ));
        assert!(
            completed
                .kernel()
                .axiom_footprint(completed.candidate())
                .is_empty()
        );
        assert_eq!(
            completed
                .kernel()
                .display_name(completed.candidate())
                .to_string(),
            source.display_name(nat.mod_eq_add_left).to_string()
        );
    }

    #[test]
    fn validates_and_reuses_existing_theorem() {
        let mut source = Kernel::new();
        build_nat_prelude(&mut source).expect("source Nat prelude must build");
        let target = source.clone();
        let before = target.environment().len();

        let completed = transport_checked_theorem_candidate(&source, &target, "Nat.add_assoc")
            .expect("same theorem must reuse");
        assert!(matches!(
            completed.receipt(),
            CandidateTransportReceipt::Reused(_)
        ));
        assert_eq!(completed.kernel().environment().len(), before);
    }
}
