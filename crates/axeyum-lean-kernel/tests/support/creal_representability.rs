//! **What pinned Lean's kernel will accept as the kind this kernel declares
//! it**, decided by inference over the checked environment rather than by a
//! list.
//!
//! # Why this exists
//!
//! `Lean.Environment.addDeclCore` refuses a `theorem` whose type does not live
//! in `Prop` — such a thing must be a `def`. This kernel has no such rule, and
//! it uses the freedom deliberately: `CReal.UniformConvergesOn` is `Type`-valued
//! so a convergence *rate* is data (`Exists.rec` cannot eliminate into `Type`),
//! and `CReal.weierstrassMTest` concludes in it. So the two kernels disagree
//! about what may be called a theorem, and a carrier-wide replay has to say so
//! rather than discover it as an opaque rejection at line 296,827 of a stream.
//!
//! Measured 2026-08-30 by `real_lean_replay_census` (L0/S4) and again here: the
//! whole `creal` carrier is 2,045 declarations, of which 73 are outside that
//! boundary — 48 `Theorem`s whose type is not a proposition, and 25 whose
//! dependency closure reaches one.
//!
//! # Two callers, one classifier
//!
//! `real_lean_replay_census` carries its own copy of this classification
//! (landed first, on 2026-08-30) and `real_lean_creal_carrier_kernel_replay`
//! includes this module. Two implementations of one rule that must stay in
//! sync is exactly what this repository warns about, so this file is the home
//! the census can adopt with a one-line `#[path]` include when its owner next
//! touches it; it is deliberately a superset of what either suite needs.
//!
//! Nothing here reads a name list: the population is `kernel.environment()`,
//! and the verdicts come from `Kernel::infer` and
//! `Kernel::declaration_dependency_closure`. An "every X" test that iterates
//! its own list measures the maintainer's memory.
#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};

use axeyum_lean_kernel::{Declaration, ExprId, ExprNode, Kernel, LevelNode, NameId};

/// Why a declaration this kernel admitted cannot be handed to Lean's kernel as
/// what this kernel calls it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Representability {
    /// The wire format carries it and Lean's kernel will accept its kind.
    Representable,
    /// **This kernel admits `Theorem`s whose type is not a proposition; Lean's
    /// kernel does not.** Not a wire-format limitation and not an export bug:
    /// a measured disagreement between two kernels about what may be called a
    /// theorem. The affected declarations are deliberate — see
    /// `creal/uniform_convergence.rs`.
    TheoremTypeNotProp,
    /// Its dependency closure contains a non-representable declaration, so it
    /// cannot be exported either. The blocker is named rather than the reason
    /// repeated, because the two are different findings.
    BlockedBy(String),
}

impl Representability {
    /// The wire word this reason is reported under. One token per class, so a
    /// residue whose reason is not one of these is visibly untyped.
    #[must_use]
    pub fn reason(&self) -> &'static str {
        match self {
            Representability::Representable => "representable",
            Representability::TheoremTypeNotProp => "theorem-type-not-prop",
            Representability::BlockedBy(_) => "blocked-by-dependency",
        }
    }
}

/// Does `ty` live in `Prop`?
///
/// Read from the kernel by inference, never from a name or a doc comment.
#[must_use]
pub fn is_a_proposition(kernel: &mut Kernel, ty: ExprId) -> bool {
    let Ok(sort) = kernel.infer(ty) else {
        return false;
    };
    let sort = kernel.whnf(sort);
    let level = match kernel.expr_node(sort) {
        ExprNode::Sort(level) => *level,
        _ => return false,
    };
    matches!(kernel.level_node(level), LevelNode::Zero)
}

/// A complete census of the checked environment.
#[derive(Debug, Clone)]
pub struct Census {
    /// Every declaration, by display name, with its verdict.
    pub verdicts: BTreeMap<String, Representability>,
}

impl Census {
    /// Every declaration Lean's kernel will accept as the kind we declare it.
    #[must_use]
    pub fn representable(&self) -> BTreeSet<String> {
        self.verdicts
            .iter()
            .filter(|(_, verdict)| **verdict == Representability::Representable)
            .map(|(name, _)| name.clone())
            .collect()
    }

    /// The `Theorem`s whose type is not a proposition.
    #[must_use]
    pub fn theorem_type_not_prop(&self) -> BTreeSet<String> {
        self.verdicts
            .iter()
            .filter(|(_, verdict)| **verdict == Representability::TheoremTypeNotProp)
            .map(|(name, _)| name.clone())
            .collect()
    }

    /// The declarations blocked by depending on one of those, each with its
    /// blocker.
    #[must_use]
    pub fn blocked(&self) -> BTreeMap<String, String> {
        self.verdicts
            .iter()
            .filter_map(|(name, verdict)| match verdict {
                Representability::BlockedBy(blocker) => Some((name.clone(), blocker.clone())),
                _ => None,
            })
            .collect()
    }

    /// Everything Lean's kernel will not take as declared, in name order.
    #[must_use]
    pub fn residue(&self) -> BTreeMap<String, Representability> {
        self.verdicts
            .iter()
            .filter(|(_, verdict)| **verdict != Representability::Representable)
            .map(|(name, verdict)| (name.clone(), verdict.clone()))
            .collect()
    }

    /// The population size.
    #[must_use]
    pub fn population(&self) -> usize {
        self.verdicts.len()
    }
}

/// Classify every declaration in the checked environment.
///
/// The population is `kernel.environment()`, so this is a complete census and
/// not a sample.
#[must_use]
pub fn classify(kernel: &mut Kernel) -> Census {
    let declarations: Vec<(NameId, String, Option<ExprId>)> = kernel
        .environment()
        .iter()
        .map(|(name, decl)| {
            let theorem_type = match decl {
                Declaration::Theorem { ty, .. } => Some(*ty),
                _ => None,
            };
            (*name, kernel.display_name(*name).to_string(), theorem_type)
        })
        .collect();

    // Pass 1: the declarations that are themselves non-representable.
    let mut verdicts: BTreeMap<String, Representability> = BTreeMap::new();
    let mut bad_names: BTreeSet<String> = BTreeSet::new();
    for (_, display, theorem_type) in &declarations {
        if let Some(ty) = *theorem_type
            && !is_a_proposition(kernel, ty)
        {
            verdicts.insert(display.clone(), Representability::TheoremTypeNotProp);
            bad_names.insert(display.clone());
        }
    }

    // Pass 2: everything whose closure reaches one of those.
    for (id, display, _) in &declarations {
        if verdicts.contains_key(display) {
            continue;
        }
        let blocker = kernel
            .declaration_dependency_closure(*id)
            .into_iter()
            .map(|dep| kernel.display_name(dep).to_string())
            .find(|dep| bad_names.contains(dep));
        verdicts.insert(
            display.clone(),
            match blocker {
                Some(name) => Representability::BlockedBy(name),
                None => Representability::Representable,
            },
        );
    }

    Census { verdicts }
}

/// The declaration Lean's kernel named when it refused a stream, if the
/// refusal was the not-a-proposition one.
///
/// Lean says `type of theorem 'CReal.weierstrassMTest' is not a proposition`.
/// Parsed rather than pattern-matched against a fixed name, so the caller can
/// require the name Lean chose to be one THIS kernel independently classified
/// — which is what turns an asserted reason into an earned one.
#[must_use]
pub fn refused_theorem_name(report: &str) -> Option<String> {
    let tail = report.split_once("type of theorem '")?.1;
    let (name, rest) = tail.split_once('\'')?;
    rest.trim_start()
        .starts_with("is not a proposition")
        .then(|| name.to_owned())
}
