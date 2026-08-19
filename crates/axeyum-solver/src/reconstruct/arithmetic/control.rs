//! The **negative control** for every axiom-freedom measurement in this
//! repository, shrunk from thirty axioms to one.
//!
//! ## What a control is for here
//!
//! Every headline number this project publishes about its trusted base is a
//! **zero**: `Kernel::axiom_footprint` of a reconstructed refutation is empty,
//! the trusted surface of seven of eight preludes is `0`, `arith_prelude_builds()`
//! is `0` on all four shipped arithmetic arms. A zero is only a result if the
//! same measurement, run the same way, can come out non-zero — otherwise it is
//! indistinguishable from a measurement that broke. That is this repository's own
//! standing audit finding: a checker that cannot fail is worse than no checker.
//!
//! The `Real` package has been playing that part. It is 30 axioms, and
//! [ADR-0509](../../../../docs/research/09-decisions/adr-0509-the-trusted-surface-is-measured-as-reached-not-only-declared.md)
//! records that its *only* remaining job is to be the thing that is not zero.
//! Thirty is twenty-nine more than the job needs.
//!
//! ## Why the control cannot simply be shrunk in place
//!
//! You cannot delete 29 of the `Real` axioms and keep a working carrier, and the
//! reason is structural rather than a matter of effort: `Real` is an **opaque**
//! carrier. Nothing can be *defined* over an opaque type, so every operation and
//! every law over it has to be assumed. The floor for an axiomatized ordered
//! commutative ring with `1` is the whole signature — one carrier, seven
//! operations, and every law any consumer invokes.
//!
//! So the control shrinks the other way round: **construct the carrier, and
//! assume exactly one of its laws.** [`build_control_carrier`] builds the
//! axiom-free `Int` development — 30 declarations, all proved, trusted surface
//! `0` — and then declares one deliberate `axiom` with the type of
//! `Int.lt_irrefl`, returning the interface with that single slot swapped. The
//! result is a genuine [`RingSignature`] that
//! [`RingSignature::validate_in`](super::signature::RingSignature::validate_in)
//! accepts, that the ordinary reconstruction routes run over unchanged, and whose
//! carrier footprint is exactly one name.
//!
//! ## Why *this* law, and why one is enough
//!
//! `lt_irrefl` is the step a Farkas refutation ends on: the whole point of the
//! derivation is to reach `lt t t` and contradict it. Measured 2026-08-18 over
//! the five fixtures of `examples/ordered_ring_refutation.rs`, `lt_irrefl` is one
//! of only three declarations — with the carrier and `lt` — that **all five**
//! reach; nine of the 30 are reached by none of them. So a control built on it is
//! reached by construction of the route rather than by luck.
//!
//! "By construction" is still a claim, so it is not asserted: [`ControlCarrier`]
//! is used through a check that the control axiom is *present* in the footprint
//! and that it is the *only* carrier axiom there. Both halves matter, and they
//! fail for different reasons —
//!
//! * an **empty** carrier footprint means the measurement stopped seeing
//!   assumptions, or the route stopped deriving its contradiction, and
//! * an **extra** name means the carrier acquired an assumption nobody declared.
//!
//! which is the distinction a control has to be able to draw: "the measurement
//! broke" and "the measurement is trivially satisfied" are different failures and
//! must not both read as green.
//!
//! ## The property thirty axioms do not have
//!
//! The control axiom is **provably redundant**, and the proof is exhibited in the
//! same environment: [`ControlCarrier::discharge`] is a theorem of the control
//! axiom's exact type whose value is `Int.lt_irrefl` and whose measured
//! `axiom_footprint` is empty. So the control adds a *reachable* assumption
//! without adding a *real* one — the environment it lives in is exactly as
//! consistent as the `Int` development.
//!
//! The `Real` package cannot say that. Its 30 axioms are only *relatively*
//! consistent (`build_int_model_of_arith` exhibits ℤ as a model), which is a
//! weaker statement than "here is the proof". Shrinking the control therefore
//! strengthens it on the one axis a control is judged by: it can still come out
//! non-zero, and it can no longer be the thing that makes the system unsound.

use axeyum_lean_kernel::{Declaration, Kernel, NameId, build_int_prelude};

use super::signature::RingSignature;
use super::{LraReconstructCtx, ReconstructError};

/// The leaf name of the single deliberate control axiom.
pub const CONTROL_AXIOM_LEAF: &str = "assumed_lt_irrefl";

/// The full rendered name of the control axiom, as a footprint spells it.
pub const CONTROL_AXIOM_NAME: &str = "axeyum.control.assumed_lt_irrefl";

/// The rendered name of the theorem that discharges the control axiom.
pub const CONTROL_DISCHARGE_NAME: &str = "axeyum.control.discharge";

/// The constructed ordered ring with exactly **one** assumed law — the negative
/// control, and the whole of it.
#[derive(Debug, Clone, Copy)]
pub struct ControlCarrier {
    /// The interface: the `Int` development's 30 declarations with `lt_irrefl`
    /// replaced by [`Self::axiom`].
    pub signature: RingSignature,
    /// The one deliberate [`Declaration::Axiom`], named
    /// [`CONTROL_AXIOM_NAME`].
    pub axiom: NameId,
    /// A theorem of the control axiom's exact type, proved by `Int.lt_irrefl`,
    /// admitted in the same environment — the exhibited discharge that makes the
    /// control assumption redundant rather than merely small.
    pub discharge: NameId,
    /// The proved law the control axiom stands in for.
    pub proved: NameId,
}

/// Build the control carrier into `kernel`.
///
/// Declares the `Int` development, then one axiom and one theorem on top of it.
/// Everything else in the returned signature is `Int`'s own proved declaration.
///
/// # Errors
///
/// [`ReconstructError::KernelRejected`] if the `Int` development does not build,
/// if `Int.lt_irrefl` is not in the environment, if the kernel refuses the
/// control axiom or its discharge, or if the discharge does not come back with
/// an **empty** axiom footprint — which is the check that the control assumes
/// nothing the `Int` development has not already proved.
pub fn build_control_carrier(kernel: &mut Kernel) -> Result<ControlCarrier, ReconstructError> {
    let int = build_int_prelude(kernel).map_err(|e| ReconstructError::KernelRejected {
        rule: "control_carrier".to_owned(),
        detail: format!("the integer development did not build: {e:?}"),
    })?;
    control_carrier_over(kernel, RingSignature::from(int))
}

/// [`build_control_carrier`] over an already-built interface.
///
/// Split out so the discharge guard below is reachable from a test: handed a
/// signature whose `lt_irrefl` is itself an **axiom** — the `Real` package's, for
/// instance — the discharge cannot be axiom-free, and building a control on an
/// assumed law is exactly the mistake the guard exists to refuse. A control
/// standing in for an assumption rather than for a theorem would be one that
/// *adds* to the trusted base instead of only being visible in it.
///
/// # Errors
///
/// As [`build_control_carrier`].
pub fn control_carrier_over(
    kernel: &mut Kernel,
    honest: RingSignature,
) -> Result<ControlCarrier, ReconstructError> {
    let proved = honest.lt_irrefl;
    let ty = kernel
        .environment()
        .get(proved)
        .map(Declaration::ty)
        .ok_or_else(|| ReconstructError::KernelRejected {
            rule: "control_carrier".to_owned(),
            detail: "the integer development does not declare `lt_irrefl`".to_owned(),
        })?;

    let anon = kernel.anon();
    let root = kernel.name_str(anon, "axeyum");
    let namespace = kernel.name_str(root, "control");
    let axiom = kernel.name_str(namespace, CONTROL_AXIOM_LEAF);
    kernel
        .add_declaration(Declaration::Axiom {
            name: axiom,
            uparams: vec![],
            ty,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "control_carrier".to_owned(),
            detail: format!("the control axiom did not admit: {e:?}"),
        })?;

    // The discharge, admitted through the same trusted gate: the control axiom's
    // own type, proved by the `Int` development's theorem. If this ever stops
    // type-checking the control has stopped standing in for a proved law.
    let discharge = kernel.name_str(namespace, "discharge");
    let value = kernel.const_(proved, vec![]);
    kernel
        .add_declaration(Declaration::Theorem {
            name: discharge,
            uparams: vec![],
            ty,
            value,
        })
        .map_err(|e| ReconstructError::KernelRejected {
            rule: "control_carrier".to_owned(),
            detail: format!("the control axiom is not discharged by the proved law: {e:?}"),
        })?;
    let residue: Vec<String> = kernel
        .axiom_footprint(discharge)
        .into_iter()
        .map(|n| kernel.display_name(n).to_string())
        .collect();
    if !residue.is_empty() {
        return Err(ReconstructError::KernelRejected {
            rule: "control_carrier".to_owned(),
            detail: format!(
                "the discharge of the control axiom is not itself axiom-free: {}",
                residue.join(", ")
            ),
        });
    }

    let mut signature = honest;
    signature.lt_irrefl = axiom;
    Ok(ControlCarrier {
        signature,
        axiom,
        discharge,
        proved,
    })
}

impl LraReconstructCtx {
    /// A reconstruction context over the [control carrier](build_control_carrier):
    /// the constructed integers with exactly one law assumed.
    ///
    /// Use it wherever a measurement claims an empty carrier footprint, so the
    /// same run reports a non-empty one beside it. See the module docs for why
    /// one axiom is the honest floor and why it is this one.
    ///
    /// # Errors
    ///
    /// As [`build_control_carrier`], plus
    /// [`RingSignature::validate_in`](super::signature::RingSignature::validate_in)'s
    /// five guards — the control axiom has the proved law's exact type, so a
    /// signature that failed them would mean the swap changed the interface.
    pub fn try_new_over_the_control_carrier() -> Result<(Self, ControlCarrier), ReconstructError> {
        let mut kernel = Kernel::new();
        let control = build_control_carrier(&mut kernel)?;
        let ctx = Self::with_ring_signature(kernel, control.signature)?;
        Ok((ctx, control))
    }
}

#[cfg(test)]
mod control_tests;
