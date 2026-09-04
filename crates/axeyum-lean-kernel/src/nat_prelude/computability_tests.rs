//! Evaluation tests for `nat_prelude::computability`'s machine model, and an
//! axiom-footprint check for its one theorem.
//!
//! `Nat.RM.diagStep`/`Nat.RM.runFuel`/`Nat.RM.Halts` are ordinary
//! `Definition`s — `Kernel::add_declaration` type-checks them and does not
//! evaluate them, so a swapped `case_true`/`case_false` value in `diagStep`
//! or a transposed `step`/accumulator in `runFuel`'s succ case type-checks
//! exactly as happily as the intended construction. Every check below is a
//! `def_eq` at concrete numerals, paired with a negative control naming the
//! specific wrong value the swap would produce.

use crate::env::Declaration;
use crate::expr::ExprId;
use crate::{Kernel, NatOps, NatPrelude, NatState, build_nat_prelude};

struct Fixture {
    k: Kernel,
    p: NatPrelude,
    st: NatState,
}

impl NatOps for Fixture {
    fn kernel(&mut self) -> &mut Kernel {
        &mut self.k
    }

    fn nat_state(&mut self) -> &mut NatState {
        &mut self.st
    }
}

impl Fixture {
    fn new() -> Self {
        let mut k = Kernel::new();
        let p = build_nat_prelude(&mut k).expect("Nat prelude must build");
        let st = NatState::new(&mut k, p);
        Self { k, p, st }
    }

    /// `fun (_ : Nat) => true`, as a genuine kernel term (not a Rust bool).
    fn const_true_fn(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let dummy = self.fresh_fvar();
        let true_ = self.bool_true();
        self.lam_fv(dummy, nat, true_)
    }

    /// `fun (_ : Nat) => false`.
    fn const_false_fn(&mut self) -> ExprId {
        let nat = self.nat_ty();
        let dummy = self.fresh_fvar();
        let false_ = self.bool_false();
        self.lam_fv(dummy, nat, false_)
    }
}

#[test]
fn diag_step_self_loops_under_the_constant_true_decider() {
    let mut f = Fixture::new();
    let p = f.p;
    let h_true = f.const_true_fn();
    for c in [1u32, 5, 9] {
        let arg = f.num(c);
        let out = f.const_app(p.rm_diag_step, &[h_true, arg]);
        assert!(
            f.k.def_eq(out, arg),
            "diagStep (const true) {c} must self-loop, reducing to {c}"
        );
        // Negative control: the OTHER branch's value (0, the halt state) --
        // exactly what a swapped case_false/case_true value would produce.
        let zero = f.zero();
        assert!(
            !f.k.def_eq(out, zero),
            "negative control: diagStep (const true) {c} must NOT reduce to 0"
        );
    }
}

#[test]
fn diag_step_halts_immediately_under_the_constant_false_decider() {
    let mut f = Fixture::new();
    let p = f.p;
    let h_false = f.const_false_fn();
    for c in [1u32, 5, 9] {
        let arg = f.num(c);
        let out = f.const_app(p.rm_diag_step, &[h_false, arg]);
        let zero = f.zero();
        assert!(
            f.k.def_eq(out, zero),
            "diagStep (const false) {c} must halt, reducing to 0"
        );
        assert!(
            !f.k.def_eq(out, arg),
            "negative control: diagStep (const false) {c} must NOT reduce to {c} (the self-loop value)"
        );
    }
}

/// `runFuel (diagStep (const true)) 1 fuel` must stay AT `1` for every
/// tested `fuel` — the concrete instance the fuel-induction lemma inside
/// `self_halting_not_decidable` proves for ALL fuel; this pins the
/// DEFINITION's behaviour at the small fuels a reduction test can reach.
#[test]
fn run_fuel_never_reaches_zero_under_the_self_loop() {
    let mut f = Fixture::new();
    let p = f.p;
    let h_true = f.const_true_fn();
    let diag_true = f.const_app(p.rm_diag_step, &[h_true]);
    let one = f.num(1);
    let zero = f.zero();
    for fuel in 0u32..5 {
        let fuel_arg = f.num(fuel);
        let out = f.const_app(p.rm_run_fuel, &[diag_true, one, fuel_arg]);
        assert!(
            f.k.def_eq(out, one),
            "runFuel (diagStep (const true)) 1 {fuel} must reduce to 1"
        );
        assert!(
            !f.k.def_eq(out, zero),
            "negative control: runFuel (diagStep (const true)) 1 {fuel} must NOT reduce to 0"
        );
    }
}

/// `runFuel (diagStep (const false)) 1 fuel` is `1` at `fuel = 0` (the base
/// case `runFuel step c 0 ≡ c`: no step has been taken yet) and `0` at every
/// `fuel ≥ 1` — the discriminating check that the succ case is `step
/// (runFuel … f)` (advances from the PREVIOUS config), not `runFuel … f`
/// re-returned unchanged (which would never advance) and not `step c`
/// re-applied to the ORIGINAL `c` every time (which happens to coincide with
/// the correct answer here, since `diagStep`'s false branch is a constant,
/// but would diverge from it for a step function whose behaviour actually
/// depends on the current configuration).
#[test]
fn run_fuel_reaches_zero_at_fuel_one_under_the_immediate_halt() {
    let mut f = Fixture::new();
    let p = f.p;
    let h_false = f.const_false_fn();
    let diag_false = f.const_app(p.rm_diag_step, &[h_false]);
    let one = f.num(1);
    let zero = f.zero();

    let at_fuel_0 = f.const_app(p.rm_run_fuel, &[diag_false, one, zero]);
    assert!(
        f.k.def_eq(at_fuel_0, one),
        "runFuel (diagStep (const false)) 1 0 must reduce to 1 (no steps taken yet)"
    );
    assert!(
        !f.k.def_eq(at_fuel_0, zero),
        "negative control: runFuel (diagStep (const false)) 1 0 must NOT already be 0"
    );

    for fuel in 1u32..4 {
        let fuel_arg = f.num(fuel);
        let out = f.const_app(p.rm_run_fuel, &[diag_false, one, fuel_arg]);
        assert!(
            f.k.def_eq(out, zero),
            "runFuel (diagStep (const false)) 1 {fuel} must reduce to 0"
        );
    }
}

#[test]
fn self_halting_not_decidable_is_a_declared_axiom_free_theorem() {
    let f = Fixture::new();
    let p = f.p;
    let name = p.rm_self_halting_not_decidable;

    let declaration =
        f.k.environment()
            .get(name)
            .unwrap_or_else(|| panic!("{name:?} must be declared"));
    assert!(
        matches!(declaration, Declaration::Theorem { .. }),
        "{name:?} must be a Theorem, not a Definition or axiom"
    );

    let footprint = f.k.axiom_footprint(name);
    assert!(
        footprint.is_empty(),
        "{name:?} must be axiom-free, found: {footprint:?}"
    );
}
