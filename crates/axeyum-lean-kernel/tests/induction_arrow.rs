//! The induction arrow, exercised from OUTSIDE the crate on a goal that is not
//! a prelude theorem.
//!
//! `docs/mathematics-2026-08/04-reachability.md` R3 measured `induction-over-nat`
//! as the top out-of-fragment request in the adversarial corpus — 16 rows,
//! double the next entry — and it is the only entry on that list that is not a
//! missing logic. The kernel has an inductive `Nat` with an ι-computing
//! `Nat.rec`, and the prelude uses it constantly. What was never established is
//! that a *caller* can drive it: take an arbitrary motive, supply a base and a
//! step, and have the trusted gate accept the assembled term.
//!
//! That matters because it is exactly the arrow a solver-side induction route
//! would need (task: ℕ-induction as a solver capability). Establishing it here,
//! against the public API only, means that route has nothing left to invent on
//! the kernel side — the remaining work is recognising the goal and discharging
//! the two obligations, not assembling the certificate.
//!
//! The goal below is deliberately **not** in the Nat prelude, so this cannot
//! pass by accidentally re-deriving something already admitted:
//!
//! ```text
//! ∀ n, n + n = 2 · n
//! ```

use axeyum_lean_kernel::{Declaration, ExprId, Kernel, NatDev, NatOps, build_nat_prelude};

/// `fun n => Eq Nat (n + n) (2 * n)`, as a motive over `n`.
fn doubling(dev: &mut NatDev<'_>, n: ExprId) -> ExprId {
    let sum = dev.add(n, n);
    let two = dev.num(2);
    let scaled = dev.mul(two, n);
    dev.eq(sum, scaled)
}

/// Assemble `∀ n, n + n = 2·n` by induction and hand it to the trusted gate.
///
/// Returns whatever `add_declaration` says, so a caller can assert on the
/// verdict rather than on this function not panicking.
fn admit_doubling(kernel: &mut Kernel, name: &str) -> Result<(), axeyum_lean_kernel::KernelError> {
    let prelude = build_nat_prelude(kernel).expect("Nat prelude must build");
    let mut dev = NatDev::new(kernel, prelude);

    let n_fv = dev.fresh_fvar();
    let n = dev.kernel().fvar(n_fv);

    let proof_body = dev.induct(
        &doubling,
        // `0 + 0 = 2 * 0` — both sides compute to `zero`.
        &|dev| {
            let zero = dev.zero();
            dev.refl(zero)
        },
        // `(k+1) + (k+1) = 2 * (k+1)`, from `k + k = 2·k`.
        //
        // Every rewrite here is a prelude lemma; nothing is assumed. The chain
        // walks the successor out of each side and lands on the induction
        // hypothesis under a `succ (succ ·)` context.
        &|dev, k, ih| {
            let succ_k = dev.succ(k);
            let two = dev.num(2);

            // LHS: `succ k + succ k ≡ succ (succ k + k)` by the defining
            // equation, then `succ k + k = succ (k + k)` by `succ_add`.
            let sk_plus_k = dev.add(succ_k, k);
            let k_plus_k = dev.add(k, k);
            let succ_add = dev.lemma(prelude.succ_add, &[k, k]);
            let succ_k_plus_k = dev.succ(k_plus_k);
            let inner = dev.congr(sk_plus_k, succ_k_plus_k, succ_add, &|dev, t| dev.succ(t));

            // Apply the induction hypothesis under `succ (succ ·)`.
            let two_k = dev.mul(two, k);
            let ih_lifted = dev.congr(k_plus_k, two_k, ih, &|dev, t| {
                let inner = dev.succ(t);
                dev.succ(inner)
            });

            // RHS: `2 * succ k = 2*k + 2 ≡ succ (succ (2*k))`.
            let mul_succ = dev.lemma(prelude.mul_succ, &[two, k]);
            let two_succ_k = dev.mul(two, succ_k);
            let two_k_plus_two = dev.add(two_k, two);
            let rhs_back = dev.symm(two_succ_k, two_k_plus_two, mul_succ);

            let start = dev.add(succ_k, succ_k);
            let after_inner = {
                let s = dev.succ(k_plus_k);
                dev.succ(s)
            };
            let after_ih = {
                let s = dev.succ(two_k);
                dev.succ(s)
            };
            let (_, chained) = dev.chain(
                start,
                &[
                    (after_inner, inner),
                    (after_ih, ih_lifted),
                    (two_succ_k, rhs_back),
                ],
            );
            chained
        },
        n,
    );

    let statement = {
        let body = doubling(&mut dev, n);
        let nat = dev.nat_ty();
        dev.pi_fv(n_fv, nat, body)
    };
    let value = {
        let nat = dev.nat_ty();
        dev.lam_fv(n_fv, nat, proof_body)
    };
    let ident = {
        let anon = dev.kernel().anon();
        dev.kernel().name_str(anon, name)
    };
    dev.kernel().add_declaration(Declaration::Theorem {
        name: ident,
        uparams: vec![],
        ty: statement,
        value,
    })
}

/// The arrow works: an arbitrary caller-supplied motive, discharged by
/// induction, accepted by the trusted gate.
#[test]
fn a_caller_can_drive_nat_induction_to_an_admitted_theorem() {
    let mut kernel = Kernel::new();
    admit_doubling(&mut kernel, "Caller.doubling").expect("the gate must accept the assembly");

    let admitted = kernel.environment().iter().any(|(_, d)| {
        matches!(d, Declaration::Theorem { name, .. }
            if kernel.display_name(*name).to_string() == "Caller.doubling")
    });
    assert!(
        admitted,
        "the theorem must be in the environment, not merely not-rejected"
    );
}

/// The control. The same assembly with a FALSE base must be refused.
///
/// Without this, the test above shows only that some term was accepted; it
/// would pass just as well against a gate that accepts anything.
#[test]
fn the_gate_refuses_an_induction_whose_base_is_wrong() {
    let mut kernel = Kernel::new();
    let prelude = build_nat_prelude(&mut kernel).expect("Nat prelude must build");
    let mut dev = NatDev::new(&mut kernel, prelude);

    let n_fv = dev.fresh_fvar();
    let n = dev.kernel().fvar(n_fv);

    // `refl 1 : 1 = 1` is a perfectly good proof — of the wrong proposition.
    // The base case needs `0 + 0 = 2 * 0`.
    let proof_body = dev.induct(
        &doubling,
        &|dev| {
            let one = dev.num(1);
            dev.refl(one)
        },
        &|_dev, _k, ih| ih,
        n,
    );
    let statement = {
        let body = doubling(&mut dev, n);
        let nat = dev.nat_ty();
        dev.pi_fv(n_fv, nat, body)
    };
    let value = {
        let nat = dev.nat_ty();
        dev.lam_fv(n_fv, nat, proof_body)
    };
    let ident = {
        let anon = dev.kernel().anon();
        dev.kernel().name_str(anon, "Caller.bogus")
    };
    let verdict = dev.kernel().add_declaration(Declaration::Theorem {
        name: ident,
        uparams: vec![],
        ty: statement,
        value,
    });
    assert!(
        verdict.is_err(),
        "a wrong base case must be refused; if this passes, the gate above proves nothing"
    );
}
