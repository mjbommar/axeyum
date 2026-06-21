//! Self-checking degree-2 sum-of-squares / PSD `unsat` evidence (ADR-0039).
//!
//! [`produce_nra_sos_evidence`] attaches an [`Evidence::UnsatSos`] certificate to a
//! conjunction whose first STRICT quadratic inequality atom is globally one-signed
//! (`p < 0` with `M ⪰ 0`, or `p > 0` with `−M ⪰ 0`). The certificate is fully
//! self-contained: [`Evidence::check`] re-validates it via `SosCertificate::verify`
//! (an exact-rational `LDLᵀ` reconstruction), independent of the producer.
//!
//! These tests assert (a) the certificate is produced and (b) it INDEPENDENTLY
//! re-validates, and (c) an indefinite/satisfiable query yields no SOS evidence
//! (never a wrong `unsat`). All arithmetic is exact — no floating point.

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::{Evidence, produce_nra_sos_evidence};

fn real(arena: &mut TermArena, name: &str) -> TermId {
    let s = arena.declare(name, Sort::Real).unwrap();
    arena.var(s)
}

fn konst(arena: &mut TermArena, c: i128) -> TermId {
    arena.real_const(Rational::integer(c))
}

#[test]
fn am_gm_two_var_produces_self_checking_sos_evidence() {
    // x²+y²−2xy < 0 (= (x−y)² < 0) ⇒ Unsat, certified by M ⪰ 0.
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let xy = arena.real_mul(x, y).unwrap();
    let two = konst(&mut arena, 2);
    let two_xy = arena.real_mul(two, xy).unwrap();
    let sum = arena.real_add(xx, yy).unwrap();
    let p = arena.real_sub(sum, two_xy).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(p, zero).unwrap();
    let assertions = [atom];

    let report = produce_nra_sos_evidence(&arena, &assertions)
        .expect("producer must not error")
        .expect("(x−y)² < 0 must produce an SOS certificate");
    assert!(
        matches!(report.evidence, Evidence::UnsatSos { .. }),
        "expected an SOS certificate, got {:?}",
        report.evidence
    );
    // Independent re-validation: the certificate verifies on its own.
    assert!(
        report
            .evidence
            .check(&arena, &assertions)
            .expect("check must not error"),
        "the SOS certificate must independently re-validate"
    );
}

#[test]
fn three_var_am_gm_produces_sos_evidence() {
    // a²+b²+c²−ab−bc−ca < 0 (= ½[(a−b)²+(b−c)²+(c−a)²] < 0) ⇒ Unsat.
    let mut arena = TermArena::new();
    let a = real(&mut arena, "a");
    let b = real(&mut arena, "b");
    let c = real(&mut arena, "c");
    let aa = arena.real_mul(a, a).unwrap();
    let bb = arena.real_mul(b, b).unwrap();
    let cc = arena.real_mul(c, c).unwrap();
    let ab = arena.real_mul(a, b).unwrap();
    let bc = arena.real_mul(b, c).unwrap();
    let ca = arena.real_mul(c, a).unwrap();
    let squares = {
        let s = arena.real_add(aa, bb).unwrap();
        arena.real_add(s, cc).unwrap()
    };
    let cross = {
        let s = arena.real_add(ab, bc).unwrap();
        arena.real_add(s, ca).unwrap()
    };
    let p = arena.real_sub(squares, cross).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(p, zero).unwrap();
    let assertions = [atom];

    let report = produce_nra_sos_evidence(&arena, &assertions)
        .expect("producer must not error")
        .expect("3-var AM–GM atom must produce an SOS certificate");
    assert!(
        matches!(report.evidence, Evidence::UnsatSos { .. }),
        "expected an SOS certificate, got {:?}",
        report.evidence
    );
    assert!(
        report
            .evidence
            .check(&arena, &assertions)
            .expect("check must not error"),
        "the 3-var SOS certificate must independently re-validate"
    );
}

#[test]
fn non_sos_query_produces_no_sos_evidence() {
    // x*y < 0 is indefinite / satisfiable (x=1, y=−1) ⇒ NO SOS certificate, never
    // a wrong unsat.
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let xy = arena.real_mul(x, y).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(xy, zero).unwrap();
    let assertions = [atom];

    let outcome = produce_nra_sos_evidence(&arena, &assertions).expect("producer must not error");
    assert!(
        outcome.is_none(),
        "x*y < 0 is satisfiable; the SOS producer must decline (no certificate)"
    );
}

#[test]
fn am_gm_evidence_carries_a_kernel_checked_lean_module() {
    // The SOS unsat's evidence carries a kernel-checked Lean proof (ADR-0041), and
    // `check` re-derives + re-verifies it through the trusted kernel.
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let xx = arena.real_mul(x, x).unwrap();
    let yy = arena.real_mul(y, y).unwrap();
    let xy = arena.real_mul(x, y).unwrap();
    let two = konst(&mut arena, 2);
    let two_xy = arena.real_mul(two, xy).unwrap();
    let sum = arena.real_add(xx, yy).unwrap();
    let p = arena.real_sub(sum, two_xy).unwrap();
    let zero = konst(&mut arena, 0);
    let atom = arena.real_lt(p, zero).unwrap(); // x²+y²−2xy < 0
    let assertions = [atom];

    let report = produce_nra_sos_evidence(&arena, &assertions)
        .expect("producer must not error")
        .expect("AM-GM must produce SOS evidence");
    // The evidence carries the Lean module for this reconstructable shape.
    let Evidence::UnsatSos {
        ref lean_module, ..
    } = report.evidence
    else {
        panic!("expected UnsatSos, got {:?}", report.evidence);
    };
    let module = lean_module
        .as_ref()
        .expect("AM-GM sum form is SOS-reconstructable, so the evidence must carry a Lean module");
    assert!(
        module.contains("axeyum_refutation"),
        "the carried module must be the kernel-checked refutation"
    );
    // `check` re-derives the module and re-verifies it through the trusted kernel.
    assert!(
        report
            .evidence
            .check(&arena, &assertions)
            .expect("check must not error"),
        "the Lean-backed SOS evidence must re-check (certificate + kernel re-derivation)"
    );
}
