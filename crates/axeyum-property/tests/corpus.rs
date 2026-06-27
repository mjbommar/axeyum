//! Committed graduated corpus gate for the typed property SDK.

use axeyum_property::{Bool, Bv, LeanStatus, ProofOutcomeSummary, Property};
use axeyum_solver::ProofOutcome;

type TestResult = Result<(), Box<dyn std::error::Error>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExpectedOutcome {
    Proved,
    Disproved,
}

#[derive(Debug)]
struct CorpusCaseReport {
    id: &'static str,
    tier: &'static str,
    expected: ExpectedOutcome,
    actual: ProofOutcomeSummary,
    lean_required: bool,
    lean_available: bool,
}

impl CorpusCaseReport {
    fn assert_matches(&self) {
        match (self.expected, &self.actual) {
            (ExpectedOutcome::Proved, ProofOutcomeSummary::Proved)
            | (ExpectedOutcome::Disproved, ProofOutcomeSummary::Disproved) => {}
            _ => panic!(
                "{} ({}) expected {:?}, got {:?}",
                self.id, self.tier, self.expected, self.actual
            ),
        }
        if self.lean_required {
            assert!(
                self.lean_available,
                "{} ({}) expected a Lean module",
                self.id, self.tier
            );
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
struct CorpusTotals {
    cases: usize,
    proved: usize,
    disproved: usize,
    unknown: usize,
    mismatches: usize,
    lean_required: usize,
    lean_required_available: usize,
}

fn tally(reports: &[CorpusCaseReport]) -> CorpusTotals {
    let mut totals = CorpusTotals {
        cases: reports.len(),
        ..CorpusTotals::default()
    };
    for report in reports {
        match report.actual {
            ProofOutcomeSummary::Proved => totals.proved += 1,
            ProofOutcomeSummary::Disproved => totals.disproved += 1,
            ProofOutcomeSummary::Unknown { .. } => totals.unknown += 1,
        }
        let matches_expected = matches!(
            (report.expected, &report.actual),
            (ExpectedOutcome::Proved, ProofOutcomeSummary::Proved)
                | (ExpectedOutcome::Disproved, ProofOutcomeSummary::Disproved)
        );
        if !matches_expected {
            totals.mismatches += 1;
        }
        if report.lean_required {
            totals.lean_required += 1;
            if report.lean_available {
                totals.lean_required_available += 1;
            }
        }
    }
    totals
}

#[test]
fn property_sdk_corpus_matches_committed_scoreboard() -> TestResult {
    let reports = [
        bv_reflexive_proof()?,
        int_assumption_proof()?,
        unsigned_bv_counterexample_minimized()?,
        signed_bv_counterexample_minimized()?,
        aggregate_counterexample_rendered()?,
    ];

    for report in &reports {
        report.assert_matches();
    }

    assert_eq!(
        tally(&reports),
        CorpusTotals {
            cases: 5,
            proved: 2,
            disproved: 3,
            unknown: 0,
            mismatches: 0,
            lean_required: 1,
            lean_required_available: 1,
        }
    );
    Ok(())
}

fn bv_reflexive_proof() -> Result<CorpusCaseReport, Box<dyn std::error::Error>> {
    let mut property = Property::new();
    let x = property.bv::<8>("x")?;
    let goal = x.equals(&mut property, x)?;

    let certificate = property.prove_with_certificate(goal)?;
    let summary = certificate.summary();
    assert!(matches!(summary.outcome, ProofOutcomeSummary::Proved));
    let evidence = summary
        .evidence
        .as_ref()
        .expect("proved corpus case should summarize checked evidence");
    assert!(evidence.kind.starts_with("unsat-"));
    assert_eq!(evidence.assertion_count, 1);
    assert_eq!(summary.lean.status, LeanStatus::Available);

    Ok(CorpusCaseReport {
        id: "sdk-bv-reflexive-proof",
        tier: "P0",
        expected: ExpectedOutcome::Proved,
        actual: summary.outcome,
        lean_required: true,
        lean_available: summary.lean.status == LeanStatus::Available,
    })
}

fn int_assumption_proof() -> Result<CorpusCaseReport, Box<dyn std::error::Error>> {
    let mut property = Property::new();
    let x = property.int("x")?;
    let three = property.int_const(3);
    let four = property.int_const(4);
    let pre = x.le(&mut property, three)?;
    property.assume(pre);
    let goal = x.le(&mut property, four)?;

    let certificate = property.prove_with_certificate(goal)?;
    let summary = certificate.summary();
    assert!(matches!(summary.outcome, ProofOutcomeSummary::Proved));
    assert!(
        summary.evidence.is_some(),
        "proved int corpus case should expose checked evidence"
    );

    Ok(CorpusCaseReport {
        id: "sdk-int-assumption-proof",
        tier: "P1",
        expected: ExpectedOutcome::Proved,
        actual: summary.outcome,
        lean_required: false,
        lean_available: summary.lean.status == LeanStatus::Available,
    })
}

fn unsigned_bv_counterexample_minimized() -> Result<CorpusCaseReport, Box<dyn std::error::Error>> {
    let mut property = Property::new();
    let x = property.symbolic::<u8>("x")?;
    let five = property.bv_const::<8>(5)?;
    let goal = x.ule(&mut property, five)?;

    let certificate = property.prove_minimized_with_certificate(goal)?;
    let ProofOutcome::Disproved(model) = &certificate.outcome else {
        panic!(
            "expected a minimized counterexample, got {:?}",
            certificate.outcome
        );
    };
    assert_eq!(property.concrete::<u8>(&x, model)?, Some(6));
    assert_eq!(
        property.counterexample(model)?.render_rust_let_bindings()?,
        "let x: u8 = 0x06_u8; // BV8\n"
    );

    let summary = certificate.summary();
    assert_eq!(summary.lean.status, LeanStatus::NotApplicable);
    Ok(CorpusCaseReport {
        id: "sdk-u8-minimized-counterexample",
        tier: "P0",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        lean_required: false,
        lean_available: false,
    })
}

fn signed_bv_counterexample_minimized() -> Result<CorpusCaseReport, Box<dyn std::error::Error>> {
    let mut property = Property::new();
    let delta = property.symbolic::<i8>("delta")?;
    let neg_three = property.bv_const::<8>(0xfd)?;
    let two = property.bv_const::<8>(2)?;
    let lower = delta.sge(&mut property, neg_three)?;
    let upper = delta.sle(&mut property, two)?;
    property.assume(lower);
    property.assume(upper);
    let goal = property.bool_const(false);

    let certificate = property.prove_minimized_with_certificate(goal)?;
    let ProofOutcome::Disproved(model) = &certificate.outcome else {
        panic!(
            "expected a signed minimized counterexample, got {:?}",
            certificate.outcome
        );
    };
    assert_eq!(property.concrete::<i8>(&delta, model)?, Some(-3));
    assert_eq!(
        property.counterexample(model)?.render_rust_let_bindings()?,
        "let delta: i8 = -3_i8; // BV8 two's-complement\n"
    );

    let summary = certificate.summary();
    assert_eq!(summary.lean.status, LeanStatus::NotApplicable);
    Ok(CorpusCaseReport {
        id: "sdk-i8-signed-minimized-counterexample",
        tier: "P1",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        lean_required: false,
        lean_available: false,
    })
}

fn aggregate_counterexample_rendered() -> Result<CorpusCaseReport, Box<dyn std::error::Error>> {
    #[derive(Debug, Clone, Copy)]
    struct TransferExpr {
        enabled: Bool,
        amount: Bv<16>,
        balance: Bv<16>,
    }

    let mut property = Property::new();
    let transfer = property.symbolic_struct("transfer", |fields| {
        Ok(TransferExpr {
            enabled: fields.field::<bool>("enabled")?,
            amount: fields.field::<u16>("amount")?,
            balance: fields.field::<u16>("balance")?,
        })
    })?;
    let goal = transfer.amount.ule(&mut property, transfer.balance)?;

    let certificate = property.prove_minimized_with_certificate(goal)?;
    let ProofOutcome::Disproved(model) = &certificate.outcome else {
        panic!(
            "expected an aggregate counterexample, got {:?}",
            certificate.outcome
        );
    };
    assert_eq!(
        property.concrete::<bool>(&transfer.enabled, model)?,
        Some(false)
    );
    assert_eq!(property.concrete::<u16>(&transfer.amount, model)?, Some(1));
    assert_eq!(property.concrete::<u16>(&transfer.balance, model)?, Some(0));
    let counterexample = property.counterexample(model)?;
    assert_eq!(
        counterexample.render_rust_named_struct_let("transfer", "TransferInput", "transfer")?,
        concat!(
            "let transfer: TransferInput = TransferInput {\n",
            "    enabled: transfer_enabled,\n",
            "    amount: transfer_amount,\n",
            "    balance: transfer_balance,\n",
            "};\n",
        )
    );

    let summary = certificate.summary();
    assert_eq!(summary.lean.status, LeanStatus::NotApplicable);
    Ok(CorpusCaseReport {
        id: "sdk-aggregate-counterexample-render",
        tier: "P1",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        lean_required: false,
        lean_available: false,
    })
}
