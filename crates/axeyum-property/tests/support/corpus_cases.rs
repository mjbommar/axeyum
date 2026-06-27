use std::fmt::Write as _;

use axeyum_property::{Bool, Bv, Counterexample, LeanStatus, ProofOutcomeSummary, Property};
use axeyum_solver::ProofOutcome;

const LAST_UPDATED: &str = "2026-06-27";

type CorpusResult<T> = Result<T, Box<dyn std::error::Error>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExpectedOutcome {
    Proved,
    Disproved,
}

#[derive(Debug)]
pub(crate) struct CorpusCaseReport {
    id: &'static str,
    tier: &'static str,
    workflow: &'static str,
    expected: ExpectedOutcome,
    actual: ProofOutcomeSummary,
    checks: &'static str,
    baseline_analogue: &'static str,
    lean_required: bool,
    lean_available: bool,
}

impl CorpusCaseReport {
    fn assert_matches(&self) {
        match (self.expected, &self.actual) {
            (ExpectedOutcome::Proved, ProofOutcomeSummary::Proved)
            | (ExpectedOutcome::Disproved, ProofOutcomeSummary::Disproved) => {}
            _ => panic!(
                "{} ({}) expected {}, got {}",
                self.id,
                self.tier,
                self.expected.label(),
                outcome_label(&self.actual)
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

impl ExpectedOutcome {
    const fn label(self) -> &'static str {
        match self {
            Self::Proved => "proved",
            Self::Disproved => "disproved",
        }
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct CorpusTotals {
    cases: usize,
    proved: usize,
    disproved: usize,
    unknown: usize,
    mismatches: usize,
    lean_required: usize,
    lean_required_available: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, axeyum_property::Symbolic)]
struct BaselineTransferInput {
    enabled: bool,
    amount: u8,
    balance: u8,
}

pub(crate) fn run_property_corpus() -> CorpusResult<Vec<CorpusCaseReport>> {
    Ok(vec![
        bv_reflexive_proof()?,
        int_assumption_proof()?,
        expression_builder_aliases_proved()?,
        unsigned_bv_counterexample_minimized()?,
        signed_bv_counterexample_minimized()?,
        aggregate_counterexample_rendered()?,
        overflow_helper_counterexample_minimized()?,
        proptest_style_baseline_counterexample_comparison()?,
        kani_style_baseline_proof_comparison()?,
        kani_style_struct_baseline_counterexample_comparison()?,
        derive_symbolic_counterexample_lifted()?,
        explicit_nested_aggregate_replay_rendered()?,
    ])
}

pub(crate) fn assert_reports_match(reports: &[CorpusCaseReport]) {
    for report in reports {
        report.assert_matches();
    }
}

pub(crate) fn expected_totals() -> CorpusTotals {
    CorpusTotals {
        cases: 12,
        proved: 4,
        disproved: 8,
        unknown: 0,
        mismatches: 0,
        lean_required: 1,
        lean_required_available: 1,
    }
}

pub(crate) fn tally(reports: &[CorpusCaseReport]) -> CorpusTotals {
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
        if report.expected.label() != outcome_label(&report.actual) {
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

pub(crate) fn render_json(reports: &[CorpusCaseReport]) -> String {
    let totals = tally(reports);
    let mut out = String::new();
    writeln!(&mut out, "{{").expect("write string");
    writeln!(&mut out, "  \"last_updated\": \"{LAST_UPDATED}\",").expect("write string");
    writeln!(
        &mut out,
        "  \"generated_by\": \"cargo run -p axeyum-property --example property_corpus_scoreboard -- json docs/consumer-track/property/corpus.json\","
    )
    .expect("write string");
    write_json_summary(&mut out, &totals);
    writeln!(&mut out, "  \"cases\": [").expect("write string");
    for (index, report) in reports.iter().enumerate() {
        write_json_case(&mut out, report, index + 1 == reports.len());
    }
    writeln!(&mut out, "  ]").expect("write string");
    writeln!(&mut out, "}}").expect("write string");
    out
}

pub(crate) fn render_markdown(reports: &[CorpusCaseReport]) -> String {
    let totals = tally(reports);
    let mut out = String::new();
    writeln!(&mut out, "# axeyum-property SCOREBOARD\n").expect("write string");
    writeln!(&mut out, "> **Auto-generated. Do not edit by hand.**").expect("write string");
    writeln!(
        &mut out,
        "> Regenerate with `cargo run -p axeyum-property --example property_corpus_scoreboard -- markdown docs/consumer-track/property/SCOREBOARD.md`.\n"
    )
    .expect("write string");
    writeln!(&mut out, "Last updated: {LAST_UPDATED}.\n").expect("write string");
    write_markdown_intro(&mut out);
    write_markdown_summary(&mut out, &totals);
    write_markdown_cases(&mut out, reports);
    write_markdown_next_gates(&mut out);
    out
}

fn write_json_summary(out: &mut String, totals: &CorpusTotals) {
    writeln!(&mut *out, "  \"summary\": {{").expect("write string");
    writeln!(&mut *out, "    \"cases\": {},", totals.cases).expect("write string");
    writeln!(&mut *out, "    \"proved\": {},", totals.proved).expect("write string");
    writeln!(&mut *out, "    \"disproved\": {},", totals.disproved).expect("write string");
    writeln!(&mut *out, "    \"unknown\": {},", totals.unknown).expect("write string");
    writeln!(&mut *out, "    \"mismatches\": {},", totals.mismatches).expect("write string");
    writeln!(&mut *out, "    \"disagree\": {},", totals.mismatches).expect("write string");
    writeln!(
        &mut *out,
        "    \"lean_required\": {},",
        totals.lean_required
    )
    .expect("write string");
    writeln!(
        &mut *out,
        "    \"lean_required_available\": {}",
        totals.lean_required_available
    )
    .expect("write string");
    writeln!(&mut *out, "  }},").expect("write string");
}

fn write_json_case(out: &mut String, report: &CorpusCaseReport, is_last: bool) {
    writeln!(&mut *out, "    {{").expect("write string");
    json_field(out, "id", report.id, true);
    json_field(out, "tier", report.tier, true);
    json_field(out, "workflow", report.workflow, true);
    json_field(out, "expected", report.expected.label(), true);
    json_field(out, "actual", outcome_label(&report.actual), true);
    json_field(out, "checks", report.checks, true);
    json_field(out, "baseline_analogue", report.baseline_analogue, true);
    writeln!(
        &mut *out,
        "      \"lean_required\": {},",
        report.lean_required
    )
    .expect("write string");
    writeln!(
        &mut *out,
        "      \"lean_available\": {}",
        report.lean_available
    )
    .expect("write string");
    let suffix = if is_last { "" } else { "," };
    writeln!(&mut *out, "    }}{suffix}").expect("write string");
}

fn write_markdown_intro(out: &mut String) {
    out.push_str("This is the committed graduated SDK corpus gate for\n");
    out.push_str(
        "`axeyum-property`. It is not yet a broad external-vs-SOTA benchmark; it is the\n",
    );
    out.push_str(
        "app-level honesty gate that prevents SDK claims from living only in ad hoc unit\n",
    );
    out.push_str(
        "tests. It now includes deterministic proved and disproved baseline comparisons;\n",
    );
    out.push_str("broader proptest/Kani-style comparison remains the next PROP.6 step.\n\n");
    out.push_str("## Commands\n\n");
    out.push_str("```sh\n");
    out.push_str(
        "CARGO_BUILD_JOBS=2 cargo test -p axeyum-property --test corpus -j1 -- --nocapture\n",
    );
    out.push_str("cargo run -p axeyum-property --example property_corpus_scoreboard -- json docs/consumer-track/property/corpus.json\n");
    out.push_str("cargo run -p axeyum-property --example property_corpus_scoreboard -- markdown docs/consumer-track/property/SCOREBOARD.md\n");
    out.push_str("```\n\n");
    out.push_str("Machine-readable artifact: [`corpus.json`](corpus.json).\n\n");
}

fn write_markdown_summary(out: &mut String, totals: &CorpusTotals) {
    out.push_str("## Summary\n\n");
    out.push_str("| metric | value |\n|---|---:|\n");
    writeln!(&mut *out, "| corpus cases | {} |", totals.cases).expect("write string");
    writeln!(&mut *out, "| proved | {} |", totals.proved).expect("write string");
    writeln!(&mut *out, "| disproved | {} |", totals.disproved).expect("write string");
    writeln!(&mut *out, "| unknown | {} |", totals.unknown).expect("write string");
    writeln!(
        &mut *out,
        "| mismatches / DISAGREE | {} |",
        totals.mismatches
    )
    .expect("write string");
    writeln!(
        &mut *out,
        "| Lean-required cases | {} |",
        totals.lean_required
    )
    .expect("write string");
    writeln!(
        &mut *out,
        "| Lean-required available | {} |",
        totals.lean_required_available
    )
    .expect("write string");
    out.push('\n');
}

fn write_markdown_cases(out: &mut String, reports: &[CorpusCaseReport]) {
    out.push_str("## Cases\n\n");
    out.push_str("| id | tier | workflow | expected | checks | baseline analogue |\n");
    out.push_str("|---|---|---|---|---|---|\n");
    for report in reports {
        writeln!(
            &mut *out,
            "| `{}` | {} | {} | {} | {} | {} |",
            report.id,
            report.tier,
            report.workflow,
            report.expected.label(),
            report.checks,
            report.baseline_analogue
        )
        .expect("write string");
    }
    out.push('\n');
}

fn write_markdown_next_gates(out: &mut String) {
    out.push_str("## Next Gates\n\n");
    out.push_str("1. Broaden the baseline runner across assumption and replay property shapes,\n");
    out.push_str(
        "   including proptest-style random/shrunk witnesses and Kani-style bounded assertions.\n",
    );
    out.push_str(
        "2. Broaden the corpus across BV widths, overflow predicates, nested aggregates,\n",
    );
    out.push_str("   assumptions, and certificate fragments.\n");
    out.push_str("3. Keep `corpus.json` and this scoreboard generated from the shared corpus\n");
    out.push_str("   module instead of hand-edited.\n");
}

fn json_field(out: &mut String, key: &str, value: &str, comma: bool) {
    let suffix = if comma { "," } else { "" };
    writeln!(
        &mut *out,
        "      \"{}\": \"{}\"{}",
        json_escape(key),
        json_escape(value),
        suffix
    )
    .expect("write string");
}

fn json_escape(value: &str) -> String {
    let mut out = String::new();
    for ch in value.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => {
                write!(&mut out, "\\u{:04x}", ch as u32).expect("write string");
            }
            ch => out.push(ch),
        }
    }
    out
}

fn outcome_label(outcome: &ProofOutcomeSummary) -> &'static str {
    match outcome {
        ProofOutcomeSummary::Proved => "proved",
        ProofOutcomeSummary::Disproved => "disproved",
        ProofOutcomeSummary::Unknown { .. } => "unknown",
    }
}

fn bv_reflexive_proof() -> CorpusResult<CorpusCaseReport> {
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
    let lean_available = summary.lean.status == LeanStatus::Available;

    Ok(CorpusCaseReport {
        id: "sdk-bv-reflexive-proof",
        tier: "P0",
        workflow: "certificate success over fixed-width BV",
        expected: ExpectedOutcome::Proved,
        actual: summary.outcome,
        checks: "checked evidence kind starts with `unsat-`; assertion count is stable; standalone Lean module is available",
        baseline_analogue: "z3.rs/Kani assertion proof",
        lean_required: true,
        lean_available,
    })
}

fn int_assumption_proof() -> CorpusResult<CorpusCaseReport> {
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
    let lean_available = summary.lean.status == LeanStatus::Available;

    Ok(CorpusCaseReport {
        id: "sdk-int-assumption-proof",
        tier: "P1",
        workflow: "integer implication under an SDK assumption",
        expected: ExpectedOutcome::Proved,
        actual: summary.outcome,
        checks: "checked evidence is present through `ProofCertificate::summary()`",
        baseline_analogue: "Kani precondition/assertion proof",
        lean_required: false,
        lean_available,
    })
}

fn expression_builder_aliases_proved() -> CorpusResult<CorpusCaseReport> {
    let mut property = Property::new();
    let x = property.bv::<8>("x")?;
    let n = property.int("n")?;
    let flag = property.bool("flag")?;

    let bv_zero = property.bv_const::<8>(0)?;
    let x_plus_zero = property.bv_add(x, bv_zero)?;
    let bv_identity = property.bv_equals(x_plus_zero, x)?;
    let int_zero = property.int_const(0);
    let n_plus_zero = property.int_add(n, int_zero)?;
    let int_identity = property.int_equals(n_plus_zero, n)?;
    let bool_identity = property.bool_implies(flag, flag)?;
    let goal = property.all([bv_identity, int_identity, bool_identity])?;

    let certificate = property.prove_with_certificate(goal)?;
    let summary = certificate.summary();
    assert!(matches!(summary.outcome, ProofOutcomeSummary::Proved));
    assert!(
        summary.evidence.is_some(),
        "builder-alias proof should expose checked evidence"
    );
    let lean_available = summary.lean.status == LeanStatus::Available;

    Ok(CorpusCaseReport {
        id: "sdk-expression-builder-alias-proof",
        tier: "P1",
        workflow: "fallible property-owned expression builders",
        expected: ExpectedOutcome::Proved,
        actual: summary.outcome,
        checks: "`Property::bv_add` / `bv_equals` / `int_add` / `int_equals` / `bool_implies` build a proved mixed Bool/BV/Int identity with checked evidence",
        baseline_analogue: "Kani assertion builder / z3.rs context-owned term builder",
        lean_required: false,
        lean_available,
    })
}

fn unsigned_bv_counterexample_minimized() -> CorpusResult<CorpusCaseReport> {
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
        workflow: "unsigned small failing input",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        checks: "minimized `u8` witness is `6`; Rust scalar replay binding renders deterministically",
        baseline_analogue: "proptest-style shrinking",
        lean_required: false,
        lean_available: false,
    })
}

fn signed_bv_counterexample_minimized() -> CorpusResult<CorpusCaseReport> {
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
        workflow: "signed fixed-width input order",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        checks: "minimized signed witness is `-3`; two's-complement Rust binding preserves signed intent",
        baseline_analogue: "Kani/proptest signed integer witness",
        lean_required: false,
        lean_available: false,
    })
}

fn aggregate_counterexample_rendered() -> CorpusResult<CorpusCaseReport> {
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
    assert_eq!(
        property
            .counterexample(model)?
            .render_rust_named_struct_let("transfer", "TransferInput", "transfer")?,
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
        workflow: "struct-shaped symbolic input",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        checks: "minimized transfer witness is `{ enabled: false, amount: 1, balance: 0 }`; direct Rust aggregate initializer renders",
        baseline_analogue: "Kani struct harness / proptest `Arbitrary` struct",
        lean_required: false,
        lean_available: false,
    })
}

fn overflow_helper_counterexample_minimized() -> CorpusResult<CorpusCaseReport> {
    let mut property = Property::new();
    let x = property.symbolic::<u8>("x")?;
    let y = property.symbolic::<u8>("y")?;
    let overflow = x.uadd_overflows(&mut property, y)?;
    let no_overflow = overflow.not(&mut property)?;

    let certificate = property.prove_minimized_with_certificate(no_overflow)?;
    let ProofOutcome::Disproved(model) = &certificate.outcome else {
        panic!(
            "expected an overflow counterexample, got {:?}",
            certificate.outcome
        );
    };
    assert_eq!(property.concrete::<u8>(&x, model)?, Some(1));
    assert_eq!(property.concrete::<u8>(&y, model)?, Some(u8::MAX));
    assert_eq!(
        property.counterexample(model)?.render_rust_let_bindings()?,
        concat!(
            "let x: u8 = 0x01_u8; // BV8\n",
            "let y: u8 = 0xff_u8; // BV8\n",
        )
    );
    let summary = certificate.summary();
    assert_eq!(summary.lean.status, LeanStatus::NotApplicable);

    Ok(CorpusCaseReport {
        id: "sdk-u8-uadd-overflow-helper-witness",
        tier: "P1",
        workflow: "unsigned overflow helper witness",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        checks: "minimized `u8` overflow witness is `(x = 1, y = 255)`; replay bindings render deterministically",
        baseline_analogue: "Kani arithmetic-overflow check / Rust verifier overflow assertion",
        lean_required: false,
        lean_available: false,
    })
}

fn proptest_style_baseline_counterexample_comparison() -> CorpusResult<CorpusCaseReport> {
    let expected = first_wrapping_add_monotonicity_failure()
        .expect("bounded executable baseline should find the first overflow witness");

    let mut property = Property::new();
    let x = property.symbolic::<u8>("x")?;
    let y = property.symbolic::<u8>("y")?;
    let sum = x.add(&mut property, y)?;
    let goal = sum.uge(&mut property, x)?;

    let certificate = property.prove_minimized_with_certificate(goal)?;
    let ProofOutcome::Disproved(model) = &certificate.outcome else {
        panic!(
            "expected a baseline-comparable counterexample, got {:?}",
            certificate.outcome
        );
    };
    let actual = (
        property
            .concrete::<u8>(&x, model)?
            .expect("model should bind x"),
        property
            .concrete::<u8>(&y, model)?
            .expect("model should bind y"),
    );
    assert_eq!(actual, expected);
    assert_eq!(
        property.counterexample(model)?.render_rust_let_bindings()?,
        concat!(
            "let x: u8 = 0x01_u8; // BV8\n",
            "let y: u8 = 0xff_u8; // BV8\n",
        )
    );
    let summary = certificate.summary();
    assert_eq!(summary.lean.status, LeanStatus::NotApplicable);

    Ok(CorpusCaseReport {
        id: "sdk-u8-baseline-counterexample-compare",
        tier: "P1",
        workflow: "bounded baseline comparison for a minimized witness",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        checks: "solver-minimized witness `(x = 1, y = 255)` matches the first executable proptest-style baseline failure",
        baseline_analogue: "proptest exhaustive/shrink baseline over the same Rust predicate",
        lean_required: false,
        lean_available: false,
    })
}

fn first_wrapping_add_monotonicity_failure() -> Option<(u8, u8)> {
    for x in u8::MIN..=u8::MAX {
        for y in u8::MIN..=u8::MAX {
            if x.wrapping_add(y) < x {
                return Some((x, y));
            }
        }
    }
    None
}

fn kani_style_baseline_proof_comparison() -> CorpusResult<CorpusCaseReport> {
    assert_eq!(
        first_wrapping_add_commutativity_failure(),
        None,
        "bounded executable baseline should find no add-commutativity failure",
    );

    let mut property = Property::new();
    let x = property.symbolic::<u8>("x")?;
    let y = property.symbolic::<u8>("y")?;
    let xy = x.add(&mut property, y)?;
    let yx = y.add(&mut property, x)?;
    let goal = xy.equals(&mut property, yx)?;

    let certificate = property.prove_with_certificate(goal)?;
    let summary = certificate.summary();
    assert!(matches!(summary.outcome, ProofOutcomeSummary::Proved));
    assert!(
        summary.evidence.is_some(),
        "proved baseline comparison should expose checked evidence"
    );
    let lean_available = summary.lean.status == LeanStatus::Available;

    Ok(CorpusCaseReport {
        id: "sdk-u8-baseline-proof-compare",
        tier: "P1",
        workflow: "bounded baseline comparison for a proved assertion",
        expected: ExpectedOutcome::Proved,
        actual: summary.outcome,
        checks: "executable baseline finds no `x + y != y + x` failure for `u8`; Axeyum proves the same assertion with checked evidence",
        baseline_analogue: "Kani exhaustive bounded assertion over the same Rust predicate",
        lean_required: false,
        lean_available,
    })
}

fn first_wrapping_add_commutativity_failure() -> Option<(u8, u8)> {
    for x in u8::MIN..=u8::MAX {
        for y in u8::MIN..=u8::MAX {
            if x.wrapping_add(y) != y.wrapping_add(x) {
                return Some((x, y));
            }
        }
    }
    None
}

fn kani_style_struct_baseline_counterexample_comparison() -> CorpusResult<CorpusCaseReport> {
    let expected = first_transfer_withdraw_failure()
        .expect("bounded executable baseline should find the first struct failure");

    let mut property = Property::new();
    let transfer = property.symbolic::<BaselineTransferInput>("transfer")?;
    let amount_within_balance = property.bv_ule(transfer.amount, transfer.balance)?;
    let goal = property.bool_implies(transfer.enabled, amount_within_balance)?;

    let certificate = property.prove_minimized_with_certificate(goal)?;
    let ProofOutcome::Disproved(model) = &certificate.outcome else {
        panic!(
            "expected a struct baseline-comparable counterexample, got {:?}",
            certificate.outcome
        );
    };
    let actual = property
        .concrete::<BaselineTransferInput>(&transfer, model)?
        .expect("model should bind transfer");
    assert_eq!(actual, expected);
    assert_eq!(
        actual,
        BaselineTransferInput {
            enabled: true,
            amount: 1,
            balance: 0,
        }
    );
    assert_eq!(
        property
            .counterexample(model)?
            .render_rust_named_struct_let("transfer", "TransferInput", "transfer")?,
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
        id: "sdk-struct-baseline-counterexample-compare",
        tier: "P1",
        workflow: "bounded struct baseline comparison for a minimized witness",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        checks: "solver-minimized `TransferInput { enabled: true, amount: 1, balance: 0 }` matches the first executable bounded struct failure",
        baseline_analogue: "Kani struct harness / proptest `Arbitrary` struct over the same predicate",
        lean_required: false,
        lean_available: false,
    })
}

fn first_transfer_withdraw_failure() -> Option<BaselineTransferInput> {
    for enabled in [false, true] {
        for amount in u8::MIN..=u8::MAX {
            for balance in u8::MIN..=u8::MAX {
                let input = BaselineTransferInput {
                    enabled,
                    amount,
                    balance,
                };
                if !transfer_withdraw_property(input) {
                    return Some(input);
                }
            }
        }
    }
    None
}

fn transfer_withdraw_property(input: BaselineTransferInput) -> bool {
    !input.enabled || input.amount <= input.balance
}

fn derive_symbolic_counterexample_lifted() -> CorpusResult<CorpusCaseReport> {
    #[derive(Debug, Clone, PartialEq, Eq, axeyum_property::Symbolic)]
    struct TransferInput {
        enabled: bool,
        amount: u16,
        balance: u16,
    }

    let mut property = Property::new();
    let transfer = property.symbolic::<TransferInput>("transfer")?;
    let goal = transfer.amount.ule(&mut property, transfer.balance)?;

    let certificate = property.prove_minimized_with_certificate(goal)?;
    let ProofOutcome::Disproved(model) = &certificate.outcome else {
        panic!(
            "expected a derived-struct counterexample, got {:?}",
            certificate.outcome
        );
    };
    assert_eq!(
        property.concrete::<TransferInput>(&transfer, model)?,
        Some(TransferInput {
            enabled: false,
            amount: 1,
            balance: 0,
        })
    );
    assert_eq!(
        property
            .counterexample(model)?
            .render_rust_named_struct_let("transfer", "TransferInput", "transfer")?,
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
        id: "sdk-derived-struct-counterexample-lift",
        tier: "P1",
        workflow: "`derive(Symbolic)` struct witness",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        checks: "derived `TransferInput` lifts to `{ enabled: false, amount: 1, balance: 0 }`; aggregate initializer renders",
        baseline_analogue: "Kani struct harness / proptest `Arbitrary` struct",
        lean_required: false,
        lean_available: false,
    })
}

fn explicit_nested_aggregate_replay_rendered() -> CorpusResult<CorpusCaseReport> {
    #[derive(Debug, Clone, Copy)]
    struct TransferExpr {
        enabled: Bool,
        amount: Bv<8>,
        fee: Bv<8>,
    }

    let mut property = Property::new();
    let transfer = property.symbolic_struct("transfer", |fields| {
        Ok(TransferExpr {
            enabled: fields.field::<bool>("enabled")?,
            amount: fields.field::<u8>("amount")?,
            fee: fields.struct_field("limits", |limits| limits.field::<u8>("fee"))?,
        })
    })?;
    let goal = transfer.amount.ule(&mut property, transfer.fee)?;

    let certificate = property.prove_minimized_with_certificate(goal)?;
    let ProofOutcome::Disproved(model) = &certificate.outcome else {
        panic!(
            "expected a nested aggregate counterexample, got {:?}",
            certificate.outcome
        );
    };
    assert_eq!(
        property.concrete::<bool>(&transfer.enabled, model)?,
        Some(false)
    );
    assert_eq!(property.concrete::<u8>(&transfer.amount, model)?, Some(1));
    assert_eq!(property.concrete::<u8>(&transfer.fee, model)?, Some(0));
    let counterexample = property.counterexample(model)?;
    let transfer_limits = counterexample.render_rust_named_struct_let(
        "transfer.limits",
        "TransferLimits",
        "transfer_limits",
    )?;
    assert_eq!(
        transfer_limits,
        concat!(
            "let transfer_limits: TransferLimits = TransferLimits {\n",
            "    fee: transfer_limits_fee,\n",
            "};\n",
        )
    );
    let transfer_init = counterexample.render_rust_named_struct_let_with_fields(
        "transfer",
        "TransferInput",
        "transfer",
        [("limits", "transfer_limits")],
    )?;
    assert_eq!(
        transfer_init,
        concat!(
            "let transfer: TransferInput = TransferInput {\n",
            "    enabled: transfer_enabled,\n",
            "    amount: transfer_amount,\n",
            "    limits: transfer_limits,\n",
            "};\n",
        )
    );
    assert_nested_replay_test_rendering(&counterexample, &transfer_limits, &transfer_init)?;
    assert_nested_replay_module_rendering(&counterexample, &transfer_limits, &transfer_init)?;
    assert_nested_replay_fixture_file_rendering(&counterexample, &transfer_limits, &transfer_init)?;
    let summary = certificate.summary();
    assert_eq!(summary.lean.status, LeanStatus::NotApplicable);

    Ok(CorpusCaseReport {
        id: "sdk-explicit-nested-aggregate-replay",
        tier: "P1",
        workflow: "caller-owned nested aggregate replay",
        expected: ExpectedOutcome::Disproved,
        actual: summary.outcome,
        checks: "generated multi-case fixture file includes caller-owned imports, nested `transfer.limits` setup, `TransferInput` setup, and a helper-rendered `Result<bool, _>` replay assertion in order",
        baseline_analogue: "Rust verifier domain replay body / Kani nested harness struct",
        lean_required: false,
        lean_available: false,
    })
}

fn assert_nested_replay_test_rendering(
    counterexample: &Counterexample,
    transfer_limits: &str,
    transfer_init: &str,
) -> CorpusResult<()> {
    assert_eq!(
        Counterexample::render_rust_replay_assertion("replay_transfer", ["transfer"]),
        "assert!(replay_transfer(transfer));\n"
    );
    assert_eq!(
        Counterexample::render_rust_replay_expect_ok(
            "replay_transfer_checked",
            ["transfer"],
            "counterexample replay failed",
        ),
        "replay_transfer_checked(transfer).expect(\"counterexample replay failed\");\n"
    );
    assert_eq!(
        Counterexample::render_rust_replay_expect_ok_assertion(
            "replay_transfer",
            ["transfer"],
            "counterexample replay failed",
        ),
        "assert!(replay_transfer(transfer).expect(\"counterexample replay failed\"));\n"
    );
    assert_eq!(
        counterexample.render_rust_test_with_replay_expect_ok_assertion(
            "nested transfer replay",
            ["use crate::{TransferInput, TransferLimits};"],
            [transfer_limits, transfer_init],
            "replay_transfer",
            ["transfer"],
            "counterexample replay failed",
        )?,
        concat!(
            "use crate::{TransferInput, TransferLimits};\n",
            "\n",
            "#[test]\n",
            "fn nested_transfer_replay() {\n",
            "    let transfer_enabled: bool = false;\n",
            "    let transfer_amount: u8 = 0x01_u8; // BV8\n",
            "    let transfer_limits_fee: u8 = 0x00_u8; // BV8\n",
            "    let transfer_limits: TransferLimits = TransferLimits {\n",
            "        fee: transfer_limits_fee,\n",
            "    };\n",
            "    let transfer: TransferInput = TransferInput {\n",
            "        enabled: transfer_enabled,\n",
            "        amount: transfer_amount,\n",
            "        limits: transfer_limits,\n",
            "    };\n",
            "    assert!(replay_transfer(transfer).expect(\"counterexample replay failed\"));\n",
            "}\n",
        )
    );
    Ok(())
}

fn assert_nested_replay_module_rendering(
    counterexample: &Counterexample,
    transfer_limits: &str,
    transfer_init: &str,
) -> CorpusResult<()> {
    let test = counterexample.render_rust_test_with_replay_expect_ok_assertion(
        "nested transfer replay",
        std::iter::empty::<&str>(),
        [transfer_limits, transfer_init],
        "replay_transfer",
        ["transfer"],
        "counterexample replay failed",
    )?;
    assert_eq!(
        Counterexample::render_rust_test_module(
            "counterexample module",
            ["use crate::{TransferInput, TransferLimits};"],
            [test.as_str()],
        ),
        concat!(
            "#[cfg(test)]\n",
            "mod counterexample_module {\n",
            "    use crate::{TransferInput, TransferLimits};\n",
            "\n",
            "    #[test]\n",
            "    fn nested_transfer_replay() {\n",
            "        let transfer_enabled: bool = false;\n",
            "        let transfer_amount: u8 = 0x01_u8; // BV8\n",
            "        let transfer_limits_fee: u8 = 0x00_u8; // BV8\n",
            "        let transfer_limits: TransferLimits = TransferLimits {\n",
            "            fee: transfer_limits_fee,\n",
            "        };\n",
            "        let transfer: TransferInput = TransferInput {\n",
            "            enabled: transfer_enabled,\n",
            "            amount: transfer_amount,\n",
            "            limits: transfer_limits,\n",
            "        };\n",
            "        assert!(replay_transfer(transfer).expect(\"counterexample replay failed\"));\n",
            "    }\n",
            "}\n",
        )
    );
    Ok(())
}

fn assert_nested_replay_fixture_file_rendering(
    counterexample: &Counterexample,
    transfer_limits: &str,
    transfer_init: &str,
) -> CorpusResult<()> {
    let test = counterexample.render_rust_test_with_replay_expect_ok_assertion(
        "nested transfer replay",
        std::iter::empty::<&str>(),
        [transfer_limits, transfer_init],
        "replay_transfer",
        ["transfer"],
        "counterexample replay failed",
    )?;
    let replay_module = Counterexample::render_rust_test_module(
        "counterexample module",
        ["use crate::{TransferInput, TransferLimits};"],
        [test.as_str()],
    );
    let smoke_module = Counterexample::render_rust_test_module(
        "fixture smoke",
        std::iter::empty::<&str>(),
        ["#[test]\nfn fixture_file_smoke() {}\n"],
    );
    let file = Counterexample::render_rust_test_file(
        ["#![allow(dead_code)]"],
        [replay_module.as_str(), smoke_module.as_str()],
    );
    assert!(
        file.starts_with("#![allow(dead_code)]\n\n#[cfg(test)]\nmod counterexample_module {\n")
    );
    assert!(
        file.contains(
            "assert!(replay_transfer(transfer).expect(\"counterexample replay failed\"));"
        )
    );
    assert!(file.contains("mod fixture_smoke {\n    #[test]\n    fn fixture_file_smoke() {}\n}"));
    let replay_index = file
        .find("mod counterexample_module")
        .expect("fixture file should include replay module");
    let smoke_index = file
        .find("mod fixture_smoke")
        .expect("fixture file should include smoke module");
    assert!(replay_index < smoke_index);
    Ok(())
}
