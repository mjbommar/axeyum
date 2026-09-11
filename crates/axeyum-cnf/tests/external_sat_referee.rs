//! The native CDCL core adjudicated by an **external SAT binary** reading the
//! DIMACS **text** we wrote (ADR-1910).
//!
//! # This file has NO feature gate, on purpose
//!
//! The referee it replaces — `tests/native_vs_batsat_differential.rs`, behind
//! `--features batsat-reference` — was measured on 2026-09-10 to be wired into
//! **no** gate, CI job, `justfile` recipe or git hook. It provided zero
//! automatic assurance from the day it landed. A referee that exists and never
//! runs is worse than no referee, because its presence is what makes the
//! assurance ledger read as covered. So this file is compiled and run by a
//! default `cargo test -p axeyum-cnf`, and is registered in `scripts/check.sh`,
//! the `justfile` and `hooks/pre-push` through
//! `scripts/check-external-sat-referee.sh`.
//!
//! # What it can see that the batsat differential could not
//!
//! The batsat differential handed the reference engine the *same*
//! [`CnfFormula`] object the native core solved, built by our own parser. A
//! defect in `parse_dimacs` or in `to_dimacs` was therefore invisible to it:
//! both engines consumed the same wrong formula and agreed.
//!
//! This referee closes that. Three verdicts are compared per instance:
//!
//! | arm | what it consumes |
//! |---|---|
//! | `native_direct` | the in-memory [`CnfFormula`] — the production path |
//! | `native_roundtrip` | `parse_dimacs(&formula.to_dimacs())` — our writer **and** our parser |
//! | external | the DIMACS **text file**, through the external binary's own parser |
//!
//! A `to_dimacs` defect separates the external arm from `native_direct`. A
//! `parse_dimacs` defect separates it from `native_roundtrip`. A shared
//! core/checker defect — the specific gap our DRAT checkers cannot close,
//! because they are the same project — separates it from both. None of those
//! three is reachable by an in-process referee fed our own `CnfFormula`.
//!
//! Every `sat` is also *replayed*: the external solver's `v`-line assignment is
//! parsed and evaluated against the ORIGINAL in-memory formula. That is a
//! second, independent probe of the writer's variable numbering — a permuted or
//! off-by-one variable map yields an external model that does not satisfy the
//! formula it supposedly came from, even when both sides say `sat`.
//!
//! # Absence is a LOUD skip, never a silent pass
//!
//! No Cargo dependency is added: `CaDiCaL` and Kissat are external binaries, which
//! is the whole reason this is strictly cheaper than the `rustsat-batsat`
//! dependency it replaces (ADR-0002's no-C/C++-in-the-default-graph rule is
//! untouched — nothing here links anything).
//!
//! Resolution order per referee: `AXEYUM_CADICAL_BIN` / `AXEYUM_KISSAT_BIN`,
//! then `PATH`, then `~/.local/bin/`. Provision with
//! `scripts/provision-external-sat-referee.sh`.
//!
//! - With at least one binary: every test adjudicates and asserts a NONZERO
//!   compared count, printing `external-sat-referee: compared=N` so the gate
//!   wrapper can re-derive the finding rather than trusting the exit status.
//! - With none: each test prints a loud multi-line banner to stderr and returns.
//!   `scripts/check-external-sat-referee.sh` is what turns that into a visible
//!   SKIP line in the aggregate gate, and `AXEYUM_REQUIRE_EXTERNAL_SAT=1` turns
//!   it into a FAILURE — set that in any lane that publishes a soundness claim.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use axeyum_cnf::{
    CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar, SatResult, parse_dimacs,
    solve_with_native_core,
};

/// Wall-clock budget handed to the external binary, in seconds.
///
/// Every instance in this file is decided by both engines in milliseconds; the
/// budget exists so a pathological regression stalls one instance instead of
/// wedging the gate. The binary's own limit flag is the backstop — the same
/// contract `tests/common_cvc5` uses for cvc5's `--tlimit`.
const EXTERNAL_BUDGET_SECS: u64 = 20;

/// One external referee: a name and a resolved binary path.
struct Referee {
    name: &'static str,
    binary: String,
}

/// A coarse verdict from any arm.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    /// Budgeted out. Adjudication-neutral: counted as skipped, never compared.
    Unknown,
}

/// What the external binary said, plus its model when it said `sat`.
struct ExternalAnswer {
    verdict: Verdict,
    /// Zero-based variable values, present exactly when `verdict == Sat`.
    model: Option<Vec<bool>>,
}

fn responds(binary: &str) -> bool {
    Command::new(binary)
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

/// Resolve one referee by env override, then `PATH`, then `~/.local/bin`.
fn resolve(name: &'static str, env_var: &str) -> Option<Referee> {
    let make = |binary: String| Referee { name, binary };
    if let Ok(binary) = std::env::var(env_var) {
        // An explicit override that does not respond is a configuration error
        // the operator asked for, so it is reported rather than silently
        // falling through to a different binary than the one named.
        return if responds(&binary) {
            Some(make(binary))
        } else {
            eprintln!(
                "external-sat-referee: {env_var}={binary} does not respond to --version; \
                 treating {name} as absent"
            );
            None
        };
    }
    if responds(name) {
        return Some(make(name.to_string()));
    }
    if let Ok(home) = std::env::var("HOME") {
        let candidate = format!("{home}/.local/bin/{name}");
        if responds(&candidate) {
            return Some(make(candidate));
        }
    }
    None
}

/// Every external referee available on this host, in a deterministic order.
fn referees() -> Vec<Referee> {
    let mut found = Vec::new();
    if let Some(referee) = resolve("cadical", "AXEYUM_CADICAL_BIN") {
        found.push(referee);
    }
    if let Some(referee) = resolve("kissat", "AXEYUM_KISSAT_BIN") {
        found.push(referee);
    }
    found
}

fn require_external() -> bool {
    std::env::var("AXEYUM_REQUIRE_EXTERNAL_SAT").as_deref() == Ok("1")
}

/// Print the loud absence banner, or panic under `AXEYUM_REQUIRE_EXTERNAL_SAT=1`.
///
/// Returns `true` when the caller should return without adjudicating. There is
/// no third outcome: a caller that gets `false` has at least one referee.
fn announce_absence(test: &str) -> bool {
    assert!(
        !require_external(),
        "AXEYUM_REQUIRE_EXTERNAL_SAT=1 but neither `cadical` nor `kissat` was found. \
         Provision one with `scripts/provision-external-sat-referee.sh`, or point \
         AXEYUM_CADICAL_BIN / AXEYUM_KISSAT_BIN at an existing binary."
    );
    eprintln!(
        "\n\
         ================================================================\n\
         external-sat-referee: SKIPPED -- {test}\n\
         NO external SAT binary found (cadical, kissat).\n\
         THIS TEST ADJUDICATED NOTHING. It is not evidence of agreement.\n\
         Provision:  scripts/provision-external-sat-referee.sh\n\
         Or set:     AXEYUM_CADICAL_BIN=/path/to/cadical\n\
         To make absence a FAILURE: AXEYUM_REQUIRE_EXTERNAL_SAT=1\n\
         ================================================================\n"
    );
    true
}

/// A unique scratch path for one instance. Never a fixed name: this repository
/// runs many lanes and many test threads against one `/tmp`.
fn scratch_path() -> PathBuf {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |d| d.as_nanos());
    let serial = COUNTER.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "axeyum-external-sat-referee-{}-{nanos}-{serial}.cnf",
        std::process::id()
    ))
}

/// Run one referee on a DIMACS **file**, returning its verdict and model.
///
/// A spawn failure, a non-{0,10,20} exit, or output that names no verdict is a
/// hard error rather than an `Unknown`: every instance here is tiny, so a
/// process-level failure is a broken referee, not a budgeted-out instance, and
/// swallowing it would be exactly the silent-pass shape this file exists to
/// avoid.
fn external_decide(referee: &Referee, path: &Path, variables: usize) -> ExternalAnswer {
    let mut command = Command::new(&referee.binary);
    match referee.name {
        "cadical" => {
            command
                .arg("-q")
                .arg("-t")
                .arg(EXTERNAL_BUDGET_SECS.to_string());
        }
        "kissat" => {
            command
                .arg("-q")
                .arg(format!("--time={EXTERNAL_BUDGET_SECS}"));
        }
        other => panic!("unknown referee {other}: no limit flag is known for it"),
    }
    command.arg(path);
    let output = command
        .output()
        .unwrap_or_else(|error| panic!("{} spawn failed: {error}", referee.binary));

    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let code = output.status.code();

    // The SAT-competition exit contract: 10 = SATISFIABLE, 20 = UNSATISFIABLE,
    // 0 = undecided. Both the status and the `s` line are read, and they must
    // agree -- a solver whose exit code and stdout disagree is a broken referee.
    let from_status = match code {
        Some(10) => Some(Verdict::Sat),
        Some(20) => Some(Verdict::Unsat),
        Some(0) => Some(Verdict::Unknown),
        _ => None,
    };
    let from_stdout = stdout.lines().find_map(|line| match line.trim() {
        "s SATISFIABLE" => Some(Verdict::Sat),
        "s UNSATISFIABLE" => Some(Verdict::Unsat),
        _ => None,
    });
    let verdict = match (from_status, from_stdout) {
        (Some(status), Some(text)) => {
            assert_eq!(
                status,
                text,
                "{} exit code and `s` line disagree on {}: stdout={stdout:?}",
                referee.binary,
                path.display()
            );
            status
        }
        (Some(Verdict::Unknown), None) => Verdict::Unknown,
        (status, text) => panic!(
            "{} produced no usable verdict on {} (exit={code:?} status_verdict={status:?} \
             stdout_verdict={text:?}) stdout={stdout:?} stderr={stderr:?}",
            referee.binary,
            path.display()
        ),
    };

    let model = (verdict == Verdict::Sat).then(|| parse_v_lines(&stdout, variables, referee, path));
    ExternalAnswer { verdict, model }
}

/// Parse the SAT-competition `v` lines into zero-based variable values.
///
/// The format allows the assignment to span several `v` lines and closes with a
/// literal `0`. A variable the solver did not mention defaults to `false`; the
/// resulting vector is always exactly `variables` long, which is what
/// [`CnfAssignment::satisfies`] requires.
fn parse_v_lines(stdout: &str, variables: usize, referee: &Referee, path: &Path) -> Vec<bool> {
    let mut values = vec![false; variables];
    let mut seen: BTreeMap<usize, bool> = BTreeMap::new();
    for line in stdout.lines() {
        let Some(rest) = line.strip_prefix("v ").or_else(|| line.strip_prefix("v\t")) else {
            continue;
        };
        for token in rest.split_whitespace() {
            let literal: i64 = token.parse().unwrap_or_else(|error| {
                panic!(
                    "{} emitted an unparseable `v` token {token:?} on {}: {error}",
                    referee.binary,
                    path.display()
                )
            });
            if literal == 0 {
                continue;
            }
            let magnitude = usize::try_from(literal.unsigned_abs())
                .expect("a DIMACS variable index fits usize");
            assert!(
                magnitude <= variables,
                "{} named variable {magnitude} on {}, which declares only {variables}",
                referee.binary,
                path.display()
            );
            seen.insert(magnitude - 1, literal > 0);
        }
    }
    for (index, value) in seen {
        values[index] = value;
    }
    values
}

fn native_verdict(result: &SatResult) -> Verdict {
    match result {
        SatResult::Sat(_) => Verdict::Sat,
        SatResult::Unsat(_) => Verdict::Unsat,
        SatResult::Unknown(_) => Verdict::Unknown,
    }
}

/// Adjudicate one formula against every available referee.
///
/// Returns the number of (instance, referee) pairs actually compared — zero
/// when an arm answered `Unknown`, which is neutral and never a disagreement.
fn adjudicate(label: &str, formula: &CnfFormula, referees: &[Referee]) -> usize {
    let text = formula.to_dimacs();
    let reparsed = parse_dimacs(&text).unwrap_or_else(|error| {
        panic!("{label}: our own writer produced text we cannot parse: {error}")
    });

    let direct = solve_with_native_core(formula).expect("native core must not error");
    let roundtrip = solve_with_native_core(&reparsed).expect("native core must not error");

    for (arm, result) in [("direct", &direct), ("roundtrip", &roundtrip)] {
        if let SatResult::Sat(model) = result {
            let target = if arm == "direct" { formula } else { &reparsed };
            assert!(
                model.satisfies(target).expect("model fits the formula"),
                "{label}: the native core's {arm} model does not satisfy the formula"
            );
        }
    }

    let path = scratch_path();
    std::fs::write(&path, &text)
        .unwrap_or_else(|error| panic!("{label}: write {}: {error}", path.display()));

    let mut compared = 0usize;
    for referee in referees {
        let answer = external_decide(referee, &path, formula.variable_count());

        if let Some(values) = &answer.model {
            let assignment = CnfAssignment::new(values.clone());
            assert!(
                assignment
                    .satisfies(formula)
                    .expect("external model has the declared variable count"),
                "{label}: {}'s model does NOT satisfy the formula it was written from. \
                 Both engines may still say `sat`, so this is a DIMACS writer or variable-map \
                 defect, not a search defect -- and it is invisible to any in-process referee.",
                referee.name
            );
        }

        for (arm, result) in [("direct", &direct), ("roundtrip", &roundtrip)] {
            let ours = native_verdict(result);
            if ours == Verdict::Unknown || answer.verdict == Verdict::Unknown {
                continue;
            }
            assert_eq!(
                ours,
                answer.verdict,
                "{label}: VERDICT DISAGREEMENT native({arm})={ours:?} {}={:?} -- this is a P0 \
                 soundness finding, not a flake. The DIMACS text is preserved at {}; record it \
                 before doing anything else.",
                referee.name,
                answer.verdict,
                path.display()
            );
            compared += 1;
        }
    }

    // Removed only on success, so a disagreement leaves the exact text both
    // engines read on disk for the panic message to name.
    let _ = std::fs::remove_file(&path);
    compared
}

/// Report the adjudicated count in a shape `scripts/check-external-sat-referee.sh`
/// re-derives the finding from, instead of trusting a zero exit status.
fn report(test: &str, compared: usize, referees: &[Referee]) {
    let names: Vec<&str> = referees.iter().map(|referee| referee.name).collect();
    println!(
        "external-sat-referee: compared={compared} test={test} referees={}",
        names.join(",")
    );
    assert!(
        compared > 0,
        "{test}: ZERO comparisons were made against {} -- the test passed while \
         adjudicating nothing, which is the failure mode this file exists to prevent",
        names.join(",")
    );
}

fn micro_cnf_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../corpus/micro-cnf")
}

#[test]
fn the_committed_micro_cnf_corpus_agrees_with_the_external_referee() {
    let referees = referees();
    if referees.is_empty() && announce_absence("micro-cnf corpus") {
        return;
    }

    let dir = micro_cnf_dir();
    let mut paths: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|error| panic!("read {}: {error}", dir.display()))
        .map(|entry| entry.expect("dir entry").path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "cnf"))
        .collect();
    paths.sort();
    assert!(
        !paths.is_empty(),
        "corpus/micro-cnf/ has no .cnf files: this test would have passed while comparing nothing"
    );

    let mut compared = 0usize;
    for path in &paths {
        let text = std::fs::read_to_string(path).expect("read CNF");
        let formula = parse_dimacs(&text).expect("parse CNF");
        let label = path.file_name().expect("file name").to_string_lossy();
        compared += adjudicate(&label, &formula, &referees);
    }
    report("micro-cnf corpus", compared, &referees);
}

/// A deterministic 64-bit LCG. Explicit and seeded, per the workspace
/// determinism promise; nothing here may depend on a system RNG.
struct Lcg(u64);

impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() >> 11).expect("63-bit value fits usize") % bound
    }

    fn bool(&mut self) -> bool {
        self.next() >> 63 == 1
    }
}

/// Random 3-SAT at the threshold ratio: `m = round(4.26 n)` clauses of three
/// distinct variables with random signs.
fn random_3sat(rng: &mut Lcg, variables: usize) -> CnfFormula {
    // 4.26 n = 426 n / 100, rounded half up, in integer arithmetic so the count
    // is exactly reproducible and no cast lint applies.
    let clauses = (variables * 426 + 50) / 100;
    let mut formula = CnfFormula::new(variables);
    for _ in 0..clauses {
        let mut vars: Vec<usize> = Vec::with_capacity(3);
        while vars.len() < 3 {
            let candidate = rng.below(variables);
            if !vars.contains(&candidate) {
                vars.push(candidate);
            }
        }
        let lits: Vec<CnfLit> = vars
            .into_iter()
            .map(|index| {
                let lit = CnfLit::positive(CnfVar::new(index).expect("variable in range"));
                if rng.bool() { lit.negated() } else { lit }
            })
            .collect();
        formula
            .add_clause(CnfClause::new(lits))
            .expect("clause fits the formula");
    }
    formula
}

#[test]
fn seeded_random_3sat_at_the_threshold_ratio_agrees_with_the_external_referee() {
    let referees = referees();
    if referees.is_empty() && announce_absence("random 3-SAT at the threshold ratio") {
        return;
    }

    let mut rng = Lcg(0x5eed_1910_5a71_c0de);
    let mut compared = 0usize;
    let mut sat = 0usize;
    let mut unsat = 0usize;
    for case in 0..120 {
        // 20..=39 variables: small enough that every engine decides every
        // instance well inside its budget, large enough that the threshold
        // ratio actually produces a mix of verdicts.
        let variables = 20 + (case % 20);
        let formula = random_3sat(&mut rng, variables);
        let label = format!("random-3sat case {case} (n={variables})");
        compared += adjudicate(&label, &formula, &referees);
        match solve_with_native_core(&formula).expect("native core") {
            SatResult::Sat(_) => sat += 1,
            SatResult::Unsat(_) => unsat += 1,
            SatResult::Unknown(_) => {}
        }
    }
    // A family that produced only one verdict would be a far weaker referee than
    // it looks: agreement on "everything is satisfiable" is cheap. At the
    // threshold ratio both verdicts must appear.
    assert!(
        sat > 0 && unsat > 0,
        "the threshold family degenerated to one verdict: sat={sat} unsat={unsat}"
    );
    report("random 3-SAT at the threshold ratio", compared, &referees);
}

/// Degenerate shapes the random family cannot produce. Each is a place where two
/// engines' normalisation, or a DIMACS writer and a DIMACS parser, can differ
/// silently.
#[test]
fn degenerate_formulas_agree_with_the_external_referee() {
    let referees = referees();
    if referees.is_empty() && announce_absence("degenerate formulas") {
        return;
    }

    let cases: Vec<(&str, CnfFormula)> = vec![
        ("empty formula", CnfFormula::new(0)),
        ("empty formula with reserved vars", CnfFormula::new(4)),
        (
            "empty clause",
            parse_dimacs("p cnf 1 1\n0\n").expect("parse"),
        ),
        (
            "unit contradiction",
            parse_dimacs("p cnf 1 2\n1 0\n-1 0\n").expect("parse"),
        ),
        (
            "tautological clause",
            parse_dimacs("p cnf 1 1\n1 -1 0\n").expect("parse"),
        ),
        (
            "duplicated literal",
            parse_dimacs("p cnf 2 2\n1 1 2 0\n-1 0\n").expect("parse"),
        ),
        (
            "variable declared but unused",
            parse_dimacs("p cnf 5 1\n1 0\n").expect("parse"),
        ),
    ];
    let mut compared = 0usize;
    for (label, formula) in &cases {
        let before = compared;
        compared += adjudicate(label, formula, &referees);
        assert!(
            compared > before,
            "{label}: a degenerate formula must be decided by both sides, not budgeted out"
        );
    }
    report("degenerate formulas", compared, &referees);
}

/// The referee's own negative control: a formula whose verdict we know
/// independently of both engines must come back with that verdict, and the
/// `v`-line replay must reject a model that is not one.
///
/// Without this, every assertion in this file is of the form "two engines
/// agreed", which is satisfied vacuously by two engines that both do nothing.
/// Here the expected answer is fixed in the test, so a referee that always says
/// `sat` — or a `v`-line parser that always returns a satisfying vector — fails.
#[test]
fn the_referee_answers_are_checked_against_known_verdicts() {
    let referees = referees();
    if referees.is_empty() && announce_absence("known-verdict control") {
        return;
    }

    let known: Vec<(&str, CnfFormula, Verdict)> = vec![
        (
            "known sat",
            parse_dimacs("p cnf 3 2\n1 2 0\n-1 3 0\n").expect("parse"),
            Verdict::Sat,
        ),
        (
            "known unsat",
            parse_dimacs("p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n").expect("parse"),
            Verdict::Unsat,
        ),
    ];

    let mut checked = 0usize;
    for (label, formula, expected) in &known {
        let text = formula.to_dimacs();
        let path = scratch_path();
        std::fs::write(&path, &text).expect("write scratch CNF");
        for referee in &referees {
            let answer = external_decide(referee, &path, formula.variable_count());
            assert_eq!(
                answer.verdict, *expected,
                "{label}: {} answered {:?} where the verdict is known to be {expected:?}",
                referee.name, answer.verdict
            );
            checked += 1;
        }
        let _ = std::fs::remove_file(&path);
    }

    // The `v`-line replay must be able to REJECT. A parser that returns an
    // all-false vector regardless of input would satisfy every `sat` assertion
    // above by accident on some families; here the all-false assignment is known
    // not to be a model, so `satisfies` must say so.
    let formula = parse_dimacs("p cnf 2 1\n1 2 0\n").expect("parse");
    let not_a_model = CnfAssignment::new(vec![false, false]);
    assert!(
        !not_a_model.satisfies(&formula).expect("length matches"),
        "the replay check cannot reject a non-model, so every `sat` assertion in this \
         file is vacuous"
    );

    report("known-verdict control", checked, &referees);
}
