//! **Behavioral probes for every row of [`SUPPORT_MATRIX`]** — one probe per
//! fragment, each running small queries through the ordinary public front door
//! and *deriving* the row's `solver-decides` status from what the engine
//! actually returned.
//!
//! Why this file exists: `SUPPORT_MATRIX` is a hand-written `const`, dispatch
//! never reads it, and before this suite 12 of its 19 rows had no behavioral
//! probe at all. A table nobody executes is documentation, not a check, and it
//! drifts silently. The rule this suite obeys is the repository's own: *make the
//! exit status depend on the finding.*
//!
//! The shape that makes it able to fail:
//!
//! 1. Each probe runs one or more scripts and records the observed verdict
//!    **class** (`sat` / `unsat` / `unknown` / the front door declining).
//! 2. Each observed class is asserted against the class the probe expects, so a
//!    change in engine behavior fails here with a diagnostic.
//! 3. The probe then **derives** a `SolverStatus` from the observed classes
//!    alone and asserts it equals `row.solver`. Flipping a row's claimed status
//!    in `support_matrix.rs` therefore fails exactly the probe for that row.
//!
//! An `unknown` witness must carry `UnknownKind::Incomplete`, never a budget
//! kind: "sound, incomplete" is a claim about the procedure, and a probe that
//! accepted a timeout would pass on a slow machine for the wrong reason.
//!
//! **Run this with `--features full`.** Most theories (the SMT-LIB front door,
//! strings, FP, the CAS routes) live behind it. Without the feature the suite
//! compiles to a single test whose NAME says it is inert, so a run that checks
//! nothing is visible in the output rather than printing `running 0 tests ... ok`:
//!
//! ```text
//! cargo test -p axeyum-solver --features full --test support_matrix_probes
//! ```

#[cfg(not(feature = "full"))]
#[test]
#[allow(non_snake_case)]
fn suite_is_INERT_without_features_full() {
    eprintln!(
        "support_matrix_probes: INERT — every behavioral probe needs `--features full`. \
         Re-run: cargo test -p axeyum-solver --features full --test support_matrix_probes"
    );
}

#[cfg(feature = "full")]
mod probes {
    use axeyum_solver::support_matrix::{SUPPORT_MATRIX, SolverStatus, SupportRow};
    use axeyum_solver::{CheckResult, SolverConfig, SolverError, UnknownKind, solve_smtlib};

    /// The verdict class a probe observes at the front door.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum Class {
        Sat,
        Unsat,
        /// A *structural* `unknown` (`UnknownKind::Incomplete`) — the procedure
        /// says it cannot decide this query, not that a budget ran out.
        UnknownIncomplete,
        /// The front door refused the input outright (`SolverError`).
        Declined,
    }

    /// One script and the class it must produce.
    #[derive(Debug, Clone, Copy)]
    struct Case {
        script: &'static str,
        expect: Class,
    }

    const fn case(script: &'static str, expect: Class) -> Case {
        Case { script, expect }
    }

    /// What a row's probe does.
    #[derive(Debug, Clone, Copy)]
    enum Kind {
        /// Run these SMT-LIB scripts through `solve_smtlib`.
        Scripts(&'static [Case]),
        /// Run the OMT front door (`optimize_smtlib`) instead; the verdict class
        /// is derived from `OptOutcome`.
        Optimize(&'static [Case]),
        /// The row's claim has no cheap observable consequence at the front
        /// door. The string is the reason, and it is REPORTED, never silently
        /// counted as coverage.
        #[allow(dead_code)]
        Unprobed(&'static str),
    }

    #[derive(Debug, Clone, Copy)]
    struct Probe {
        fragment: &'static str,
        kind: Kind,
    }

    // -----------------------------------------------------------------------
    // Verdict-class derivation. This is the whole point: the status is COMPUTED
    // from observations, never copied from the row being checked.
    // -----------------------------------------------------------------------

    fn derive_status(observed: &[Class]) -> SolverStatus {
        let sat = observed.contains(&Class::Sat);
        let unsat = observed.contains(&Class::Unsat);
        let unknown = observed.contains(&Class::UnknownIncomplete);
        match (sat, unsat, unknown) {
            // Both directions decided and nothing structurally undecided.
            (true, true, false) => SolverStatus::Decides,
            // Both directions reachable, but the procedure admits it is
            // incomplete on a query inside the fragment.
            (true, true, true) => SolverStatus::SoundIncomplete,
            // `unsat` decided; the satisfiable direction degrades to unknown.
            (false, true, true) => SolverStatus::UnsatSatUnknown,
            // Nothing was decided in both directions.
            _ => SolverStatus::Unsupported,
        }
    }

    fn row(fragment: &str) -> &'static SupportRow {
        SUPPORT_MATRIX
            .iter()
            .find(|r| r.fragment == fragment)
            .unwrap_or_else(|| {
                panic!(
                    "no SUPPORT_MATRIX row named {fragment:?} — the probe table and the \
                     matrix disagree; fix the probe's fragment key"
                )
            })
    }

    /// Probes run in an aggregate gate, so they are deliberately small: measured
    /// 2026-09-09, the whole 21-test suite ran in **2.53 s** at
    /// `--test-threads=4`, and its slowest single case was the `QF_NIA` Pell
    /// witness at 2.5 s. This budget exists only so a route that regresses into
    /// a search cannot hang the gate. A probe that NEEDS this budget is a bug in
    /// the probe: an `unknown` produced by hitting it carries
    /// `UnknownKind::Timeout`, which `classify` rejects.
    fn config() -> SolverConfig {
        SolverConfig {
            timeout: Some(std::time::Duration::from_secs(30)),
            ..SolverConfig::default()
        }
    }

    fn classify(result: Result<axeyum_solver::SmtLibOutcome, SolverError>) -> Class {
        match result {
            Ok(outcome) => match outcome.result {
                CheckResult::Sat(_) => Class::Sat,
                CheckResult::Unsat => Class::Unsat,
                CheckResult::Unknown(reason) => {
                    assert_eq!(
                        reason.kind,
                        UnknownKind::Incomplete,
                        "an `unknown` used as evidence of incompleteness must be \
                         structural (UnknownKind::Incomplete), not a budget: {reason:?}"
                    );
                    Class::UnknownIncomplete
                }
            },
            Err(_) => Class::Declined,
        }
    }

    fn classify_opt(result: Result<Vec<axeyum_solver::OptOutcome>, SolverError>) -> Class {
        use axeyum_solver::OptOutcome;
        match result {
            Ok(outcomes) => {
                assert!(!outcomes.is_empty(), "optimize probe produced no outcome");
                // Worst class wins, so an undecided objective cannot hide behind
                // a decided sibling.
                if outcomes.iter().any(|o| matches!(o, OptOutcome::Unknown(_))) {
                    for o in &outcomes {
                        if let OptOutcome::Unknown(reason) = o {
                            assert_eq!(
                                reason.kind,
                                UnknownKind::Incomplete,
                                "OMT `unknown` used as evidence of incompleteness must be \
                                 structural: {reason:?}"
                            );
                        }
                    }
                    Class::UnknownIncomplete
                } else if outcomes.iter().any(|o| matches!(o, OptOutcome::Infeasible)) {
                    Class::Unsat
                } else {
                    Class::Sat
                }
            }
            Err(_) => Class::Declined,
        }
    }

    /// Runs one row's probe: assert every case's class, then derive the row's
    /// `solver-decides` status from the observations and assert the matrix
    /// claims exactly that.
    fn run(fragment: &str) {
        let probe = PROBES
            .iter()
            .find(|p| p.fragment == fragment)
            .unwrap_or_else(|| panic!("no probe entry for {fragment:?}"));
        let r = row(fragment);

        let cases: &[Case] = match probe.kind {
            Kind::Unprobed(reason) => {
                assert!(
                    !reason.is_empty(),
                    "an unprobed row must carry a reason: {fragment}"
                );
                eprintln!("UNPROBED  {fragment}\n          reason: {reason}");
                return;
            }
            Kind::Scripts(cases) | Kind::Optimize(cases) => cases,
        };
        assert!(!cases.is_empty(), "probe for {fragment} has no cases");

        let mut observed = Vec::with_capacity(cases.len());
        for c in cases {
            let started = std::time::Instant::now();
            let got = match probe.kind {
                Kind::Optimize(_) => {
                    classify_opt(axeyum_solver::optimize_smtlib(c.script, &config()))
                }
                _ => classify(solve_smtlib(c.script, &config())),
            };
            // Printed, not asserted: probe COST is a thing a reader of this gate
            // must be able to see, but a wall-clock assertion would be flaky
            // under lane contention and would fail for the wrong reason.
            eprintln!(
                "probe {fragment} :: {:?} in {:.2}s",
                got,
                started.elapsed().as_secs_f64()
            );
            assert_eq!(
                got, c.expect,
                "\nrow: {fragment}\nscript: {}\nexpected {:?}, observed {got:?}",
                c.script, c.expect
            );
            observed.push(got);
        }

        let derived = derive_status(&observed);
        assert_eq!(
            derived, r.solver,
            "\nrow: {fragment}\nSUPPORT_MATRIX claims solver-decides = {:?}\n\
             but the observed verdict classes {observed:?} derive {derived:?}.\n\
             Either the claim is wrong or the probe is.",
            r.solver
        );
    }

    // -----------------------------------------------------------------------
    // The probe table. One entry per SUPPORT_MATRIX row; `every_matrix_row_has_a_probe`
    // derives the required key set from the matrix itself, never from a literal.
    // -----------------------------------------------------------------------

    macro_rules! probe_table {
        ( $( $test:ident : $frag:literal => $kind:expr ),* $(,)? ) => {
            const PROBES: &[Probe] = &[ $( Probe { fragment: $frag, kind: $kind } ),* ];
            $(
                #[test]
                fn $test() { run($frag); }
            )*
        };
    }

    probe_table! {
        probe_qf_bv: "QF_BV (scalar bit-vectors)" => Kind::Scripts(&[
            case("(declare-const x (_ BitVec 8))(assert (= x #x01))(assert (= x #x02))(check-sat)", Class::Unsat),
            case("(declare-const x (_ BitVec 8))(assert (bvult x #x05))(check-sat)", Class::Sat),
        ]),

        probe_qf_abv: "QF_ABV (arrays)" => Kind::Scripts(&[
            case("(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))\
                  (declare-const i (_ BitVec 4))\
                  (assert (not (= (select (store a i #x1) i) #x1)))(check-sat)", Class::Unsat),
            case("(declare-const a (Array (_ BitVec 4) (_ BitVec 4)))\
                  (assert (= (select a #x0) #x1))(check-sat)", Class::Sat),
        ]),

        probe_qf_uf: "QF_UF (EUF / congruence)" => Kind::Scripts(&[
            case("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
                  (declare-const a (_ BitVec 8))(declare-const b (_ BitVec 8))\
                  (assert (= (f a) #x01))(assert (= (f b) #x02))(assert (= a b))(check-sat)", Class::Unsat),
            case("(declare-fun f ((_ BitVec 8)) (_ BitVec 8))\
                  (declare-const a (_ BitVec 8))(declare-const b (_ BitVec 8))\
                  (assert (= (f a) #x01))(assert (= (f b) #x02))(check-sat)", Class::Sat),
        ]),

        probe_qf_lia: "QF_LIA (general linear integer)" => Kind::Scripts(&[
            case("(declare-const x Int)(assert (> x 0))(assert (< x 1))(check-sat)", Class::Unsat),
            case("(declare-const x Int)(declare-const y Int)\
                  (assert (> (+ x y) 3))(assert (< x 2))(check-sat)", Class::Sat),
        ]),

        probe_qf_lia_diophantine: "QF_LIA · integer infeasibility (Diophantine + interval)" => Kind::Scripts(&[
            case("(declare-const x Int)(assert (= (* 2 x) 1))(check-sat)", Class::Unsat),
            case("(declare-const x Int)(assert (= (* 2 x) 4))(check-sat)", Class::Sat),
        ]),

        probe_qf_lra: "QF_LRA (linear real)" => Kind::Scripts(&[
            case("(declare-const x Real)(assert (< x 0.0))(assert (> x 1.0))(check-sat)", Class::Unsat),
            case("(declare-const x Real)(assert (> x 0.0))(check-sat)", Class::Sat),
        ]),

        probe_difference_logic: "QF_IDL / QF_RDL (difference logic)" => Kind::Scripts(&[
            case("(declare-const x Int)(declare-const y Int)\
                  (assert (<= (- x y) 0))(assert (<= (- y x) (- 1)))(check-sat)", Class::Unsat),
            case("(declare-const x Int)(declare-const y Int)\
                  (assert (<= (- x y) 3))(assert (<= (- y x) 3))(check-sat)", Class::Sat),
        ]),

        probe_qf_nia: "QF_NIA (nonlinear integer)" => Kind::Scripts(&[
            case("(declare-const x Int)(assert (= (* x x) 2))(check-sat)", Class::Unsat),
            case("(declare-const x Int)(declare-const y Int)\
                  (assert (= (* x y) 6))(assert (> x 1))(assert (> y 1))(check-sat)", Class::Sat),
            // Incompleteness witness. Pell: x² − 2y² = 1 with y > 10⁹ IS
            // satisfiable — the first such solution is y = 3,166,815,962
            // (x = 4,478,554,083), and y exceeds 2³¹ = 2,147,483,648, so the
            // witness lies outside the bounded integer blast. The route returns
            // a sound structural unknown ("no model within the bounded integer
            // width 32") rather than a wrong `unsat`. Measured 2.5 s.
            case("(declare-const x Int)(declare-const y Int)\
                  (assert (= (- (* x x) (* 2 (* y y))) 1))\
                  (assert (> y 1000000000))(check-sat)", Class::UnknownIncomplete),
        ]),

        probe_qf_nra_general: "QF_NRA (general nonlinear real)" => Kind::Scripts(&[
            case("(declare-const x Real)(assert (> (* x x) 4.0))(assert (< x 1.0))(assert (> x 0.0))(check-sat)", Class::Unsat),
            case("(declare-const x Real)(assert (> (* x x) 4.0))(check-sat)", Class::Sat),
            // Incompleteness witness: a coupled degree-4 two-variable system the
            // resultant/CAD side declines ("2-variable resultant elimination
            // could not certify"), and which the general fallback also cannot
            // settle — so the front door returns a sound structural unknown.
            // Measured 0.1 s.
            case("(declare-const x Real)(declare-const y Real)\
                  (assert (= (+ (* x x x x) (* y y y y)) 1.0))\
                  (assert (= (* x x y y) 0.3))\
                  (assert (> x 0.0))(assert (> y 0.0))(check-sat)", Class::UnknownIncomplete),
        ]),

        probe_qf_nra_cad: "QF_NRA · cylindrical decomposition (coupled, mixed/non-strict, any dimension)" => Kind::Scripts(&[
            case("(declare-const x Real)(declare-const y Real)\
                  (assert (>= (+ (* x x) (* y y)) 4.0))(assert (<= x 1.0))(assert (>= x (- 1.0)))\
                  (assert (<= y 1.0))(assert (>= y (- 1.0)))(check-sat)", Class::Unsat),
            case("(declare-const x Real)(declare-const y Real)\
                  (assert (= (+ (* x x) (* y y)) 1.0))(assert (> x 0.0))(check-sat)", Class::Sat),
        ]),

        probe_qf_nra_sos: "QF_NRA · degree-2 SOS / globally-(non)negative quadratic forms" => Kind::Scripts(&[
            case("(declare-const x Real)(declare-const y Real)\
                  (assert (< (+ (* x x) (* y y)) 0.0))(check-sat)", Class::Unsat),
            case("(declare-const x Real)(declare-const y Real)\
                  (assert (> (+ (* x x) (* y y)) 1.0))(check-sat)", Class::Sat),
        ]),

        probe_qf_nra_univariate: "QF_NRA · single-variable real-algebraic" => Kind::Scripts(&[
            case("(declare-const x Real)(assert (= (* x x) (- 1.0)))(check-sat)", Class::Unsat),
            case("(declare-const x Real)(assert (= (* x x) 2.0))(check-sat)", Class::Sat),
        ]),

        probe_uf_arith: "QF_UFLIA / QF_UFLRA (UF + arithmetic)" => Kind::Scripts(&[
            case("(declare-fun f (Int) Int)(declare-const a Int)(declare-const b Int)\
                  (assert (= (f a) 1))(assert (= (f b) 2))(assert (= a b))(check-sat)", Class::Unsat),
            case("(declare-fun f (Int) Int)(declare-const a Int)(declare-const b Int)\
                  (assert (= (f a) 1))(assert (= (f b) 2))(check-sat)", Class::Sat),
        ]),

        probe_qf_fp: "QF_FP (floating-point)" => Kind::Scripts(&[
            case("(declare-const x Float32)(assert (fp.isNaN x))(assert (fp.isZero x))(check-sat)", Class::Unsat),
            case("(declare-const x Float32)(assert (fp.isNaN x))(check-sat)", Class::Sat),
        ]),

        probe_quantifiers: "quantifiers (∃/∀, finite-domain + instantiation)" => Kind::Scripts(&[
            case("(declare-fun p ((_ BitVec 2)) Bool)\
                  (assert (forall ((x (_ BitVec 2))) (p x)))(assert (not (p #b00)))(check-sat)", Class::Unsat),
            case("(declare-fun p ((_ BitVec 2)) Bool)\
                  (assert (forall ((x (_ BitVec 2))) (p x)))(check-sat)", Class::Sat),
            // Incompleteness witness: a forall/exists alternation over an
            // INFINITE domain, outside the finite (Bool/BV), guarded-finite Int
            // and single-variable Fourier-Motzkin fragments the row claims to be
            // complete over. The route says so structurally -- "instantiation is
            // satisfiable; the universal may still be violated outside the
            // instantiated terms" -- in 0.00 s.
            //
            // An earlier candidate here (a f(f(x)) > f(x) refutation) reached
            // `Incomplete` only after 20 s of search, and at a 5 s budget the
            // SAME query returned `ResourceLimit` instead. That is a probe whose
            // verdict depends on host load, so it was replaced rather than kept.
            case("(assert (forall ((x Int)) (exists ((y Int)) (= (* x y) 1))))\
                  (check-sat)", Class::UnknownIncomplete),
        ]),

        probe_datatypes: "datatypes (algebraic)" => Kind::Scripts(&[
            case("(declare-datatypes ((Color 0)) (((red) (green) (blue))))(declare-const c Color)\
                  (assert (not (= c red)))(assert (not (= c green)))(assert (not (= c blue)))(check-sat)", Class::Unsat),
            case("(declare-datatypes ((Color 0)) (((red) (green) (blue))))(declare-const c Color)\
                  (assert (not (= c red)))(check-sat)", Class::Sat),
        ]),

        probe_strings: "strings (bounded)" => Kind::Scripts(&[
            case("(declare-const s String)(assert (= s \"a\"))(assert (= (str.len s) 2))(check-sat)", Class::Unsat),
            case("(declare-const s String)(assert (= (str.len s) 2))(check-sat)", Class::Sat),
            // Incompleteness witness: an unbounded word/Int combination. The
            // recorded length facts force a length past the packed-BV window,
            // so the route reports a structural unknown instead of an
            // encoding-bound "unsat". Measured 0.6-1.3 s.
            case("(declare-const s String)(declare-const n Int)\
                  (assert (= n (str.to_int s)))(assert (> n 1000000000))\
                  (assert (= (str.len s) 40))(check-sat)", Class::UnknownIncomplete),
        ]),

        probe_optimization: "optimization (OMT: box/lex/Pareto, MaxSAT, MILP)" => Kind::Optimize(&[
            case("(declare-const x Int)(assert (<= x 10))(assert (>= x 0))(maximize x)(check-sat)", Class::Sat),
            case("(declare-const x Int)(assert (<= x 10))(assert (>= x 20))(maximize x)(check-sat)", Class::Unsat),
            // Incompleteness witness, and the row's own note verbatim: the
            // optimum "degrades to a sound OptOutcome::Unknown when a probe is
            // undecided". The feasibility probe here is the same undecided
            // string/Int query the strings row uses. Measured 0.1 s.
            case("(declare-const s String)(declare-const n Int)\
                  (assert (= n (str.to_int s)))(assert (> n 1000000000))\
                  (assert (= (str.len s) 40))(maximize n)(check-sat)", Class::UnknownIncomplete),
        ]),

        probe_incremental: "incremental (push/pop, reset-assertions)" => Kind::Scripts(&[
            case("(declare-const x (_ BitVec 4))(assert (= x #x1))\
                  (push 1)(assert (= x #x2))(check-sat)", Class::Unsat),
            case("(declare-const x (_ BitVec 4))(assert (= x #x1))\
                  (push 1)(assert (= x #x2))(pop 1)(check-sat)", Class::Sat),
        ]),
    }

    // -----------------------------------------------------------------------
    // Coverage: derived from the matrix, not from a literal count.
    // -----------------------------------------------------------------------

    /// The probe suite must not be inert, and must cover the matrix exactly.
    #[test]
    fn every_matrix_row_has_a_probe() {
        assert!(
            !PROBES.is_empty(),
            "probe table is empty — the suite is inert"
        );
        let rows: std::collections::BTreeSet<&str> =
            SUPPORT_MATRIX.iter().map(|r| r.fragment).collect();
        let probed: std::collections::BTreeSet<&str> = PROBES.iter().map(|p| p.fragment).collect();
        assert_eq!(
            probed.len(),
            PROBES.len(),
            "duplicate fragment key in the probe table"
        );
        let missing: Vec<_> = rows.difference(&probed).collect();
        let extra: Vec<_> = probed.difference(&rows).collect();
        assert!(
            missing.is_empty() && extra.is_empty(),
            "probe table and SUPPORT_MATRIX disagree.\nrows with no probe: {missing:?}\n\
             probes with no row: {extra:?}"
        );
        assert_eq!(
            PROBES.len(),
            SUPPORT_MATRIX.len(),
            "one probe per row, exactly"
        );
    }

    /// How many rows we could NOT probe. Measured 2026-09-09: **zero** — every
    /// one of the 19 `SUPPORT_MATRIX` rows has a behavioral probe.
    const UNPROBED_ROWS: usize = 0;

    /// The unprobed count is a FINDING, so it is pinned exactly. Marking a row
    /// `Kind::Unprobed` fails here until someone edits this number, which is the
    /// point: silently dropping a row's coverage should cost an edit and a
    /// reason, not nothing.
    ///
    /// `assert_eq!`, not `<=`: the first draft of this guard wrote
    /// `unprobed.len() <= MAX_UNPROBED` with `MAX_UNPROBED = 0`, which is a
    /// comparison a `usize` can never fail — a checker that cannot fail, the
    /// exact thing this whole item exists to remove. Clippy caught it.
    #[test]
    fn unprobed_rows_are_pinned_at_the_measured_count() {
        let unprobed: Vec<(&str, &str)> = PROBES
            .iter()
            .filter_map(|p| match p.kind {
                Kind::Unprobed(reason) => Some((p.fragment, reason)),
                Kind::Scripts(_) | Kind::Optimize(_) => None,
            })
            .collect();
        for (frag, reason) in &unprobed {
            eprintln!("UNPROBED  {frag}\n          reason: {reason}");
        }
        assert_eq!(
            unprobed.len(),
            UNPROBED_ROWS,
            "the unprobed-row count moved: {unprobed:?}. If a row genuinely \
             cannot be probed at the front door, say so in its `Kind::Unprobed` \
             reason and update `UNPROBED_ROWS` — do not widen this check."
        );
    }
}
