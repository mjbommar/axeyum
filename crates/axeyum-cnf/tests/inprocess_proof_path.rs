//! The proof-carrying inprocessing path: does the certificate survive it?
//!
//! ADR-1750. Three obligations, and the third is the one that has teeth:
//!
//! 1. **Zero wrong verdicts.** Every enabled pass combination agrees with the
//!    unreduced solver on every instance, and every `sat` model — after the
//!    reduction's lift — satisfies the **original** formula.
//! 2. **Every `unsat` still produces a proof our own checker accepts**, over a
//!    corpus run end to end, against the original formula rather than the
//!    reduced one.
//! 3. **A soundness-negative test per pass.** For each pass, the prefix it
//!    emitted is corrupted the way a real emission bug corrupts it, and the
//!    checker is required to reject. A pass whose corruption still yields an
//!    accepted proof is not a passing test — it means the certificate cannot
//!    express the distinction the pass makes, and that impossibility would be
//!    the finding.
//!
//! Obligation 3 is why this file exists at all. Obligations 1 and 2 are
//! satisfied by a proof route that emits nothing and reduces nothing; only 3
//! can fail for a checker that cannot fail.

use axeyum_cnf::{
    CnfAssignment, CnfClause, CnfFormula, CnfLit, CnfVar, DratStep, InprocessOptions,
    ProofSolveOutcome, SatResult, VecProofSink, check_drat, check_drat_backward, check_lrat,
    elaborate_drat_to_lrat, inprocess_into, solve_with_drat_proof_inprocessed,
    solve_with_drat_proof_with_limits, solve_with_native_core,
};

/// Conflict budget for every solve here. Generous relative to the fixtures (all
/// decide in far fewer), so a `ResourceOut` would be a real signal and not a
/// budget artifact.
const CONFLICT_BUDGET: usize = 200_000;

fn v(i: usize) -> CnfVar {
    CnfVar::new(i).expect("variable index in range")
}
fn pos(i: usize) -> CnfLit {
    CnfLit::positive(v(i))
}
fn neg(i: usize) -> CnfLit {
    CnfLit::positive(v(i)).negated()
}

fn formula(nvars: usize, clauses: Vec<Vec<CnfLit>>) -> CnfFormula {
    let mut f = CnfFormula::new(nvars);
    for c in clauses {
        f.add_clause(CnfClause::new(c)).expect("variables in range");
    }
    f
}

/// Pigeonhole: `pigeons` into `holes`. Unsatisfiable iff `pigeons > holes`.
fn pigeonhole(pigeons: usize, holes: usize) -> CnfFormula {
    let idx = |p: usize, h: usize| p * holes + h;
    let mut clauses = Vec::new();
    for p in 0..pigeons {
        clauses.push((0..holes).map(|h| pos(idx(p, h))).collect());
    }
    for h in 0..holes {
        for a in 0..pigeons {
            for b in (a + 1)..pigeons {
                clauses.push(vec![neg(idx(a, h)), neg(idx(b, h))]);
            }
        }
    }
    formula(pigeons * holes, clauses)
}

/// Deterministic 32-bit LCG. Explicit seeds are a workspace API promise; a
/// corpus generated from an ambient RNG would make a failure unreproducible.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }
    fn below(&mut self, n: usize) -> usize {
        usize::try_from(self.next()).expect("31-bit output fits usize") % n
    }
}

/// Random k-CNF at a chosen clause/variable ratio. Around 4.26 for k=3 the
/// instances straddle the satisfiability threshold, so a corpus built this way
/// carries both verdicts without the generator having to be told which.
///
/// Deliberately allows repeated literals and tautological clauses: those are
/// exactly the inputs the normalization prelude exists for, and a generator
/// that filtered them would make the prelude untested. (Same class of hole as
/// the `div`-by-**constant**-zero fuzz gap in `CLAUDE.md`'s hard rules — a
/// generator that cannot emit the degenerate case leaves the gate blind on the
/// axis where it matters.)
fn random_cnf(seed: u64, nvars: usize, nclauses: usize, k: usize) -> CnfFormula {
    let mut rng = Lcg(seed);
    let mut clauses = Vec::with_capacity(nclauses);
    for _ in 0..nclauses {
        let mut lits = Vec::with_capacity(k);
        for _ in 0..k {
            let var = rng.below(nvars);
            lits.push(if rng.next().is_multiple_of(2) {
                pos(var)
            } else {
                neg(var)
            });
        }
        clauses.push(lits);
    }
    formula(nvars, clauses)
}

/// The corpus every obligation runs over: named so a failure says which shape
/// broke. Mixed on purpose — structured unsat (pigeonhole), random around the
/// threshold in both k and ratio, and the degenerate shapes (duplicate
/// literals, tautologies, an empty clause, a formula that is already a
/// contradiction at level zero).
fn corpus() -> Vec<(String, CnfFormula)> {
    let mut out: Vec<(String, CnfFormula)> = vec![
        ("pigeonhole-3-2".to_owned(), pigeonhole(3, 2)),
        ("pigeonhole-4-3".to_owned(), pigeonhole(4, 3)),
        ("pigeonhole-5-4".to_owned(), pigeonhole(5, 4)),
        ("pigeonhole-4-4-sat".to_owned(), pigeonhole(4, 4)),
        (
            "unit-contradiction".to_owned(),
            formula(1, vec![vec![pos(0)], vec![neg(0)]]),
        ),
        (
            "tautology-and-duplicates".to_owned(),
            formula(
                3,
                vec![
                    vec![pos(0), neg(0)],
                    vec![pos(1), pos(1), pos(2)],
                    vec![pos(1), pos(2)],
                    vec![neg(1), pos(2), pos(2)],
                    vec![neg(2)],
                ],
            ),
        ),
        (
            "chain-strengthenable".to_owned(),
            formula(
                4,
                vec![
                    vec![pos(0), pos(1), pos(2)],
                    vec![neg(1), pos(2)],
                    vec![pos(0), pos(2), pos(3)],
                    vec![neg(3), pos(2)],
                    vec![neg(2)],
                    vec![neg(0)],
                ],
            ),
        ),
    ];
    for (seed, nvars, nclauses, k) in [
        (1_u64, 12_usize, 51_usize, 3_usize),
        (2, 12, 55, 3),
        (3, 16, 68, 3),
        (4, 16, 76, 3),
        (5, 20, 85, 3),
        (6, 20, 96, 3),
        (7, 24, 102, 3),
        (8, 24, 118, 3),
        (9, 14, 40, 4),
        (10, 14, 60, 4),
        (11, 10, 60, 2),
        (12, 10, 22, 2),
    ] {
        out.push((
            format!("random-k{k}-v{nvars}-c{nclauses}-s{seed}"),
            random_cnf(seed, nvars, nclauses, k),
        ));
    }
    out
}

/// The pass combinations under test, plus the `OFF` control.
fn option_sets() -> Vec<(&'static str, InprocessOptions)> {
    vec![
        ("off", InprocessOptions::OFF),
        (
            "subsume",
            InprocessOptions {
                subsume: true,
                ..InprocessOptions::OFF
            },
        ),
        (
            "vivify",
            InprocessOptions {
                vivify: true,
                ..InprocessOptions::OFF
            },
        ),
        (
            "bve",
            InprocessOptions {
                bve: true,
                ..InprocessOptions::OFF
            },
        ),
        ("preprocess", InprocessOptions::preprocess()),
        ("preprocess-full", InprocessOptions::preprocess_full()),
    ]
}

fn verdict_name(outcome: &ProofSolveOutcome) -> &'static str {
    match outcome {
        ProofSolveOutcome::Sat(_) => "sat",
        ProofSolveOutcome::Unsat(_) => "unsat",
        ProofSolveOutcome::ResourceOut => "resource-out",
        ProofSolveOutcome::Interrupted => "interrupted",
    }
}

fn satisfies(f: &CnfFormula, model: &CnfAssignment) -> bool {
    f.evaluate(model.values()) == Ok(true)
}

/// Obligation 1. Every option set reaches the same verdict as the unreduced
/// solver, and every `sat` model satisfies the ORIGINAL formula after the lift.
///
/// The check is against the original, not the reduced, formula: a model that
/// only satisfies what the passes left behind is precisely the failure mode a
/// broken BVE reconstruction produces, and checking it against the reduced
/// formula would pass through that bug silently.
#[test]
fn no_option_set_changes_a_verdict() {
    let corpus = corpus();
    assert!(corpus.len() >= 19, "corpus must not silently shrink");
    for (name, f) in &corpus {
        let baseline = solve_with_drat_proof_with_limits(f, None, CONFLICT_BUDGET);
        assert!(
            matches!(
                baseline,
                ProofSolveOutcome::Sat(_) | ProofSolveOutcome::Unsat(_)
            ),
            "{name}: the control run must decide, else the comparison is vacuous \
             (got {})",
            verdict_name(&baseline)
        );
        for (arm, options) in option_sets() {
            let got = solve_with_drat_proof_inprocessed(f, None, CONFLICT_BUDGET, options);
            assert_eq!(
                verdict_name(&got),
                verdict_name(&baseline),
                "{name} / {arm}: verdict disagrees with the unreduced solver"
            );
            if let ProofSolveOutcome::Sat(model) = &got {
                assert!(
                    satisfies(f, model),
                    "{name} / {arm}: lifted model does not satisfy the ORIGINAL formula"
                );
            }
        }
    }
}

/// Obligation 2. Every `unsat` the inprocessed path produces carries a proof
/// `check_drat` accepts **against the original formula**, with the empty clause
/// derived.
#[test]
fn every_unsat_proof_checks_against_the_original_formula() {
    let mut checked = 0usize;
    for (name, f) in corpus() {
        for (arm, options) in option_sets() {
            let ProofSolveOutcome::Unsat(proof) =
                solve_with_drat_proof_inprocessed(&f, None, CONFLICT_BUDGET, options)
            else {
                continue;
            };
            assert_eq!(
                check_drat(&f, &proof),
                Ok(true),
                "{name} / {arm}: proof does not check against the ORIGINAL formula"
            );
            checked += 1;
        }
    }
    // A corpus that produced no `unsat` would pass the loop above having checked
    // nothing. Pin the count so that shrinking the corpus, or an inprocessing
    // change that turns refutations into `ResourceOut`, breaks this test instead
    // of quietly emptying it.
    // 9 of the 19 corpus instances are unsatisfiable, times 6 arms. Pinned at the
    // measured value rather than at a comfortable round number: an inprocessing
    // change that turns a refutation into a `ResourceOut` has to break this test
    // rather than quietly emptying it.
    assert_eq!(
        checked, 54,
        "the number of checked refutations moved; recount before adjusting"
    );
}

/// Every pass's prefix, on its own and before any search step, is a `DRAT`
/// derivation of the original formula. This isolates the prefix from the search
/// so a prefix defect cannot hide behind a search that would have refuted the
/// formula anyway.
#[test]
fn every_pass_prefix_verifies_on_its_own() {
    for (name, f) in corpus() {
        for (arm, options) in option_sets() {
            let mut sink = VecProofSink::new();
            let out = inprocess_into(&f, options, None, &mut sink).expect("VecProofSink is total");
            let prefix = sink.into_steps();
            assert!(
                check_drat(&f, &prefix).is_ok(),
                "{name} / {arm}: a prefix step does not verify"
            );
            assert_eq!(out.stats.proof_steps, prefix.len(), "{name} / {arm}");
        }
    }
}
// --- Obligation 3: the soundness-negative half ------------------------------
//
// The first design of this section asserted that dropping a literal from ANY
// clause a pass added must make the checker reject, over the whole corpus. It
// failed on the first honest run: 11 of 12 over-strengthened BVE mutants on
// `pigeonhole-3-2` were ACCEPTED. That is not a checker defect and the assertion
// was simply false — once a `DRAT` prefix has driven the active set to
// inconsistency (BVE refutes small pigeonhole outright), *every* clause is `RUP`,
// so a strictly shorter resolvent follows too. The mutation was producing a
// different valid derivation, not an unjustified step: an inverted negative
// control, in the sense of `negative-controls-fail-two-ways`.
//
// What replaced it distinguishes the two halves of what a pass emits, which
// turn out not to be equally load-bearing:
//
//   * **The `Add` half is soundness-critical.** The search runs over clauses the
//     passes derived. If those derivations are not in the stream, the checker is
//     asked to verify steps against clauses it was never given, and it must
//     reject.
//   * **The `Delete` half is not.** Deletion only shrinks the checker's active
//     set. Omitting every deletion leaves a strict superset of the reduced
//     formula, and `RUP` is monotone in the clause set, so the proof still
//     verifies — it just costs more to check. A pass that reduces *only* by
//     deleting (subsumption with no strengthening) is therefore sound to run
//     silently, which is worth knowing precisely because it is the case where
//     "we preprocessed and did not say so" does no harm.
//
// Both directions are asserted, so the asymmetry is a measured property of this
// pipeline and not a remark.

/// Runs the passes and then the search separately, so a corruption can be
/// applied to the prefix while the search's own steps stay untouched.
///
/// Returns `None` when the search did not refute the reduced formula (a `sat` or
/// budget-exhausted instance has no proof to corrupt).
fn split_proof(
    f: &CnfFormula,
    options: InprocessOptions,
) -> Option<(Vec<DratStep>, Vec<DratStep>)> {
    let mut prefix_sink = VecProofSink::new();
    let reduced =
        inprocess_into(f, options, None, &mut prefix_sink).expect("VecProofSink is total");
    let prefix = prefix_sink.into_steps();

    let mut search_sink = VecProofSink::new();
    match axeyum_cnf::solve_with_drat_proof_streaming(
        &reduced.formula,
        None,
        CONFLICT_BUDGET,
        &mut search_sink,
    ) {
        axeyum_cnf::StreamingProofOutcome::Unsat => Some((prefix, search_sink.into_steps())),
        _ => None,
    }
}

fn is_add(step: &DratStep) -> bool {
    matches!(step, DratStep::Add(_))
}

/// The pass combinations that actually derive clauses, i.e. the ones for which
/// silence is a soundness question at all.
fn adding_option_sets() -> Vec<(&'static str, InprocessOptions)> {
    option_sets()
        .into_iter()
        .filter(|(_, o)| !o.is_off())
        .collect()
}

/// **The negative test that matters: a pass that does not record what it derived
/// produces a proof the checker rejects.**
///
/// This is the exact defect this lane exists to prevent — a solver that reduces
/// its formula and then emits a proof as if it had not. The corruption is
/// therefore not a hand-picked bad step but the whole failure mode: drop every
/// `Add` the passes emitted, keep everything else, and require the concatenated
/// proof to stop verifying.
///
/// The control is the uncorrupted concatenation in the same loop, asserted to be
/// `Ok(true)`. Without it this test would pass for a checker that rejects
/// everything.
#[test]
fn a_pass_that_does_not_record_its_derivations_is_rejected() {
    let mut control_checked = 0usize;
    let mut corruption_caught = 0usize;
    let mut corruption_built = 0usize;
    let mut per_arm: Vec<(&'static str, usize, usize)> = Vec::new();

    for (arm, options) in adding_option_sets() {
        let mut arm_caught = 0usize;
        let mut arm_built = 0usize;
        for (name, f) in corpus() {
            let Some((prefix, search)) = split_proof(&f, options) else {
                continue;
            };

            // Control: the real concatenation verifies against the original.
            let mut full = prefix.clone();
            full.extend(search.iter().cloned());
            assert_eq!(
                check_drat(&f, &full),
                Ok(true),
                "{name} / {arm}: the uncorrupted proof must verify, else the \
                 corruption below proves nothing"
            );
            control_checked += 1;

            // Corruption: the passes stayed silent about every clause they derived.
            if !prefix.iter().any(is_add) {
                continue; // nothing was derived here; silence is not a defect
            }
            let mut silent: Vec<DratStep> = prefix.iter().filter(|s| !is_add(s)).cloned().collect();
            silent.extend(search.iter().cloned());
            arm_built += 1;
            corruption_built += 1;
            if check_drat(&f, &silent) != Ok(true) {
                arm_caught += 1;
                corruption_caught += 1;
            }
        }
        per_arm.push((arm, arm_caught, arm_built));
    }

    for (arm, caught, built) in &per_arm {
        println!("silent-derivations: {arm}: {caught} rejected of {built} corrupted proofs");
    }
    assert!(
        control_checked >= 20,
        "too few control proofs ({control_checked}) for this to be evidence"
    );
    assert!(
        corruption_built >= 20,
        "too few corrupted proofs ({corruption_built}) for this to be evidence"
    );
    assert_eq!(
        corruption_caught,
        corruption_built,
        "{} of {corruption_built} proofs still verified after the passes were made \
         silent about every clause they derived. An accepted proof there means the \
         certificate does not depend on the derivations the search actually used, \
         which is the finding, not a passing test.",
        corruption_built - corruption_caught
    );
}

/// The other half of the asymmetry, asserted rather than remarked: **omitting
/// every deletion leaves the proof valid.**
///
/// Deletion only shrinks the checker's active set, and `RUP` is monotone in that
/// set, so a stream with the deletions removed verifies against a strict
/// superset of what the search saw. This is why a purely deleting pass
/// (subsumption with no strengthening) is sound to run without emitting
/// anything, and it is the reason the previous test filters on `Add` steps
/// rather than on the prefix being non-empty.
///
/// It is asserted because the alternative — writing it in a comment — would make
/// it a claim nothing checks, and it is load-bearing for how the emission sites
/// are allowed to be written.
#[test]
fn omitting_the_deletions_leaves_the_proof_valid() {
    let mut checked = 0usize;
    for (arm, options) in adding_option_sets() {
        for (name, f) in corpus() {
            let Some((prefix, search)) = split_proof(&f, options) else {
                continue;
            };
            let mut no_deletes: Vec<DratStep> =
                prefix.iter().filter(|s| is_add(s)).cloned().collect();
            no_deletes.extend(search.iter().cloned());
            assert_eq!(
                check_drat(&f, &no_deletes),
                Ok(true),
                "{name} / {arm}: dropping the prefix's deletions broke the proof, so \
                 deletion is NOT the cost-only half it is documented to be"
            );
            checked += 1;
        }
    }
    assert!(checked >= 20, "too few proofs checked ({checked})");
}

/// **What a `DRAT` prefix does NOT carry, measured rather than assumed.**
///
/// A step-level mutation — drop one literal from a clause a pass added, i.e. the
/// pass removed a literal it had no right to remove — is *not* always rejected,
/// and the two reasons are worth separating because only one of them was
/// obvious:
///
/// 1. On an **unsatisfiable** formula the prefix can drive the active set to
///    inconsistency (BVE refutes small pigeonhole on its own), after which every
///    clause is `RUP` and a shorter one is a perfectly valid step.
/// 2. On a **satisfiable** formula, where 1 cannot happen, 6 of 25 mutants were
///    still accepted on the first run. The reason is the format, not the
///    pipeline: [`check_drat`] accepts `RUP` **or `RAT`**, and `RAT` is
///    *satisfiability-preserving*, not entailment-preserving. A clause that
///    removes models can still be a legitimate `RAT` addition. So **a `DRAT`
///    proof does not certify that each added clause was entailed** — only that
///    adding it preserved satisfiability, which is exactly what an `unsat` proof
///    needs and strictly less than "the pass was entitled to strengthen here".
///
/// Consequence for how this pipeline is checked: the step-level mutation is a
/// measurement, printed and floor-asserted so it cannot silently reach zero, and
/// the *soundness* obligation is carried by the end-to-end test below, which
/// asks the question `DRAT` actually answers.
#[test]
fn step_level_over_strengthening_is_only_partly_observable() {
    let mut built_total = 0usize;
    let mut killed_total = 0usize;
    for (name, f) in corpus() {
        let satisfiable = matches!(
            solve_with_native_core(&f).expect("core reports a valid model"),
            SatResult::Sat(_)
        );
        for (arm, options) in adding_option_sets() {
            let mut sink = VecProofSink::new();
            inprocess_into(&f, options, None, &mut sink).expect("VecProofSink is total");
            let prefix = sink.into_steps();
            let adds = prefix.iter().filter(|s| is_add(s)).count();
            let mut built = 0usize;
            let mut killed = 0usize;
            for target in 0..adds {
                let Some(mutant) = drop_one_literal_from_add(&prefix, target) else {
                    continue;
                };
                built += 1;
                if check_drat(&f, &mutant).is_err() {
                    killed += 1;
                }
            }
            if built > 0 && killed < built {
                println!(
                    "step-mutation survivors: {name} / {arm} ({}): {} of {built} accepted",
                    if satisfiable { "sat" } else { "unsat" },
                    built - killed
                );
            }
            built_total += built;
            killed_total += killed;
        }
    }
    println!("step-mutation: {killed_total} rejected of {built_total} mutants");
    assert!(
        built_total >= 200,
        "too few mutants built ({built_total}) for this to be evidence"
    );
    // A floor, not an equality: the point of this test is the measurement and the
    // reason for the survivors, and an equality would pin a number the format
    // does not owe us. Zero would mean the prefix is not load-bearing at all,
    // which would itself be the finding.
    assert!(
        killed_total * 2 > built_total,
        "only {killed_total} of {built_total} step mutations were rejected; the \
         prefix has stopped being load-bearing"
    );
}

/// **The soundness question `DRAT` does answer: a wrong `unsat` never comes back
/// with an accepted proof.**
///
/// The corruption is applied to the pass's *output*, not only to its proof: a
/// clause the pass produced is over-strengthened in the reduced formula **and**
/// in the emitted prefix, exactly as a buggy strengthening would do both. The
/// search then runs on the corrupted formula. Whenever that turns a satisfiable
/// original into an `unsat`, the concatenated proof must be rejected — a wrong
/// verdict returning with a checkable certificate is the worst outcome this
/// pipeline has available, and this is the test that would see it.
///
/// The counted quantity is how many corruptions actually *produced* a wrong
/// `unsat`, because a run where none did would pass while checking nothing.
#[test]
fn a_wrong_unsat_from_a_corrupted_pass_never_carries_an_accepted_proof() {
    let mut wrong_unsats = 0usize;
    for (name, f) in corpus() {
        let SatResult::Sat(_) = solve_with_native_core(&f).expect("core reports a valid model")
        else {
            continue; // only a satisfiable original can expose a wrong `unsat`
        };
        for (arm, options) in adding_option_sets() {
            let mut sink = VecProofSink::new();
            let reduced = inprocess_into(&f, options, None, &mut sink).expect("total");
            let prefix = sink.into_steps();

            for target in 0..reduced.formula.clauses().len() {
                let Some(corrupted_formula) = shorten_clause(&reduced.formula, target) else {
                    continue;
                };
                let victim = reduced.formula.clauses()[target].lits().to_vec();
                let corrupted_prefix = shorten_matching_add(&prefix, &victim);

                let mut search_sink = VecProofSink::new();
                if !matches!(
                    axeyum_cnf::solve_with_drat_proof_streaming(
                        &corrupted_formula,
                        None,
                        CONFLICT_BUDGET,
                        &mut search_sink,
                    ),
                    axeyum_cnf::StreamingProofOutcome::Unsat
                ) {
                    continue; // this corruption did not produce a wrong verdict
                }
                wrong_unsats += 1;

                let mut proof = corrupted_prefix;
                proof.extend(search_sink.into_steps());
                assert_ne!(
                    check_drat(&f, &proof),
                    Ok(true),
                    "{name} / {arm} / clause {target}: an over-strengthened pass \
                     refuted a SATISFIABLE formula and the checker ACCEPTED the proof"
                );
            }
        }
    }
    println!("corrupted passes that produced a wrong `unsat`: {wrong_unsats}");
    assert!(
        wrong_unsats >= 20,
        "only {wrong_unsats} corruptions produced a wrong `unsat`, too few for this \
         test to be evidence that the checker catches them"
    );
}

/// A copy of `f` with the `target`-th clause missing its last literal, or `None`
/// if that clause is empty.
fn shorten_clause(f: &CnfFormula, target: usize) -> Option<CnfFormula> {
    let mut clauses: Vec<Vec<CnfLit>> = f.clauses().iter().map(|c| c.lits().to_vec()).collect();
    if clauses[target].is_empty() {
        return None;
    }
    clauses[target].pop();
    Some(formula(f.variable_count(), clauses))
}

/// Applies the same shortening to the prefix's `Add` of `victim`, if it has one.
/// A clause the passes did not derive (an untouched input clause) leaves the
/// prefix alone, which is the honest model of the bug: the pass corrupted what
/// it produced, not what it copied.
fn shorten_matching_add(prefix: &[DratStep], victim: &[CnfLit]) -> Vec<DratStep> {
    let mut out = prefix.to_vec();
    for step in &mut out {
        if let DratStep::Add(lits) = step
            && same_clause(lits, victim)
        {
            lits.pop();
            break;
        }
    }
    out
}

fn same_clause(a: &[CnfLit], b: &[CnfLit]) -> bool {
    let key = |c: &[CnfLit]| {
        let mut k: Vec<(usize, bool)> = c
            .iter()
            .map(|l| (l.var().index(), l.is_negated()))
            .collect();
        k.sort_unstable();
        k.dedup();
        k
    };
    key(a) == key(b)
}

/// Drops the last literal of the `target`-th `Add` step, or `None` if that step
/// has no literal to drop.
fn drop_one_literal_from_add(prefix: &[DratStep], target: usize) -> Option<Vec<DratStep>> {
    let at = prefix
        .iter()
        .enumerate()
        .filter(|(_, s)| is_add(s))
        .map(|(i, _)| i)
        .nth(target)?;
    let mut out = prefix.to_vec();
    let DratStep::Add(lits) = &mut out[at] else {
        unreachable!("indexed an Add");
    };
    if lits.is_empty() {
        return None;
    }
    lits.pop();
    Some(out)
}

/// **A second, independent checker sees the same thing.**
///
/// Six of the tests above reach their verdict through one call to
/// [`check_drat`]. That is the shape `CLAUDE.md` warns about — a suite whose
/// guards all reject through a single shared check is a suite with one guard —
/// and it is only half-mitigated by the tests differing in *what* they feed the
/// checker. So the backward checker, a different algorithm over the same bytes
/// (it re-derives only the steps the refutation needs, rather than replaying
/// every step forward against a growing active set), is required to agree on
/// every proof this path produces, in both directions:
///
/// * a proof the forward checker accepts, the backward checker accepts;
/// * a proof made unverifiable by silencing the passes' derivations, both
///   reject.
///
/// A `check_drat` that accepted everything would make the other tests vacuous
/// and would fail here.
#[test]
fn the_backward_checker_agrees_on_every_proof_and_every_corruption() {
    let mut agreed = 0usize;
    let mut corruptions = 0usize;
    for (arm, options) in adding_option_sets() {
        for (name, f) in corpus() {
            let Some((prefix, search)) = split_proof(&f, options) else {
                continue;
            };
            let mut full = prefix.clone();
            full.extend(search.iter().cloned());
            assert_eq!(
                check_drat_backward(&f, &full),
                Ok(true),
                "{name} / {arm}: forward accepts this proof and backward does not"
            );
            agreed += 1;

            if !prefix.iter().any(is_add) {
                continue;
            }
            let mut silent: Vec<DratStep> = prefix.iter().filter(|s| !is_add(s)).cloned().collect();
            silent.extend(search.iter().cloned());
            assert_ne!(
                check_drat_backward(&f, &silent),
                Ok(true),
                "{name} / {arm}: backward ACCEPTED a proof whose passes were silent \
                 about every clause they derived"
            );
            corruptions += 1;
        }
    }
    assert!(agreed >= 20, "too few proofs cross-checked ({agreed})");
    assert!(
        corruptions >= 20,
        "too few corruptions cross-checked ({corruptions})"
    );
}

/// The reduced formula is not merely equisatisfiable in the abstract: solving it
/// with a route that has nothing to do with the proof path agrees with the
/// baseline too. An independent second opinion on obligation 1, so a shared bug
/// in `solve_with_drat_proof_inprocessed` cannot make both sides agree.
#[test]
fn the_reduced_formula_agrees_with_an_independent_route() {
    for (name, f) in corpus() {
        let baseline = solve_with_native_core(&f).expect("core reports a valid model");
        for (arm, options) in option_sets() {
            let mut sink = VecProofSink::new();
            let out = inprocess_into(&f, options, None, &mut sink).expect("VecProofSink is total");
            let got = solve_with_native_core(&out.formula).expect("core reports a valid model");
            let same = matches!(
                (&baseline, &got),
                (SatResult::Sat(_), SatResult::Sat(_)) | (SatResult::Unsat(_), SatResult::Unsat(_))
            );
            assert!(
                same,
                "{name} / {arm}: reduced formula changed satisfiability"
            );
            if let SatResult::Sat(model) = &got {
                let lifted = CnfAssignment::new(out.reconstruction.extend(model.values()));
                assert!(
                    satisfies(&f, &lifted),
                    "{name} / {arm}: lifted model does not satisfy the original"
                );
            }
        }
    }
}

/// **The inprocessed proof survives the rest of the evidence pipeline, not just
/// the checker.**
///
/// A certificate that verifies but cannot be elaborated stops at the crate
/// boundary: `elaborate_drat_to_lrat` is what turns a DRAT stream into the
/// hint-carrying form the Lean/Alethe route consumes, and it resolves deletions
/// through its own clause lookup. That lookup has the same set-versus-multiset
/// choice the two checkers disagreed on, and the normalization prelude puts a
/// live set-equal, multiset-different pair in front of it on every instance with
/// a repeated literal. So it is exercised here rather than assumed.
#[test]
fn every_inprocessed_proof_still_elaborates_to_checkable_lrat() {
    let mut elaborated = 0usize;
    for (name, f) in corpus() {
        for (arm, options) in option_sets() {
            let ProofSolveOutcome::Unsat(proof) =
                solve_with_drat_proof_inprocessed(&f, None, CONFLICT_BUDGET, options)
            else {
                continue;
            };
            let steps = elaborate_drat_to_lrat(&f, &proof)
                .unwrap_or_else(|e| panic!("{name} / {arm}: elaboration failed: {e:?}"));
            assert_eq!(
                check_lrat(&f, &steps),
                Ok(true),
                "{name} / {arm}: elaborated LRAT does not check"
            );
            elaborated += 1;
        }
    }
    assert_eq!(
        elaborated, 54,
        "the number of elaborated refutations moved; recount before adjusting"
    );
}
