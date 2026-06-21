//! Adversarial differential soundness fuzzer for the nonlinear-real (NRA)
//! sat/unsat deciders against the Z3 oracle.
//!
//! The recently-built CAD/grid NRA path (`nra_real_root.rs`) gained the
//! algebraic-grid lift for all-equality 2-var coupled systems, complete 2-var
//! strict-inequality CAD, and recursive N-var strict-inequality CAD. These are
//! soundness-critical: a wrong `Unsat` (claiming no solution when one exists) or
//! a wrong `Sat` (a non-replaying model, or one Z3 refutes) would be the worst
//! possible bug.
//!
//! This harness deterministically generates thousands of small random NRA
//! instances (no `Math::random`/`Date::now` — a fixed-seed LCG drives every
//! choice), decides each with both the default pure-Rust `solve` front door and
//! the Z3 backend, and gates on the joint verdict:
//!
//! - axeyum `Sat` ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Sat` → the returned model is **independently replayed** through the
//!   IR ground evaluator on every original atom; a non-replaying Sat panics
//!   regardless of Z3.
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `Unknown`/timeout → the instance is skipped (cannot adjudicate).
//!
//! The test passes iff disagreements == 0 AND every axeyum `Sat` replayed.

#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Rational, Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Bool, Real};
use z3::{Params, SatResult, Solver};

/// Number of instances generated and adjudicated. Each is tiny (≤ 4 vars, ≤ 4
/// atoms, degree ≤ 2 per atom) so Z3 decides in well under its 2 s timeout. A few
/// of the recursive-CAD axeyum shapes are *much* slower than Z3, so each axeyum
/// solve runs under a hard wall-clock cap (`AXEYUM_TIMEOUT`) and a slow one is
/// counted as a timeout (sound: it is treated like `Unknown`), keeping the whole
/// sweep within a few minutes.
const INSTANCES: u64 = 2000;

/// Per-instance Z3 wall-clock budget. Small polys ⇒ Z3 decides far faster; this
/// only bounds the rare pathological shape so the test never hangs.
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

/// Per-instance hard wall-clock cap on the axeyum `solve`. The NRA abstraction
/// path honors `SolverConfig::timeout`, but the recursive strict-CAD path in
/// `nra_real_root.rs` does not propagate a deadline and can run for hundreds of
/// seconds on a few shapes. We therefore run each solve on a worker thread and
/// join with this cap; a solve that overruns is recorded as `AxeyumTimeout`
/// (adjudication-neutral, exactly like `Unknown`) and the sweep moves on. This is
/// sound — a timeout is never a sat/unsat verdict — and bounds total runtime.
const AXEYUM_TIMEOUT: Duration = Duration::from_secs(4);

/// A deterministic linear-congruential PRNG (the MMIX multiplier/increment).
/// No clock, no OS entropy: the whole sweep is reproducible from the seed.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        // Mix the seed once so consecutive seeds 0,1,2,… don't start correlated.
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }

    /// Advance and return the next 64-bit state.
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    /// A uniform integer in `0..n` (`n > 0`), returned as a `usize`.
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }

    /// A small signed coefficient in `lo..=hi` (inclusive).
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        debug_assert!(lo <= hi);
        let span = u64::try_from(hi - lo + 1).expect("non-negative span");
        lo + i64::try_from(self.next_u64() % span).expect("offset within span")
    }
}

/// The six comparators we mix: equalities, strict, non-strict, and `!=` (covers
/// the algebraic-grid lift, the strict CAD, and shapes that legitimately decline
/// to the abstraction layer).
#[derive(Clone, Copy)]
enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl Cmp {
    fn pick(rng: &mut Lcg) -> Cmp {
        match rng.below(6) {
            // (`below` is uniform over 0..6)
            0 => Cmp::Eq,
            1 => Cmp::Ne,
            2 => Cmp::Lt,
            3 => Cmp::Le,
            4 => Cmp::Gt,
            _ => Cmp::Ge,
        }
    }

    fn symbol(self) -> &'static str {
        match self {
            Cmp::Eq => "=",
            Cmp::Ne => "!=",
            Cmp::Lt => "<",
            Cmp::Le => "<=",
            Cmp::Gt => ">",
            Cmp::Ge => ">=",
        }
    }

    /// Build `lhs ⋈ 0` as an IR Bool term.
    fn build(self, a: &mut TermArena, lhs: TermId, zero: TermId) -> TermId {
        match self {
            Cmp::Eq => a.eq(lhs, zero).unwrap(),
            Cmp::Ne => {
                let e = a.eq(lhs, zero).unwrap();
                a.not(e).unwrap()
            }
            Cmp::Lt => a.real_lt(lhs, zero).unwrap(),
            Cmp::Le => a.real_le(lhs, zero).unwrap(),
            Cmp::Gt => a.real_gt(lhs, zero).unwrap(),
            Cmp::Ge => a.real_ge(lhs, zero).unwrap(),
        }
    }
}

/// One monomial: an integer coefficient times a product of 0–2 variable factors
/// (an index list into the instance's variables). An empty factor list is a
/// constant term. Kept as plain data so the same monomial both builds the IR
/// term and pretty-prints for a reproducing dump.
#[derive(Clone)]
struct Monomial {
    coeff: i64,
    factors: Vec<usize>,
}

/// A generated atom: a polynomial `Σ monomials ⋈ 0`.
#[derive(Clone)]
struct Atom {
    monomials: Vec<Monomial>,
    cmp: Cmp,
}

/// A full generated instance: the variable count and the atoms. Owns only plain
/// data (no IR handles), so it is `Send` + `Clone` — a clone can be moved onto an
/// axeyum worker thread while the original drives the Z3 query and dumps.
#[derive(Clone)]
struct Instance {
    num_vars: usize,
    atoms: Vec<Atom>,
}

impl Instance {
    /// Deterministically generate an instance from the PRNG.
    ///
    /// Distribution:
    /// - 2..=4 real variables;
    /// - 1..=4 atoms;
    /// - each atom: 1..=3 monomials, each a coefficient in `-3..=3` times a
    ///   product of 0..=2 variable factors (so degree ≤ 2 per atom, occasionally
    ///   a single var squared when the two factors collide), plus an optional
    ///   constant monomial in `-3..=3`;
    /// - comparator uniform over the six.
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(3) + 2; // 2..=4
        let num_atoms = rng.below(4) + 1; // 1..=4
        let mut atoms = Vec::with_capacity(num_atoms);
        for _ in 0..num_atoms {
            let num_monos = rng.below(3) + 1; // 1..=3
            let mut monomials = Vec::with_capacity(num_monos + 1);
            for _ in 0..num_monos {
                let coeff = rng.in_range(-3, 3);
                let degree = rng.below(3); // 0..=2 variable factors
                let mut factors = Vec::with_capacity(degree);
                for _ in 0..degree {
                    factors.push(rng.below(num_vars as u64));
                }
                monomials.push(Monomial { coeff, factors });
            }
            // Optional constant monomial (~half the time).
            if rng.below(2) == 0 {
                monomials.push(Monomial {
                    coeff: rng.in_range(-3, 3),
                    factors: Vec::new(),
                });
            }
            atoms.push(Atom {
                monomials,
                cmp: Cmp::pick(rng),
            });
        }
        Instance { num_vars, atoms }
    }

    /// Materialize the instance as IR assertions over a fresh arena, returning
    /// the arena, the per-variable symbol ids, and the assertion term ids.
    fn build(&self) -> (TermArena, Vec<SymbolId>, Vec<TermId>) {
        let mut a = TermArena::new();
        let names = ["x", "y", "z", "w"];
        let syms: Vec<SymbolId> = (0..self.num_vars)
            .map(|i| a.declare(names[i], Sort::Real).unwrap())
            .collect();
        let vars: Vec<TermId> = syms.iter().map(|&s| a.var(s)).collect();
        let zero = a.real_const(Rational::zero());

        let mut assertions = Vec::with_capacity(self.atoms.len());
        for atom in &self.atoms {
            // Build the polynomial as a sum of monomial terms.
            let mut poly: Option<TermId> = None;
            for m in &atom.monomials {
                // coeff * (factor product)
                let coeff_t = a.real_const(Rational::integer(i128::from(m.coeff)));
                let mut term = coeff_t;
                for &f in &m.factors {
                    term = a.real_mul(term, vars[f]).unwrap();
                }
                poly = Some(match poly {
                    None => term,
                    Some(acc) => a.real_add(acc, term).unwrap(),
                });
            }
            // A monomial list is never empty (≥ 1 monomial generated).
            let lhs = poly.expect("every atom has at least one monomial");
            assertions.push(atom.cmp.build(&mut a, lhs, zero));
        }
        (a, syms, assertions)
    }

    /// Build the same instance as a list of Z3 `Bool` atoms over fresh Z3
    /// `Real` constants. The `Z3Backend` oracle does not yet lower real terms
    /// (ADR-0015), so the adjudication queries Z3 directly with the z3 crate's
    /// real arithmetic — the exact same theory the deciders target.
    fn to_z3(&self) -> Vec<Bool> {
        let names = ["x", "y", "z", "w"];
        let vars: Vec<Real> = (0..self.num_vars)
            .map(|i| Real::new_const(names[i]))
            .collect();
        let zero = Real::from_rational(0, 1);

        self.atoms
            .iter()
            .map(|atom| {
                // Sum the monomials.
                let mut poly: Option<Real> = None;
                for m in &atom.monomials {
                    let mut term = Real::from_rational(m.coeff, 1);
                    for &f in &m.factors {
                        term *= vars[f].clone();
                    }
                    poly = Some(match poly {
                        None => term,
                        Some(acc) => acc + term,
                    });
                }
                let lhs = poly.expect("every atom has at least one monomial");
                match atom.cmp {
                    Cmp::Eq => lhs.eq(&zero),
                    Cmp::Ne => lhs.ne(&zero),
                    Cmp::Lt => lhs.lt(&zero),
                    Cmp::Le => lhs.le(&zero),
                    Cmp::Gt => lhs.gt(&zero),
                    Cmp::Ge => lhs.ge(&zero),
                }
            })
            .collect()
    }

    /// An SMT-ish dump of the instance for a reproducing panic message.
    fn dump(&self) -> String {
        let names = ["x", "y", "z", "w"];
        let mut lines = vec![format!("vars: {}", &names[..self.num_vars].join(", "))];
        for (i, atom) in self.atoms.iter().enumerate() {
            let parts: Vec<String> = atom
                .monomials
                .iter()
                .map(|m| {
                    let mut s = m.coeff.to_string();
                    for &f in &m.factors {
                        s.push('*');
                        s.push_str(names[f]);
                    }
                    s
                })
                .collect();
            lines.push(format!(
                "  atom[{i}]: {} {} 0",
                parts.join(" + "),
                atom.cmp.symbol()
            ));
        }
        lines.join("\n")
    }
}

/// A coarse verdict label, abstracting away the model/reason payloads.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

fn label(r: &CheckResult) -> Verdict {
    match r {
        CheckResult::Sat(_) => Verdict::Sat,
        CheckResult::Unsat => Verdict::Unsat,
        CheckResult::Unknown(_) => Verdict::Unknown,
    }
}

/// The replay outcome of an axeyum `Sat`, computed on the worker thread (which
/// owns the arena). The IR ground evaluator is the soundness trust anchor, but it
/// is incomplete over the algebraic field: real `add`/`mul` of two distinct
/// `RealAlgebraic` operands is deferred past ADR-0038 slice 1 and returns
/// `Err(AlgebraicArithmeticUnsupported)`. So a `Sat` replay is one of:
#[derive(Clone, PartialEq, Eq, Debug)]
enum Replay {
    /// Not a `Sat` verdict (no model to replay).
    NotSat,
    /// Every original atom evaluated `true` at the model — a verified replay.
    AllTrue,
    /// The evaluator declined ≥ 1 atom (`Err`) and refuted none — indeterminate;
    /// the Z3 cross-check still adjudicates the verdict.
    Indeterminate,
    /// An atom evaluated `false` at the model — a WRONG SAT (carries the atom
    /// index and a model dump for the panic).
    Violated { atom: usize, model: String },
}

/// The full axeyum result for one instance, decided on a worker thread under a
/// hard wall-clock cap.
struct AxeyumOutcome {
    verdict: Verdict,
    replay: Replay,
    /// A model dump for a `Sat` (used only when reporting a disagreement).
    model_dump: Option<String>,
    /// For an `Unknown` verdict, the classified reason kind + detail string
    /// (captured only for the opt-in `NRA_DUMP_UNKNOWN` capability-gap dump).
    unknown_reason: Option<(String, String)>,
}

/// Decide an instance with axeyum on a worker thread, joining under
/// [`AXEYUM_TIMEOUT`]. Returns `None` if the solve overran the cap (recorded as a
/// timeout by the caller — adjudication-neutral, never a verdict).
///
/// The arena, the model, and the replay all live on the worker thread; only the
/// `Send` summary ([`AxeyumOutcome`]) crosses back. The instance is moved in as
/// plain `Send` data (it owns no IR handles).
fn solve_axeyum_bounded(inst: Instance) -> Option<AxeyumOutcome> {
    let (tx, rx) = mpsc::channel();
    // A detached worker: if it overruns the cap we stop waiting and move on. It
    // keeps running to completion in the background (memory is bounded; the test
    // process reaps it on exit), but never blocks the sweep.
    std::thread::spawn(move || {
        let (mut a, syms, assertions) = inst.build();
        let result = solve(&mut a, &assertions, &SolverConfig::default());
        let outcome = match result {
            Err(_) => None, // solve must not error; surface as a worker failure
            Ok(ax) => {
                let verdict = label(&ax);
                let unknown_reason = match &ax {
                    CheckResult::Unknown(r) => Some((format!("{:?}", r.kind), r.detail.clone())),
                    _ => None,
                };
                let (replay, model_dump) = match &ax {
                    CheckResult::Sat(model) => {
                        let asg = model.to_assignment();
                        let dump = dump_model(&syms, model);
                        let mut replay = Replay::AllTrue;
                        for (i, &assertion) in assertions.iter().enumerate() {
                            match eval(&a, assertion, &asg) {
                                Ok(Value::Bool(true)) => {}
                                Ok(Value::Bool(false)) => {
                                    replay = Replay::Violated {
                                        atom: i,
                                        model: dump.clone(),
                                    };
                                    break;
                                }
                                // `Err(..)` (algebraic-field eval gap) or a non-Bool
                                // result: indeterminate, not a refutation. Keep
                                // scanning in case a later atom is truly violated.
                                _ => {
                                    if replay == Replay::AllTrue {
                                        replay = Replay::Indeterminate;
                                    }
                                }
                            }
                        }
                        (replay, Some(dump))
                    }
                    _ => (Replay::NotSat, None),
                };
                Some(AxeyumOutcome {
                    verdict,
                    replay,
                    model_dump,
                    unknown_reason,
                })
            }
        };
        // The receiver may be gone (we timed out); ignore a send error.
        let _ = tx.send(outcome);
    });

    match rx.recv_timeout(AXEYUM_TIMEOUT) {
        Ok(Some(outcome)) => Some(outcome),
        Ok(None) => {
            panic!("axeyum solve returned an error (Unknown must be a result, not an error)")
        }
        Err(mpsc::RecvTimeoutError::Timeout) => None,
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            panic!("axeyum worker thread panicked")
        }
    }
}

/// Decide an instance with Z3 over real arithmetic, with a tiny wall-clock
/// timeout. Returns `Unknown` on timeout/incompleteness (the instance is then
/// skipped — Z3 cannot adjudicate it).
fn z3_decide(inst: &Instance) -> Verdict {
    let solver = Solver::new();
    let mut params = Params::new();
    params.set_u32(
        "timeout",
        u32::try_from(Z3_TIMEOUT.as_millis()).unwrap_or(u32::MAX),
    );
    solver.set_params(&params);
    for atom in inst.to_z3() {
        solver.assert(&atom);
    }
    match solver.check() {
        SatResult::Sat => Verdict::Sat,
        SatResult::Unsat => Verdict::Unsat,
        SatResult::Unknown => Verdict::Unknown,
    }
}

#[test]
fn nra_differential_fuzz_disagree_zero() {
    let mut total = 0u64;
    let mut jointly_decided = 0u64;
    let mut agreements = 0u64;
    let mut axeyum_unknown = 0u64;
    let mut axeyum_timeout = 0u64;
    let mut z3_unknown_skipped = 0u64;
    let mut sat_replayed = 0u64;
    let mut sat_replay_indeterminate = 0u64;

    for seed in 0..INSTANCES {
        total += 1;
        if seed % 200 == 0 {
            eprintln!(
                "[nra-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, agree={agreements}, \
                 ax_unknown={axeyum_unknown}, ax_timeout={axeyum_timeout})"
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        // --- axeyum: the default pure-Rust front door, hard-capped. -----------
        // A slow recursive-CAD solve is recorded as a timeout (adjudication-
        // neutral, like Unknown) so it can never dominate the sweep or wedge it.
        let Some(outcome) = solve_axeyum_bounded(inst.clone()) else {
            axeyum_timeout += 1;
            continue;
        };
        let ax_label = outcome.verdict;

        // A `Sat` whose model VIOLATES an original atom under the independent
        // ground evaluator is a wrong sat — the worst bug — regardless of Z3.
        if let Replay::Violated { atom, model } = &outcome.replay {
            panic!(
                "WRONG SAT (seed {seed}): axeyum returned Sat but its model makes \
                 atom[{atom}] FALSE under the independent ground evaluator — a \
                 soundness bug.\nmodel: {model}\ninstance:\n{}",
                inst.dump()
            );
        }
        match outcome.replay {
            Replay::AllTrue => sat_replayed += 1,
            Replay::Indeterminate => sat_replay_indeterminate += 1,
            Replay::NotSat | Replay::Violated { .. } => {}
        }

        if ax_label == Verdict::Unknown {
            axeyum_unknown += 1;
        }

        // --- Z3 oracle: a direct real-arithmetic query, tiny timeout. ---------
        let z3_label = z3_decide(&inst);

        if z3_label == Verdict::Unknown {
            // Cannot adjudicate this instance; skip (Z3 timeout/incomplete).
            z3_unknown_skipped += 1;
            continue;
        }

        // Both sides committed to Sat/Unsat (axeyum may still be Unknown).
        if ax_label == Verdict::Unknown {
            // axeyum incomplete here; not a joint decision, nothing to adjudicate.
            // Opt-in capability-gap dump: Z3 decided but axeyum declined. Emits a
            // single machine-greppable line per gap when `NRA_DUMP_UNKNOWN` is set;
            // zero behavior change (no output) when the env var is unset.
            if std::env::var_os("NRA_DUMP_UNKNOWN").is_some() {
                let (kind, detail) = outcome
                    .unknown_reason
                    .clone()
                    .unwrap_or_else(|| ("?".to_string(), "(no reason)".to_string()));
                let dump = inst.dump().replace('\n', " | ");
                eprintln!(
                    "UNKNOWN_GAP seed={seed} z3={z3_label:?} kind={kind} detail={detail:?} \
                     vars={} atoms={} inst=[{dump}]",
                    inst.num_vars,
                    inst.atoms.len()
                );
            }
            continue;
        }

        jointly_decided += 1;

        // THE SOUNDNESS GATE: a jointly-decided instance must AGREE. A mismatch
        // panics immediately with a reproducing dump, so reaching the tally
        // below means the sweep found zero disagreements.
        if ax_label == z3_label {
            agreements += 1;
        } else {
            let model_dump = outcome
                .model_dump
                .unwrap_or_else(|| "(no axeyum model)".to_string());
            panic!(
                "DISAGREEMENT (seed {seed}): axeyum = {ax_label:?}, Z3 = {z3_label:?}.\n\
                 This is a {} soundness bug.\n\
                 axeyum model: {model_dump}\n\
                 instance:\n{}",
                match (ax_label, z3_label) {
                    (Verdict::Sat, Verdict::Unsat) => "WRONG-SAT",
                    (Verdict::Unsat, Verdict::Sat) => "WRONG-UNSAT (worst case)",
                    _ => "verdict",
                },
                inst.dump()
            );
        }
    }

    println!("=== NRA differential fuzz tally ===");
    println!("total instances:      {total}");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum Unknown:       {axeyum_unknown}");
    println!("axeyum timeout:       {axeyum_timeout} (slow CAD; capped, adjudication-neutral)");
    println!("Z3 Unknown (skipped): {z3_unknown_skipped}");
    println!("Sat replays verified: {sat_replayed}");
    println!(
        "Sat replay declined:  {sat_replay_indeterminate} (algebraic-field eval gap; Z3-adjudicated)"
    );
    println!("DISAGREEMENTS:        0");

    // Reaching here means no disagreement panicked: DISAGREE=0 over the sweep.
    // Sanity: the sweep must actually exercise the joint deciders, not skip
    // everything (guards against a silently-broken Z3 plumbing that always
    // times out, which would make DISAGREE=0 vacuous).
    assert!(
        jointly_decided > 100,
        "too few jointly-decided instances ({jointly_decided}); the differential \
         gate is not meaningfully exercised"
    );
}

/// Pretty-print an axeyum model's bindings for the named symbols.
fn dump_model(syms: &[SymbolId], model: &axeyum_solver::Model) -> String {
    let names = ["x", "y", "z", "w"];
    let mut parts = Vec::new();
    for (i, &s) in syms.iter().enumerate() {
        let v = model.get(s);
        parts.push(format!("{}={:?}", names[i], v));
    }
    parts.join(", ")
}
