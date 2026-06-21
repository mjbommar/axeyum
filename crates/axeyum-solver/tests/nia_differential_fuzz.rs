//! Adversarial differential soundness fuzzer for the integer-arithmetic
//! (`QF_NIA` / `QF_LIA`) sat/unsat deciders against the Z3 oracle.
//!
//! Integer reasoning routes through several soundness-critical deciders: the
//! linear-integer (LIA) simplex/Gomory path, the nonlinear-integer (NIA)
//! square/product handling, the Int `div`/`mod` Euclidean elimination, and the
//! real-relaxation fallbacks. A wrong `Unsat` (claiming no integer solution when
//! one exists) or a wrong `Sat` (a model that does not satisfy the original
//! atoms, or one Z3 refutes) would be the worst possible bug.
//!
//! This harness — mirroring the proven NRA fuzzer (`nra_differential_fuzz.rs`) —
//! deterministically generates thousands of small random integer constraint
//! systems (no `Math::random`/`Date::now`; a fixed-seed LCG drives every choice),
//! decides each with both the default pure-Rust `solve` front door and a direct
//! Z3 integer query over the same terms, and gates on the joint verdict:
//!
//! - axeyum `Sat` ∧ Z3 `Unsat` → **PANIC** (wrong sat).
//! - axeyum `Unsat` ∧ Z3 `Sat` → **PANIC** (wrong unsat — the worst bug).
//! - axeyum `Sat` → the returned integer model is **independently replayed**
//!   through the IR ground evaluator on every original atom; a non-replaying Sat
//!   panics regardless of Z3.
//! - axeyum `Unknown` is ALLOWED (incomplete is sound) — counted, never failed.
//! - Z3 `Unknown`/timeout → the instance is skipped (cannot adjudicate).
//!
//! The test passes iff disagreements == 0 AND every axeyum `Sat` replayed.
//!
//! ## Div/mod convention check
//!
//! The optional `div`/`mod` atoms only ever divide by a *nonzero* small constant.
//! axeyum's `Op::IntDiv`/`Op::IntMod` evaluate via `i128::div_euclid`/`rem_euclid`
//! (see `axeyum-ir/src/eval.rs`) and the builder documents SMT-LIB Euclidean
//! semantics (`0 ≤ mod a b < |b|`). The z3 crate's `Int::div`/`Int::modulo` lower
//! to `Z3_mk_div`/`Z3_mk_mod`, which are the SMT-LIB Euclidean `div`/`mod`. For a
//! nonzero divisor the two conventions are identical, so these atoms are a fair
//! differential test (the divide-by-zero corner — where the two pick different
//! by-convention values — is never generated).

#![cfg(feature = "z3")]

use std::sync::mpsc;
use std::time::Duration;

use axeyum_ir::{Sort, SymbolId, TermArena, TermId, Value, eval};
use axeyum_solver::{CheckResult, SolverConfig, solve};
use z3::ast::{Bool, Int};
use z3::{Params, SatResult, Solver};

/// Number of instances generated and adjudicated. Each is tiny (≤ 3 vars, ≤ 4
/// atoms, degree ≤ 2 per atom) so Z3 decides well within its timeout.
const INSTANCES: u64 = 2500;

/// Per-instance Z3 wall-clock budget. Small polys ⇒ Z3 decides far faster; this
/// only bounds the rare pathological shape so the test never hangs.
const Z3_TIMEOUT: Duration = Duration::from_secs(2);

/// Per-instance hard wall-clock cap on the axeyum `solve`. A slow NIA shape is
/// run on a worker thread and joined with this cap; a solve that overruns is
/// recorded as a timeout (adjudication-neutral, exactly like `Unknown`) and the
/// sweep moves on. This is sound — a timeout is never a sat/unsat verdict — and
/// bounds total runtime.
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

/// The six comparators we mix: equalities, strict, non-strict, and `!=`.
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

    /// Build `lhs ⋈ 0` as an IR Bool term over the integer sort.
    fn build(self, a: &mut TermArena, lhs: TermId, zero: TermId) -> TermId {
        match self {
            Cmp::Eq => a.eq(lhs, zero).unwrap(),
            Cmp::Ne => {
                let e = a.eq(lhs, zero).unwrap();
                a.not(e).unwrap()
            }
            Cmp::Lt => a.int_lt(lhs, zero).unwrap(),
            Cmp::Le => a.int_le(lhs, zero).unwrap(),
            Cmp::Gt => a.int_gt(lhs, zero).unwrap(),
            Cmp::Ge => a.int_ge(lhs, zero).unwrap(),
        }
    }

    /// Build `lhs ⋈ 0` as a Z3 `Bool` over integer terms.
    fn build_z3(self, lhs: &Int, zero: &Int) -> Bool {
        match self {
            Cmp::Eq => lhs.eq(zero),
            Cmp::Ne => lhs.ne(zero),
            Cmp::Lt => lhs.lt(zero),
            Cmp::Le => lhs.le(zero),
            Cmp::Gt => lhs.gt(zero),
            Cmp::Ge => lhs.ge(zero),
        }
    }
}

/// One monomial: an integer coefficient times a product of 0–2 variable factors
/// (an index list into the instance's variables). An empty factor list is a
/// constant term. The optional `divmod` decorates the whole monomial with a
/// linear Euclidean `div` or `mod` by a *nonzero* constant — i.e. the monomial
/// value becomes `(coeff * Πfactors) div d` or `… mod d`. Kept as plain data so
/// the same monomial both builds the IR term and pretty-prints for a repro dump.
#[derive(Clone)]
struct Monomial {
    coeff: i64,
    factors: Vec<usize>,
    /// `Some((op, d))` wraps the monomial in a Euclidean `op` by the nonzero
    /// constant `d` (`op` is `Div` or `Mod`).
    divmod: Option<(DivMod, i64)>,
}

#[derive(Clone, Copy)]
enum DivMod {
    Div,
    Mod,
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
    /// - 1..=3 integer variables;
    /// - 1..=4 atoms;
    /// - each atom: 1..=3 monomials, each a coefficient in `-4..=4` times a
    ///   product of 0..=2 variable factors (so degree ≤ 2 per atom — a single
    ///   var squared when the two factors collide), plus an optional constant
    ///   monomial in `-4..=4`;
    /// - on ≈⅓ of instances, exactly one (non-constant) monomial is wrapped in a
    ///   Euclidean `div`/`mod` by a nonzero constant in `2..=4` (or its negation),
    ///   exercising the Int div/mod elimination on a convention both sides share;
    /// - comparator uniform over the six.
    fn generate(rng: &mut Lcg) -> Instance {
        let num_vars = rng.below(3) + 1; // 1..=3
        let num_atoms = rng.below(4) + 1; // 1..=4
        // Decide up front whether this instance carries a div/mod atom (~1/3).
        let use_divmod = rng.below(3) == 0;

        let mut atoms = Vec::with_capacity(num_atoms);
        // If div/mod is enabled, pick which atom hosts it.
        let divmod_atom = if use_divmod {
            Some(rng.below(num_atoms as u64))
        } else {
            None
        };

        for atom_idx in 0..num_atoms {
            let num_monos = rng.below(3) + 1; // 1..=3
            let mut monomials = Vec::with_capacity(num_monos + 1);
            for _ in 0..num_monos {
                let coeff = rng.in_range(-4, 4);
                let degree = rng.below(3); // 0..=2 variable factors
                let mut factors = Vec::with_capacity(degree);
                for _ in 0..degree {
                    factors.push(rng.below(num_vars as u64));
                }
                monomials.push(Monomial {
                    coeff,
                    factors,
                    divmod: None,
                });
            }
            // Optional constant monomial (~half the time).
            if rng.below(2) == 0 {
                monomials.push(Monomial {
                    coeff: rng.in_range(-4, 4),
                    factors: Vec::new(),
                    divmod: None,
                });
            }
            // If this is the chosen div/mod atom, decorate the first monomial
            // that has at least one variable factor (a purely-constant monomial
            // under div/mod is uninteresting and would fold away).
            if Some(atom_idx) == divmod_atom {
                if let Some(m) = monomials.iter_mut().find(|m| !m.factors.is_empty()) {
                    let op = if rng.below(2) == 0 {
                        DivMod::Div
                    } else {
                        DivMod::Mod
                    };
                    // Nonzero divisor magnitude in 2..=4, random sign.
                    let mag = rng.in_range(2, 4);
                    let d = if rng.below(2) == 0 { mag } else { -mag };
                    m.divmod = Some((op, d));
                }
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
        let names = ["x", "y", "z"];
        let syms: Vec<SymbolId> = (0..self.num_vars)
            .map(|i| a.declare(names[i], Sort::Int).unwrap())
            .collect();
        let vars: Vec<TermId> = syms.iter().map(|&s| a.var(s)).collect();
        let zero = a.int_const(0);

        let mut assertions = Vec::with_capacity(self.atoms.len());
        for atom in &self.atoms {
            // Build the polynomial as a sum of monomial terms.
            let mut poly: Option<TermId> = None;
            for m in &atom.monomials {
                // coeff * (factor product)
                let coeff_t = a.int_const(i128::from(m.coeff));
                let mut term = coeff_t;
                for &f in &m.factors {
                    term = a.int_mul(term, vars[f]).unwrap();
                }
                // Optional Euclidean div/mod by a nonzero constant.
                if let Some((op, d)) = m.divmod {
                    let d_t = a.int_const(i128::from(d));
                    term = match op {
                        DivMod::Div => a.int_div(term, d_t).unwrap(),
                        DivMod::Mod => a.int_mod(term, d_t).unwrap(),
                    };
                }
                poly = Some(match poly {
                    None => term,
                    Some(acc) => a.int_add(acc, term).unwrap(),
                });
            }
            // A monomial list is never empty (≥ 1 monomial generated).
            let lhs = poly.expect("every atom has at least one monomial");
            assertions.push(atom.cmp.build(&mut a, lhs, zero));
        }
        (a, syms, assertions)
    }

    /// Build the same instance as a list of Z3 `Bool` atoms over fresh Z3
    /// `Int` constants. The adjudication queries Z3 directly with the z3 crate's
    /// integer arithmetic — the exact same theory the deciders target.
    fn to_z3(&self) -> Vec<Bool> {
        let names = ["x", "y", "z"];
        let vars: Vec<Int> = (0..self.num_vars)
            .map(|i| Int::new_const(names[i]))
            .collect();
        let zero = Int::from_i64(0);

        self.atoms
            .iter()
            .map(|atom| {
                // Sum the monomials.
                let mut poly: Option<Int> = None;
                for m in &atom.monomials {
                    let mut term = Int::from_i64(m.coeff);
                    for &f in &m.factors {
                        term = Int::mul(&[term, vars[f].clone()]);
                    }
                    if let Some((op, d)) = m.divmod {
                        let d_t = Int::from_i64(d);
                        term = match op {
                            DivMod::Div => term.div(&d_t),
                            DivMod::Mod => term.modulo(&d_t),
                        };
                    }
                    poly = Some(match poly {
                        None => term,
                        Some(acc) => Int::add(&[acc, term]),
                    });
                }
                let lhs = poly.expect("every atom has at least one monomial");
                atom.cmp.build_z3(&lhs, &zero)
            })
            .collect()
    }

    /// An SMT-ish dump of the instance for a reproducing panic message.
    fn dump(&self) -> String {
        let names = ["x", "y", "z"];
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
                    if let Some((op, d)) = m.divmod {
                        let opname = match op {
                            DivMod::Div => "div",
                            DivMod::Mod => "mod",
                        };
                        s = format!("({s} {opname} {d})");
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
/// owns the arena). Unlike the algebraic-real case, integer ground evaluation is
/// total over this fragment, so a well-formed `Sat` model is expected to replay
/// `AllTrue`. `Indeterminate` is kept defensively (e.g. an overflow in the
/// evaluator) and is adjudication-neutral; only `Violated` is a wrong sat.
#[derive(Clone, PartialEq, Eq, Debug)]
enum Replay {
    /// Not a `Sat` verdict (no model to replay).
    NotSat,
    /// Every original atom evaluated `true` at the model — a verified replay.
    AllTrue,
    /// The evaluator declined ≥ 1 atom (`Err`) and refuted none — indeterminate.
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
}

/// Decide an instance with axeyum on a worker thread, joining under
/// [`AXEYUM_TIMEOUT`]. Returns `None` if the solve overran the cap (recorded as a
/// timeout by the caller — adjudication-neutral, never a verdict).
fn solve_axeyum_bounded(inst: Instance) -> Option<AxeyumOutcome> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let (mut a, syms, assertions) = inst.build();
        let result = solve(&mut a, &assertions, &SolverConfig::default());
        let outcome = match result {
            Err(_) => None, // solve must not error; surface as a worker failure
            Ok(ax) => {
                let verdict = label(&ax);
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
                                // `Err(..)` or a non-Bool result: indeterminate,
                                // not a refutation. Keep scanning in case a later
                                // atom is truly violated.
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
                })
            }
        };
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

/// Decide an instance with Z3 over integer arithmetic, with a tiny wall-clock
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
fn nia_differential_fuzz_disagree_zero() {
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
        if seed % 250 == 0 {
            eprintln!(
                "[nia-fuzz] seed {seed}/{INSTANCES} (joint={jointly_decided}, agree={agreements}, \
                 ax_unknown={axeyum_unknown}, ax_timeout={axeyum_timeout})"
            );
        }
        let mut rng = Lcg::new(seed);
        let inst = Instance::generate(&mut rng);

        // --- axeyum: the default pure-Rust front door, hard-capped. -----------
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

        // --- Z3 oracle: a direct integer-arithmetic query, tiny timeout. ------
        let z3_label = z3_decide(&inst);

        if z3_label == Verdict::Unknown {
            z3_unknown_skipped += 1;
            continue;
        }

        // Both sides committed to Sat/Unsat (axeyum may still be Unknown).
        if ax_label == Verdict::Unknown {
            continue;
        }

        jointly_decided += 1;

        // THE SOUNDNESS GATE: a jointly-decided instance must AGREE.
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

    println!("=== NIA differential fuzz tally ===");
    println!("total instances:      {total}");
    println!("jointly decided:      {jointly_decided}");
    println!("agreements:           {agreements}");
    println!("axeyum Unknown:       {axeyum_unknown}");
    println!("axeyum timeout:       {axeyum_timeout} (slow NIA; capped, adjudication-neutral)");
    println!("Z3 Unknown (skipped): {z3_unknown_skipped}");
    println!("Sat replays verified: {sat_replayed}");
    println!("Sat replay declined:  {sat_replay_indeterminate} (eval gap; Z3-adjudicated)");
    println!("DISAGREEMENTS:        0");

    // Reaching here means no disagreement panicked: DISAGREE=0 over the sweep.
    // Sanity: the sweep must actually exercise the joint deciders.
    assert!(
        jointly_decided > 100,
        "too few jointly-decided instances ({jointly_decided}); the differential \
         gate is not meaningfully exercised"
    );
}

/// Pretty-print an axeyum model's bindings for the named symbols.
fn dump_model(syms: &[SymbolId], model: &axeyum_solver::Model) -> String {
    let names = ["x", "y", "z"];
    let mut parts = Vec::new();
    for (i, &s) in syms.iter().enumerate() {
        let v = model.get(s);
        parts.push(format!("{}={:?}", names[i], v));
    }
    parts.join(", ")
}
