//! ADR-2132: the builds-per-file screen is a ROUTING change, never a verdict
//! change — and the file that proves it is one query run under all three arms in
//! ONE process.
//!
//! # Why the three arms have to be in one process
//!
//! `AXEYUM_LRA_WARM_CUBE` is read once into a `OnceLock`, which is right for a
//! measurement (a mid-run change cannot produce two halves of one A/B) and wrong
//! for this fixture. The property the screen must have is that `off`, `on` and
//! `screened` AGREE, and three separate test binaries could not assert that:
//! each would compare its own arm against a verdict written into the source,
//! which is the maintainer's memory of the answer rather than a comparison. So
//! the lever is passed as an argument here through
//! [`axeyum_solver::check_with_lra_dpll_within_mode`], whose one production
//! caller reads the environment.
//!
//! # The population this fixture publishes about itself
//!
//! A run in which the screen never opened would satisfy "the three arms agree"
//! by never having done anything — [ADR-2125]'s own inert-arm failure, which it
//! caught only because a mechanism probe was written. So the crossing test
//! asserts the MECHANISM as well as the verdict: the `off` arm must have built
//! more than the threshold's worth of tableaux, and the screened arm must have
//! answered at least one cube on a warm basis. Both are read from the counters,
//! not inferred.
//!
//! And the non-crossing test asserts the opposite half, which is the screen's
//! actual claim: below the threshold the screened arm answers ZERO cubes warm,
//! so a file of that shape runs the route it runs today.

#![cfg(feature = "full")]

use axeyum_ir::{Rational, Sort, TermArena, TermId};
use axeyum_solver::theories::arithmetic::{WarmCubeMode, check_with_lra_dpll_within_mode};
use axeyum_solver::{CheckResult, LazySmtCountersGuard, SolverConfig, last_lazy_smt_counters};

/// Atoms per instance. Past the **1,024** the online CDCL(T) engine admits, so
/// the query is refused there and lands in the offline lazy-SMT loop — the only
/// route this lever is on. [ADR-2125]'s own seed class needed the same width and
/// for the same reason; a narrow instance would exercise a different engine and
/// this file would go green having tested nothing.
const ATOMS: usize = 1_100;
/// The online screen's own arithmetic, restated so that a budget change there
/// fails HERE rather than silently redirecting this file to the warm online
/// engine, where every arm agrees trivially.
const ONLINE_ADMITTED_ATOMS: usize = 1_024;

/// The width claim, checked by the COMPILER.
///
/// This was a `#[test]` comparing two constants until clippy's
/// `assertions_on_constants` pointed out that such an assertion asserts nothing
/// at runtime. A `const` block is strictly stronger: a generator narrowed below
/// the online engine's admission no longer fails a test somebody has to run, it
/// fails the build.
///
/// It is only half the claim. That the CONSTANT is large enough is this; that
/// the generator and the abstraction actually produce that many atoms is a
/// different statement, and `the_generator_outruns_the_online_admission_screen`
/// below measures it from the loop's own counter.
const _: () = assert!(
    ATOMS > ONLINE_ADMITTED_ATOMS,
    "the generator does not outrun the online engine's admission, so every \
     instance in this file would be decided by a different engine"
);
const VARS: usize = 3;

/// Deterministic LCG (MMIX constants, the house convention). No clock, no
/// entropy source: determinism is a public promise and a fixture that generates
/// a different instance per run cannot be bisected.
struct Lcg(u64);

impl Lcg {
    fn new(seed: u64) -> Self {
        Lcg(seed
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407))
    }
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> usize {
        usize::try_from(self.next_u64() % n).expect("modulus fits usize")
    }
    fn in_range(&mut self, lo: i64, hi: i64) -> i64 {
        let span = u64::try_from(hi - lo + 1).expect("non-negative span");
        lo + i64::try_from(self.next_u64() % span).expect("offset within span")
    }
}

/// A wide, shallow `QF_LRA` query over `VARS` reals.
///
/// `disjoin_in` sets the disjunction rate as "one atom in N opens a two-atom
/// `or`", which is what decides how many refinement ROUNDS the offline loop
/// takes — and therefore how many from-scratch tableaux it builds. It is a
/// parameter because the two fixtures below need opposite sides of the screen:
/// one query that crosses [`MIN_BUILDS`] and one that does not.
///
/// Equalities and disequalities are deliberately absent, for [ADR-2125]'s
/// reason: an equality asserted FALSE is a disjunction the conjunctive theory
/// cannot represent, so the warm decider refuses the whole cube on one, and a
/// fixture full of them would measure the fall-through rather than the decider.
fn build(seed: u64, disjoin_in: u64) -> (TermArena, Vec<TermId>) {
    let mut rng = Lcg::new(seed);
    let mut a = TermArena::new();
    let names = ["x", "y", "z"];
    let vars: Vec<TermId> = (0..VARS)
        .map(|i| {
            let s = a.declare(names[i], Sort::Real).expect("declare real");
            a.var(s)
        })
        .collect();
    let zero = a.real_const(Rational::zero());

    let lits: Vec<TermId> = (0..ATOMS)
        .map(|_| {
            let nterms = rng.below(VARS as u64) + 1;
            let mut poly: Option<TermId> = None;
            for _ in 0..nterms {
                let coeff = rng.in_range(-3, 3);
                let v = rng.below(VARS as u64);
                let c = a.real_const(Rational::integer(i128::from(coeff)));
                let term = a.real_mul(c, vars[v]).expect("mul");
                poly = Some(poly.map_or(term, |acc| a.real_add(acc, term).expect("add")));
            }
            let k = a.real_const(Rational::integer(i128::from(rng.in_range(-6, 6))));
            let lhs = poly.map_or(k, |acc| a.real_add(acc, k).expect("add"));
            match rng.below(4) {
                0 => a.real_lt(lhs, zero).expect("lt"),
                1 => a.real_le(lhs, zero).expect("le"),
                2 => a.real_gt(lhs, zero).expect("gt"),
                _ => a.real_ge(lhs, zero).expect("ge"),
            }
        })
        .collect();

    let disjoin: Vec<bool> = (0..ATOMS).map(|_| rng.below(disjoin_in) == 0).collect();
    let mut assertions = Vec::with_capacity(lits.len());
    let mut i = 0usize;
    while i < lits.len() {
        if disjoin[i] && i + 1 < lits.len() {
            assertions.push(a.or(lits[i], lits[i + 1]).expect("or"));
            i += 2;
        } else {
            assertions.push(lits[i]);
            i += 1;
        }
    }
    (a, assertions)
}

/// The threshold the screen is registered at, restated here rather than imported
/// so this file fails LOUDLY if the constant moves.
///
/// A fixture that imported the constant would follow it anywhere, including to
/// zero — which is the mutation criterion 5 of this lane's brief requires to
/// kill exactly one named test. That mutation has to be VISIBLE to a fixture,
/// and it is invisible to one whose expectations are written in terms of the
/// mutated value.
const MIN_BUILDS: u64 = 64;

/// One arm's verdict, plus the three counters that say whether it did anything.
struct Arm {
    verdict: &'static str,
    cold_builds: u64,
    warm_checks: u64,
    warm_restarts: u64,
    /// The stable token `warm_cube_build` renders as on the `; lazy-smt` line.
    ///
    /// Read as the LABEL rather than as the enum, because the label is what
    /// every consumer of the trail reads and it is the thing that can silently
    /// stop distinguishing two cases.
    build: &'static str,
    /// Atoms the abstraction handed the loop — what
    /// `the_generator_outruns_the_online_admission_screen` measures, and the
    /// only number here that can say the file exercised the OFFLINE route.
    atoms: u64,
}

fn run(mode: WarmCubeMode, seed: u64, disjoin_in: u64) -> Arm {
    let (mut arena, assertions) = build(seed, disjoin_in);
    let config = SolverConfig::default();
    let _guard = LazySmtCountersGuard::enable();
    let result = check_with_lra_dpll_within_mode(&mut arena, &assertions, &config, None, mode)
        .expect("the offline loop decides or declines; it does not error");
    let c = last_lazy_smt_counters().expect("the loop was entered, so counters exist");
    Arm {
        verdict: match result {
            CheckResult::Sat(_) => "sat",
            CheckResult::Unsat => "unsat",
            CheckResult::Unknown(_) => "unknown",
        },
        cold_builds: c.simplex_cold_builds,
        warm_checks: c.warm_cube_checks,
        warm_restarts: c.warm_cube_cold_restarts,
        build: c.warm_cube_build.label(),
        atoms: c.atoms,
    }
}

/// The transition fixture criterion 3 of ADR-2132 names: a query whose cubes
/// CROSS the threshold mid-run must return the verdict the `off` arm returns.
///
/// It checks five things, and the mechanism ones are not decoration:
///
/// 1. the `off` arm really does build past the threshold, so the screen had
///    something to open on — without this the agreement is vacuous;
/// 2. the screened arm really did answer cubes warm;
/// 3. it answered FEWER than the `on` arm, which is the screen's own signature:
///    the rounds below the threshold ran cold in one arm and warm in the other;
/// 4. all three verdicts agree; and
/// 5. neither treatment arm restarted from a pristine basis. That last one is
///    the only assertion here that can see a warm basis being quietly rebuilt —
///    a rebuild gives identical verdicts, identical churn counts, and differs
///    only in the clock, so items 1–4 all pass over it.
#[test]
fn a_file_that_crosses_the_threshold_mid_run_decides_what_off_decides() {
    // One atom in TWO opens a disjunction. Measured on this generator at
    // `examples`-sweep time: this pair builds **124** from-scratch tableaux in
    // about 560 ms, so it crosses the 64 comfortably without being a query that
    // costs the suite a minute. The pair is a measurement and not a guess --
    // one atom in four gives 5 builds on this width, which is the reading the
    // vacuity assertion below caught on this fixture's first run.
    let (seed, disjoin_in) = (0x2132_0003, 2);
    let off = run(WarmCubeMode::Off, seed, disjoin_in);
    let on = run(WarmCubeMode::On, seed, disjoin_in);
    let screened = run(WarmCubeMode::Screened, seed, disjoin_in);

    assert!(
        off.cold_builds > MIN_BUILDS,
        "this fixture is VACUOUS unless the off arm builds past the screen: \
         {} tableaux against a threshold of {MIN_BUILDS}. Raise the disjunction \
         rate or the atom count; do not lower the threshold.",
        off.cold_builds
    );
    assert!(
        screened.warm_checks > 0,
        "the screen never opened ({} cubes answered warm) although the off arm \
         built {} tableaux -- the arms agree because nothing ran, which is the \
         inert-arm reading ADR-2125 had to publish about ADR-2111",
        screened.warm_checks,
        off.cold_builds
    );
    assert!(
        on.warm_checks > screened.warm_checks,
        "the screened arm answered {} cubes warm and the unscreened arm {}: the \
         screen's whole signature is that the rounds below the threshold ran \
         COLD, so `screened` must answer strictly fewer",
        screened.warm_checks,
        on.warm_checks
    );
    assert_eq!(
        (off.verdict, off.verdict),
        (on.verdict, screened.verdict),
        "the lever is a routing change: off={} on={} screened={}",
        off.verdict,
        on.verdict,
        screened.verdict
    );
    // A warm basis that is quietly being rebuilt gives identical verdicts,
    // identical counts, and differs only in the clock. This is the only thing
    // here that can see it.
    assert_eq!(
        (on.warm_restarts, screened.warm_restarts),
        (0, 0),
        "the basis was discarded and rebuilt: on={} screened={}",
        on.warm_restarts,
        screened.warm_restarts
    );
}

/// The other half of the screen's claim, and the half that is its whole point: a
/// query that stays BELOW the threshold must answer no cube warm at all, so it
/// runs exactly the route it runs with the lever off.
///
/// This is the assertion that dies when the screen is mutated to admit at 0
/// builds, and it is the reason the threshold is restated in this file rather
/// than imported.
#[test]
fn a_file_below_the_threshold_keeps_no_basis_at_all() {
    // The SAME disjunction rate as the crossing fixture, at a different seed.
    // That is deliberate: a below-threshold case built by removing the
    // disjunctions would differ from the crossing one in shape as well as in
    // size, and then "the screen stayed shut" could be a fact about the shape.
    // Measured at **34** builds against the crossing case's 124.
    let (seed, disjoin_in) = (0x2132_0001, 2);
    let off = run(WarmCubeMode::Off, seed, disjoin_in);
    let screened = run(WarmCubeMode::Screened, seed, disjoin_in);

    assert!(
        off.cold_builds > 0 && off.cold_builds < MIN_BUILDS,
        "this fixture needs a query that REACHES the loop and stays below the \
         screen; it built {} tableaux against a threshold of {MIN_BUILDS}",
        off.cold_builds
    );
    assert_eq!(
        screened.warm_checks, 0,
        "the screen opened on a file that built only {} tableaux -- below \
         {MIN_BUILDS} the screened arm must be the cold route, unchanged",
        off.cold_builds
    );
    // The trail must SAY the screen refused, not merely fail to say it opened.
    // `off` is what a run with the lever disabled renders, so without a separate
    // token a screened arm that refused every row is indistinguishable from an
    // arm nobody turned on -- and "the screen is too tight" and "the lever was
    // off" are the two readings a `net +0` on this arm has to be told apart by.
    assert_eq!(
        (off.build, screened.build),
        ("off", "below-screen"),
        "the `off` arm rendered {} and the screened arm {}",
        off.build,
        screened.build
    );
    assert_eq!(
        off.verdict, screened.verdict,
        "off={} screened={}",
        off.verdict, screened.verdict
    );
}

/// The generator outruns the online admission screen — measured from the loop's
/// own counter, not restated from the constants.
///
/// [ADR-2125] wrote a check like this for its own seed class and gave the
/// reason: the screen lives in another module, so a budget change there would
/// silently redirect this whole file to the warm ONLINE engine, where all three
/// arms agree because none of them is the arm under test and nothing goes red.
///
/// The CONSTANT half of that claim is the `const _` above, where the compiler
/// enforces it. This is the half a constant cannot make: that the generator and
/// the Boolean abstraction actually hand the offline loop more atoms than the
/// online engine admits. A generator that silently produced fewer — a changed
/// disjunction rate, an arena that folded duplicate literals — would satisfy the
/// constant and still test the wrong engine.
#[test]
fn the_generator_outruns_the_online_admission_screen() {
    let arm = run(WarmCubeMode::Off, 0x2132_0003, 2);
    assert!(
        arm.atoms > ONLINE_ADMITTED_ATOMS as u64,
        "the loop saw {} atoms, which does not outrun the online engine's \
         {ONLINE_ADMITTED_ATOMS}: this file would be measuring a different engine",
        arm.atoms
    );
}
