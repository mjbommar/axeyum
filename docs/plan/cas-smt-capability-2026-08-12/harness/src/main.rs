//! CAS/SMT arithmetic **capability corpus** harness.
//!
//! Measures where axeyum's arithmetic reasoning decides and where it does not,
//! per query: verdict, **deciding route**, full dispatch trace, wall time.
//!
//! Three properties make this a measurement rather than a demo:
//!
//! 1. **Expected verdicts come from `../ground_truth.py`, not from axeyum.**
//!    Every entry's `expect` field is justified there by a Python-verified
//!    witness, a bounded enumeration, a hand proof, or a cited theorem.
//! 2. **Every `unsat` entry has a minimally-different `sat` control.** A route
//!    that answers `unsat` to everything scores zero, not full marks.
//! 3. **Some entries must NOT decide.** The `open` tier is two Diophantine
//!    equations believed unresolved by mathematics; the `tripwire` tier is
//!    satisfiable queries whose only witnesses are astronomically large. A
//!    change that makes the `open` tier decide, or that flips a tripwire to
//!    `unsat`, has broken soundness — it has not gained capability.
//!
//! Route provenance uses `check_auto_explained`, never `check_auto`: a verdict
//! without a route is not evidence about *which* machinery did the work.
//!
//! Usage:
//! ```sh
//! cargo run --release -- [--json out.json] [--only <axis-letter>] [--budget-scale N]
//! ```

use std::collections::BTreeMap;
use std::time::{Duration, Instant};

use axeyum_ir::{Sort, TermArena, TermId, Value};
use axeyum_solver::{CheckResult, RouteOutcome, SolverConfig, check_auto_explained};

// ---------------------------------------------------------------- term builder

/// A query under construction: an arena plus the assertion list, plus the names
/// of every declared variable so a `sat` model can be printed as a witness that
/// a human (or `ground_truth.py`) can re-check by hand.
struct Q {
    ar: TermArena,
    parts: Vec<TermId>,
    names: Vec<String>,
}

impl Q {
    fn new() -> Self {
        Self { ar: TermArena::new(), parts: Vec::new(), names: Vec::new() }
    }
    fn var(&mut self, name: &str) -> TermId {
        self.names.push(name.to_string());
        self.ar.int_var(name).unwrap()
    }
    fn k(&mut self, n: i128) -> TermId {
        self.ar.int_const(n)
    }
    fn add(&mut self, a: TermId, b: TermId) -> TermId {
        self.ar.int_add(a, b).unwrap()
    }
    fn sub(&mut self, a: TermId, b: TermId) -> TermId {
        self.ar.int_sub(a, b).unwrap()
    }
    fn mul(&mut self, a: TermId, b: TermId) -> TermId {
        self.ar.int_mul(a, b).unwrap()
    }
    fn imod(&mut self, a: TermId, b: TermId) -> TermId {
        self.ar.int_mod(a, b).unwrap()
    }
    /// `x^n` by repeated multiplication (`n >= 1`), left-associated.
    fn pw(&mut self, x: TermId, n: u32) -> TermId {
        let mut acc = x;
        for _ in 1..n {
            acc = self.mul(acc, x);
        }
        acc
    }
    fn le(&mut self, a: TermId, b: TermId) -> TermId {
        self.ar.int_le(a, b).unwrap()
    }
    fn lt(&mut self, a: TermId, b: TermId) -> TermId {
        self.ar.int_lt(a, b).unwrap()
    }
    fn ge(&mut self, a: TermId, b: TermId) -> TermId {
        self.ar.int_ge(a, b).unwrap()
    }
    fn eq(&mut self, a: TermId, b: TermId) -> TermId {
        self.ar.eq(a, b).unwrap()
    }
    fn ne(&mut self, a: TermId, b: TermId) -> TermId {
        let e = self.ar.eq(a, b).unwrap();
        self.ar.not(e).unwrap()
    }
    fn not(&mut self, a: TermId) -> TermId {
        self.ar.not(a).unwrap()
    }
    fn all(&mut self, ps: &[TermId]) -> TermId {
        let mut it = ps.iter().copied();
        let mut acc = it.next().expect("non-empty conjunction");
        for p in it {
            acc = self.ar.and(acc, p).unwrap();
        }
        acc
    }
    fn assert(&mut self, t: TermId) {
        self.parts.push(t);
    }
    /// `lo <= e <= hi` as a single conjunct.
    fn between(&mut self, lo: TermId, e: TermId, hi: TermId) -> TermId {
        let a = self.le(lo, e);
        let b = self.le(e, hi);
        self.all(&[a, b])
    }
    /// Convenience: assert `a >= n`.
    fn assert_ge_k(&mut self, a: TermId, n: i128) {
        let c = self.k(n);
        let t = self.ge(a, c);
        self.assert(t);
    }
    /// Convenience: assert `a <= n`.
    fn assert_le_k(&mut self, a: TermId, n: i128) {
        let c = self.k(n);
        let t = self.le(a, c);
        self.assert(t);
    }
}

// ---------------------------------------------------------------- corpus model

/// Which capability axis an entry probes.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Axis {
    /// Units and variable-divisor divisibility.
    A,
    /// Opaque symbol versus instantiated form.
    B,
    /// Monolithic versus decomposed hypothesis sets.
    C,
    /// Polynomial identities, degree 2-4 in 2-3 variables.
    D,
    /// Nonzero-polynomial-but-unsat traps (integrality beats zero-testing).
    F,
    /// Tripwires: huge witnesses, deep theorems, open problems.
    G,
    /// Anchors that must not regress.
    H,
    /// Boundary probe for the `cas-int-units` route added in `175372bdc`:
    /// queries that structurally resemble `a*p = 1` but are satisfiable.
    U,
}

impl Axis {
    fn letter(self) -> &'static str {
        match self {
            Axis::A => "A",
            Axis::B => "B",
            Axis::C => "C",
            Axis::D => "D",
            Axis::F => "F",
            Axis::G => "G",
            Axis::H => "H",
            Axis::U => "U",
        }
    }
    fn name(self) -> &'static str {
        match self {
            Axis::A => "units / variable-divisor divisibility",
            Axis::B => "opaque symbol vs instantiated",
            Axis::C => "monolithic vs decomposed hypotheses",
            Axis::D => "polynomial identities deg 2-4, 2-3 vars",
            Axis::F => "nonzero-polynomial-but-unsat traps",
            Axis::G => "tripwires: huge witnesses / deep theorems / OPEN",
            Axis::H => "anchors that must not regress",
            Axis::U => "unit-shape boundary: sat queries that LOOK like a*p = 1",
        }
    }
}

/// How an entry is judged when the measurement is repeated after a change.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Tier {
    /// Elementary; deciding it is the point. `unknown` is a capability gap.
    Core,
    /// The expected verdict is known, but only by deep mathematics. `unknown`
    /// is the honest answer; a decisive verdict is only a win if it carries a
    /// proof, and must be independently re-checked before it is believed.
    Hard,
    /// The opposite verdict would be a WRONG ANSWER. `unknown` is acceptable.
    Tripwire,
    /// Believed unresolved by mathematics. Must stay `unknown`.
    Open,
    /// Decided at the baseline. A later `unknown` here is a regression.
    Anchor,
}

impl Tier {
    fn label(self) -> &'static str {
        match self {
            Tier::Core => "core",
            Tier::Hard => "hard",
            Tier::Tripwire => "tripwire",
            Tier::Open => "open",
            Tier::Anchor => "anchor",
        }
    }
    fn budget_secs(self) -> u64 {
        match self {
            Tier::Core => 10,
            Tier::Hard | Tier::Tripwire | Tier::Open => 20,
            Tier::Anchor => 5,
        }
    }
}

struct Case {
    id: &'static str,
    axis: Axis,
    tier: Tier,
    /// `"unsat"`, `"sat"`, or `"open"` (no expected verdict).
    expect: &'static str,
    /// The query, stated mathematically. Must match `ground_truth.py`.
    formula: &'static str,
    /// How `ground_truth.py` justifies `expect` — independent of axeyum.
    why: &'static str,
    build: fn() -> Q,
}

// ---------------------------------------------------------------- the runner

struct Row {
    id: String,
    axis: String,
    tier: String,
    expect: String,
    verdict: String,
    kind: String,
    route: String,
    trace: String,
    secs: f64,
    status: String,
    witness: String,
    replayed: String,
    formula: String,
    why: String,
}

/// Judgement of one measured outcome against its independently-established
/// expectation. The vocabulary is deliberately blunt.
fn judge(expect: &str, verdict: &str, tier: Tier) -> &'static str {
    match (expect, verdict) {
        ("open", "unknown") => "OPEN-STAYS-UNKNOWN",
        ("open", _) => "ALARM-OPEN-DECIDED",
        (_, "unknown") => match tier {
            Tier::Anchor => "REGRESSION-ANCHOR-UNDECIDED",
            Tier::Hard | Tier::Tripwire => "UNDECIDED-EXPECTED",
            _ => "UNDECIDED-GAP",
        },
        ("unsat", "unsat") | ("sat", "sat") => "DECIDED-OK",
        ("unsat", "sat") | ("sat", "unsat") => "ALARM-WRONG-VERDICT",
        _ => "?",
    }
}

fn run_case(c: &Case, budget_scale: f64) -> Row {
    let mut q = (c.build)();
    let goal = q.all(&q.parts.clone());
    let secs = (c.tier.budget_secs() as f64 * budget_scale).max(1.0) as u64;
    let cfg = SolverConfig { timeout: Some(Duration::from_secs(secs)), ..SolverConfig::default() };

    let t0 = Instant::now();
    let res = check_auto_explained(&mut q.ar, &[goal], &cfg);
    let elapsed = t0.elapsed().as_secs_f64();

    let (verdict, kind) = match &res {
        Ok((CheckResult::Sat(_), _)) => ("sat".to_string(), String::new()),
        Ok((CheckResult::Unsat, _)) => ("unsat".to_string(), String::new()),
        Ok((CheckResult::Unknown(u), _)) => ("unknown".to_string(), format!("{:?}", u.kind)),
        Err(e) => (format!("ERROR({e:?})"), String::new()),
    };

    // The deciding route: the LAST attempt that actually decided. An empty
    // string here means "no route claimed the verdict", which is itself
    // reportable — a verdict with no provenance is not evidence.
    let (route, trace) = match &res {
        Ok((_, tr)) => {
            let deciding = tr
                .attempts()
                .iter()
                .rev()
                .find(|a| matches!(a.outcome, RouteOutcome::Decided(_)))
                .map(|a| a.route.to_string());
            let declined_last = tr
                .attempts()
                .iter()
                .rev()
                .find(|a| matches!(a.outcome, RouteOutcome::Declined(_)))
                .map(|a| format!("(none; last decline: {})", a.route));
            let r = deciding
                .or(declined_last)
                .unwrap_or_else(|| "<no-route-recorded>".to_string());
            let full = tr
                .attempts()
                .iter()
                .map(|a| format!("{a}"))
                .collect::<Vec<_>>()
                .join(" | ");
            (r, full)
        }
        Err(_) => ("<error>".to_string(), String::new()),
    };

    // For `sat`: print the model as a witness AND replay it against the goal.
    // Replay uses axeyum's own evaluator, so it is a self-consistency check, not
    // an independent one — the independent check is copying the printed witness
    // into `ground_truth.py`.
    let (witness, replayed) = match &res {
        Ok((CheckResult::Sat(m), _)) => {
            let mut shown = Vec::new();
            for n in &q.names {
                if let Some(s) = q.ar.find_symbol(n) {
                    if let Some(Value::Int(i)) = m.get(s) {
                        shown.push(format!("{n}={i}"));
                    }
                }
            }
            let assignment = m.to_assignment();
            let rep = match axeyum_ir::eval(&q.ar, goal, &assignment) {
                Ok(Value::Bool(true)) => "yes",
                Ok(Value::Bool(false)) => "NO-MODEL-DOES-NOT-SATISFY",
                _ => "not-evaluable",
            };
            (shown.join(" "), rep.to_string())
        }
        _ => (String::new(), String::new()),
    };

    let status = judge(c.expect, &verdict, c.tier).to_string();

    Row {
        id: c.id.to_string(),
        axis: c.axis.letter().to_string(),
        tier: c.tier.label().to_string(),
        expect: c.expect.to_string(),
        verdict,
        kind,
        route,
        trace,
        secs: elapsed,
        status,
        witness,
        replayed,
        formula: c.formula.to_string(),
        why: c.why.to_string(),
    }
}

fn esc(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 8);
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mut json_path: Option<String> = None;
    let mut only: Option<String> = None;
    let mut ids: Option<Vec<String>> = None;
    let mut selftest = false;
    let mut budget_scale = 1.0_f64;
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--json" => {
                json_path = args.get(i + 1).cloned();
                i += 2;
            }
            "--selftest" => {
                selftest = true;
                i += 1;
            }
            "--ids" => {
                ids = args
                    .get(i + 1)
                    .map(|s| s.split(',').map(|t| t.trim().to_string()).collect());
                i += 2;
            }
            "--only" => {
                only = args.get(i + 1).cloned();
                i += 2;
            }
            "--budget-scale" => {
                budget_scale = args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or(1.0);
                i += 2;
            }
            _ => i += 1,
        }
    }

    if selftest {
        std::process::exit(run_selftest());
    }

    let cases = corpus();
    let selected: Vec<&Case> = cases
        .iter()
        .filter(|c| only.as_ref().is_none_or(|o| c.axis.letter() == o))
        .filter(|c| ids.as_ref().is_none_or(|v| v.iter().any(|s| s == c.id)))
        .collect();

    println!("CAS/SMT arithmetic capability corpus — {} queries", selected.len());
    println!(
        "Ground truth: ../ground_truth.py (independent of axeyum). Route provenance: \
         check_auto_explained."
    );
    println!(
        "MACHINE IS CONTENDED — every wall time below is an UPPER BOUND, not a timing.\n"
    );

    let mut rows = Vec::new();
    let mut current_axis: Option<&'static str> = None;
    for c in &selected {
        if current_axis != Some(c.axis.letter()) {
            current_axis = Some(c.axis.letter());
            println!("\n=== axis {} — {} ===", c.axis.letter(), c.axis.name());
        }
        let row = run_case(c, budget_scale);
        let v = if row.kind.is_empty() {
            row.verdict.clone()
        } else {
            format!("{}({})", row.verdict, row.kind)
        };
        println!(
            "  {:<22} {:<6} want={:<6} got={:<22} {:>7.2}s  {:<28} {}",
            row.id, row.tier, row.expect, v, row.secs, row.status, row.route
        );
        if !row.witness.is_empty() {
            println!("      wit | {}   (model replays against the goal: {})", row.witness, row.replayed);
        }
        rows.push(row);
    }

    // ------------------------------------------------------------- summary
    println!("\n\n===================== SUMMARY =====================");
    let mut by_status: BTreeMap<&str, usize> = BTreeMap::new();
    for r in &rows {
        *by_status.entry(r.status.as_str()).or_insert(0) += 1;
    }
    for (k, v) in &by_status {
        println!("  {v:>4}  {k}");
    }

    println!("\n  --- decided vs undecided, by axis ---");
    let mut per_axis: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    for r in &rows {
        let e = per_axis.entry(r.axis.clone()).or_insert((0, 0));
        if r.verdict == "unknown" {
            e.1 += 1;
        } else {
            e.0 += 1;
        }
    }
    for (ax, (dec, unk)) in &per_axis {
        println!("  axis {ax}: decided {dec:>3}   unknown {unk:>3}");
    }

    println!("\n  --- deciding routes (count of queries each route decided) ---");
    let mut routes: BTreeMap<String, usize> = BTreeMap::new();
    for r in &rows {
        if r.verdict == "sat" || r.verdict == "unsat" {
            *routes.entry(r.route.clone()).or_insert(0) += 1;
        }
    }
    for (rt, n) in &routes {
        println!("  {n:>4}  {rt}");
    }

    let alarms: Vec<&Row> = rows.iter().filter(|r| r.status.starts_with("ALARM")).collect();
    let regressions: Vec<&Row> = rows.iter().filter(|r| r.status.starts_with("REGRESSION")).collect();
    let bad_replay: Vec<&Row> = rows.iter().filter(|r| r.replayed.starts_with("NO-MODEL")).collect();
    println!("\n  ALARMS: {}   ANCHOR REGRESSIONS: {}   BAD MODEL REPLAYS: {}",
        alarms.len(), regressions.len(), bad_replay.len());
    for r in alarms.iter().chain(regressions.iter()).chain(bad_replay.iter()) {
        println!("    !! {} want={} got={} route={}", r.id, r.expect, r.verdict, r.route);
    }

    if let Some(p) = json_path {
        let mut s = String::from("[\n");
        for (n, r) in rows.iter().enumerate() {
            s.push_str(&format!(
                "  {{\"id\":\"{}\",\"axis\":\"{}\",\"tier\":\"{}\",\"expect\":\"{}\",\
                 \"verdict\":\"{}\",\"unknown_kind\":\"{}\",\"route\":\"{}\",\
                 \"secs\":{:.3},\"status\":\"{}\",\"witness\":\"{}\",\"replayed\":\"{}\",\
                 \"formula\":\"{}\",\"why\":\"{}\",\"trace\":\"{}\"}}{}\n",
                esc(&r.id), esc(&r.axis), esc(&r.tier), esc(&r.expect),
                esc(&r.verdict), esc(&r.kind), esc(&r.route), r.secs,
                esc(&r.status), esc(&r.witness), esc(&r.replayed),
                esc(&r.formula), esc(&r.why), esc(&r.trace),
                if n + 1 == rows.len() { "" } else { "," }
            ));
        }
        s.push_str("]\n");
        std::fs::write(&p, s).expect("write json");
        println!("\n  wrote {p}");
    }
}

// ---------------------------------------------------------------- self-test
//
// This repository's own rule: a gate that never fires proves nothing. In the
// baseline run every alarm counter reads zero, which is indistinguishable from
// an alarm classifier that is simply broken. `--selftest` poses two DELIBERATELY
// MIS-DECLARED queries whose true verdicts are trivially known, and requires the
// classifier to raise the corresponding alarm on each. It exits non-zero if it
// does not.

fn run_selftest() -> i32 {
    let bad: Vec<Case> = vec![
        // Genuinely unsat, declared `sat` -> must raise ALARM-WRONG-VERDICT.
        Case {
            id: "SELFTEST-wrong-verdict", axis: Axis::H, tier: Tier::Anchor, expect: "sat",
            formula: "x + y = 3 /\\ x + y = 4  [DELIBERATELY declared sat; it is unsat]",
            why: "self-test of the ALARM-WRONG-VERDICT path",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let s = q.add(x, y); let three = q.k(3); let e = q.eq(s, three); q.assert(e);
                let s2 = q.add(x, y); let four = q.k(4); let e = q.eq(s2, four); q.assert(e); q },
        },
        // Trivially sat, declared `open` -> must raise ALARM-OPEN-DECIDED.
        Case {
            id: "SELFTEST-open-decided", axis: Axis::H, tier: Tier::Open, expect: "open",
            formula: "x = 1  [DELIBERATELY declared open; it is trivially sat]",
            why: "self-test of the ALARM-OPEN-DECIDED path",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let one = q.k(1);
                let e = q.eq(x, one); q.assert(e); q },
        },
    ];
    println!("=== harness self-test: the alarm classifier must FIRE ===");
    let mut failures = 0;
    let expected = ["ALARM-WRONG-VERDICT", "ALARM-OPEN-DECIDED"];
    for (c, want) in bad.iter().zip(expected) {
        let row = run_case(c, 1.0);
        let hit = row.status == want;
        println!(
            "  {:<26} got verdict={:<8} status={:<22} want status={:<22} {}",
            c.id, row.verdict, row.status, want,
            if hit { "OK" } else { "*** SELF-TEST FAILED ***" }
        );
        if !hit {
            failures += 1;
        }
    }
    println!("  self-test failures: {failures}");
    i32::from(failures > 0)
}

// ---------------------------------------------------------------- the corpus
//
// Every entry's `expect` is justified in ../ground_truth.py under the SAME id.
// Every `unsat` entry is followed by a minimally-different `sat` control.

fn corpus() -> Vec<Case> {
    vec![
        // ================================================== axis A: units
        Case {
            id: "A1-unit-direct", axis: Axis::A, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ a*p = 1",
            why: "|a*p| >= 2 whenever a >= 2 and p != 0; p = 0 gives 0",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_ge_k(a, 2);
                let ap = q.mul(a, p); let one = q.k(1); let e = q.eq(ap, one); q.assert(e); q },
        },
        Case {
            id: "A2-unit-ctrl-a1", axis: Axis::A, tier: Tier::Core, expect: "sat",
            formula: "a >= 1 /\\ a*p = 1", why: "witness a=1 p=1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_ge_k(a, 1);
                let ap = q.mul(a, p); let one = q.k(1); let e = q.eq(ap, one); q.assert(e); q },
        },
        Case {
            id: "A3-unit-neg", axis: Axis::A, tier: Tier::Core, expect: "unsat",
            formula: "a <= -2 /\\ a*p = 1", why: "same magnitude argument as A1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_le_k(a, -2);
                let ap = q.mul(a, p); let one = q.k(1); let e = q.eq(ap, one); q.assert(e); q },
        },
        Case {
            id: "A4-unit-ctrl-neg", axis: Axis::A, tier: Tier::Core, expect: "sat",
            formula: "a <= -1 /\\ a*p = 1", why: "witness a=-1 p=-1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_le_k(a, -1);
                let ap = q.mul(a, p); let one = q.k(1); let e = q.eq(ap, one); q.assert(e); q },
        },
        Case {
            id: "A5-unit-signed", axis: Axis::A, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ p >= 1 /\\ a*p = 1",
            why: "a*p >= 2 (the sign hypothesis is handed to the solver)",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_ge_k(a, 2); q.assert_ge_k(p, 1);
                let ap = q.mul(a, p); let one = q.k(1); let e = q.eq(ap, one); q.assert(e); q },
        },
        Case {
            id: "A6-unit-product", axis: Axis::A, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ b >= 1 /\\ (a*b)*p = 1", why: "a*b >= 2, so (a*b)*p != 1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let p = q.var("p");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1);
                let ab = q.mul(a, b); let abp = q.mul(ab, p);
                let one = q.k(1); let e = q.eq(abp, one); q.assert(e); q },
        },
        Case {
            id: "A7-notdiv1-witness", axis: Axis::A, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ NOT(1 = a*0 + 1 /\\ 1 <= 1 <= a-1)",
            why: "the witness direction of A1: s=0, r=1 discharges 'a does not divide 1'",
            build: || { let mut q = Q::new();
                let a = q.var("a"); q.assert_ge_k(a, 2);
                let zero = q.k(0); let one = q.k(1);
                let as_ = q.mul(a, zero); let sum = q.add(as_, one);
                let e = q.eq(one, sum);
                let am1 = q.sub(a, one);
                let rng = q.between(one, one, am1);
                let conj = q.all(&[e, rng]); let n = q.not(conj); q.assert(n); q },
        },
        Case {
            id: "A8-notdiv1-wit-ctrl", axis: Axis::A, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ NOT(1 = a*0 + 0 /\\ 1 <= 0 <= a-1)",
            why: "r=0 is a bogus remainder witness (1 <= 0 is false), so the negation holds",
            build: || { let mut q = Q::new();
                let a = q.var("a"); q.assert_ge_k(a, 2);
                let zero = q.k(0); let one = q.k(1);
                let as_ = q.mul(a, zero); let sum = q.add(as_, zero);
                let e = q.eq(one, sum);
                let am1 = q.sub(a, one);
                let rng = q.between(one, zero, am1);
                let conj = q.all(&[e, rng]); let n = q.not(conj); q.assert(n); q },
        },
        Case {
            id: "A9-div-var-x", axis: Axis::A, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ b >= 1 /\\ x = a*b^2 + 1 /\\ x = a*p",
            why: "a | x and a | a*b^2 give a | 1, contradicting a >= 2",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let x = q.var("x"); let p = q.var("p");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1);
                let b2 = q.pw(b, 2); let ab2 = q.mul(a, b2); let one = q.k(1);
                let rhs = q.add(ab2, one); let e1 = q.eq(x, rhs); q.assert(e1);
                let ap = q.mul(a, p); let e2 = q.eq(x, ap); q.assert(e2); q },
        },
        Case {
            id: "A10-nondiv-x-witness", axis: Axis::A, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ b >= 1 /\\ x = a*b^2+1 /\\ NOT(x = a*(b^2) + 1 /\\ 1 <= 1 <= a-1)",
            why: "witness direction of A9: s = b^2, r = 1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let x = q.var("x");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1);
                let b2 = q.pw(b, 2); let ab2 = q.mul(a, b2); let one = q.k(1);
                let rhs = q.add(ab2, one); let e1 = q.eq(x, rhs); q.assert(e1);
                let ab2b = q.mul(a, b2); let sum = q.add(ab2b, one);
                let e2 = q.eq(x, sum);
                let am1 = q.sub(a, one); let rng = q.between(one, one, am1);
                let conj = q.all(&[e2, rng]); let n = q.not(conj); q.assert(n); q },
        },
        Case {
            id: "A11-div-var-x-ctrl", axis: Axis::A, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ b >= 1 /\\ x = a*b^2 /\\ x = a*p", why: "witness p = b^2",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let x = q.var("x"); let p = q.var("p");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1);
                let b2 = q.pw(b, 2); let ab2 = q.mul(a, b2);
                let e1 = q.eq(x, ab2); q.assert(e1);
                let ap = q.mul(a, p); let e2 = q.eq(x, ap); q.assert(e2); q },
        },
        Case {
            id: "A12-cube-nondiv", axis: Axis::A, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ z = a^2*(a+1) /\\ z = a^3*p",
            why: "a^3*p = a^3 + a^2 forces a*(p-1) = 1, i.e. A1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let z = q.var("z"); let p = q.var("p");
                q.assert_ge_k(a, 2);
                let a2 = q.pw(a, 2); let one = q.k(1); let ap1 = q.add(a, one);
                let rhs = q.mul(a2, ap1); let e1 = q.eq(z, rhs); q.assert(e1);
                let a3 = q.pw(a, 3); let a3p = q.mul(a3, p);
                let e2 = q.eq(z, a3p); q.assert(e2); q },
        },
        Case {
            id: "A13-cube-nondiv-ctrl", axis: Axis::A, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ z = a^3*(a+1) /\\ z = a^3*p", why: "witness p = a+1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let z = q.var("z"); let p = q.var("p");
                q.assert_ge_k(a, 2);
                let a3 = q.pw(a, 3); let one = q.k(1); let ap1 = q.add(a, one);
                let rhs = q.mul(a3, ap1); let e1 = q.eq(z, rhs); q.assert(e1);
                let a3b = q.pw(a, 3); let a3p = q.mul(a3b, p);
                let e2 = q.eq(z, a3p); q.assert(e2); q },
        },
        Case {
            id: "A14-mod-phrasing", axis: Axis::A, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ (1 mod a) != 1",
            why: "Euclidean mod gives 1 mod a = 1 for every a >= 2; native-operator phrasing of A1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); q.assert_ge_k(a, 2);
                let one = q.k(1); let m = q.imod(one, a);
                let n = q.ne(m, one); q.assert(n); q },
        },
        Case {
            id: "A15-mod-phrasing-ctrl", axis: Axis::A, tier: Tier::Core, expect: "sat",
            formula: "a >= 1 /\\ (1 mod a) != 1", why: "witness a=1: 1 mod 1 = 0 != 1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); q.assert_ge_k(a, 1);
                let one = q.k(1); let m = q.imod(one, a);
                let n = q.ne(m, one); q.assert(n); q },
        },

        // ================================================== axis B: opaque vs instantiated
        Case {
            id: "B1-opaque-window", axis: Axis::B, tier: Tier::Core, expect: "unsat",
            formula: "M >= 1 /\\ 1 <= M*c /\\ M*c <= M-1",
            why: "M*c >= 1 and <= M-1 give M >= 2, then c >= 1, so M*c >= M > M-1",
            build: || { let mut q = Q::new();
                let m = q.var("M"); let c = q.var("c");
                q.assert_ge_k(m, 1);
                let mc = q.mul(m, c); let one = q.k(1);
                let mm1 = q.sub(m, one);
                let r = q.between(one, mc, mm1); q.assert(r); q },
        },
        Case {
            id: "B2-opaque-window-ctrl", axis: Axis::B, tier: Tier::Core, expect: "sat",
            formula: "M >= 1 /\\ 1 <= M*c <= M", why: "witness M=1 c=1",
            build: || { let mut q = Q::new();
                let m = q.var("M"); let c = q.var("c");
                q.assert_ge_k(m, 1);
                let mc = q.mul(m, c); let one = q.k(1);
                let r = q.between(one, mc, m); q.assert(r); q },
        },
        Case {
            id: "B3-inst-window", axis: Axis::B, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ r = a^2*(w-s) /\\ 1 <= r <= a^2-1",
            why: "the M := a^2 instance of B1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let w = q.var("w"); let s = q.var("s"); let r = q.var("r");
                q.assert_ge_k(a, 2);
                let a2 = q.pw(a, 2); let d = q.sub(w, s); let prod = q.mul(a2, d);
                let e = q.eq(r, prod); q.assert(e);
                let one = q.k(1); let a2b = q.pw(a, 2); let hi = q.sub(a2b, one);
                let rng = q.between(one, r, hi); q.assert(rng); q },
        },
        Case {
            id: "B4-inst-window-ctrl", axis: Axis::B, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ r = a^2*(w-s) /\\ 1 <= r <= a^2", why: "witness a=2 w=1 s=0 r=4",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let w = q.var("w"); let s = q.var("s"); let r = q.var("r");
                q.assert_ge_k(a, 2);
                let a2 = q.pw(a, 2); let d = q.sub(w, s); let prod = q.mul(a2, d);
                let e = q.eq(r, prod); q.assert(e);
                let one = q.k(1); let hi = q.pw(a, 2);
                let rng = q.between(one, r, hi); q.assert(rng); q },
        },
        Case {
            id: "B5-opaque-window-M4", axis: Axis::B, tier: Tier::Core, expect: "unsat",
            formula: "M >= 4 /\\ 1 <= M*c <= M-1",
            why: "B1 with the lower bound a^2 >= 4 supplied but the FORM still opaque",
            build: || { let mut q = Q::new();
                let m = q.var("M"); let c = q.var("c");
                q.assert_ge_k(m, 4);
                let mc = q.mul(m, c); let one = q.k(1);
                let mm1 = q.sub(m, one);
                let r = q.between(one, mc, mm1); q.assert(r); q },
        },
        Case {
            id: "B6-opaque-mono", axis: Axis::B, tier: Tier::Core, expect: "unsat",
            formula: "M >= 1 /\\ w >= 1 /\\ M*w < M", why: "M*w >= M*1 = M",
            build: || { let mut q = Q::new();
                let m = q.var("M"); let w = q.var("w");
                q.assert_ge_k(m, 1); q.assert_ge_k(w, 1);
                let mw = q.mul(m, w); let t = q.lt(mw, m); q.assert(t); q },
        },
        Case {
            id: "B7-inst-mono", axis: Axis::B, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ b >= 1 /\\ w >= 1 /\\ (a*b)*w < a*b",
            why: "the M := a*b instance of B6 — the REVERSE direction of B1 vs B3",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let w = q.var("w");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1); q.assert_ge_k(w, 1);
                let ab = q.mul(a, b); let abw = q.mul(ab, w);
                let ab2 = q.mul(a, b); let t = q.lt(abw, ab2); q.assert(t); q },
        },
        Case {
            id: "B8-opaque-mono-ctrl", axis: Axis::B, tier: Tier::Core, expect: "sat",
            formula: "M >= 1 /\\ w >= 1 /\\ M*w <= M", why: "witness M=1 w=1 (equality)",
            build: || { let mut q = Q::new();
                let m = q.var("M"); let w = q.var("w");
                q.assert_ge_k(m, 1); q.assert_ge_k(w, 1);
                let mw = q.mul(m, w); let t = q.le(mw, m); q.assert(t); q },
        },
        Case {
            id: "B9-uf-opaque-identity", axis: Axis::B, tier: Tier::Core, expect: "unsat",
            formula: "NOT((f(x)+y)^2 = f(x)^2 + 2*f(x)*y + y^2), f uninterpreted Int->Int",
            why: "a ring identity in the OPAQUE atom f(x); valid for every value it can take",
            build: || { let mut q = Q::new();
                let f = q.ar.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
                let x = q.var("x"); let y = q.var("y");
                let fx = q.ar.apply(f, &[x]).unwrap();
                let s = q.add(fx, y); let lhs = q.pw(s, 2);
                let f2 = q.mul(fx, fx); let two = q.k(2);
                let fy = q.mul(fx, y); let tfy = q.mul(two, fy);
                let y2 = q.mul(y, y);
                let r0 = q.add(f2, tfy); let rhs = q.add(r0, y2);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "B10-uf-opaque-ctrl", axis: Axis::B, tier: Tier::Core, expect: "sat",
            formula: "NOT((f(x)+y)^2 = f(x)^2 + 2*f(x)*y + y^2 + 1)", why: "witness f(x)=0 y=0",
            build: || { let mut q = Q::new();
                let f = q.ar.declare_fun("f", &[Sort::Int], Sort::Int).unwrap();
                let x = q.var("x"); let y = q.var("y");
                let fx = q.ar.apply(f, &[x]).unwrap();
                let s = q.add(fx, y); let lhs = q.pw(s, 2);
                let f2 = q.mul(fx, fx); let two = q.k(2);
                let fy = q.mul(fx, y); let tfy = q.mul(two, fy);
                let y2 = q.mul(y, y); let one = q.k(1);
                let r0 = q.add(f2, tfy); let r1 = q.add(r0, y2); let rhs = q.add(r1, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },

        // ================================================== axis C: monolithic vs decomposed
        Case {
            id: "C1-mono-k2-colour1", axis: Axis::C, tier: Tier::Core, expect: "unsat",
            formula: "a>=2, b>=1, t>=1, N=a*b, z=a*t, x=y+b*t, y>=1, x<=N, x=a*px, y=a*py, a*u+b*v=1",
            why: "a|x, a|y => a|b*t; Bezout => a|t => x-y = N*w >= N, but x-y <= N-1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let t = q.var("t");
                let n = q.var("N"); let z = q.var("z"); let x = q.var("x"); let y = q.var("y");
                let px = q.var("px"); let py = q.var("py");
                let u = q.var("u"); let v = q.var("v");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1); q.assert_ge_k(t, 1); q.assert_ge_k(y, 1);
                let ab = q.mul(a, b); let e = q.eq(n, ab); q.assert(e);
                let at = q.mul(a, t); let e = q.eq(z, at); q.assert(e);
                let bt = q.mul(b, t); let ybt = q.add(y, bt); let e = q.eq(x, ybt); q.assert(e);
                let e = q.le(x, n); q.assert(e);
                let apx = q.mul(a, px); let e = q.eq(x, apx); q.assert(e);
                let apy = q.mul(a, py); let e = q.eq(y, apy); q.assert(e);
                let au = q.mul(a, u); let bv = q.mul(b, v); let s = q.add(au, bv);
                let one = q.k(1); let e = q.eq(s, one); q.assert(e); q },
        },
        Case {
            id: "C2-mono-k2-no-gcd", axis: Axis::C, tier: Tier::Core, expect: "sat",
            formula: "same as C1 WITHOUT the Bezout conjunct a*u+b*v=1",
            why: "witness a=4 b=2 t=2 y=4 x=8 N=8 px=2 py=1 (the enumerated (4,2) defect)",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let t = q.var("t");
                let n = q.var("N"); let z = q.var("z"); let x = q.var("x"); let y = q.var("y");
                let px = q.var("px"); let py = q.var("py");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1); q.assert_ge_k(t, 1); q.assert_ge_k(y, 1);
                let ab = q.mul(a, b); let e = q.eq(n, ab); q.assert(e);
                let at = q.mul(a, t); let e = q.eq(z, at); q.assert(e);
                let bt = q.mul(b, t); let ybt = q.add(y, bt); let e = q.eq(x, ybt); q.assert(e);
                let e = q.le(x, n); q.assert(e);
                let apx = q.mul(a, px); let e = q.eq(x, apx); q.assert(e);
                let apy = q.mul(a, py); let e = q.eq(y, apy); q.assert(e); q },
        },
        Case {
            id: "C3-L1-cancel", axis: Axis::C, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ a*t = a^2*q /\\ t != a*q", why: "cancel a != 0",
            build: || { let mut qq = Q::new();
                let a = qq.var("a"); let t = qq.var("t"); let qv = qq.var("q");
                qq.assert_ge_k(a, 2);
                let at = qq.mul(a, t); let a2 = qq.pw(a, 2); let a2q = qq.mul(a2, qv);
                let e = qq.eq(at, a2q); qq.assert(e);
                let aq = qq.mul(a, qv); let n = qq.ne(t, aq); qq.assert(n); qq },
        },
        Case {
            id: "C4-L1-cancel-ctrl", axis: Axis::C, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ a*t = a^2*q /\\ t != a*q + 1", why: "witness a=2 t=0 q=0",
            build: || { let mut qq = Q::new();
                let a = qq.var("a"); let t = qq.var("t"); let qv = qq.var("q");
                qq.assert_ge_k(a, 2);
                let at = qq.mul(a, t); let a2 = qq.pw(a, 2); let a2q = qq.mul(a2, qv);
                let e = qq.eq(at, a2q); qq.assert(e);
                let aq = qq.mul(a, qv); let one = qq.k(1); let aq1 = qq.add(aq, one);
                let n = qq.ne(t, aq1); qq.assert(n); qq },
        },
        Case {
            id: "C5-L2-positivity", axis: Axis::C, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ t >= 1 /\\ t = a*w /\\ w < 1", why: "t = a*w >= 1 with a >= 2 forces w >= 1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let t = q.var("t"); let w = q.var("w");
                q.assert_ge_k(a, 2); q.assert_ge_k(t, 1);
                let aw = q.mul(a, w); let e = q.eq(t, aw); q.assert(e);
                let one = q.k(1); let n = q.lt(w, one); q.assert(n); q },
        },
        Case {
            id: "C6-L2-positivity-ctrl", axis: Axis::C, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ t >= 1 /\\ t = a*w /\\ w < 2", why: "witness a=2 t=2 w=1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let t = q.var("t"); let w = q.var("w");
                q.assert_ge_k(a, 2); q.assert_ge_k(t, 1);
                let aw = q.mul(a, w); let e = q.eq(t, aw); q.assert(e);
                let two = q.k(2); let n = q.lt(w, two); q.assert(n); q },
        },
        Case {
            id: "C7-L3-mono", axis: Axis::C, tier: Tier::Core, expect: "unsat",
            formula: "a>=2 /\\ b>=1 /\\ w>=1 /\\ t = a*w /\\ b*t < a*b",
            why: "b*t = (a*b)*w >= a*b for w >= 1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let w = q.var("w"); let t = q.var("t");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1); q.assert_ge_k(w, 1);
                let aw = q.mul(a, w); let e = q.eq(t, aw); q.assert(e);
                let bt = q.mul(b, t); let ab = q.mul(a, b);
                let n = q.lt(bt, ab); q.assert(n); q },
        },
        Case {
            id: "C8-L3-mono-ctrl", axis: Axis::C, tier: Tier::Core, expect: "sat",
            formula: "a>=2 /\\ b>=1 /\\ w>=1 /\\ t = a*w /\\ b*t <= a*b",
            why: "witness a=2 b=1 w=1 t=2 (equality case)",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let w = q.var("w"); let t = q.var("t");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1); q.assert_ge_k(w, 1);
                let aw = q.mul(a, w); let e = q.eq(t, aw); q.assert(e);
                let bt = q.mul(b, t); let ab = q.mul(a, b);
                let n = q.le(bt, ab); q.assert(n); q },
        },
        Case {
            id: "C9-L4-endpoint", axis: Axis::C, tier: Tier::Core, expect: "unsat",
            formula: "y >= 1 /\\ x = y + P /\\ P >= M /\\ x <= M", why: "y <= 0 follows, contradicting y >= 1",
            build: || { let mut q = Q::new();
                let y = q.var("y"); let x = q.var("x"); let p = q.var("P"); let m = q.var("M");
                q.assert_ge_k(y, 1);
                let yp = q.add(y, p); let e = q.eq(x, yp); q.assert(e);
                let e = q.ge(p, m); q.assert(e);
                let e = q.le(x, m); q.assert(e); q },
        },
        Case {
            id: "C10-L4-endpoint-ctrl", axis: Axis::C, tier: Tier::Core, expect: "sat",
            formula: "y >= 1 /\\ x = y + P /\\ P >= M-1 /\\ x <= M", why: "witness y=1 P=0 M=1",
            build: || { let mut q = Q::new();
                let y = q.var("y"); let x = q.var("x"); let p = q.var("P"); let m = q.var("M");
                q.assert_ge_k(y, 1);
                let yp = q.add(y, p); let e = q.eq(x, yp); q.assert(e);
                let one = q.k(1); let mm1 = q.sub(m, one);
                let e = q.ge(p, mm1); q.assert(e);
                let e = q.le(x, m); q.assert(e); q },
        },
        Case {
            id: "C11-L5-distribute", axis: Axis::C, tier: Tier::Core, expect: "unsat",
            formula: "x = a*px /\\ y = a*py /\\ x - y = b*t /\\ b*t != a*(px-py)",
            why: "ring identity a*px - a*py = a*(px-py)",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let t = q.var("t");
                let x = q.var("x"); let y = q.var("y");
                let px = q.var("px"); let py = q.var("py");
                let apx = q.mul(a, px); let e = q.eq(x, apx); q.assert(e);
                let apy = q.mul(a, py); let e = q.eq(y, apy); q.assert(e);
                let d = q.sub(x, y); let bt = q.mul(b, t); let e = q.eq(d, bt); q.assert(e);
                let pd = q.sub(px, py); let apd = q.mul(a, pd);
                let bt2 = q.mul(b, t); let n = q.ne(bt2, apd); q.assert(n); q },
        },
        Case {
            id: "C12-L5-distribute-ctrl", axis: Axis::C, tier: Tier::Core, expect: "sat",
            formula: "... /\\ b*t != a*(px-py) + 1", why: "witness a=2 px=3 py=1 (4 != 5)",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let t = q.var("t");
                let x = q.var("x"); let y = q.var("y");
                let px = q.var("px"); let py = q.var("py");
                let apx = q.mul(a, px); let e = q.eq(x, apx); q.assert(e);
                let apy = q.mul(a, py); let e = q.eq(y, apy); q.assert(e);
                let d = q.sub(x, y); let bt = q.mul(b, t); let e = q.eq(d, bt); q.assert(e);
                let pd = q.sub(px, py); let apd = q.mul(a, pd);
                let one = q.k(1); let apd1 = q.add(apd, one);
                let bt2 = q.mul(b, t); let n = q.ne(bt2, apd1); q.assert(n); q },
        },
        Case {
            id: "C13-L6-bezout", axis: Axis::C, tier: Tier::Core, expect: "unsat",
            formula: "a*u + b*v = 1 /\\ b*t = a*d /\\ t != a*(t*u + v*d)",
            why: "t = t*(a*u+b*v) = a*(t*u) + (b*t)*v = a*(t*u) + (a*d)*v = a*(t*u + d*v)",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let t = q.var("t"); let d = q.var("d");
                let u = q.var("u"); let v = q.var("v");
                let au = q.mul(a, u); let bv = q.mul(b, v); let s = q.add(au, bv);
                let one = q.k(1); let e = q.eq(s, one); q.assert(e);
                let bt = q.mul(b, t); let ad = q.mul(a, d); let e = q.eq(bt, ad); q.assert(e);
                let tu = q.mul(t, u); let vd = q.mul(v, d); let inner = q.add(tu, vd);
                let rhs = q.mul(a, inner); let n = q.ne(t, rhs); q.assert(n); q },
        },
        Case {
            id: "C14-L6-bezout-ctrl", axis: Axis::C, tier: Tier::Core, expect: "sat",
            formula: "b*t = a*d /\\ t != a*(t*u + v*d)   [Bezout hypothesis DROPPED]",
            why: "witness a=4 b=2 t=-2 d=-1 u=-1 v=4 (-2 != -8) — the gcd hypothesis is load-bearing",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b"); let t = q.var("t"); let d = q.var("d");
                let u = q.var("u"); let v = q.var("v");
                let bt = q.mul(b, t); let ad = q.mul(a, d); let e = q.eq(bt, ad); q.assert(e);
                let tu = q.mul(t, u); let vd = q.mul(v, d); let inner = q.add(tu, vd);
                let rhs = q.mul(a, inner); let n = q.ne(t, rhs); q.assert(n); q },
        },

        // ================================================== axis D: polynomial identities
        Case {
            id: "D1-id2-square", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "NOT((x+y)^2 = x^2 + 2xy + y^2)", why: "ring identity, degree 2, 2 vars",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let s = q.add(x, y); let lhs = q.pw(s, 2);
                let x2 = q.mul(x, x); let two = q.k(2); let xy = q.mul(x, y);
                let txy = q.mul(two, xy); let y2 = q.mul(y, y);
                let r0 = q.add(x2, txy); let rhs = q.add(r0, y2);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D2-id2-square-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "NOT((x+y)^2 = x^2 + 2xy + y^2 + 1)", why: "witness x=0 y=0 (0 != 1)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let s = q.add(x, y); let lhs = q.pw(s, 2);
                let x2 = q.mul(x, x); let two = q.k(2); let xy = q.mul(x, y);
                let txy = q.mul(two, xy); let y2 = q.mul(y, y); let one = q.k(1);
                let r0 = q.add(x2, txy); let r1 = q.add(r0, y2); let rhs = q.add(r1, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D3-id3-cube", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "NOT((x+y)^3 = x^3 + 3x^2 y + 3x y^2 + y^3)", why: "ring identity, degree 3, 2 vars",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let s = q.add(x, y); let lhs = q.pw(s, 3);
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3);
                let three = q.k(3);
                let x2 = q.pw(x, 2); let x2y = q.mul(x2, y); let t1 = q.mul(three, x2y);
                let y2 = q.pw(y, 2); let xy2 = q.mul(x, y2); let t2 = q.mul(three, xy2);
                let r0 = q.add(x3, t1); let r1 = q.add(r0, t2); let rhs = q.add(r1, y3);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D4-id3-cube-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "NOT((x+y)^3 = x^3 + 3x^2 y + 3x y^2 + y^3 + 1)", why: "witness x=0 y=0",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let s = q.add(x, y); let lhs = q.pw(s, 3);
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3);
                let three = q.k(3);
                let x2 = q.pw(x, 2); let x2y = q.mul(x2, y); let t1 = q.mul(three, x2y);
                let y2 = q.pw(y, 2); let xy2 = q.mul(x, y2); let t2 = q.mul(three, xy2);
                let one = q.k(1);
                let r0 = q.add(x3, t1); let r1 = q.add(r0, t2); let r2 = q.add(r1, y3);
                let rhs = q.add(r2, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D5-id3-sumcubes", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "NOT(x^3 + y^3 = (x+y)(x^2 - xy + y^2))", why: "factorisation identity",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let lhs = q.add(x3, y3);
                let s = q.add(x, y);
                let x2 = q.pw(x, 2); let xy = q.mul(x, y); let y2 = q.pw(y, 2);
                let d = q.sub(x2, xy); let f = q.add(d, y2);
                let rhs = q.mul(s, f);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D6-id3-sumcubes-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "NOT(x^3 + y^3 = (x+y)(x^2 - xy + y^2) + 1)", why: "witness x=0 y=0",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let lhs = q.add(x3, y3);
                let s = q.add(x, y);
                let x2 = q.pw(x, 2); let xy = q.mul(x, y); let y2 = q.pw(y, 2);
                let d = q.sub(x2, xy); let f = q.add(d, y2);
                let p = q.mul(s, f); let one = q.k(1); let rhs = q.add(p, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D7-id4-binom", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "NOT((x+y)^4 = x^4 + 4x^3y + 6x^2y^2 + 4xy^3 + y^4)", why: "ring identity, degree 4",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let s = q.add(x, y); let lhs = q.pw(s, 4);
                let x4 = q.pw(x, 4); let y4 = q.pw(y, 4);
                let four = q.k(4); let six = q.k(6);
                let x3 = q.pw(x, 3); let x3y = q.mul(x3, y); let t1 = q.mul(four, x3y);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let x2y2 = q.mul(x2, y2);
                let t2 = q.mul(six, x2y2);
                let y3 = q.pw(y, 3); let xy3 = q.mul(x, y3); let t3 = q.mul(four, xy3);
                let r0 = q.add(x4, t1); let r1 = q.add(r0, t2); let r2 = q.add(r1, t3);
                let rhs = q.add(r2, y4);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D8-id4-binom-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "NOT((x+y)^4 = x^4 + 4x^3y + 6x^2y^2 + 4xy^3 + y^4 + 1)", why: "witness x=0 y=0",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let s = q.add(x, y); let lhs = q.pw(s, 4);
                let x4 = q.pw(x, 4); let y4 = q.pw(y, 4);
                let four = q.k(4); let six = q.k(6); let one = q.k(1);
                let x3 = q.pw(x, 3); let x3y = q.mul(x3, y); let t1 = q.mul(four, x3y);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let x2y2 = q.mul(x2, y2);
                let t2 = q.mul(six, x2y2);
                let y3 = q.pw(y, 3); let xy3 = q.mul(x, y3); let t3 = q.mul(four, xy3);
                let r0 = q.add(x4, t1); let r1 = q.add(r0, t2); let r2 = q.add(r1, t3);
                let r3 = q.add(r2, y4); let rhs = q.add(r3, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D9-id2-three-var", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "NOT((x+y+z)^2 = x^2+y^2+z^2+2xy+2xz+2yz)", why: "ring identity, degree 2, 3 vars",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let s0 = q.add(x, y); let s = q.add(s0, z); let lhs = q.pw(s, 2);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let z2 = q.pw(z, 2);
                let two = q.k(2);
                let xy = q.mul(x, y); let t1 = q.mul(two, xy);
                let xz = q.mul(x, z); let t2 = q.mul(two, xz);
                let yz = q.mul(y, z); let t3 = q.mul(two, yz);
                let r0 = q.add(x2, y2); let r1 = q.add(r0, z2);
                let r2 = q.add(r1, t1); let r3 = q.add(r2, t2); let rhs = q.add(r3, t3);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D10-id2-three-var-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "NOT((x+y+z)^2 = x^2+y^2+z^2+2xy+2xz+2yz + 1)", why: "witness x=y=z=0",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let s0 = q.add(x, y); let s = q.add(s0, z); let lhs = q.pw(s, 2);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let z2 = q.pw(z, 2);
                let two = q.k(2); let one = q.k(1);
                let xy = q.mul(x, y); let t1 = q.mul(two, xy);
                let xz = q.mul(x, z); let t2 = q.mul(two, xz);
                let yz = q.mul(y, z); let t3 = q.mul(two, yz);
                let r0 = q.add(x2, y2); let r1 = q.add(r0, z2);
                let r2 = q.add(r1, t1); let r3 = q.add(r2, t2); let r4 = q.add(r3, t3);
                let rhs = q.add(r4, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D11-id3-cyclic", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "NOT(x^3+y^3+z^3-3xyz = (x+y+z)(x^2+y^2+z^2-xy-yz-zx))",
            why: "classical factorisation, degree 3, 3 vars",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let z3 = q.pw(z, 3);
                let three = q.k(3); let xy = q.mul(x, y); let xyz = q.mul(xy, z);
                let t = q.mul(three, xyz);
                let l0 = q.add(x3, y3); let l1 = q.add(l0, z3); let lhs = q.sub(l1, t);
                let s0 = q.add(x, y); let s = q.add(s0, z);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let z2 = q.pw(z, 2);
                let yz = q.mul(y, z); let zx = q.mul(z, x);
                let f0 = q.add(x2, y2); let f1 = q.add(f0, z2);
                let f2 = q.sub(f1, xy); let f3 = q.sub(f2, yz); let f4 = q.sub(f3, zx);
                let rhs = q.mul(s, f4);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D12-id3-cyclic-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "NOT(x^3+y^3+z^3-3xyz = (x+y+z)(...) + 1)", why: "witness x=y=z=0 (0 != 1)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let z3 = q.pw(z, 3);
                let three = q.k(3); let xy = q.mul(x, y); let xyz = q.mul(xy, z);
                let t = q.mul(three, xyz);
                let l0 = q.add(x3, y3); let l1 = q.add(l0, z3); let lhs = q.sub(l1, t);
                let s0 = q.add(x, y); let s = q.add(s0, z);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let z2 = q.pw(z, 2);
                let yz = q.mul(y, z); let zx = q.mul(z, x);
                let f0 = q.add(x2, y2); let f1 = q.add(f0, z2);
                let f2 = q.sub(f1, xy); let f3 = q.sub(f2, yz); let f4 = q.sub(f3, zx);
                let p = q.mul(s, f4); let one = q.k(1); let rhs = q.add(p, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D13-id4-sophie-germain", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "NOT(x^4 + 4y^4 = (x^2+2y^2-2xy)(x^2+2y^2+2xy))",
            why: "Sophie Germain identity, degree 4, 2 vars",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x4 = q.pw(x, 4); let y4 = q.pw(y, 4); let four = q.k(4);
                let f4y = q.mul(four, y4); let lhs = q.add(x4, f4y);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let two = q.k(2);
                let ty2 = q.mul(two, y2); let base = q.add(x2, ty2);
                let xy = q.mul(x, y); let txy = q.mul(two, xy);
                let f1 = q.sub(base, txy); let f2 = q.add(base, txy);
                let rhs = q.mul(f1, f2);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D14-id4-sophie-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "NOT(x^4 + 4y^4 = (x^2+2y^2-2xy)(x^2+2y^2+2xy) + 1)", why: "witness x=1 y=0 (1 != 2)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x4 = q.pw(x, 4); let y4 = q.pw(y, 4); let four = q.k(4);
                let f4y = q.mul(four, y4); let lhs = q.add(x4, f4y);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let two = q.k(2);
                let ty2 = q.mul(two, y2); let base = q.add(x2, ty2);
                let xy = q.mul(x, y); let txy = q.mul(two, xy);
                let f1 = q.sub(base, txy); let f2 = q.add(base, txy);
                let p = q.mul(f1, f2); let one = q.k(1); let rhs = q.add(p, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D15-id4-difference", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "NOT(x^4 - y^4 = (x-y)(x+y)(x^2+y^2))", why: "factorisation identity",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x4 = q.pw(x, 4); let y4 = q.pw(y, 4); let lhs = q.sub(x4, y4);
                let d = q.sub(x, y); let s = q.add(x, y);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let sq = q.add(x2, y2);
                let p0 = q.mul(d, s); let rhs = q.mul(p0, sq);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D16-id4-difference-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "NOT(x^4 - y^4 = (x-y)(x+y)(x^2+y^2) + 1)", why: "witness x=2 y=1 (15 != 16)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x4 = q.pw(x, 4); let y4 = q.pw(y, 4); let lhs = q.sub(x4, y4);
                let d = q.sub(x, y); let s = q.add(x, y);
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let sq = q.add(x2, y2);
                let p0 = q.mul(d, s); let p1 = q.mul(p0, sq);
                let one = q.k(1); let rhs = q.add(p1, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D17-id-congruence", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "x = y /\\ x^3 != y^3", why: "congruence: equals have equal cubes",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let e = q.eq(x, y); q.assert(e);
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3);
                let n = q.ne(x3, y3); q.assert(n); q },
        },
        Case {
            id: "D18-id-congruence-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "x = y + 1 /\\ x^3 != y^3", why: "witness x=2 y=1 (8 != 1)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let one = q.k(1); let y1 = q.add(y, one);
                let e = q.eq(x, y1); q.assert(e);
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3);
                let n = q.ne(x3, y3); q.assert(n); q },
        },
        Case {
            id: "D19-id4-brahmagupta", axis: Axis::D, tier: Tier::Core, expect: "unsat",
            formula: "NOT((x^2+y^2)(z^2+1) = (xz-y)^2 + (x+yz)^2)",
            why: "Brahmagupta-Fibonacci identity, degree 4, 3 vars",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let z2 = q.pw(z, 2);
                let one = q.k(1);
                let l = q.add(x2, y2); let r = q.add(z2, one); let lhs = q.mul(l, r);
                let xz = q.mul(x, z); let a1 = q.sub(xz, y); let s1 = q.pw(a1, 2);
                let yz = q.mul(y, z); let a2 = q.add(x, yz); let s2 = q.pw(a2, 2);
                let rhs = q.add(s1, s2);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },
        Case {
            id: "D20-id4-brahmagupta-ctrl", axis: Axis::D, tier: Tier::Core, expect: "sat",
            formula: "NOT((x^2+y^2)(z^2+1) = (xz-y)^2 + (x+yz)^2 + 1)", why: "witness x=1 y=0 z=0 (1 != 2)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x2 = q.pw(x, 2); let y2 = q.pw(y, 2); let z2 = q.pw(z, 2);
                let one = q.k(1);
                let l = q.add(x2, y2); let r = q.add(z2, one); let lhs = q.mul(l, r);
                let xz = q.mul(x, z); let a1 = q.sub(xz, y); let s1 = q.pw(a1, 2);
                let yz = q.mul(y, z); let a2 = q.add(x, yz); let s2 = q.pw(a2, 2);
                let p = q.add(s1, s2); let rhs = q.add(p, one);
                let n = q.ne(lhs, rhs); q.assert(n); q },
        },

        // ================================================== axis F: nonzero-poly-but-unsat
        Case {
            id: "F1-square-eq-2", axis: Axis::F, tier: Tier::Core, expect: "unsat",
            formula: "x*x = 2",
            why: "TRAP: x^2-2 is NOT the zero polynomial, yet the query is unsat over Z (1<2<4)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let xx = q.mul(x, x); let two = q.k(2);
                let e = q.eq(xx, two); q.assert(e); q },
        },
        Case {
            id: "F2-square-eq-4", axis: Axis::F, tier: Tier::Core, expect: "sat",
            formula: "x*x = 4", why: "witness x=2",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let xx = q.mul(x, x); let four = q.k(4);
                let e = q.eq(xx, four); q.assert(e); q },
        },
        Case {
            id: "F3-sum2sq-3", axis: Axis::F, tier: Tier::Core, expect: "unsat",
            formula: "x^2 + y^2 = 3", why: "no integer n = 3 mod 4 is a sum of two squares",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x2 = q.mul(x, x); let y2 = q.mul(y, y); let s = q.add(x2, y2);
                let three = q.k(3); let e = q.eq(s, three); q.assert(e); q },
        },
        Case {
            id: "F4-sum2sq-5", axis: Axis::F, tier: Tier::Core, expect: "sat",
            formula: "x^2 + y^2 = 5", why: "witness x=1 y=2",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x2 = q.mul(x, x); let y2 = q.mul(y, y); let s = q.add(x2, y2);
                let five = q.k(5); let e = q.eq(s, five); q.assert(e); q },
        },
        Case {
            id: "F5-sum3sq-7", axis: Axis::F, tier: Tier::Hard, expect: "unsat",
            formula: "x^2 + y^2 + z^2 = 7", why: "Legendre three-square theorem (7 = 4^0(8*0+7))",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x2 = q.mul(x, x); let y2 = q.mul(y, y); let z2 = q.mul(z, z);
                let s0 = q.add(x2, y2); let s = q.add(s0, z2);
                let seven = q.k(7); let e = q.eq(s, seven); q.assert(e); q },
        },
        Case {
            id: "F6-sum3sq-6", axis: Axis::F, tier: Tier::Core, expect: "sat",
            formula: "x^2 + y^2 + z^2 = 6", why: "witness x=1 y=1 z=2",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x2 = q.mul(x, x); let y2 = q.mul(y, y); let z2 = q.mul(z, z);
                let s0 = q.add(x2, y2); let s = q.add(s0, z2);
                let six = q.k(6); let e = q.eq(s, six); q.assert(e); q },
        },
        Case {
            id: "F7-pythag-3-5", axis: Axis::F, tier: Tier::Core, expect: "unsat",
            formula: "x = 3 /\\ y = 5 /\\ x^2 + y^2 = z^2", why: "34 is not a perfect square",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let three = q.k(3); let e = q.eq(x, three); q.assert(e);
                let five = q.k(5); let e = q.eq(y, five); q.assert(e);
                let x2 = q.mul(x, x); let y2 = q.mul(y, y); let s = q.add(x2, y2);
                let z2 = q.mul(z, z); let e = q.eq(s, z2); q.assert(e); q },
        },
        Case {
            id: "F8-pythag-3-4", axis: Axis::F, tier: Tier::Core, expect: "sat",
            formula: "x = 3 /\\ y = 4 /\\ x^2 + y^2 = z^2", why: "witness z=5",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let three = q.k(3); let e = q.eq(x, three); q.assert(e);
                let four = q.k(4); let e = q.eq(y, four); q.assert(e);
                let x2 = q.mul(x, x); let y2 = q.mul(y, y); let s = q.add(x2, y2);
                let z2 = q.mul(z, z); let e = q.eq(s, z2); q.assert(e); q },
        },
        Case {
            id: "F9-linear-gcd-3", axis: Axis::F, tier: Tier::Anchor, expect: "unsat",
            formula: "4x + 6y = 3", why: "the left side is even",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let four = q.k(4); let six = q.k(6);
                let a = q.mul(four, x); let b = q.mul(six, y); let s = q.add(a, b);
                let three = q.k(3); let e = q.eq(s, three); q.assert(e); q },
        },
        Case {
            id: "F10-linear-gcd-2", axis: Axis::F, tier: Tier::Anchor, expect: "sat",
            formula: "4x + 6y = 2", why: "witness x=-1 y=1",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let four = q.k(4); let six = q.k(6);
                let a = q.mul(four, x); let b = q.mul(six, y); let s = q.add(a, b);
                let two = q.k(2); let e = q.eq(s, two); q.assert(e); q },
        },
        Case {
            id: "F11-sqrt2-descent", axis: Axis::F, tier: Tier::Hard, expect: "unsat",
            formula: "x*x = 2*y*y /\\ y >= 1", why: "irrationality of sqrt 2 (infinite descent)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                q.assert_ge_k(y, 1);
                let xx = q.mul(x, x); let yy = q.mul(y, y);
                let two = q.k(2); let t = q.mul(two, yy);
                let e = q.eq(xx, t); q.assert(e); q },
        },
        Case {
            id: "F12-sqrt2-descent-ctrl", axis: Axis::F, tier: Tier::Core, expect: "sat",
            formula: "x*x = 4*y*y /\\ y >= 1", why: "witness x=2 y=1",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                q.assert_ge_k(y, 1);
                let xx = q.mul(x, x); let yy = q.mul(y, y);
                let four = q.k(4); let t = q.mul(four, yy);
                let e = q.eq(xx, t); q.assert(e); q },
        },
        Case {
            id: "F13-square-eq-cube", axis: Axis::F, tier: Tier::Core, expect: "sat",
            formula: "x^2 = y^3 /\\ x >= 2 /\\ y >= 2", why: "witness x=8 y=4 (64 = 64)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                q.assert_ge_k(x, 2); q.assert_ge_k(y, 2);
                let x2 = q.pw(x, 2); let y3 = q.pw(y, 3);
                let e = q.eq(x2, y3); q.assert(e); q },
        },
        Case {
            id: "F14-mordell-7", axis: Axis::F, tier: Tier::Hard, expect: "unsat",
            formula: "x^2 = y^3 + 7", why: "the Mordell curve y^3 = x^2 - 7 has no integer point",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x2 = q.pw(x, 2); let y3 = q.pw(y, 3);
                let seven = q.k(7); let r = q.add(y3, seven);
                let e = q.eq(x2, r); q.assert(e); q },
        },

        // ================================================== axis G: tripwires
        Case {
            id: "G1-pell-61", axis: Axis::G, tier: Tier::Tripwire, expect: "sat",
            formula: "x^2 - 61*y^2 = 1 /\\ y >= 1",
            why: "TRIPWIRE. sat; the SMALLEST witness is x=1766319049 y=226153980. An `unsat` \
                  here is a WRONG ANSWER produced by a bounded abstraction. `unknown` is fine.",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                q.assert_ge_k(y, 1);
                let x2 = q.mul(x, x); let y2 = q.mul(y, y);
                let d = q.k(61); let dy = q.mul(d, y2);
                let lhs = q.sub(x2, dy); let one = q.k(1);
                let e = q.eq(lhs, one); q.assert(e); q },
        },
        Case {
            id: "G2-pell-109", axis: Axis::G, tier: Tier::Tripwire, expect: "sat",
            formula: "x^2 - 109*y^2 = 1 /\\ y >= 1",
            why: "TRIPWIRE. sat; smallest witness x=158070671986249 y=15140424455100 (~1.6e14). \
                  Far outside any 32- or 64-bit blast box. `unsat` = wrong answer.",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                q.assert_ge_k(y, 1);
                let x2 = q.mul(x, x); let y2 = q.mul(y, y);
                let d = q.k(109); let dy = q.mul(d, y2);
                let lhs = q.sub(x2, dy); let one = q.k(1);
                let e = q.eq(lhs, one); q.assert(e); q },
        },
        Case {
            id: "G3-pell-61-neg", axis: Axis::G, tier: Tier::Tripwire, expect: "sat",
            formula: "x^2 - 61*y^2 = -1 /\\ y >= 1",
            why: "TRIPWIRE. sat with witness x=29718 y=3805. `unsat` = wrong answer.",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                q.assert_ge_k(y, 1);
                let x2 = q.mul(x, x); let y2 = q.mul(y, y);
                let d = q.k(61); let dy = q.mul(d, y2);
                let lhs = q.sub(x2, dy); let m1 = q.k(-1);
                let e = q.eq(lhs, m1); q.assert(e); q },
        },
        Case {
            id: "G4-pell-square-d", axis: Axis::G, tier: Tier::Core, expect: "unsat",
            formula: "x^2 - 4*y^2 = 2", why: "(x-2y)(x+2y) = 2 is impossible by parity",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let x2 = q.mul(x, x); let y2 = q.mul(y, y);
                let d = q.k(4); let dy = q.mul(d, y2);
                let lhs = q.sub(x2, dy); let two = q.k(2);
                let e = q.eq(lhs, two); q.assert(e); q },
        },
        Case {
            id: "G5-flt-4", axis: Axis::G, tier: Tier::Hard, expect: "unsat",
            formula: "x^4 + y^4 = z^4 /\\ x,y,z >= 1",
            why: "Fermat n=4 (elementary infinite descent). `unknown` is the honest answer; an \
                  `unsat` must be checked for an actual proof before it counts.",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                q.assert_ge_k(x, 1); q.assert_ge_k(y, 1); q.assert_ge_k(z, 1);
                let x4 = q.pw(x, 4); let y4 = q.pw(y, 4); let z4 = q.pw(z, 4);
                let s = q.add(x4, y4); let e = q.eq(s, z4); q.assert(e); q },
        },
        Case {
            id: "G6-flt-4-nearmiss", axis: Axis::G, tier: Tier::Core, expect: "sat",
            formula: "x^4 + y^4 = z^4 + 1 /\\ x,y,z >= 1", why: "witness x=y=z=1 (1+1 = 1+1)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                q.assert_ge_k(x, 1); q.assert_ge_k(y, 1); q.assert_ge_k(z, 1);
                let x4 = q.pw(x, 4); let y4 = q.pw(y, 4); let z4 = q.pw(z, 4);
                let one = q.k(1); let r = q.add(z4, one);
                let s = q.add(x4, y4); let e = q.eq(s, r); q.assert(e); q },
        },
        Case {
            id: "G7-flt-3", axis: Axis::G, tier: Tier::Hard, expect: "unsat",
            formula: "x^3 + y^3 = z^3 /\\ x,y,z >= 1", why: "Euler, n=3. `unknown` is the honest answer.",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                q.assert_ge_k(x, 1); q.assert_ge_k(y, 1); q.assert_ge_k(z, 1);
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let z3 = q.pw(z, 3);
                let s = q.add(x3, y3); let e = q.eq(s, z3); q.assert(e); q },
        },
        Case {
            id: "G8-taxicab-1729", axis: Axis::G, tier: Tier::Core, expect: "sat",
            formula: "x^3 + y^3 = 1729 /\\ x >= 1 /\\ y >= 1", why: "witness x=9 y=10 (also 1,12)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                q.assert_ge_k(x, 1); q.assert_ge_k(y, 1);
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let s = q.add(x3, y3);
                let n = q.k(1729); let e = q.eq(s, n); q.assert(e); q },
        },
        Case {
            id: "G9-three-cubes-4", axis: Axis::G, tier: Tier::Hard, expect: "unsat",
            formula: "x^3 + y^3 + z^3 = 4", why: "cubes are {0,1,8} mod 9; no triple sums to 4 mod 9",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let z3 = q.pw(z, 3);
                let s0 = q.add(x3, y3); let s = q.add(s0, z3);
                let four = q.k(4); let e = q.eq(s, four); q.assert(e); q },
        },
        Case {
            id: "G10-three-cubes-5", axis: Axis::G, tier: Tier::Hard, expect: "unsat",
            formula: "x^3 + y^3 + z^3 = 5", why: "same mod-9 obstruction as G9",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let z3 = q.pw(z, 3);
                let s0 = q.add(x3, y3); let s = q.add(s0, z3);
                let five = q.k(5); let e = q.eq(s, five); q.assert(e); q },
        },
        Case {
            id: "G11-three-cubes-3", axis: Axis::G, tier: Tier::Core, expect: "sat",
            formula: "x^3 + y^3 + z^3 = 3", why: "witness (1,1,1); also the famous (4,4,-5)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let z3 = q.pw(z, 3);
                let s0 = q.add(x3, y3); let s = q.add(s0, z3);
                let three = q.k(3); let e = q.eq(s, three); q.assert(e); q },
        },
        Case {
            id: "G12-three-cubes-33", axis: Axis::G, tier: Tier::Tripwire, expect: "sat",
            formula: "x^3 + y^3 + z^3 = 33",
            why: "TRIPWIRE. sat, but the only known witness has |x| ~ 8.9e15 and cubes ~ 7e47, \
                  i.e. beyond i128. `unsat` = wrong answer. An overflow-driven `unknown` is the \
                  correct conservative behaviour and is what we expect.",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let z3 = q.pw(z, 3);
                let s0 = q.add(x3, y3); let s = q.add(s0, z3);
                let n = q.k(33); let e = q.eq(s, n); q.assert(e); q },
        },
        Case {
            id: "G13-three-cubes-114-OPEN", axis: Axis::G, tier: Tier::Open, expect: "open",
            formula: "x^3 + y^3 + z^3 = 114",
            why: "OPEN as of 2026: nobody knows whether an integer solution exists. Any decisive \
                  verdict is a bug OR a research result — a `sat` model must verify in Python \
                  before it is believed; an `unsat` is a theorem nobody has proved.",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let z3 = q.pw(z, 3);
                let s0 = q.add(x3, y3); let s = q.add(s0, z3);
                let n = q.k(114); let e = q.eq(s, n); q.assert(e); q },
        },
        Case {
            id: "G14-three-cubes-390-OPEN", axis: Axis::G, tier: Tier::Open, expect: "open",
            formula: "x^3 + y^3 + z^3 = 390", why: "OPEN as of 2026; same status as G13",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let x3 = q.pw(x, 3); let y3 = q.pw(y, 3); let z3 = q.pw(z, 3);
                let s0 = q.add(x3, y3); let s = q.add(s0, z3);
                let n = q.k(390); let e = q.eq(s, n); q.assert(e); q },
        },
        Case {
            id: "G15-brocard-5", axis: Axis::G, tier: Tier::Core, expect: "sat",
            formula: "m^2 = 121 /\\ m >= 1", why: "witness m=11 (the 5!+1 = 11^2 Brocard instance)",
            build: || { let mut q = Q::new();
                let m = q.var("m"); q.assert_ge_k(m, 1);
                let m2 = q.mul(m, m); let n = q.k(121);
                let e = q.eq(m2, n); q.assert(e); q },
        },

        // ================================================== axis H: anchors
        Case {
            id: "H1-linear-sat", axis: Axis::H, tier: Tier::Anchor, expect: "sat",
            formula: "x + y = 3 /\\ x - y = 1", why: "witness x=2 y=1",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let s = q.add(x, y); let three = q.k(3); let e = q.eq(s, three); q.assert(e);
                let d = q.sub(x, y); let one = q.k(1); let e = q.eq(d, one); q.assert(e); q },
        },
        Case {
            id: "H2-linear-unsat", axis: Axis::H, tier: Tier::Anchor, expect: "unsat",
            formula: "x + y = 3 /\\ x + y = 4", why: "a sum cannot equal both 3 and 4",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y");
                let s = q.add(x, y); let three = q.k(3); let e = q.eq(s, three); q.assert(e);
                let s2 = q.add(x, y); let four = q.k(4); let e = q.eq(s2, four); q.assert(e); q },
        },
        Case {
            id: "H3-mul-lower-bound", axis: Axis::H, tier: Tier::Anchor, expect: "unsat",
            formula: "a >= 2 /\\ b >= 1 /\\ a*b < 1", why: "a*b >= 2",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 1);
                let ab = q.mul(a, b); let one = q.k(1);
                let t = q.lt(ab, one); q.assert(t); q },
        },
        Case {
            id: "H4-dl-negative-cycle", axis: Axis::H, tier: Tier::Anchor, expect: "unsat",
            formula: "x-y <= 3 /\\ y-z <= 2 /\\ z-x <= -6", why: "cycle weight 3+2-6 = -1 < 0",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let d = q.sub(x, y); let k = q.k(3); let e = q.le(d, k); q.assert(e);
                let d = q.sub(y, z); let k = q.k(2); let e = q.le(d, k); q.assert(e);
                let d = q.sub(z, x); let k = q.k(-6); let e = q.le(d, k); q.assert(e); q },
        },
        Case {
            id: "H5-dl-zero-cycle", axis: Axis::H, tier: Tier::Anchor, expect: "sat",
            formula: "x-y <= 3 /\\ y-z <= 2 /\\ z-x <= -5", why: "witness x=5 y=2 z=0 (all tight)",
            build: || { let mut q = Q::new();
                let x = q.var("x"); let y = q.var("y"); let z = q.var("z");
                let d = q.sub(x, y); let k = q.k(3); let e = q.le(d, k); q.assert(e);
                let d = q.sub(y, z); let k = q.k(2); let e = q.le(d, k); q.assert(e);
                let d = q.sub(z, x); let k = q.k(-5); let e = q.le(d, k); q.assert(e); q },
        },

        // ================================================== axis U: unit-shape boundary
        //
        // Added AFTER the baseline, to probe the boundary of the `cas-int-units`
        // route introduced in 175372bdc. Each entry has the syntactic shape the
        // route fires on (`<product of variables> = <small constant>` under a
        // lower bound) but most of them are SATISFIABLE. A route that pattern-
        // matches the shape rather than checking the arithmetic answers a wrong
        // `unsat` here. Run against BOTH the baseline and the after binary.
        Case {
            id: "U1-unit-neg-p", axis: Axis::U, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ p <= -1 /\\ a*p = 1", why: "a*p <= -2 < 1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_ge_k(a, 2); q.assert_le_k(p, -1);
                let ap = q.mul(a, p); let one = q.k(1); let e = q.eq(ap, one); q.assert(e); q },
        },
        Case {
            id: "U2-product-eq-a", axis: Axis::U, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ a*p = a", why: "witness a=2 p=1 — RHS is `a`, not 1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_ge_k(a, 2);
                let ap = q.mul(a, p); let e = q.eq(ap, a); q.assert(e); q },
        },
        Case {
            id: "U3-product-eq-0", axis: Axis::U, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ a*p = 0", why: "witness a=2 p=0",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_ge_k(a, 2);
                let ap = q.mul(a, p); let zero = q.k(0); let e = q.eq(ap, zero); q.assert(e); q },
        },
        Case {
            id: "U4-unit-unbounded", axis: Axis::U, tier: Tier::Core, expect: "sat",
            formula: "a*p = 1  [no bound on a at all]", why: "witness a=1 p=1 (also a=p=-1)",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                let ap = q.mul(a, p); let one = q.k(1); let e = q.eq(ap, one); q.assert(e); q },
        },
        Case {
            id: "U5-two-factors-eq-1", axis: Axis::U, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ b >= 2 /\\ a*b = 1", why: "a*b >= 4 > 1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 2);
                let ab = q.mul(a, b); let one = q.k(1); let e = q.eq(ab, one); q.assert(e); q },
        },
        Case {
            id: "U6-two-factors-eq-4", axis: Axis::U, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ b >= 2 /\\ a*b = 4", why: "witness a=2 b=2",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let b = q.var("b");
                q.assert_ge_k(a, 2); q.assert_ge_k(b, 2);
                let ab = q.mul(a, b); let four = q.k(4); let e = q.eq(ab, four); q.assert(e); q },
        },
        Case {
            id: "U7-unit-minus-one", axis: Axis::U, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ a*p = -1", why: "|a*p| is 0 or >= 2, never 1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_ge_k(a, 2);
                let ap = q.mul(a, p); let m1 = q.k(-1); let e = q.eq(ap, m1); q.assert(e); q },
        },
        Case {
            id: "U8-product-eq-2", axis: Axis::U, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ a*p = 2", why: "witness a=2 p=1",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p");
                q.assert_ge_k(a, 2);
                let ap = q.mul(a, p); let two = q.k(2); let e = q.eq(ap, two); q.assert(e); q },
        },
        Case {
            id: "U9-three-factors-eq-1", axis: Axis::U, tier: Tier::Core, expect: "unsat",
            formula: "a >= 2 /\\ a*p*r = 1", why: "a | 1 is impossible for a >= 2",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p"); let r = q.var("r");
                q.assert_ge_k(a, 2);
                let ap = q.mul(a, p); let apr = q.mul(ap, r);
                let one = q.k(1); let e = q.eq(apr, one); q.assert(e); q },
        },
        Case {
            id: "U10-three-factors-eq-8", axis: Axis::U, tier: Tier::Core, expect: "sat",
            formula: "a >= 2 /\\ p >= 2 /\\ r >= 2 /\\ a*p*r = 8", why: "witness a=p=r=2",
            build: || { let mut q = Q::new();
                let a = q.var("a"); let p = q.var("p"); let r = q.var("r");
                q.assert_ge_k(a, 2); q.assert_ge_k(p, 2); q.assert_ge_k(r, 2);
                let ap = q.mul(a, p); let apr = q.mul(ap, r);
                let eight = q.k(8); let e = q.eq(apr, eight); q.assert(e); q },
        },
    ]
}
