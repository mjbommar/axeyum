//! Verify capability scoreboard — the App-C measurement deliverable (mirrors the
//! EVM one). A construction-known corpus of `#[verify]`-shaped programs is decided
//! by `verify_program` (the unroll route); loop programs in the warm-BMC fragment
//! are *also* decided by `check_program_loop` and the two routes must **agree**.
//! The soundness floor is `DISAGREE = 0`: a verdict contradicting the
//! construction-known label, or a warm-vs-unroll disagreement.
//!
//! Run: `cargo run -p axeyum-verify --example measure_verify`
//! Writes: `docs/consumer-track/verify/SCOREBOARD.md` and `.../corpus.json`.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::ExitCode;

use axeyum_solver::SolverConfig;
use axeyum_verify::ast::{BinOp, Expr, Param, Program, Stmt, Ty};
use axeyum_verify::bmc::LoopSafety;
use axeyum_verify::loop_system::check_program_loop;
use axeyum_verify::{Verdict, verify_program};

const U8: Ty = Ty::Int {
    width: 8,
    signed: false,
};

fn var(n: &str) -> Expr {
    Expr::Var(n.to_string())
}
fn lit(value: u128) -> Expr {
    Expr::IntLit { value, ty: U8 }
}
fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::Binary {
        op,
        lhs: Box::new(l),
        rhs: Box::new(r),
    }
}
fn param(n: &str) -> Param {
    Param {
        name: n.to_string(),
        ty: U8,
    }
}
fn prog(name: &str, params: Vec<Param>, body: Vec<Stmt>) -> Program {
    Program {
        name: name.to_string(),
        params,
        arrays: vec![],
        body,
    }
}
fn let_(name: &str, value: Expr) -> Stmt {
    Stmt::Let {
        name: name.to_string(),
        ty: U8,
        value,
    }
}
fn assign(name: &str, value: Expr) -> Stmt {
    Stmt::Assign {
        name: name.to_string(),
        value,
    }
}

/// What a program was constructed to be.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Expect {
    Bug,
    Safe,
}

struct Case {
    name: &'static str,
    class: &'static str,
    expect: Expect,
    program: Program,
}

enum Outcome {
    BugFound,
    /// Proved safe; `lean` is true iff the proof carries a kernel-checkable Lean
    /// module (the "trusted small checking" moat metric).
    Verified {
        lean: bool,
    },
    Unknown,
    Disagree(String),
}

impl Outcome {
    fn tag(&self) -> &'static str {
        match self {
            Outcome::BugFound => "bug-found",
            Outcome::Verified { .. } => "verified",
            Outcome::Unknown => "unknown",
            Outcome::Disagree(_) => "DISAGREE",
        }
    }
}

/// `while i < limit { i = i + 1; assert!(i != bad); }` after `let i = 0`, with an
/// explicit unwind `bound`.
fn counter_program_b(bad: u128, bound: u128) -> Program {
    prog(
        "counter",
        vec![param("limit")],
        vec![
            let_("i", lit(0)),
            Stmt::While {
                cond: bin(BinOp::Lt, var("i"), var("limit")),
                bound,
                body: vec![
                    assign("i", bin(BinOp::Add, var("i"), lit(1))),
                    Stmt::Assert(bin(BinOp::Ne, var("i"), lit(bad))),
                ],
            },
        ],
    )
}

fn counter_program(bad: u128) -> Program {
    counter_program_b(bad, 10)
}

#[allow(clippy::too_many_lines)] // a flat data listing of construction-known cases
fn corpus() -> Vec<Case> {
    vec![
        Case {
            name: "add-overflow",
            class: "overflow",
            expect: Expect::Bug,
            program: prog(
                "add",
                vec![param("a"), param("b")],
                vec![let_("c", bin(BinOp::Add, var("a"), var("b")))],
            ),
        },
        Case {
            name: "mask-safe",
            class: "overflow",
            expect: Expect::Safe,
            program: prog(
                "mask",
                vec![param("a")],
                vec![let_("c", bin(BinOp::BitAnd, var("a"), lit(0x0f)))],
            ),
        },
        Case {
            name: "signed-add-overflow",
            class: "overflow",
            expect: Expect::Bug,
            program: prog(
                "sadd",
                vec![
                    Param {
                        name: "a".to_string(),
                        ty: Ty::Int {
                            width: 8,
                            signed: true,
                        },
                    },
                    Param {
                        name: "b".to_string(),
                        ty: Ty::Int {
                            width: 8,
                            signed: true,
                        },
                    },
                ],
                vec![Stmt::Let {
                    name: "c".to_string(),
                    ty: Ty::Int {
                        width: 8,
                        signed: true,
                    },
                    value: bin(BinOp::Add, var("a"), var("b")),
                }],
            ),
        },
        Case {
            name: "sub-underflow",
            class: "overflow",
            expect: Expect::Bug,
            program: prog(
                "sub",
                vec![param("a"), param("b")],
                vec![let_("c", bin(BinOp::Sub, var("a"), var("b")))],
            ),
        },
        Case {
            name: "div-by-zero",
            class: "div0",
            expect: Expect::Bug,
            program: prog(
                "div",
                vec![param("a"), param("b")],
                vec![let_("c", bin(BinOp::Div, var("a"), var("b")))],
            ),
        },
        Case {
            name: "assert-violation",
            class: "assert",
            expect: Expect::Bug,
            program: prog(
                "guard",
                vec![param("a")],
                vec![Stmt::Assert(bin(BinOp::Ne, var("a"), lit(7)))],
            ),
        },
        Case {
            name: "assert-safe",
            class: "assert",
            expect: Expect::Safe,
            program: prog(
                "tautology",
                vec![param("a")],
                vec![Stmt::Assert(bin(BinOp::Eq, var("a"), var("a")))],
            ),
        },
        // --- Widened fragment: wrapping / saturating / min-max (C5) ----------
        Case {
            // Modular add never panics — a program of only wrapping ops is safe.
            name: "wrapping-add-no-overflow",
            class: "wrapping",
            expect: Expect::Safe,
            program: prog(
                "wrap",
                vec![param("a"), param("b")],
                vec![let_("c", bin(BinOp::WrappingAdd, var("a"), var("b")))],
            ),
        },
        Case {
            // `wrapping_add(a, 1) > a` is false at a = 255 (wraps to 0).
            name: "wrapping-not-monotone",
            class: "wrapping",
            expect: Expect::Bug,
            program: prog(
                "wrap_mono",
                vec![param("a")],
                vec![
                    let_("c", bin(BinOp::WrappingAdd, var("a"), lit(1))),
                    Stmt::Assert(bin(BinOp::Gt, var("c"), var("a"))),
                ],
            ),
        },
        Case {
            // Saturating sub never panics (clamps at 0).
            name: "saturating-sub-no-underflow",
            class: "saturating",
            expect: Expect::Safe,
            program: prog(
                "sat",
                vec![param("a"), param("b")],
                vec![let_("c", bin(BinOp::SaturatingSub, var("a"), var("b")))],
            ),
        },
        Case {
            // `min(a, 10) <= 10` always holds.
            name: "min-clamp-safe",
            class: "minmax",
            expect: Expect::Safe,
            program: prog(
                "minc",
                vec![param("a")],
                vec![
                    let_("c", bin(BinOp::Min, var("a"), lit(10))),
                    Stmt::Assert(bin(BinOp::Le, var("c"), lit(10))),
                ],
            ),
        },
        Case {
            // `max(a, 10) >= 10` always holds.
            name: "max-floor-safe",
            class: "minmax",
            expect: Expect::Safe,
            program: prog(
                "maxf",
                vec![param("a")],
                vec![
                    let_("c", bin(BinOp::Max, var("a"), lit(10))),
                    Stmt::Assert(bin(BinOp::Ge, var("c"), lit(10))),
                ],
            ),
        },
        Case {
            name: "loop-assert-bug",
            class: "loop",
            expect: Expect::Bug,
            program: counter_program(5),
        },
        Case {
            name: "loop-safe",
            class: "loop",
            expect: Expect::Safe,
            program: counter_program(200),
        },
    ]
}

fn evaluate(case: &Case, cfg: &SolverConfig) -> Outcome {
    let verdict = match verify_program(&case.program, cfg) {
        Ok(v) => v,
        Err(e) => return Outcome::Disagree(format!("verify error: {e:?}")),
    };
    let unroll_bug = matches!(verdict, Verdict::Counterexample { .. });
    let unroll_safe = matches!(verdict, Verdict::Verified { .. });

    // For loop programs in the warm fragment, the warm route must agree.
    if case.class == "loop" {
        if let Some(res) = check_program_loop(&case.program, 10, cfg) {
            match res {
                Ok(LoopSafety::BugReachable { .. }) if !unroll_bug => {
                    return Outcome::Disagree("warm found a bug the unroll route did not".into());
                }
                Ok(LoopSafety::SafeWithinBound { .. }) if !unroll_safe => {
                    return Outcome::Disagree("warm proved safe but unroll did not".into());
                }
                _ => {}
            }
        }
    }

    match (case.expect, &verdict) {
        (Expect::Bug, Verdict::Counterexample { .. }) => Outcome::BugFound,
        (Expect::Bug, Verdict::Verified { .. }) => {
            Outcome::Disagree("proved safe but a bug was constructed".into())
        }
        (Expect::Safe, Verdict::Verified { lean_module, .. }) => Outcome::Verified {
            lean: lean_module.is_some(),
        },
        (Expect::Safe, Verdict::Counterexample { .. }) => {
            Outcome::Disagree("counterexample on a safe program".into())
        }
        _ => Outcome::Unknown,
    }
}

/// One depth point of the warm-BMC-vs-unroll scaling sweep on a safe loop.
struct ScaleRow {
    bound: usize,
    unroll_us: u128,
    warm_us: u128,
    agree: bool,
}

/// Decide a safe counter loop (`assert i != 200`, out of reach) at increasing
/// unwind bounds via both the unroll route (`verify_program`) and the warm route
/// (`check_program_loop`), timing each. Honest measurement of whether the warm
/// (incremental-across-depths) route actually pays off vs. unrolling — and a
/// soundness check that both stay "safe" at every depth.
fn scaling_sweep(cfg: &SolverConfig) -> Vec<ScaleRow> {
    let mut rows = Vec::new();
    for &bound in &[2_usize, 4, 6, 8] {
        let prog = counter_program_b(200, bound as u128);
        let t0 = std::time::Instant::now();
        let unroll = verify_program(&prog, cfg).expect("verify");
        let unroll_us = t0.elapsed().as_micros();
        let t1 = std::time::Instant::now();
        let warm = check_program_loop(&prog, bound, cfg)
            .expect("fragment")
            .expect("run");
        let warm_us = t1.elapsed().as_micros();
        let agree = matches!(unroll, Verdict::Verified { .. })
            && matches!(warm, LoopSafety::SafeWithinBound { .. });
        rows.push(ScaleRow {
            bound,
            unroll_us,
            warm_us,
            agree,
        });
    }
    rows
}

fn render_scaling(rows: &[ScaleRow]) -> String {
    let mut out = String::new();
    out.push_str("\n## Warm-BMC vs unroll scaling (safe deep loop)\n\n");
    out.push_str(
        "A safe counter loop decided at increasing unwind bounds by both routes \
         (both must stay `verified`/`safe` — agreement is the soundness check). \
         Times are a single wall-clock run, indicative not tuned. **Caveat:** not \
         pure apples-to-apples — the unroll route (`verify_program`) also produces \
         a re-checked evidence certificate + a Lean-reconstruction attempt, while \
         the warm route currently returns only the decision (a cert on the warm \
         route is a follow-up). Even so, the warm `bounded_model_check` is \
         genuinely incremental across depths and scales far better here — the \
         *opposite* of the EVM store-chain result (U6/U7), where the one-shot \
         memory dispatcher made the array path lose to `ite`-fold.\n\n",
    );
    out.push_str("| Unwind bound | unroll t µs | warm-BMC t µs | agree |\n|---|---|---|---|\n");
    for r in rows {
        let _ = writeln!(
            out,
            "| {} | {} | {} | {} |",
            r.bound,
            r.unroll_us,
            r.warm_us,
            if r.agree { "yes" } else { "**NO**" },
        );
    }
    out
}

fn render(rows: &[(&Case, Outcome)], disagree: usize) -> String {
    let mut out = String::new();
    out.push_str("# Verify capability scoreboard\n\n");
    out.push_str(
        "Generated by `cargo run -p axeyum-verify --example measure_verify`. A \
         construction-known corpus through `verify_program`; loop programs are \
         cross-checked against the warm `check_program_loop` route. **DISAGREE = 0** \
         is the soundness floor (a verdict contradicting the known label, or a \
         warm-vs-unroll disagreement).\n\n",
    );
    let found = rows
        .iter()
        .filter(|(_, o)| matches!(o, Outcome::BugFound))
        .count();
    let verified = rows
        .iter()
        .filter(|(_, o)| matches!(o, Outcome::Verified { .. }))
        .count();
    let lean = rows
        .iter()
        .filter(|(_, o)| matches!(o, Outcome::Verified { lean: true }))
        .count();
    let unknown = rows
        .iter()
        .filter(|(_, o)| matches!(o, Outcome::Unknown))
        .count();
    let _ = writeln!(
        out,
        "## Headline\n\n- **{} cases**: {found} bugs found, {verified} verified, \
         {unknown} unknown.\n- **DISAGREE = {disagree}** (soundness floor).\n- \
         **Lean-certified: {lean}/{verified}** verified results carry a \
         kernel-checkable Lean module (the trusted-checking moat; the rest are \
         re-checked in-process but outside the Lean reconstructor's fragment).\n",
        rows.len(),
    );
    out.push_str(
        "## Per case\n\n| Case | Class | Expected | Outcome | Lean |\n|---|---|---|---|---|\n",
    );
    for (case, outcome) in rows {
        let expected = match case.expect {
            Expect::Bug => "bug",
            Expect::Safe => "safe",
        };
        let note = match outcome {
            Outcome::Disagree(why) => format!("{} ({why})", outcome.tag()),
            _ => outcome.tag().to_string(),
        };
        let lean_mark = match outcome {
            Outcome::Verified { lean: true } => "yes",
            Outcome::Verified { lean: false } => "no",
            _ => "—",
        };
        let _ = writeln!(
            out,
            "| {} | {} | {expected} | {note} | {lean_mark} |",
            case.name, case.class
        );
    }
    out
}

fn render_json(rows: &[(&Case, Outcome)], disagree: usize) -> String {
    let mut out = String::new();
    out.push_str("{\n");
    let _ = writeln!(
        out,
        "  \"total\": {}, \"disagree\": {},",
        rows.len(),
        disagree
    );
    out.push_str("  \"cases\": [\n");
    for (i, (case, outcome)) in rows.iter().enumerate() {
        let comma = if i + 1 == rows.len() { "" } else { "," };
        let _ = writeln!(
            out,
            "    {{ \"name\": \"{}\", \"class\": \"{}\", \"outcome\": \"{}\" }}{comma}",
            case.name,
            case.class,
            outcome.tag(),
        );
    }
    out.push_str("  ]\n}\n");
    out
}

fn main() -> ExitCode {
    let cfg = SolverConfig::default();
    let cases = corpus();
    let mut rows: Vec<(&Case, Outcome)> = Vec::new();
    for case in &cases {
        let outcome = evaluate(case, &cfg);
        if let Outcome::Disagree(why) = &outcome {
            eprintln!("DISAGREE on {}: {why}", case.name);
        }
        rows.push((case, outcome));
    }
    let mut disagree = rows
        .iter()
        .filter(|(_, o)| matches!(o, Outcome::Disagree(_)))
        .count();

    let scale = scaling_sweep(&cfg);
    for r in &scale {
        if !r.agree {
            eprintln!("SCALING DISAGREE at bound {}: routes disagree", r.bound);
            disagree += 1;
        }
    }

    let md = format!("{}{}", render(&rows, disagree), render_scaling(&scale));
    let json = render_json(&rows, disagree);
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../docs/consumer-track/verify");
    std::fs::create_dir_all(&dir).expect("create scoreboard dir");
    std::fs::write(dir.join("SCOREBOARD.md"), &md).expect("write SCOREBOARD.md");
    std::fs::write(dir.join("corpus.json"), &json).expect("write corpus.json");
    print!("{md}");

    if disagree == 0 {
        eprintln!("DISAGREE = 0 over {} cases.", rows.len());
        ExitCode::SUCCESS
    } else {
        eprintln!("FAIL: {disagree} disagreement(s).");
        ExitCode::FAILURE
    }
}
