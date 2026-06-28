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
    Verified,
    Unknown,
    Disagree(String),
}

impl Outcome {
    fn tag(&self) -> &'static str {
        match self {
            Outcome::BugFound => "bug-found",
            Outcome::Verified => "verified",
            Outcome::Unknown => "unknown",
            Outcome::Disagree(_) => "DISAGREE",
        }
    }
}

/// `while i < limit { i = i + 1; assert!(i != bad); }` after `let i = 0`.
fn counter_program(bad: u128) -> Program {
    prog(
        "counter",
        vec![param("limit")],
        vec![
            let_("i", lit(0)),
            Stmt::While {
                cond: bin(BinOp::Lt, var("i"), var("limit")),
                bound: 10,
                body: vec![
                    assign("i", bin(BinOp::Add, var("i"), lit(1))),
                    Stmt::Assert(bin(BinOp::Ne, var("i"), lit(bad))),
                ],
            },
        ],
    )
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

    match case.expect {
        Expect::Bug if unroll_bug => Outcome::BugFound,
        Expect::Bug if unroll_safe => {
            Outcome::Disagree("proved safe but a bug was constructed".into())
        }
        Expect::Safe if unroll_safe => Outcome::Verified,
        Expect::Safe if unroll_bug => Outcome::Disagree("counterexample on a safe program".into()),
        _ => Outcome::Unknown,
    }
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
        .filter(|(_, o)| matches!(o, Outcome::Verified))
        .count();
    let unknown = rows
        .iter()
        .filter(|(_, o)| matches!(o, Outcome::Unknown))
        .count();
    let _ = writeln!(
        out,
        "## Headline\n\n- **{} cases**: {found} bugs found, {verified} verified, \
         {unknown} unknown.\n- **DISAGREE = {disagree}**.\n",
        rows.len(),
    );
    out.push_str("## Per case\n\n| Case | Class | Expected | Outcome |\n|---|---|---|---|\n");
    for (case, outcome) in rows {
        let expected = match case.expect {
            Expect::Bug => "bug",
            Expect::Safe => "safe",
        };
        let note = match outcome {
            Outcome::Disagree(why) => format!("{} ({why})", outcome.tag()),
            _ => outcome.tag().to_string(),
        };
        let _ = writeln!(
            out,
            "| {} | {} | {expected} | {note} |",
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
    let disagree = rows
        .iter()
        .filter(|(_, o)| matches!(o, Outcome::Disagree(_)))
        .count();

    let md = render(&rows, disagree);
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
