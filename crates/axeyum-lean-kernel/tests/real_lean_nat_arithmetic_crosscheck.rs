//! Differential control for literal `Nat` arithmetic against pinned official
//! Lean 4.30.
//!
//! The obligations handed to `lean` are **computed by this kernel**, not written
//! down by hand: for each operation and argument pair, `Kernel::whnf` produces a
//! value, and that value is rendered into an `example … := rfl`. A wrong
//! accelerated answer therefore becomes a Lean type error rather than a test
//! that agrees with itself. Hand-written expectations are what
//! `nat_literal_arithmetic.rs` asserts; this file exists to check the
//! expectations too.
//!
//! Two real-Lean invocations: the generated positive module, and a negative
//! control proving the positive one could have failed.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::{Command, Output};

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, ExprNode, Kernel, Lit, NameId, NatLit, ReducibilityHint,
};

#[path = "support/lean_probe.rs"]
mod lean_probe;

fn run_lean(lean: &PathBuf, file: &std::path::Path) -> Output {
    Command::new(lean)
        .args(["-j", "1", "-s", "1024", "-M", "4096"])
        .arg(file)
        .output()
        .expect("run official Lean Nat arithmetic cross-check")
}

/// The cases. Chosen to hit the corners a kernel gets wrong rather than the ones
/// it gets right: both totality conventions, truncated subtraction, `gcd` with a
/// zero, `pow` of zero, and values past 2^32 and 2^64 where a machine word would
/// wrap.
const CASES: &[(&str, &str, &str)] = &[
    ("add", "0", "0"),
    ("add", "18446744073709551615", "1"),
    ("sub", "3", "9"),
    ("sub", "18446744073709551616", "1"),
    ("mul", "4294967296", "4294967296"),
    ("mul", "0", "18446744073709551616"),
    ("div", "7", "0"),
    ("div", "18446744073709551616", "4294967296"),
    ("mod", "7", "0"),
    ("mod", "18446744073709551617", "4294967296"),
    ("gcd", "0", "12"),
    ("gcd", "12", "0"),
    ("gcd", "462", "1071"),
    ("pow", "0", "0"),
    ("pow", "2", "64"),
    ("land", "4294967295", "4008636142"),
    ("lor", "3735928559", "4008636142"),
    ("xor", "3735928559", "4008636142"),
    ("shiftLeft", "1", "64"),
    ("shiftRight", "18446744073709551616", "64"),
    ("beq", "4294967296", "4294967296"),
    ("beq", "4294967296", "4294967297"),
    ("ble", "4294967296", "4294967297"),
    ("ble", "4294967297", "4294967296"),
];

struct Env {
    nat: NameId,
    nat_type: ExprId,
    bool_true: NameId,
    bool_false: NameId,
}

/// A Lean-shaped `Nat`/`Bool` environment with every accelerated operation
/// declared at its Lean type. The bodies are stubs — `Nat.div` and friends are
/// well-founded recursions in Lean and have no runnable kernel body — which is
/// precisely why the *answers* need an external check.
fn lean_shaped_kernel() -> (Kernel, Env) {
    let mut kernel = Kernel::new();
    let anon = kernel.anon();
    let zero_level = kernel.level_zero();
    let one_level = kernel.level_succ(zero_level);
    let type0 = kernel.sort(one_level);

    let nat = kernel.name_str(anon, "Nat");
    let nat_zero = kernel.name_str(nat, "zero");
    let nat_succ = kernel.name_str(nat, "succ");
    let nat_type = kernel.const_(nat, vec![]);
    let succ_type = kernel.pi(anon, nat_type, nat_type, BinderInfo::Default);
    kernel
        .add_inductive(
            nat,
            &[],
            0,
            type0,
            &[(nat_zero, nat_type), (nat_succ, succ_type)],
        )
        .expect("Nat");

    let bool_name = kernel.name_str(anon, "Bool");
    let bool_false = kernel.name_str(bool_name, "false");
    let bool_true = kernel.name_str(bool_name, "true");
    let bool_type = kernel.const_(bool_name, vec![]);
    kernel
        .add_inductive(
            bool_name,
            &[],
            0,
            type0,
            &[(bool_false, bool_type), (bool_true, bool_type)],
        )
        .expect("Bool");

    for segment in [
        "add",
        "sub",
        "mul",
        "div",
        "mod",
        "gcd",
        "pow",
        "land",
        "lor",
        "xor",
        "shiftLeft",
        "shiftRight",
        "beq",
        "ble",
    ] {
        let result = if segment == "beq" || segment == "ble" {
            bool_type
        } else {
            nat_type
        };
        let name = kernel.name_str(nat, segment);
        let inner_ty = kernel.pi(anon, nat_type, result, BinderInfo::Default);
        let ty = kernel.pi(anon, nat_type, inner_ty, BinderInfo::Default);
        let stub = if result == bool_type {
            kernel.const_(bool_false, vec![])
        } else {
            kernel.const_(nat_zero, vec![])
        };
        let inner = kernel.lam(anon, nat_type, stub, BinderInfo::Default);
        let value = kernel.lam(anon, nat_type, inner, BinderInfo::Default);
        kernel
            .add_declaration(Declaration::Definition {
                name,
                uparams: Vec::new(),
                ty,
                value,
                hint: ReducibilityHint::Regular(1),
            })
            .expect("operation");
    }

    (
        kernel,
        Env {
            nat,
            nat_type,
            bool_true,
            bool_false,
        },
    )
}

/// This kernel's answer for `Nat.<segment> a b`, rendered as Lean source.
fn our_answer(kernel: &mut Kernel, env: &Env, segment: &str, a: &str, b: &str) -> String {
    let name = kernel.name_str(env.nat, segment);
    let head = kernel.const_(name, vec![]);
    let a = kernel.lit(Lit::Nat(NatLit::from_decimal(a).expect("decimal")));
    let b = kernel.lit(Lit::Nat(NatLit::from_decimal(b).expect("decimal")));
    let applied = kernel.app(head, a);
    let applied = kernel.app(applied, b);
    let normal = kernel.whnf(applied);
    match kernel.expr_node(normal) {
        ExprNode::Lit(Lit::Nat(value)) => value.to_string(),
        ExprNode::Const(name, _) if *name == env.bool_true => "true".to_owned(),
        ExprNode::Const(name, _) if *name == env.bool_false => "false".to_owned(),
        other => panic!("Nat.{segment} {a:?} {b:?} did not reduce to a value: {other:?}"),
    }
}

#[test]
fn literal_arithmetic_answers_agree_with_pinned_lean() {
    let Some(lean) = lean_probe::lean_bin_or_skip("nat-arithmetic", 2) else {
        return;
    };
    let version = Command::new(&lean)
        .arg("--version")
        .output()
        .expect("query official Lean version");
    let version_text = format!(
        "{}{}",
        String::from_utf8_lossy(&version.stdout),
        String::from_utf8_lossy(&version.stderr)
    );
    lean_probe::assert_pinned_version("nat-arithmetic", &version_text);

    let (mut kernel, env) = lean_shaped_kernel();
    let mut source = String::from("set_option maxRecDepth 10000\n");
    let mut rendered = 0usize;
    for (segment, a, b) in CASES {
        let answer = our_answer(&mut kernel, &env, segment, a, b);
        let ty = if *segment == "beq" || *segment == "ble" {
            "Bool"
        } else {
            "Nat"
        };
        writeln!(
            source,
            "example : (Nat.{segment} {a} {b} : {ty}) = {answer} := rfl"
        )
        .expect("writing to a String cannot fail");
        rendered += 1;
    }
    assert_eq!(
        rendered,
        CASES.len(),
        "every case must reach the generated module"
    );
    let _ = env.nat_type;

    let directory = std::env::temp_dir().join(format!(
        "axeyum_nat_arithmetic_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create cross-check directory");
    let file = directory.join("NatArithmeticPositive.lean");
    std::fs::write(&file, &source).expect("write positive Lean control");
    let positive = run_lean(&lean, &file);
    assert!(
        positive.status.success(),
        "official Lean rejected an answer this kernel computed ({})\nstdout:\n{}\nstderr:\n{}\nsource:\n{source}",
        lean.display(),
        String::from_utf8_lossy(&positive.stdout),
        String::from_utf8_lossy(&positive.stderr),
    );

    // The negative control. Without it, a module Lean silently accepted because
    // (say) every `example` was mis-parsed would read as a pass.
    let negative_source =
        "example : (Nat.div 7 0 : Nat) = 7 := rfl\nexample : (Nat.mod 7 0 : Nat) = 0 := rfl\n";
    let negative_file = directory.join("NatArithmeticNegative.lean");
    std::fs::write(&negative_file, negative_source).expect("write negative Lean control");
    let negative = run_lean(&lean, &negative_file);
    assert!(
        !negative.status.success(),
        "official Lean accepted the wrong division-by-zero convention\nsource:\n{negative_source}"
    );

    let _ = std::fs::remove_dir_all(directory);
    lean_probe::report_checked("nat-arithmetic", 2);
}
