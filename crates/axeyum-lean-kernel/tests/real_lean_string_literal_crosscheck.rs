//! Differential control for primitive `String` literal semantics against pinned
//! official Lean 4.30.
//!
//! The obligations handed to `lean` are **computed by this kernel**, not written
//! down by hand. For each payload, `Kernel::whnf` reduces the projection of a
//! string literal through the `String.ofList` expansion, and the Unicode scalar
//! values are read back **out of that reduct** — so the list Lean is asked to
//! confirm is the one the kernel's own conversion produced. A byte-oriented
//! decode, a reordered list, a dropped scalar or a normalized one therefore
//! becomes a Lean type error rather than a test that agrees with itself.
//! Hand-written expectations are what `string_literal_semantics.rs` asserts;
//! this file exists to check the expectations too.
//!
//! Two real-Lean invocations: the generated positive module, and a negative
//! control proving the positive one could have failed.

use std::fmt::Write as _;
use std::path::PathBuf;
use std::process::{Command, Output};

use axeyum_lean_kernel::{ExprNode, Kernel, Lit};

#[path = "support/lean_probe.rs"]
mod lean_probe;

#[path = "support/lean_shaped_string.rs"]
mod lean_shaped_string;

use lean_shaped_string::{Env, Mutation, lean_shaped_kernel};

/// The payloads. Chosen for the corners a literal conversion gets wrong rather
/// than the ones it gets right: empty, the JSON/Lean escape characters, control
/// characters including NUL, a two-byte scalar, a three-byte scalar, a
/// supplementary-plane scalar, and the composed/decomposed pair that a
/// normalizing conversion would collapse.
const PAYLOADS: &[&str] = &[
    "",
    "ab",
    "a\"b\\c",
    "\n\t\r",
    "\u{0}\u{1f}\u{7f}",
    "\u{e9}",
    "e\u{301}",
    "\u{2192}",
    "\u{1f642}",
    "a\u{e9}\u{2192}\u{1f642}z",
];

fn run_lean(lean: &PathBuf, file: &std::path::Path) -> Output {
    Command::new(lean)
        .args(["-j", "1", "-s", "1024", "-M", "4096"])
        .arg(file)
        .output()
        .expect("run official Lean String literal cross-check")
}

/// The Unicode scalar values **this kernel** converted the literal to, read out
/// of the reduct rather than recomputed from the payload.
///
/// The route is the projection hook: `Proj(String, 0, literal)` normalizes to
/// the expansion's field, which is the `List Char` of `Char.ofNat <Nat literal>`
/// applications. Walking it back is the only place in this file that knows the
/// expansion's shape, and it knows it as a *reader*.
fn kernel_scalars(kernel: &mut Kernel, env: &Env, payload: &str) -> Vec<String> {
    let literal = kernel.lit(Lit::Str(payload.to_owned()));
    let projection = kernel.proj(env.string, 0, literal);
    let mut cursor = kernel.whnf(projection);
    let mut scalars = Vec::new();
    loop {
        let (head, args) = unfold(kernel, cursor);
        let ExprNode::Const(name, _) = kernel.expr_node(head) else {
            panic!("{payload:?}: expansion reduct is not a constructor application");
        };
        let name = *name;
        if name == env.list_nil {
            assert_eq!(
                args.len(),
                1,
                "{payload:?}: List.nil is applied to its type"
            );
            return scalars;
        }
        assert_eq!(
            name, env.list_cons,
            "{payload:?}: expansion reduct is neither List.nil nor List.cons"
        );
        assert_eq!(args.len(), 3, "{payload:?}: List.cons arity");
        let (of_nat_head, of_nat_args) = unfold(kernel, args[1]);
        assert!(
            matches!(kernel.expr_node(of_nat_head), ExprNode::Const(name, _) if *name == env.char_of_nat),
            "{payload:?}: a character is not a Char.ofNat application"
        );
        assert_eq!(of_nat_args.len(), 1, "{payload:?}: Char.ofNat arity");
        let ExprNode::Lit(Lit::Nat(scalar)) = kernel.expr_node(of_nat_args[0]) else {
            panic!("{payload:?}: a code point is not a Nat literal");
        };
        scalars.push(scalar.to_string());
        cursor = kernel.whnf(args[2]);
    }
}

/// `(head, arguments)` of an application spine.
fn unfold(
    kernel: &Kernel,
    expression: axeyum_lean_kernel::ExprId,
) -> (axeyum_lean_kernel::ExprId, Vec<axeyum_lean_kernel::ExprId>) {
    let mut arguments = Vec::new();
    let mut cursor = expression;
    while let ExprNode::App(function, argument) = kernel.expr_node(cursor) {
        arguments.push(*argument);
        cursor = *function;
    }
    arguments.reverse();
    (cursor, arguments)
}

/// The payload as Lean 4 source.
///
/// Lean's escape grammar is narrower than it looks: there is no `\u{...}` form
/// and `\uXXXX` takes exactly four hex digits with **no surrogate pairing** (a
/// pair silently becomes two NULs, measured on 4.30.0). So a supplementary-plane
/// scalar is emitted raw — Lean source is UTF-8 — and everything else that is
/// not printable ASCII goes through `\xNN` or `\uXXXX`.
fn lean_literal(payload: &str) -> String {
    let mut out = String::from("\"");
    for character in payload.chars() {
        let code = u32::from(character);
        match character {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            _ if (0x20..0x7f).contains(&code) => out.push(character),
            _ if code < 0x100 => {
                let _ = write!(out, "\\x{code:02x}");
            }
            _ if code <= 0xffff => {
                let _ = write!(out, "\\u{code:04x}");
            }
            _ => out.push(character),
        }
    }
    out.push('"');
    out
}

#[test]
fn string_literal_expansions_agree_with_pinned_lean() {
    let Some(lean) = lean_probe::lean_bin_or_skip("string-literal", 2) else {
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
    lean_probe::assert_pinned_version("string-literal", &version_text);

    let (mut kernel, env) = lean_shaped_kernel(Mutation::None);
    let mut source = String::from("set_option maxRecDepth 10000\n");
    let mut rendered = 0usize;
    for payload in PAYLOADS {
        let scalars = kernel_scalars(&mut kernel, &env, payload);
        let characters: Vec<String> = scalars
            .iter()
            .map(|scalar| format!("Char.ofNat {scalar}"))
            .collect();
        writeln!(
            source,
            "example : {} = String.ofList [{}] := rfl",
            lean_literal(payload),
            characters.join(", ")
        )
        .expect("writing to a String cannot fail");
        rendered += 1;
    }
    assert_eq!(
        rendered,
        PAYLOADS.len(),
        "every payload must reach the generated module"
    );

    let directory = std::env::temp_dir().join(format!(
        "axeyum_string_literal_crosscheck_{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("create cross-check directory");
    let file = directory.join("StringLiteralPositive.lean");
    std::fs::write(&file, &source).expect("write positive Lean control");
    let positive = run_lean(&lean, &file);
    assert!(
        positive.status.success(),
        "official Lean rejected an expansion this kernel computed ({})\nstdout:\n{}\nstderr:\n{}\nsource:\n{source}",
        lean.display(),
        String::from_utf8_lossy(&positive.stdout),
        String::from_utf8_lossy(&positive.stderr),
    );

    // The negative control, in the two ways a conversion goes wrong: UTF-8
    // bytes instead of scalars, and the right scalars in the wrong order.
    // Without it, a module Lean accepted because every `example` was mis-parsed
    // would read as a pass.
    let negative_source = concat!(
        "example : \"\\u00e9\" = String.ofList [Char.ofNat 195, Char.ofNat 169] := rfl\n",
        "example : \"ab\" = String.ofList [Char.ofNat 98, Char.ofNat 97] := rfl\n",
    );
    let negative_file = directory.join("StringLiteralNegative.lean");
    std::fs::write(&negative_file, negative_source).expect("write negative Lean control");
    let negative = run_lean(&lean, &negative_file);
    assert!(
        !negative.status.success(),
        "official Lean accepted a byte-oriented or reordered expansion\nsource:\n{negative_source}"
    );

    let _ = std::fs::remove_dir_all(directory);
    lean_probe::report_checked("string-literal", 2);
}
