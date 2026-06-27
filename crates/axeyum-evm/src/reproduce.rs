//! Render a [`Finding`] into a runnable `#[test]` that
//! reproduces the bug from its calldata witness — reusing App B's shared
//! [`render_reproduction_test`] so a found bug becomes a committed regression
//! test rather than a transient log line.
//!
//! The emitted test re-runs the contract through the **concrete oracle**
//! ([`crate::concrete::run`] / [`crate::concrete::overflow_reproduces`]) on the
//! witness bytes and asserts the bug fires — i.e. it is exactly the DISAGREE = 0
//! re-check, frozen as source. The caller supplies the contract bytes (so the
//! generated test is self-contained) and writes the source into a test file.
//!
//! ```rust
//! use axeyum_evm::{analyze, AnalyzeConfig};
//! use axeyum_evm::reproduce::reproduction_source;
//!
//! // x + y with no overflow guard (see the crate tests).
//! let bytecode = [
//!     0x60, 0x00, 0x35, 0x60, 0x20, 0x35, 0x01,
//!     0x60, 0x00, 0x52, 0x60, 0x20, 0x60, 0x00, 0xf3,
//! ];
//! let report = analyze(&bytecode, &AnalyzeConfig::default());
//! let finding = &report.findings[0];
//! let src = reproduction_source("add_overflow_repro", &bytecode, finding);
//! assert!(src.contains("#[test]"));
//! assert!(src.contains("fn add_overflow_repro()"));
//! ```

use axeyum_property::{Reproduction, WitnessBinding, render_reproduction_test};

use crate::{Finding, FindingKind};

impl axeyum_property::Witness for Finding {
    fn bindings(&self) -> Vec<WitnessBinding> {
        vec![
            WitnessBinding::new(
                "calldata",
                "Vec<u8>",
                byte_vec_literal(&self.calldata_witness),
            ),
            WitnessBinding::new("callvalue", "[u8; 32]", byte_array_literal(&self.callvalue)),
            WitnessBinding::new("caller", "[u8; 32]", byte_array_literal(&self.caller)),
            WitnessBinding::new("pc", "usize", format!("{}", self.pc)),
        ]
    }
}

/// Renders a self-contained reproduction `#[test]` (as Rust source text) for
/// `finding` on `bytecode`. The body re-runs the concrete oracle on the witness
/// and asserts the same bug the solver found actually fires.
#[must_use]
pub fn reproduction_source(test_name: &str, bytecode: &[u8], finding: &Finding) -> String {
    use axeyum_property::Witness as _;

    let mut bindings = finding.bindings();
    bindings.insert(
        0,
        WitnessBinding::new("bytecode", "Vec<u8>", byte_vec_literal(bytecode)),
    );

    let body = match finding.kind {
        FindingKind::Revert => REVERT_BODY,
        FindingKind::Invalid => INVALID_BODY,
        FindingKind::AddOverflow => ADD_OVERFLOW_BODY,
        FindingKind::MulOverflow => MUL_OVERFLOW_BODY,
    };

    // Slow 256-bit MUL bit-blast reproductions stay #[ignore]d (perf is upstream).
    let ignore = matches!(finding.kind, FindingKind::MulOverflow);

    render_reproduction_test(
        &Reproduction::new(test_name, bindings)
            .body(body)
            .ignore(ignore),
    )
}

const REVERT_BODY: &str = concat!(
    "let program = axeyum_evm::opcode::decode(&bytecode);\n",
    "let env = axeyum_evm::concrete::Env {\n",
    "    calldata: calldata.clone(),\n",
    "    callvalue: axeyum_evm::word::Word::from_be_bytes(&callvalue),\n",
    "    caller: axeyum_evm::word::Word::from_be_bytes(&caller),\n",
    "};\n",
    "let _ = pc;\n",
    "let halt = axeyum_evm::concrete::run(&program, &env, 10_000);\n",
    "assert!(matches!(halt, axeyum_evm::concrete::Halt::Revert(_)), \"witness must REVERT: {halt:?}\");"
);

const INVALID_BODY: &str = concat!(
    "let program = axeyum_evm::opcode::decode(&bytecode);\n",
    "let env = axeyum_evm::concrete::Env {\n",
    "    calldata: calldata.clone(),\n",
    "    callvalue: axeyum_evm::word::Word::from_be_bytes(&callvalue),\n",
    "    caller: axeyum_evm::word::Word::from_be_bytes(&caller),\n",
    "};\n",
    "let _ = pc;\n",
    "let halt = axeyum_evm::concrete::run(&program, &env, 10_000);\n",
    "assert!(matches!(halt, axeyum_evm::concrete::Halt::Invalid), \"witness must hit INVALID: {halt:?}\");"
);

const ADD_OVERFLOW_BODY: &str = concat!(
    "let program = axeyum_evm::opcode::decode(&bytecode);\n",
    "let env = axeyum_evm::concrete::Env {\n",
    "    calldata: calldata.clone(),\n",
    "    callvalue: axeyum_evm::word::Word::from_be_bytes(&callvalue),\n",
    "    caller: axeyum_evm::word::Word::from_be_bytes(&caller),\n",
    "};\n",
    "assert!(axeyum_evm::concrete::overflow_reproduces(&program, &env, pc, false, 10_000), \"witness must overflow the ADD at pc\");"
);

const MUL_OVERFLOW_BODY: &str = concat!(
    "let program = axeyum_evm::opcode::decode(&bytecode);\n",
    "let env = axeyum_evm::concrete::Env {\n",
    "    calldata: calldata.clone(),\n",
    "    callvalue: axeyum_evm::word::Word::from_be_bytes(&callvalue),\n",
    "    caller: axeyum_evm::word::Word::from_be_bytes(&caller),\n",
    "};\n",
    "assert!(axeyum_evm::concrete::overflow_reproduces(&program, &env, pc, true, 10_000), \"witness must overflow the MUL at pc\");"
);

/// A deterministic `vec![0x.., ..]` literal.
fn byte_vec_literal(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut s = String::from("vec![");
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        let _ = write!(s, "0x{b:02x}");
    }
    s.push(']');
    s
}

/// A deterministic `[0x.., ..; 32]`-style array literal (32 elements).
fn byte_array_literal(bytes: &[u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::from("[");
    for (i, b) in bytes.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        let _ = write!(s, "0x{b:02x}");
    }
    s.push(']');
    s
}
