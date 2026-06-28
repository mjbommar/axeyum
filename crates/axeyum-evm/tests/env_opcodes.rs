//! A2.1 — environment opcodes (`GAS`, `BALANCE`, block/context, …) modeled as
//! witnessed symbolic inputs. Before A2.1 these were `Op::Unsupported` and any
//! path through them terminated as `Unknown`; now a contract that branches on
//! environment nondeterminism is explored, and a bug after it is reported with a
//! replay-validated witness (the concrete oracle replays the env values).

use axeyum_evm::{AnalyzeConfig, FindingKind, Verdict, analyze};

const STOP: u8 = 0x00;
const ISZERO: u8 = 0x15;
const POP: u8 = 0x50;
const JUMPI: u8 = 0x57;
const JUMPDEST: u8 = 0x5b;
const PUSH1: u8 = 0x60;
const REVERT: u8 = 0xfd;
const GAS: u8 = 0x5a;

#[test]
fn gas_branch_revert_is_found_and_validated() {
    // if (gas() == 0) revert;  — reachable since `gas()` is nondeterministic.
    #[rustfmt::skip]
    let bytecode = [
        GAS, ISZERO, PUSH1, 0x07, JUMPI, STOP, STOP, // 0..6 (dest = 7)
        JUMPDEST, PUSH1, 0x00, PUSH1, 0x00, REVERT,  // 7..12
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "the gas()==0 branch is reachable and must be found (was Unknown before A2.1)"
    );
    let f = &report.findings[0];
    assert_eq!(f.kind, FindingKind::Revert);
    assert!(
        !f.env_inputs.is_empty(),
        "the witness must pin the env (gas) value it branched on"
    );
}

#[test]
fn contract_using_gas_is_no_longer_unknown_when_safe() {
    // `gas(); pop; stop` — uses an env opcode but has no bug. Before A2.1 the env
    // opcode forced Unknown; now it is provably safe.
    let bytecode = [GAS, POP, STOP];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(!report.has_findings());
    assert!(
        matches!(report.verdict, Some(Verdict::SafeUpToBound { .. })),
        "a safe contract that merely reads gas() must now prove safe, got {:?}",
        report.verdict
    );
}

const CALL: u8 = 0xf1;

#[test]
fn revert_on_failed_call_is_found_and_validated() {
    // success = call(...); if (!success) revert;  with retLen=0 (return data not
    // needed). The call may fail (success is nondeterministic), so the revert is
    // reachable and reported with a witness pinning success = 0.
    #[rustfmt::skip]
    let bytecode = [
        // push 7 zero args (gas, addr, value, argsOff, argsLen, retOff, retLen=0)
        PUSH1, 0x00, PUSH1, 0x00, PUSH1, 0x00, PUSH1, 0x00,
        PUSH1, 0x00, PUSH1, 0x00, PUSH1, 0x00,            // 0..13
        CALL, ISZERO, PUSH1, 0x15, JUMPI, STOP, STOP,     // 14..20 (dest = 21)
        JUMPDEST, PUSH1, 0x00, PUSH1, 0x00, REVERT,       // 21..26
    ];
    let report = analyze(&bytecode, &AnalyzeConfig::default());
    assert!(
        report.has_findings(),
        "the failed-call revert is reachable (was Unknown before A2.2)"
    );
    assert_eq!(report.findings[0].kind, FindingKind::Revert);
}
