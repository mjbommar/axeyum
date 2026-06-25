//! # axeyum-evm — EVM bytecode symbolic bug-hunter
//!
//! Symbolically execute raw EVM runtime bytecode over symbolic calldata to find
//! arithmetic-overflow / assertion-violation (`REVERT`/`INVALID`/`Panic(0x11)`)
//! bugs, emitting a **replayable calldata witness** on a bug and a re-checked
//! (Lean-checkable, when in fragment) **no-bug certificate** when a function is
//! proven safe up to a bound.
//!
//! The decidable EVM core is `QF_BV`/`QF_ABV` — axeyum's strongest fragments:
//! 256-bit words = `BV256`, byte memory + word storage = arrays, keccak / external
//! `CALL` / gas are **havoc'd** to a sound `Unknown` (never wrong-pruned, exactly
//! as halmos/hevm defer). Built on the `SymbolicExecutor` path explorer.
//!
//! **Scaffold:** this is the linking smoke test; the opcode interpreter +
//! `SymbolicExecutor` driver + witness/cert output are built iteratively — see
//! `docs/consumer-track/evm/PLAN.md`.
#![forbid(unsafe_code)]

/// Smoke check: confirms the crate links `axeyum-solver` and the `axeyum-property`
/// certificate plumbing it builds on. Replaced by the real entry point as the
/// interpreter lands.
#[must_use]
pub fn dependencies_linked() -> bool {
    let _config = axeyum_solver::SolverConfig::default();
    let _ctx = axeyum_property::Ctx::new();
    true
}

#[cfg(test)]
mod tests {
    use super::dependencies_linked;

    #[test]
    fn links() {
        assert!(dependencies_linked());
    }
}
