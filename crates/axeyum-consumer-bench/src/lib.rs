//! # axeyum-consumer-bench — the consumer-track measurement/QA backbone (App D)
//!
//! This crate is the **honesty gate** for the consumer track: it measures the
//! [`axeyum_property`] SDK (App B) against a **construction-known** bounded-property
//! corpus and emits a committed, regenerable scoreboard with a hard
//! **`DISAGREE = 0`** soundness floor.
//!
//! ## Why construction-known (no external oracle needed)
//!
//! Every corpus property is tagged with its **true** status by *construction*
//! ([`Status::ShouldProve`] or [`Status::ShouldFindCounterexample`]) — we author
//! the property so we already know the answer (an `abs ≥ 0` is provable; an
//! unguarded 8-bit `a + b ≥ a` has the wrap counterexample `a=1, b=255`). So the
//! ground truth does not depend on z3/hevm/halmos/Kani being installed. The
//! `:status`-trick from `crates/axeyum-bench/examples/measure_graduated.rs`,
//! carried into pure Rust.
//!
//! A verdict that *contradicts* the construction-known status (axeyum says
//! `Proved` for a `ShouldFindCounterexample`, or vice-versa) is a hard soundness
//! failure and is counted in [`Aggregate::disagree`]; [`Outcome::Unknown`] is
//! always allowed and never a contradiction.
//!
//! ## The differentiator: Lean-certificate coverage
//!
//! For every `Proved` result we additionally record whether
//! [`axeyum_property::Certificate::verify`] independently re-checks the evidence,
//! and whether [`axeyum_property::Certificate::to_lean_module`] yielded a
//! standalone Lean module. The fraction of `Proved` results carrying a *verified*
//! Lean module is the headline number no fast-but-unproven competitor surfaces.
//!
//! ## Parameterized vs-SOTA shape (honestly install-gated)
//!
//! [`ExternalOracle`] models the `run_z3`-style "shell an external binary and read
//! its verdict" pattern from `measure_corpus.rs`, so a future "vs hevm / halmos /
//! Kani" run drops in cleanly. Those tools are **not installed** (the network is
//! offline), so no external scoreboard is faked here — see
//! `docs/consumer-track/measurement/STATUS.md`. The self-contained property
//! scoreboard + each app's own soundness oracle are what ship now.
#![forbid(unsafe_code)]

pub mod corpus;
pub mod harness;
pub mod oracle;
pub mod report;

pub use corpus::{Case, Status, corpus};
pub use harness::{Aggregate, CaseResult, Verdict, run_corpus};
pub use oracle::ExternalOracle;
pub use report::render_scoreboard;
