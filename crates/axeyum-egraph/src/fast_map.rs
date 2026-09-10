//! Fast, deterministic hash map/set aliases for the e-graph's hot-path tables.
//!
//! Mirrors [`axeyum_ir::fast_map`], which landed the same swap for the term
//! intern table on 2026-09-05. That pass was deliberately scoped to
//! `axeyum-ir`; this crate was in the remainder it named. The reasoning there
//! applies here unchanged, so it is not repeated — what is new is the
//! measurement that made this crate worth doing.
//!
//! ## The measurement
//!
//! `std::collections::HashMap`'s default hasher is SipHash-1-3, a
//! *cryptographic* keyed hash with a per-process random seed. This crate keys
//! its hottest maps on [`crate::ENodeId`], which is a `u32` newtype allocated
//! densely as `ENodeId(self.nodes.len())`.
//!
//! Profiled 2026-09-10 with `perf` on
//! `QF_UF/QG-classification/qg7/iso_icl_repgen004.smt2` — an order-7
//! quasigroup that z3 refutes in 0.1 s and the online CDCL(T) EUF route took
//! 70 s — sampling a 60 s run:
//!
//! | symbol | self time |
//! |---|---:|
//! | `hash_one::<&ENodeId>` | **18.5%** |
//! | `DefaultHasher::write` | 7.0% |
//! | `HashMap<ENodeId, _>::insert` + `reserve_rehash` | 8.9% |
//! | `malloc`/`free` | 16.0% |
//!
//! So roughly a third of the solve was spent running a cryptographic hash over
//! a `u32` in the congruence-closure inner loop.
//!
//! ## Iteration-order audit (2026-09-10)
//!
//! Required before any hasher swap, because a deterministic hasher does not by
//! itself make iteration order safe — it only removes the RNG seed.
//!
//! Every `HashMap`/`HashSet` type position in `crates/axeyum-egraph/src/` was
//! enumerated (10 occurrences) and every `.iter()`, `.keys()`, `.values()`,
//! `.into_iter()` and `.drain()` in the crate was attributed to its receiver
//! (15 calls). **None is on a hash map or set** — every one is on a `Vec`
//! (`node.args`, `self.nodes`, `scopes`, `apps`, …). The signature table is
//! reached only through `get`, `insert` and `remove`.
//!
//! The audit's own coverage was checked rather than assumed: the receiver grep
//! returns 15 matches on this file, so an empty result for the map names is a
//! real negative and not a broken pattern.
//!
//! So this swap is invisible to behaviour, and the verdict-invariance check in
//! the accompanying measurement note confirms that empirically rather than
//! resting on the audit alone.

/// A [`std::collections::HashMap`] using `rustc-hash`'s `FxHasher`.
pub(crate) type FastMap<K, V> = std::collections::HashMap<K, V, rustc_hash::FxBuildHasher>;

/// A [`std::collections::HashSet`] using `rustc-hash`'s `FxHasher`.
#[allow(dead_code)]
pub(crate) type FastSet<T> = std::collections::HashSet<T, rustc_hash::FxBuildHasher>;
