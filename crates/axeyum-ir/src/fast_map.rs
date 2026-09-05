//! Fast, deterministic hash map/set aliases for `axeyum-ir`'s internal
//! lookup tables and the term intern table.
//!
//! ## Why not `std::collections::HashMap`
//!
//! `std::collections::HashMap`'s default hasher is `SipHash-1-3` with a
//! per-process random seed. Two consequences, both bad here:
//!
//! - **Slow.** `SipHash` is a *cryptographic* keyed hash (built to resist an
//!   attacker who chooses keys to force collisions); every insert/lookup
//!   pays that cost even though nothing in this crate's maps is fed
//!   attacker-chosen keys across a trust boundary that matters for hashing
//!   (an adversarial SMT-LIB file can pick term shapes, but the interner's
//!   correctness does not depend on the hash function resisting that — only
//!   the arena's `PartialEq`/`Hash` agreement does, which any hasher
//!   preserves).
//! - **Non-deterministic across runs.** Determinism is a public API promise
//!   of this project (`CLAUDE.md`, "Hard Rules"): dense IDs are assigned in
//!   insertion order, and insertion order for anything read back out of a
//!   `HashMap` (iteration, not point lookup) depends on the per-process
//!   random seed. `intern: HashMap<TermNode, TermId>` never needs to be
//!   *iterated* for correctness (`TermId` assignment happens at insert time,
//!   not by walking the map), but every other map that could ever be
//!   iterated inherits the same risk, and a future refactor that adds an
//!   iteration is one accidental `.values()` away from breaking the promise
//!   silently. A deterministic hasher does not fix that by itself (see the
//!   iteration-order audit in
//!   `docs/research/11-design-review/2026-09-05-intern-table-hasher-measured.md`),
//!   but it removes RNG-seeded hashing from the picture entirely, which is
//!   strictly more auditable than "the order happens to not matter, today".
//!
//! ## Why `rustc-hash` (`FxHash`) and not `ahash`
//!
//! `ahash` is also fast, but its default `RandomState` is randomized per
//! process (seeded from the OS RNG / ASLR, same problem as std) unless the
//! caller constructs it with an explicit fixed seed
//! (`ahash::RandomState::with_seeds`) — which means every call site (or at
//! least every map constructor) has to opt in correctly, and a new call site
//! that uses `AHashMap::default()` silently reintroduces randomization.
//! `rustc-hash`'s `FxHashMap`/`FxHashSet` are deterministic *by construction*:
//! `FxHasher`'s multiplier is a fixed constant (no seed field to get wrong),
//! so there is no "use the right constructor" discipline to maintain. It is
//! also the hasher `rustc` itself uses for compiler-internal maps at exactly
//! this kind of hot path (dense integer/small-struct keys), is pure Rust
//! (MIT/Apache-2.0, no C/C++, satisfies the workspace's no-C-dependency
//! rule), and needs no extra feature work for the `wasm32-unknown-unknown`
//! target this workspace supports (ADR-0017).
//!
//! ## Is `TermNode` `FxHash`-safe?
//!
//! `FxHash` (`hash = (hash.rotate_left(5) ^ word) * K` per machine word) is
//! known to be weak specifically on **low-entropy single-word keys**: hashing
//! a bare `u32`/`u64` directly (e.g. `FxHashMap<u32, V>` keyed on a dense
//! counter) can leave enough structure in the low bits that a `HashMap`'s
//! bucket index (itself usually just the hash's low bits) clusters. That
//! *does* matter here, because `axeyum-ir` is exactly the kind of crate with
//! dense small-integer IDs: `TermId`/`SymbolId`/`FuncId` are `u32` newtypes
//! assigned by successive `+1` in insertion order, and several of this
//! crate's maps (`symbol_lookup`, `function_lookup`, …) are keyed on
//! `String` (fine — `FxHash` mixes over every byte, no single-word
//! degenerate case) while others are keyed on those dense IDs directly
//! (`eval.rs`'s `bindings: HashMap<SymbolId, Value>`,
//! `functions: HashMap<FuncId, FuncValue>`, and the `TermId`-keyed memo
//! tables in `eval.rs`/`fmt.rs`/`stats.rs`).
//!
//! `intern: HashMap<TermNode, TermId>` — the one this module was written
//! for — is **not** a single-word key, though: `TermNode` is a multi-field
//! enum (`BoolConst(bool)`, `BvConst { width: u32, value: u128 }`,
//! `WideBvConst(WideUint)`, `IntConst(i128)`, `RealConst(Rational)`,
//! `Symbol(SymbolId)`, `App { op: Op, args: Box<[TermId]> }`; see
//! `term.rs`). `#[derive(Hash)]` on an enum first mixes in the discriminant,
//! then every field in declaration order, so a `TermNode` hash is always a
//! multi-word `FxHash` fold — the pathological single-word case does not
//! apply to the intern table itself. Two things are still worth flagging
//! rather than asserting away:
//!
//! - `Op` (the `App` variant's operator tag) is itself a many-variant
//!   `#[derive(Hash)]` enum whose discriminant is a small dense integer, and
//!   `args: Box<[TermId]>` is a slice of small dense `u32`s — so a `TermNode`
//!   built for a common shape (e.g. many binary `BoolAnd` applications over
//!   small operand IDs early in a build) folds several low-entropy words
//!   together. Folding does not eliminate clustering risk the way
//!   independent high-entropy words would, but it is materially better than
//!   hashing one such word alone.
//!   `BvConst { width: u32, value: u128 }` and `IntConst(i128)` are the
//!   sharpest single-field case: benchmark corpora lean heavily on `0`, `1`,
//!   small widths (`1`, `8`, `32`, `64`), and small constants, so those
//!   variants' hashes are dominated by a handful of recurring small values —
//!   exactly `FxHash`'s weak spot — mixed with only the variant discriminant
//!   as a second word.
//! - The measurement in
//!   `docs/research/11-design-review/2026-09-05-intern-table-hasher-measured.md`
//!   is the actual check for whether this theoretical risk shows up as wall
//!   time or a load-factor pathology on a real corpus; this doc comment
//!   states the risk, it does not resolve it by argument.
//!
//! `SymbolId`/`FuncId`/`TermId` keys elsewhere in this crate (`bindings`,
//! `functions`, the memo tables) are exactly the single-word degenerate case
//! described above, and were carried over to `FastMap` unchanged rather than
//! given special-cased hashing, because none of them are on the measured hot
//! path here (they are evaluator/formatter/stats memo tables, not the
//! per-term intern lookup) — a target for a later lane if profiling ever
//! shows otherwise, not a fix this pass makes speculatively.
//!
//! ## Why not `indexmap`
//!
//! `indexmap::IndexMap` gives *insertion-ordered* iteration on top of a fast
//! hash map, which would remove the iteration-order determinism risk noted
//! above outright. It is not adopted here because nothing in this crate's
//! maps is iterated in a way that reaches output today (see the audit in
//! the measured note); adding a new dependency and a heavier map structure
//! (`IndexMap` carries a second parallel storage) ahead of a demonstrated
//! need is exactly the kind of thing this pass is scoped to avoid — swap
//! `FastMap`'s definition to `indexmap::IndexMap` later, in this one place,
//! if an iteration order ever needs to become part of the public
//! determinism contract instead of an absence-of-iteration argument.
//!
//! ## Migration note for later lanes
//!
//! Every `std::collections::HashMap`/`HashSet` in this crate's non-test code
//! now goes through `FastMap`/`FastSet`. Swapping the hasher again (or
//! swapping to `indexmap`) means editing this module's two `pub type`
//! lines, not every call site. `axeyum-solver`'s ~470 `HashMap`/`HashSet`
//! uses (D5 in the review above) are explicitly **out of scope** for this
//! pass; see the measured note for the recommendation on whether that sweep
//! is worth a lane.

use rustc_hash::FxBuildHasher;

/// A `std::collections::HashMap` using the deterministic, seedless `FxHash`
/// algorithm (`rustc-hash`) instead of std's randomized `SipHash`. See the
/// module doc comment for why this hasher, and what it does and does not
/// buy for `TermNode` keys specifically.
pub type FastMap<K, V> = std::collections::HashMap<K, V, FxBuildHasher>;

/// A `std::collections::HashSet` using the deterministic, seedless `FxHash`
/// algorithm (`rustc-hash`) instead of std's randomized `SipHash`. See the
/// module doc comment.
pub type FastSet<T> = std::collections::HashSet<T, FxBuildHasher>;
