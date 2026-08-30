# Notes: 136-congruence-deriver

Detail moved out of [`../status/136-congruence-deriver.md`](../status/136-congruence-deriver.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

New `crates/axeyum-lean-kernel/src/creal/congruence.rs`:
- **Registry** (`registry(p: CRealPrelude) -> Vec<CongrEntry>`): six entries
  (`Neg`/`Abs`/`Add`/`Mul`/`Min`/`Max`), each an operation's own `CReal`
  constant, its congruence lemma's `NameId`, and its `Arity` (`Unary`:
  `lemma(x, y, h)`; `Binary`: `lemma(x, x', y, y', h1, h2)`, verified against
  three independent existing call sites before being encoded —
  `power.rs::declare_pow_congr`, `series.rs::declare_sum_range_congr`,
  `lattice.rs`'s `abs_congr` derivation). `Pow` is handled separately
  (`CongruExpr::Pow`) since `pow_congr`'s signature is congruent only in the
  base with the `Nat` exponent trailing the hypothesis, a shape no other entry
  shares.
- **Term representation** (`CongruExpr`, an enum, not a closure — chosen so
  the deriver can *inspect* a node to pick its lemma without ever running the
  term): `Var` (the point), `Const` (`Equiv`-irrelevant, refl), `Unary`/
  `Binary` (registered ops), `Pow`, and `Opaque` (a raw function term that
  ALWAYS declines — the negative control's building block, independent of
  what the registry happens to contain).
- **`derive`**: structural recursion, `Result<(ExprId, ExprId), CongrError>`
  — never panics, declines with a typed error the moment it reaches an
  unregistered op or an `Opaque` node.
- **One permanent registration**: `CReal.mulPowCongr : ∀ (c : Nat → CReal) (j
  : Nat) (x y : CReal), Equiv x y → Equiv (mul (c j) (pow x j)) (mul (c j)
  (pow y j))` — the power-series term congruence, dispatched last in
  `build_creal_prelude_uncached` (after `polynomial::declare_polynomial`).
  Grepped the whole merged tree for a hand-built equivalent before writing
  this (co-occurring `mul_congr`/`pow_congr` in a congruence proof across
  every `creal/*.rs`); none exists, so this is a new name, not a verified
  match — documented in the declaring function's own doc comment.

Four demos, all `#[cfg(test)]` in `congruence.rs`, each kernel-checked via
`Kernel::add_declaration`:
- (a) re-derives `CReal.abs_congr` under a throwaway name; asserts
  `kernel.render_lean` renders identically to the hand-built theorem's type.
- (b) exercised through the SAME production dispatch path
  (`declare_congruence_extras`) `build_creal_prelude` itself runs — checks
  `CReal.mulPowCongr`'s rendered type mentions `CReal.mul`/`CReal.pow`/
  `CReal.Equiv`.
- (c) the deepest demo, `abs(min(add x (ofRat 0), mul x x))` — five
  registered-op nodes deep, its own cost measured and reported: **7.62 ms**
  derive+check.
- (d) the negative control: a term built from a raw non-congruent function
  `fvar` (`Opaque`) — asserted to return `Err(CongrError::Unregistered)`,
  never reaching `Kernel::add_declaration`.
- Mutation test: `registry_without(p, Op::Add)` — an `Add`-using term declines
  through the SAME `Unregistered` path (name-checked), while a `Neg`-using
  term still derives against the SAME pruned registry in the same run.

Inventory shard: new `creal/inventory/congruence.rs` (one entry,
`CReal.mulPowCongr`, `"theorem"`). Registrations: `mod congruence;` in
`creal.rs` (alphabetical, between `completeness`/`convergence`) plus its
dispatch call at the tail of the phase chain; `mod congruence;` +
`all.extend(congruence::entries(p))` in `creal/inventory.rs`. Added exactly
one field to `CRealPrelude` (`mul_pow_congr: NameId`) and its intern line —
required because the inventory shard's `entries(p: CRealPrelude)` signature
has no `Kernel` access, so a permanent, coverage-checked name has to be a
struct field, not a dynamically-recomputed `kernel.name_str` call. No other
`creal/*.rs` module file touched.

**Verified:**
- `cargo check -p axeyum-lean-kernel --lib`: clean (after fixing 3 initial
  `E0499` double-mutable-borrow errors from building both `equiv()` arguments
  inline — each fixed by binding `lhs`/`rhs` to locals first).
- `cargo clippy -p axeyum-lean-kernel --lib --tests -- -D warnings`: 23
  pre-existing errors, ALL in `creal/integral.rs`/other files this lane did
  not touch (confirmed: `grep -c congruence` on the clippy output is 0).
  Matches the shape the `shard-inventory` lane (`135-shard-inventory.md`)
  already reported (25 pre-existing errors, same files) — not this lane's to
  fix.
- `env -u RUST_MIN_STACK scripts/cargo-serialized.sh test -p
  axeyum-lean-kernel --lib creal:: -- --nocapture`: **137 passed, 0
  failed**, 316.13s wall (full `creal::` module, second run after fixing
  the bug below; first run was 136 passed / 1 failed). Deepest demo
  (`composite_clamp_like_term_derives_and_checks`, `abs(min(add x (ofRat
  0), mul x x))`) derive+check cost: **7.62 ms**.
- `scripts/check-deep-stack-call-sites.py`: OK, 225 files, 0 unprotected
  sites.
- `rustfmt --edition 2024` on every touched/new file: clean (one reformat
  pass on `congruence.rs` itself, no content change).

**Kernel rejections during development**: two distinct problems, both
found by actually running the gate rather than by inspection.
1. Three `E0499` borrow-checker errors (compile-time, not kernel rejections)
   from calling `equiv(d, p, d.const_app(...), d.const_app(...))` inline —
   Rust's evaluation order requires both mutable borrows of `d` live
   simultaneously. Fixed by binding each side to a `let` first.
2. One REAL `Kernel::add_declaration` rejection,
   `Kernel(UnboundFVar { id: 1001 })`, caught by the first full
   `cargo test -p axeyum-lean-kernel --lib creal::` run (136 passed / 1
   failed) — demo (c)'s `Const` leaf was a fresh `IntDev` fvar (`q`) that
   `declare_derived_congr` never quantified (it only binds `x`/`y`/`h`), so
   the closed term still mentioned an unbound variable. Not a deriver design
   flaw: `CongruExpr::Const` is documented as requiring a term that does not
   mention `Var`, but nothing enforces "closed" vs. "merely `Var`-free", and
   a test built one that was `Var`-free but NOT closed. Fixed by using
   `ofRat (Rat.zero)` instead of a free variable; confirmed by a second full
   run, 137 passed / 0 failed. Every congruence LEMMA's own argument order,
   separately, was read from an existing call site before use (see
   `Arity::Binary`'s doc comment for the three sites checked) and never
   needed correction — the retrospective this task's brief warns about
   ("assuming a mirror exists") did not recur for the lemma-application
   side, only for this one test-construction mistake.

**Candidates for retirement** (not retired by this lane — report only, per
scope): none of the CURRENT hand-built congruences in the merged tree are
pure compositions this deriver could replace outright — `neg_congr`,
`add_congr`, `mul_congr`, `min_congr`/`max_congr`/`abs_congr`, `pow_congr`,
`sum_range_congr` are all BASE cases the registry itself depends on (deriving
them via the deriver would be circular). The deriver's value is for
COMPOSITE congruences built ON TOP of these — `CReal.mulPowCongr` is the
first such composite, and any future power-series/clamp-style congruence
should go through `derive`/`declare_derived_congr` rather than being
hand-assembled.
