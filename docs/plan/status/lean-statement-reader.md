# Lane: lean-statement-reader — a native reader for the kernel-core statement fragment

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, lean-statement-reader, 2026-09-05).**
[Next Ten item 9](../../math-department/14-lean-lang.md#the-next-ten-in-priority-order),
FIRST HALF ONLY (the census in ADR-1662 found the Mathlib-surface half gated
at 5 elaboration-blocked rows, so its demand gate is not met — not built,
per the brief).

`Kernel::read_lean` (`crates/axeyum-lean-kernel/src/lean_read.rs`) parses the
`Kernel::render_lean` fragment back into a kernel `ExprId`: binders,
Pi-as-arrow, flat application spines, `Sort`, dotted constant names with
`.{levels}`, `let`, projections, Nat/Str literals. It is untrusted (calls
only public term constructors, never an admission gate) and lives outside
`scripts/check-kernel-trusted-core.py`'s trusted set — measured unchanged at
5,545 of the 5,900-line ceiling, same 9 files, guard D's pinned
`TRUSTED_FILES` set untouched.

15 unit tests in `lean_read.rs` cover the grammar directly (round trips,
shadowing, a doubly atom-wrapped Pi, projection, literals, max/imax levels)
plus negative controls (renamed constant, dropped universe, garbage input,
trailing input, unknown-constant vs unbound-variable classification, and a
regression test for the cross-fact contamination bug below).

**A real bug the ledger-wide gate found, not invented in the abstract.** The
first design resolved a constant by name-TABLE membership alone
(`lookup_name_str`), reasoning that a name reachable there must already be
declared. True for one statement; false once one kernel reads 2,020 in
sequence for efficiency, because interning is a table SHARED across every
`read_lean` call: an earlier fact's ordinary local binder (e.g. some
statement's own `n`) mints `NameNode::Str(anon, "n")`, and a LATER,
unrelated fact's bare `n` was silently accepted as if it denoted that same
constant. Concretely this misdirected `F:nat-le-refl`'s read into a
confusing `expected ')', found ':'` deep in the fallback parse, instead of a
precisely located `unbound-variable`. Fixed with one
`environment().contains(name)` check after the full segment walk, before
building the `Const` node.

`crates/axeyum-lean-kernel/tests/lean_read_round_trip.rs` is the ledger-wide
gate (outcome B): every `formal.language == "lean4"` fact, derived from
`artifacts/facts/*.json` at test time, read against ONE kernel carrying every
prelude this crate builds (mirrors `real_lean_replay_census_all.rs`'s
`everything` carrier), scored for byte-exact round trip and, where
`kernel_theorem` names a resolvable declaration, `def_eq` against its
declared type. Three more negative controls run against real ledger facts
(swapped argument order, renamed constant, dropped universe argument), all
passing.

**Final measured totals** (post-fix, `missing == 0` asserted): of **2,020**
`lean4` facts, **1,964 read**, **1,958 round-trip byte-exact**, **1,920 of
1,922** resolvable `kernel_theorem`s `def_eq` their declared type. Every
failure is classified (roundtrip-mismatch 6, def-eq-mismatch 2,
trailing-input 19, unexpected-token 19, unbound-variable 16,
unknown-constant 2) and traced to a specific cause in ADR-1680's
per-fragment table — almost all ledger-content findings (hand-authored
prose mislabeled `lean4`, `imported-kernel-lean` facts in Mathlib's own
vocabulary, two stale statements, six stale `Nat` renderings), plus one
honest reader limitation (non-ASCII/Greek identifiers, 3 facts) and one
test-construction coverage gap (`Geo` prelude not in the union kernel, 1
fact).

**Registration (outcome D) needed no edits.** Both places the brief named are
auto-discovered, not literal lists:
`scripts/check-kernel-suites.sh --list` scans `crates/axeyum-lean-kernel/tests/*.rs`
by content (does the suite use `support/lean_probe.rs`?), so the new suite is
automatically classified `push` (no external Lean needed) —
verified: `lean_read_round_trip                                 push`.
`justfile`'s `check` target already runs `test` (`scripts/check-workspace-tests.sh`,
which is `cargo test --workspace` under the hood) and `kernel-suite-partition`
(re-validates the same auto-discovered split); neither needed a new line. No
Python checker was added, so `scripts/check.sh` needed no new step either.

<!-- plan-section: landed-changes -->

| 2026-09-05 | lean-statement-reader | `crates/axeyum-lean-kernel/src/lean_read.rs` added: `Kernel::read_lean`, typed `ReadError` (7 classes), 14 unit tests; wired via `mod lean_read;` + `pub use lean_read::ReadError;` in `lib.rs`. Trusted core unchanged (5,545/5,900 lines, same 9 files, guard D 0 failures). `209bb940f` |
| 2026-09-05 | lean-statement-reader | Ledger-wide round-trip suite `crates/axeyum-lean-kernel/tests/lean_read_round_trip.rs` added and found a real cross-fact contamination bug in constant resolution (see lane-status); fixed with one `environment().contains()` check, 15th unit test added as a regression control. See ADR-1680 for the corrected per-fragment table. |
