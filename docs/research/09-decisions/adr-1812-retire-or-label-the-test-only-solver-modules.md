# ADR-1812: Retire or label the test-only solver modules

Status: accepted
Date: 2026-09-09
Index-summary: The eleven test-only `axeyum-solver` modules: two wired, one wire-pending, eight labelled, none deleted
Index-status: accepted

## Context

[`docs/solver-inventory-2026-09/11-wiring-and-integration.md`](../../solver-inventory-2026-09/11-wiring-and-integration.md)
measured every `mod X;` in `crates/axeyum-solver/src/lib.rs` against every other
file in the crate and found that eleven modules were referenced only from the
crate's own test suite: `abduct`, `enums`, `faithfulness`, `horn`,
`hypothesis_min`, `imc_lia`, `lex_reconstruct`, `pb`, `pdr_lia`, `records`,
`toy_bv_vm`. Roadmap item 2.7 of
[`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md)
requires each one to be dispatched, moved, or deleted, with an ADR for the
deletions and a re-run of the measurement as the exit criterion.

"Test-only" is a finding, not a verdict. `axeyum-solver` is a library, and some
of its modules are public API entry points whose caller is by construction
outside the crate. The question this ADR closes is which of the eleven is which,
so the next inventory does not re-litigate all eleven from scratch.

## Decision

**Two are wired, one is wire-pending in a file this lane does not own, eight are
labelled in their module docs, and none are deleted.**

| Module | Outcome | Why |
|---|---|---|
| `pdr_lia` | **wired** | Now reached through `horn::dispatch` |
| `imc_lia` | **wired** | Now reached through `horn::dispatch` |
| `lex_reconstruct` | **wire-pending** | Belongs in `smtlib.rs`; edit recorded below |
| `horn` | labelled | A front-end, so no in-crate caller — but its own `Int` decline was what orphaned the two above |
| `abduct` | labelled | User-facing query; no decision needs an abduct |
| `enums` | labelled | Superseded as a decision route, kept as a builder |
| `records` | labelled | Same, and recorded once in `enums` |
| `faithfulness` | labelled | Assurance instrument, not a solve step |
| `hypothesis_min` | labelled | Its caller is a proof-search driver, not `check_auto` |
| `pb` | labelled | Term builders; called by whoever writes the query |
| `toy_bv_vm` | labelled | An exercised reference for the P4.2 frontend contract |

`horn` is worth reading twice: it is labelled, because `solve_horn` is a
front-end whose caller is the library user (SMT-LIB CHC input would give it an
in-crate caller and is not parsed). But a module with no caller of its own was
the thing keeping two *other* modules unreachable, which is the finding of this
whole item — "test-only" says nothing about how much sits behind a module.

Every labelled module carries the marker string `No in-crate caller` in a module
doc section giving the reason. `crates/axeyum-solver/tests/test_only_module_labels.rs`
enforces both directions of that: a labelled module that acquires a caller fails,
and an inventory module that loses its disposition fails.

### The wiring: `horn` → `pdr_lia` / `imc_lia`

`horn.rs`'s `state_class` classified an all-`Int` predicate vocabulary as
`StateClass::Unsupported`, and `dispatch` / `dispatch_self` declined it with
"only Real, BitVec, and Bool are dispatched; Int/Array/etc. decline". That single
decline is why `pdr_lia.rs` and `imc_lia.rs` — 1,771 lines of native-ℤ IC3/PDR
and interpolation-based model checking — had no production caller: their only
references anywhere in the tree were four `pub use` lines in `lib.rs`.

`StateClass::Int` now routes to `prove_safety_pdr_lia` with a
`prove_safety_imc_lia` fallback, mirroring the `Real` branch exactly, in both
dispatch functions; `tag_sort_for` / `tag_constant` gained the matching `Int` tag
column so a mutually-recursive `Int` SCC merges the way the `Real` one does.

This is the SMT-LIB CHC workhorse shape. `(declare-fun inv (Int Int) Bool)` is
what Z3's Spacer is usually pointed at, and until now this crate declined all of
it while holding two engines built for it.

Soundness does not rest on the new branch. `solve_horn` re-checks the candidate
interpretation against every original clause with `check_auto` before returning
`Sat` (`verify_horn_solution`), and each engine's `Reachable` is already a
replay-checked counterexample confirmed by a `check_auto`-`Sat` of the concrete
unrolling. A wrong `Int` invariant can only become `Unknown`. Note also that
routing `Int` to the *`LRA`* engines would have been sound for the same reason
and useless for the same reason — a real relaxation's invariant would be
rejected by the ℤ re-check — which is why the native engines are the right
target.

### The wire-pending: `lex_reconstruct`

The lex *verdict* is wired: `smtlib.rs`'s `apply_lex_order_route` /
`lex_order_verdict` already turn an `axeyum_strings::refute_lex` `Unsat` into a
front-door `unsat`. The lex *evidence* is not: nothing calls
`reconstruct_lex_clash_to_lean_module`, so a lex `unsat` ships without the
kernel-checked Lean `False` that module can produce.

It cannot ride the arena-scanning `prove_unsat_to_lean_module` dispatch in
`reconstruct.rs`, because a `LexProblem` is not represented in the `axeyum-ir`
term arena — it lives in the parser's side channel, exactly like the regex
`MembershipProblem`. The precedent is `smtlib.rs`'s
`membership_unsat_lean_module`, which threads
`reconstruct_regex_emptiness_to_lean_module` at the point where the deciding
object is in hand. The lex mirror belongs beside it:

```rust
/// The lex mirror of [`membership_unsat_lean_module`]: when the
/// lexicographic-order route decides `unsat`, reconstruct that same refutation
/// to a kernel-checked Lean module. Never changes the verdict.
#[must_use]
pub fn lex_unsat_lean_module(script: &Script, _config: &SolverConfig) -> Option<String> {
    let problem = script.lex_problem.as_ref()?;
    crate::reconstruct_lex_clash_to_lean_module(problem).ok()
}
```

`smtlib.rs` is owned by another lane this round, so the edit is recorded here
rather than made. `reconstruct_lex_clash_to_lean_module` re-runs `refute_lex`
itself as its sole `unsat` gate and kernel-checks the assembled `False` before
returning, so the wrapper cannot fabricate evidence: it declines to `None`.

### Why nothing is deleted

The deletion test applied to each module was: *would removing it lose a
capability nothing else has?*

For nine of the eleven the answer is plainly yes — the CHC front-end has no
second implementation, abduction has no second
implementation, `hypothesis_min` is the only minimiser that can start when the
full set is `unknown` (`auto::unsat_core` returns `None` unless the whole set is
already solver-`unsat`, which is the exact phenomenon it exists for), `pb`
generalizes the cardinality family, `toy_bv_vm` is the frontend contract in
executable form, and the model-checking engines are now on a dispatch path.

`enums` and `records` are the genuine deletion candidates and were kept
deliberately. They are **superseded as a decision route**: `axeyum-ir` now has a
first-class datatype sort (`Sort::Datatype`, `declare_datatype` /
`add_constructor` / `dt_select` / `dt_test`, recursion included), `axeyum-smtlib`
parses `declare-datatype`/`declare-datatypes`, and `datatype_native.rs` decides
such queries by eager tag/field expansion — which is the generalization of the
same tag-bit-vector idea `enums.rs` implements. Their own module docs said this
increment "would need a first-class datatype sort in the IR"; it landed, and it
bypassed them rather than replacing them.

What survives is a *builder* role: a finite enumeration or fixed-width product
lowered to pure bit-vectors with no datatype declaration and no expansion pass.
That is sound, tested, cheap, and public API. Deleting working public API on a
supersession argument is a one-way door, so the argument is recorded instead of
acted on, with the condition made explicit: **delete `enums.rs`, `records.rs`,
`tests/enums.rs`, `tests/records.rs`, the four `lib.rs` re-exports and their
`tests/api_namespaces.rs` rows the moment the builder role is shown to have no
user.** Do not re-derive the supersession; it is recorded in `enums.rs`.

## Evidence

The inventory's method was re-implemented rather than trusted, and it needed two
corrections — each of which changed an answer for a module in this set:

1. **Comments and string literals are not code.** `capabilities.rs` and
   `config_registry.rs` describe most of this crate in prose tables. A plain name
   search over the source counts those as callers, and `pdr_lia`, `imc_lia`,
   `horn` and `hypothesis_min` all looked referenced for exactly that reason.
   String literals must be stripped over the *whole* text, not line by line — a
   Rust literal continues across lines with `\`, and a line-wise strip leaves the
   continuation lines looking like code. That bug was live in the first run of
   this lane's own script and reported four modules as wired that are not.
2. **A bare identifier is not an import.** `quant_bool_model_sat.rs` defines its
   own `const MAX_CANDIDATES`, which is also `abduct`'s re-exported name. A name
   search calls that a caller. A re-exported name counts only when the file
   imported it or wrote `crate::NAME`.

With both corrections, at base commit `6dd85fc78` the measurement reports **20**
modules with no in-crate caller (19 reachable from tests or another crate, plus
`hypothesis_min`, which has no reference anywhere at all — even its tests are
inline). That is the inventory's 15 plus `abduct`, `cardinality`, `distinct`,
`enums` and `pb`, which the looser method had credited to comment or collision
matches. All eleven modules of the inventory's finding are confirmed test-only at
base. The extras are outside item 2.7's scope and are recorded here so the next
inventory starts from the corrected number rather than 15.

After this ADR the same measurement reports **18**: `pdr_lia` and `imc_lia` are
gone from the list, which is the whole observable effect of the wiring. The other
nine of the eleven are still there and each now carries its recorded reason —
which is the second clause of item 2.7's exit criterion, and the honest one.

The `Int` dispatch is verified by `crates/axeyum-solver/tests/horn_lia.rs`, which
asserts a **definite** `Sat` (re-checked test-side against every clause,
independently of the solver's own gate) and a **definite** `Unsat`, never
accepting `Unknown`. Its negative control is real: restoring the `Unsupported`
classification for all-`Int` makes exactly those two tests fail with
`got Unknown { reason: "Horn predicate argument sorts are outside this slice's
reach…" }`, while the mixed-`Int`/`Real` decline test still passes.

## Alternatives

**Delete the eight instead of labelling.** Rejected: eight of them are sound,
tested public API or exercised references, and "no in-crate caller" is the normal
condition for a library's entry points. Deleting on that signal alone would
remove capability to improve a metric.

**Label all eleven and wire none.** Rejected on the `horn`/`Int` finding. The
inventory called `pdr_lia`/`imc_lia` test-only; the *cause* was a four-line
classification in a third module, and finding it turned a labelling exercise into
1,771 lines of newly reachable capability. A label there would have recorded a
decline as a design.

**Route `Int` Horn systems to the `LRA` engines** (a real relaxation) rather than
adding an engine family. Rejected: the ℤ re-check in `verify_horn_solution` would
reject a relaxed invariant, so the work would be spent to reach the same
`Unknown`.

**Wire `lex_reconstruct` through `reconstruct.rs`'s `ProofFragment` dispatch.**
Not possible: that dispatch scans a `TermArena`, and a `LexProblem` is not in the
arena. The regex reconstruction already established the side-channel pattern.

## Consequences

- CHC over `LIA` — the shape SMT-LIB CHC benchmarks are actually written in — is
  decided rather than declined, and the two `LIA` model-checking engines have a
  production caller for the first time.
- `tests/test_only_module_labels.rs` makes both halves of this ADR falsifiable:
  a stale label and a reverted wiring each turn it red. It is a source-text
  measurement, so it cannot see dispatch through a trait object, a macro, or a
  registry table, and it sees modules rather than functions — the inventory's own
  limits, inherited deliberately.
- The next wiring inventory should start from 18, not 15, and should apply the
  two corrections above before reporting any module dead.
- `lex_reconstruct` stays unwired until a lane that owns `smtlib.rs` applies the
  recorded edit. That is the one piece of item 2.7 this ADR does not finish.
- Roadmap item 3.7 (interpolation strength and shape) named IMC/PDR as "themselves
  unwired" and gated itself on this item. The `LIA` half is now wired, so that
  gate is partly lifted: an interpolation-strength consumer exists.
