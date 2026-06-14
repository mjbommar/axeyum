# ADR-0022: First-Class Datatype Sort in the IR

Status: proposed
Date: 2026-06-13

## Context

Datatype support so far is **lowering-based and finite-only**: `EnumSort`
(nullary-constructor sums) and `RecordSort` (fixed-width products) compile to
bit-vectors with no new IR sort (this session, iters H–I). That covers the
common non-recursive case soundly and cheaply, but it cannot express
**recursive or mutually-recursive datatypes** — lists, trees, option/either over
unbounded payloads — because they have no finite bit-width to lower to. Reaching
Z3/cvc5 datatype parity therefore requires a **first-class datatype sort** in the
IR. This ADR decides the representation and solving approach so the
implementation (a cross-crate change) can be done deliberately and soundly in a
focused session, rather than improvised.

This closes the "datatypes" line item in the remaining-parity roadmap
(PLAN.md, 2026-06-13) and the datatype entry in the
[foundational DAG](../08-planning/foundational-dag.md).

## Decision (proposed)

**Add an interned datatype declaration table and a `Sort::Datatype(DatatypeId)`
variant, with constructor/selector/tester operators, and decide it by a native
datatype solver in the lazy-SMT loop (congruence + acyclicity), with eager
bounded unfolding as the first, simpler implementation step.**

Concretely, in dependency order:

1. **IR representation.** `Sort` currently is `Copy` and self-contained; recursive
   datatypes break that (a constructor field can have the datatype's own sort).
   Introduce a `DatatypeId` (`Copy`) interned in the `TermArena` alongside symbols
   and functions; a datatype declaration is `name + Vec<Constructor>`, each
   constructor `name + Vec<(selector name, Sort)>` where a field `Sort` may be the
   datatype itself (recursion) or a mutually-declared sibling. `Sort` gains
   `Datatype(DatatypeId)` and stays `Copy` (the recursion lives behind the id, not
   in the enum). New `Op`s: `Constructor(ConstructorId)`, `Selector(SelectorId)`,
   `Tester(ConstructorId)` (`is-c`).
2. **Evaluator.** A datatype value is `constructor id + field values` (a boxed,
   `Clone` tree, like the existing `Array` value). `select`/`tester` are total on
   well-constructed values; selector-on-wrong-constructor is a chosen-total
   convention (an ADR sub-decision — likely a fixed default per field sort, as the
   BV totality convention does), so the evaluator stays total and replay stays
   sound.
3. **Solving — step A (eager bounded unfolding).** For a query with datatype
   terms, unfold constructors to a bounded depth, Ackermann-ize selectors over
   the finite constructor set, and reduce the constructor *tag* to a small
   bit-vector (the `EnumSort` trick) — giving a sound, complete-up-to-depth
   decision reusing the bit-blasting backend. `unsat` is sound; `sat` is replayed;
   exceeding the depth is `unknown` (never wrong), mirroring bounded LIA.
4. **Solving — step B (native, later).** A datatype theory solver in the DPLL(T)
   loop: congruence closure over constructors/selectors with the
   injectivity/distinctness/exhaustiveness rules and an **acyclicity** check, for
   completeness without a depth bound. Its own ADR when step A's limits bind.

## Evidence

- The finite lowering (`EnumSort`/`RecordSort`, this session) is the proof of
  concept for the *tag-as-bitvector* and *field-as-slice* encodings step A
  reuses, and is the honest demonstration that the finite case needs no sort —
  isolating exactly what the new sort is *for* (recursion).
- The `Array` value already shows the IR/evaluator can carry a non-`Copy`,
  `Clone` structured value behind a `Copy` handle — the pattern a datatype value
  follows.
- cvc5 and Z3 decide datatypes by exactly this combination (congruence +
  acyclicity, with selectors total by convention); their behavior is the
  reference and differential oracle.
- **Measured blast radius (2026-06-13, two passes).** A first `cargo build`-only
  probe (placeholder `Sort::Datatype` + datatype ops) suggested the breakage was
  contained to 4 `axeyum-ir` files. A fuller implementation attempt **corrected
  this**: building the whole workspace *including tests* surfaces exhaustive
  matches that also need datatype arms in **`axeyum-rewrite`** (`canonical.rs`'s
  `build_app` over `Op`, plus `Sort`/`Value` matches), **`axeyum-query`**
  (`planning.rs`, `lib.rs`), and `axeyum-ir`'s own test modules — i.e. the
  `cargo build`-only probe undercounted because it does not compile test code or
  every reduction path. So the change is genuinely **multi-crate** (though most
  added arms are mechanical: reject/skip the datatype sort, or rebuild the new
  ops in `build_app`). The substantive work — confirmed by the attempt — is the
  IR semantic core: `DatatypeId`/`ConstructorId` tables in the arena, the
  two-phase declare for recursion (reserve the id, then add constructors that can
  reference `Sort::Datatype(id)`), the recursive `Value::Datatype` tree, the
  construct/select/test evaluator ops (built in the `Result`-returning recursion
  so a wrong-constructor select can return an `IrError` rather than fabricate a
  value), and a new `IrError::DatatypeConstructorMismatch`. The attempt was
  **reverted to keep the workspace green** rather than land a large partial diff;
  the next session should implement it end-to-end (arena tables + ops + eval +
  all match arms + tests) as one focused unit, then audit downstream wildcard
  arms to confirm they reject datatype sorts soundly before any datatype solving.

## Alternatives

- **Keep lowering everything (no sort).** Rejected: impossible for recursive
  datatypes (no finite width); the whole reason this ADR exists.
- **Make `Sort` non-`Copy` / recursive directly.** Rejected: `Sort` is `Copy`
  across the whole codebase (interning, evaluator, every match); the
  `DatatypeId`-behind-an-id design keeps `Copy` and localizes the change to the
  arena's declaration table.
- **Native theory first (skip eager unfolding).** Deferred: the native solver
  (acyclicity + congruence) is more code and more soundness surface; eager
  bounded unfolding lands a sound, useful slice first and reuses the proven
  bit-blasting + replay path, exactly as bounded LIA preceded the LIA simplex.

## Implementation checklist (from the 2026-06-13 attempt)

An ordered, executable plan distilled from the reverted attempt, so the next
session lands it in one green pass. **Probe caveat:** `cargo build` stops at the
first crate that fails to compile, so adding the IR variants and building made
only `axeyum-ir` errors visible; the downstream sites below appear only once
`axeyum-ir` compiles. Build IR green *first*, then the workspace, then tests.

1. **`term.rs`** — add `DatatypeId(u32)` and `ConstructorId(u32)` (mirror
   `FuncId`, derive `Ord`/`Hash`); add ops `DtConstruct { constructor,
   datatype }`, `DtSelect { constructor, index }`, `DtTest(constructor)` (note:
   `Op::Select` already exists for arrays — use the `Dt` prefix).
2. **`sort.rs`** — `Sort::Datatype(DatatypeId)`; arms in `bv_width`,
   `array_widths`, `Display`.
3. **`value.rs`** — `Value::Datatype { datatype, constructor, fields: Vec<Value> }`;
   arms in `sort`, `as_bool/as_bv/as_array/as_int/as_real`, `scalar_code`,
   `from_scalar_code`, `encode_to`, `Display` (datatype is non-scalar → panic in
   the scalar encode/decode paths, `None` in the `as_*` accessors).
4. **`bits.rs`** — reject `Value::Datatype` / `Sort::Datatype` in
   `value_to_lsb_bits` and `lsb_bits_to_value` (`SortMismatch`).
5. **`error.rs`** — add `IrError::DatatypeConstructorMismatch` + its `Display` arm.
6. **`eval.rs`** — handle the three ops in the *`Result`-returning recursion*
   (not infallible `apply`): `DtConstruct` builds the value; `DtSelect` projects
   field `index` when the constructor matches, else returns
   `DatatypeConstructorMismatch`; `DtTest` compares constructors. Add an
   `unreachable!` arm for the three ops in `apply`.
7. **`arena.rs`** — `datatypes: Vec<DatatypeInfo>` and `constructors:
   Vec<ConstructorInfo>` tables; `declare_datatype(name) -> DatatypeId` then
   `add_constructor(dt, name, fields: &[(String, Sort)]) -> ConstructorId`
   (two-phase, so a field `Sort::Datatype(dt)` can reference its own datatype for
   recursion); accessors; builders `construct`/`select`/`test` (sort-checked,
   passing the result sort to `app`); arms in the `expect_*` helpers and
   `check_scalar_width` (reject the datatype sort).
8. **`axeyum-rewrite/canonical.rs`** — `build_app` must rebuild the three ops
   (call the arena builders); add datatype arms to its `Sort`/`Value` matches.
9. **`axeyum-query`** (`planning.rs`, `lib.rs`) and **IR test modules** — add the
   mechanical reject/skip arms the compiler flags.
10. **Tests** — a recursive datatype (e.g. `IntList = nil | cons(head: BitVec(8),
    tail: IntList)`): construct `cons(5, nil)`, `select head -> 5`, `is-cons ->
    true`, eval round-trip; and a non-recursive `Option`. Defer datatype
    *solving* (downstream wildcards already make it `Unsupported`); audit those
    wildcards reject soundly before wiring any solving.

## Consequences

- **Easier:** lists/trees/option/either become expressible — a large class of
  verification problems; a base for tuples-with-named-fields beyond `RecordSort`.
- **Harder / to watch:** adding a `Sort` variant touches every exhaustive `Sort`
  match across crates (the compiler enforces completeness, so no site is missed,
  but each needs correct handling); the selector-totality convention must be
  fixed once and shared by the evaluator and the lowering or replay breaks; `Op`
  growth (constructor/selector/tester) continues the enum-size pressure noted in
  earlier ADRs.
- **Revisited when:** step A (eager unfolding) is implemented and its depth bound
  is felt — step B (the native acyclicity+congruence datatype theory) gets its
  own ADR then. The selector-totality convention is also recorded as a small
  follow-up decision before step A's evaluator lands.
