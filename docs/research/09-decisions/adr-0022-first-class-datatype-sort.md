# ADR-0022: First-Class Datatype Sort in the IR

Status: accepted (IR foundation implemented 2026-06-13; datatype solving deferred)
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

## Step B gate: the selector-totality convention (found while building step A)

Native solving of *free* datatype variables (eager expansion: a tag variable +
per-constructor field variables, replacing `is_c` with `tag == c` and
`select_{c,i}` with the field variable) needs **model projection** — reconstruct a
`Value::Datatype` from the solved tag + field values, then replay the original
assertions. Replay exposes a concrete blocker:

- The original may contain `select_{c,i}(o)` where the projected model gives `o`
  the constructor `d != c`. The iter-Q evaluator currently **errors** on such a
  wrong-constructor select (`DatatypeConstructorMismatch`), so replay of an
  otherwise-valid `sat` model would fail. (This also means iter-Q quietly
  introduced a *partial* operator, against eval.rs's "all operators are total"
  invariant — worth reconciling regardless.)
- For replay to be sound, `select` must be **total**: wrong-constructor select
  returns a fixed default of the *field's* sort, and the eager reduction must use
  the *same* default. Defaults for `Bool`/`BitVec`/`Int`/`Real`/`Array` are
  trivial, but a field whose sort is a (recursive) datatype needs a default
  datatype value — which requires **well-foundedness analysis**: pick a base
  (least-recursive) constructor and recurse, terminating only for datatypes that
  have a base case. Non-well-founded datatypes (no base constructor) are
  uninhabited and need separate handling.

So step B's first task is fixing the totality convention (total `select` with a
well-founded default, shared by evaluator and reduction), then the
tag/field-variable expansion and model projection. This is the careful design the
ADR flagged; it is recorded here so the implementing session resolves it before
writing the reduction, rather than discovering it mid-change.

**Resolved (2026-06-14): the totality convention is now implemented.**
`axeyum_ir::well_founded_default(arena, sort)` computes the chosen default for any
sort — `false`/`0`/empty-array for the scalar sorts, and for a datatype a
*well-founded* base value found by a cycle-guarded search over constructors (it
returns `None` only for an uninhabited datatype, where no finite value exists).
The evaluator's `select`-over-wrong-constructor now returns this default instead
of erroring, so `select` is total (restoring eval.rs's "all operators are total"
invariant that iter-Q had broken) and a projected `Value::Datatype` model replays
soundly. The same function is the shared default the step-B reduction must reuse.
Tests: `well_founded_default_picks_a_base_constructor` (recursive-first list →
`nil`), `well_founded_default_none_for_uninhabited_datatype` (`Stream` with no
base → `None`), and `selector_on_wrong_constructor_returns_field_default`. The
`z3` adapter gained explicit datatype-reject arms (sort lift, symbol translation,
op translation) so the new variants stay sound under `--all-features`.

What remains for step B is now purely the **tag + per-constructor field-variable
expansion and the model projection back through `well_founded_default`** — the
totality gate is closed.

**Implemented (2026-06-14): native free-variable solving, first slice.**
`axeyum_solver::check_with_datatype_native` decides queries with free datatype
variables over the **non-recursive, scalar-field** fragment by eager tag/field
expansion: each variable `o : D` becomes a tag bit-vector (domain-constrained to
the constructor range) plus a field variable per constructor/field; `is-c(o)`
rewrites to `tag_o == c` and `select_{c,i}(o)` to the field variable, with a guard
`tag_o == c \/ field == default` pinning every non-active field to its
`well_founded_default` so `select` agrees with the evaluator. The expansion is
equisatisfiable (so `unsat`/`unknown` transfer), and a `sat` model is projected
back to a `Value::Datatype` and **replayed against the (simplified) assertions**
with the ground evaluator before being returned, so a projection bug is a replay
error, never a wrong `sat`. The dispatcher (`check_with_datatype_elimination`,
reached from `solve`/`check_auto`) now routes the read-over-construct residual
here instead of returning `Unsupported`. The bit-vector backends' `complete_model`
was generalized to fill any leftover symbol via `well_founded_default` (so a
datatype variable that survives into the arena but not the reduced query no longer
panics). Tests: `tests/datatype_native.rs` (enum sat with projected constructor,
`some(7)` via select, contradictory testers unsat, wrong-ctor select == default
sat / != default unsat, dispatcher routing) and an updated `tests/datatype_elim.rs`
(free variable now sat; recursive variable still `Unsupported`).

**Datatype equality (2026-06-14):** `o == o'` over two variables of the same
non-recursive scalar-field datatype is now decided too — it reduces to
`tag_o == tag_o'` conjoined with field-wise equality, which is exact structural
equality because the field-default guards pin non-active fields to the same
default on both sides. Tests: conflicting testers under equality (unsat),
equality forcing `7 == 8` (unsat), and matching values (sat, both variables
projected to the same value).

**Recursive datatypes, untraversed-field slice (2026-06-14):** recursive and
nested datatypes are now solved *as long as their datatype-typed fields are never
traversed* (`select` into a datatype field) or compared (`==`). Such a field
never affects satisfiability, so it gets no expansion variable and is projected
to its `well_founded_default`; the reduction stays **equisatisfiable** (sound
`sat` *and* `unsat`, no depth bound, no `unknown` hedge). E.g. on
`IntList = nil | cons(head, tail)`: `is-cons(l)` (sat, tail defaults to `nil`),
`is-cons(l) ∧ select head(l) == 5` (sat), and `is-cons(l) ∧ is-nil(l)` (sound
`unsat`) all decide. Tests in `tests/datatype_native.rs` and
`tests/datatype_elim.rs`.

**Traversed datatype fields (2026-06-14):** `select` *into* a datatype field is
now solved by unfolding (`unfold_traversals`): each traversed datatype-field
`select` becomes a fresh **free** child datatype variable, recursively, to
exactly the depth the (quantifier-free) query accesses. The insight that made
this safe without the depth-bound/`unknown` machinery I'd feared: a free child is
a **relaxation** (it only enlarges the model space), so reduced-`unsat` ⇒
original-`unsat` is sound *with no guards*, and a `sat` candidate is projected
through the links and **replayed** — a replay failure (the parent's constructor
left free, child ≠ wrong-constructor default) yields `unknown`, never a wrong
answer. So traversal is **sound always**, and **complete when the accessed
parents' constructors are determined** (e.g. `is-cons(l) ∧ P(tail l)`); when a
parent is otherwise unconstrained it may return `unknown` (sound). Tests cover
traversal sat, the tail forced to a deeper `cons` (would catch an
over-constraining wrong-`unsat`), sound `unsat` on a traversed field, and nested
scalar access. This means the earlier "must return `unknown` not `unsat`" worry
was misplaced for QF explicit-select access — relaxation handles `unsat`.

**Equality over datatype-fielded datatypes (2026-06-14):** also handled by the
same relaxation. `build_dt_eq` compares tag + scalar fields and *skips* datatype
fields, which is a *weaker* constraint than full structural equality (original ⊆
reduced), so reduced-`unsat` ⇒ original-`unsat` is sound; a `sat` candidate is
replay-checked (equal projections — e.g. both datatype fields defaulted to the
same value — pass; a genuine difference is `unknown`). Decides e.g.
`l == m ∧ is-cons(l) ∧ is-nil(m)` (unsat via tags) and
`l == m ∧ head(l)==5 ∧ head(m)==6` (unsat via scalar fields). Tests in
`tests/datatype_native.rs`.

Still open: array/UF datatype fields, `is`/`select`/`==` over a non-variable
datatype term, and the **acyclicity + congruence** native theory (plus exact
field guards to make the relaxed `unknown` cases complete). Those are the next
datatype unit.

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
