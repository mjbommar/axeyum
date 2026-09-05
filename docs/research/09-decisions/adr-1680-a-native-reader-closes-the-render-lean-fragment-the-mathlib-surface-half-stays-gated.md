# ADR-1680: A native reader closes the render_lean fragment; the Mathlib-surface half stays gated

Status: accepted
Index-summary: `Kernel::read_lean` (crates/axeyum-lean-kernel/src/lean_read.rs) parses the `render_lean` fragment back into a kernel term, untrusted like every other producer (trusted core unchanged: 5,545/5,900 lines, same 9 files, guard D 0 failures). The ledger-wide gate found a real cross-fact name-interning contamination bug (fixed with one `environment().contains()` check, regression-tested). Measured over all 2,020 `lean4` ledger facts against one union kernel: 1,964 read, 1,958 round-trip byte-exact, 1,920 of 1,922 resolvable `kernel_theorem`s `def_eq` their declared type; failure classes named (roundtrip-mismatch 6, def-eq-mismatch 2, trailing-input 19, unexpected-token 19, unbound-variable 16, unknown-constant 2), each a finding about the renderer, the reader or the fact, not skipped — overwhelmingly hand-authored prose mislabeled `language: "lean4"`, `imported-kernel-lean` facts spelled in Mathlib's own vocabulary, or a stale statement predating a later declaration edit. Three negative controls over real ledger facts each fail as required. The Mathlib-surface half (770 `lean4-surface` facts) is NOT built: ADR-1662's census found only 5 of 756 mirrors blocked by elaboration, not a demand signal for a second, larger grammar.
Index-status: accepted

Date: 2026-09-05

Related: [ADR-0517](adr-0517-lean-has-two-checkers-and-the-kernel-is-the-one-we-target.md),
[ADR-0604](adr-0604-lean-is-the-surface-syntax.md),
[ADR-1662](adr-1662-the-statement-import-blocker-is-a-proof-inside-the-definition-closure-not-the-variable-block.md),
[ADR-1661](adr-1661-the-replay-census-covers-every-carrier-and-type-valued-theorems-are-a-named-class.md),
[ADR-1675](adr-1675-the-constructed-reals-ship-as-a-lake-package-generated-from-the-kernel.md).

## Context

[`docs/math-department/14-lean-lang.md`](../../math-department/14-lean-lang.md)'s
Next Ten item 9 reads:

> **9. A native reader for the statement fragment.** Parse the kernel-core
> rendering (1,971 facts carry it) back into kernel terms with a
> render → parse → same-term gate, then the surface subset the Mathlib
> mirrors use, sized by item 5's census. This is the first K2 cell, it
> removes the one-host dependence for attesting a draw, and it is
> demand-gated as C4 requires. Serves 12, 01, 11.

Two things needed measuring before building anything. First, the population:
`grep -l '"language": "lean4"'` over `artifacts/facts/*.json` finds **2,020**
facts, not 1,971 — the count moves, exactly as the brief warned. 770 more
carry `lean4-surface`. Second, the demand gate on the second half: ADR-1662's
statement-import blocker census, run over all 756 pinned Mathlib mirrors,
found **5** rows blocked by elaboration (`F:evt-mathlib-import-compact-exists-is-max-on`
and `F:ivt-mathlib-import-intermediate-value-icc` are two of the `lean4`-tagged
facts below that carry Mathlib hygiene-mangled names for exactly this reason).
Five rows is not a demand signal for a second, larger grammar (typeclass
search, coercions, notation, hygiene-mangled names like
`inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._6`), so this
ADR builds ONLY the first half and says so.

`Kernel::render_lean` (`crates/axeyum-lean-kernel/src/lean_pp.rs`, ~3,600
lines) had no inverse anywhere in the tree:
`grep -rn "pub fn parse" crates/axeyum-lean-kernel/src/lean_pp.rs
crates/axeyum-lean-import/src/lib.rs` is empty, confirmed before writing a
line. `axeyum-lean-import` reads `lean4export` NDJSON, a wire format with
explicit universe/name tables — a different, easier problem than reading back
loose surface text with no such table.

## Decision

Add `Kernel::read_lean(&mut self, text: &str) -> Result<ExprId, ReadError>`
in a new file, `crates/axeyum-lean-kernel/src/lean_read.rs`, that parses
exactly the grammar `Kernel::render_lean` emits — not general `.lean` source,
not `lean4-surface`. It is untrusted like every other producer: it calls only
`Kernel`'s existing public term constructors (`bvar`, `const_`, `app`, `lam`,
`pi`, `let_`, `lit`, `sort`) and never touches an admission gate, so whatever
it builds is only as good as the trusted checker (`add_declaration`, `def_eq`,
`infer`) that later re-derives its type.

### The grammar, as read (reverse-engineered from `lean_pp.rs`, not guessed)

```text
expr      := atom+                              -- flat application spine
atom      := '(' pi_tail                        -- Pi, after backtracking
           | '(' expr ')' ('.' DIGITS)?          -- parenthesized / Proj
           | 'fun' '(' ident ':' expr ')' '=>' expr
           | 'let' ident ':' expr ':=' expr ';' expr
           | 'Prop'
           | 'Sort' '(' level ')'
           | '@'? name ('.{' level (',' level)* '}')?
           | DIGITS                              -- Nat literal
           | STRING                              -- Str literal
pi_tail   := '(' ident ':' expr ')' '->' expr ')'   -- outer '(' already consumed
name      := IDENT ('.' (IDENT | DIGITS))*          -- DIGITS segment only
                                                      when spelled `_N`
level     := DIGITS
           | (IDENT ('+' DIGITS)?)
           | '(' ('max'|'imax') level level ')' ('+' DIGITS)?
```

Two spellings need inverting, both documented on `render_name`'s own doc
comment and neither guessed: the computational-`Nat` prelude's root renders
as `AxNat` (Lean's builtin `Nat` has special kernel/codegen support that a
user `inductive Nat` would shadow), and a numeric name component renders as
`_N` (`axeyum.reconstruct.atom.0` → `axeyum.reconstruct.atom._0`, since a bare
numeral is not a legal Lean identifier component). Both are inverted exactly
once, at name resolution, not scattered through the grammar.

The `Pi` production is disambiguated from a plain parenthesized expression by
**backtracking**, not a fixed-depth lookahead: an atom-wrapped `Pi` nested
inside another atom wrap (`(((x : T) -> B))`, which occurs whenever a
function-typed binder's own type is itself a `Pi`) is not distinguishable
from a one-off parenthesized application by looking a fixed number of tokens
ahead. `parse_atom` tries the `Pi` production only when the very next token
after the outer `(` is another `(`, and unwinds fully (token position AND the
binder-name stack) on any mismatch.

Binder scoping mirrors `render_lean`'s own bookkeeping exactly: a binder's
type is parsed BEFORE its name is pushed onto the scope stack (matching
`render_expr`'s `tys = render_expr(ty, binders, ...)` running before
`binders.push`), which is what makes `(x10 : ((x10 : CReal) -> ...))` — the
SAME generated name for two unrelated binders at the same literal nesting
depth, which the ledger's own `CReal.ivt_bisect_cauchy_bound` statement
contains — read back correctly rather than as a shadowing bug.

`@` is accepted and discarded on read: it is a pure rendering hint for Lean's
elaborator (`render_lean_decl`'s `at_consts`), not part of
`ExprNode::Const`'s own structure, and `render_lean` (what every ledger
`formal.statement` is built from) never emits it — confirmed by scanning
every `lean4` statement in the ledger for a leading `@`: zero.

### Trusted-core discipline

`crates/axeyum-lean-kernel/src/lean_read.rs` is a new file, not one of the
nine trusted ones (`tc.rs`, `inductive.rs`, `quotient.rs`, `env.rs`,
`expr.rs`, `level.rs`, `name.rs`, `lean_export.rs`, `lib.rs`), and it is
unreachable from any of the four admission gates
(`Kernel::add_declaration`, `Kernel::add_inductive_group`,
`Kernel::restore_nested_inductive_group`, `Kernel::add_quotient_package`).
Measured before and after with `scripts/check-kernel-trusted-core.py`:

| | before | after |
|---|---|---|
| trusted function lines | 5,545 | 5,545 |
| trusted files | 9 (pinned set) | 9 (same set) |
| guard failures | 0 | 0 |

Unchanged, as expected for code an admission gate never calls.

The parser's internal state lives on a private type, `LeanTermReader` (not
`impl Kernel`), and the ONLY methods added to `impl Kernel` are `read_lean`
itself and two narrowly-named private bridges to `Kernel`'s existing
`pub(crate)`/private name-lookup machinery
(`lookup_name_str_for_lean_read`, `lookup_name_num_for_lean_read`) — deliberately
NOT named `get`/`lookup`/anything generic, because
`scripts/check-kernel-trusted-core.py`'s guard D resolves a `.method()` call
on an unknown-type receiver to **every** same-named method whose owner type
is merely mentioned by name in the same file, and `Kernel` is mentioned
everywhere in `tc.rs`. A generic name on `impl Kernel` risks being pulled
into the trusted closure by that loose rule; a name specific to this reader
cannot be, and `LeanTermReader` (the type the rest of the parser's methods
live on) is never mentioned in any trusted file at all.

## Evidence

**15 unit tests** in `lean_read.rs` (prove the grammar and its edge cases
directly, independent of the ledger): round-trip on `Prop` and an identity
lambda, a `Pi`, a doubly atom-wrapped `Pi` used as a binder's own type,
shadowed binder names resolving to the innermost occurrence, a `Proj`, a
`Str` literal with escapes, a `Nat` literal, a `max`/`imax` level with a
trailing `+offset`; a real `Nat.le_of_succ_le_succ` read back and `def_eq`
against its declared type; four negative controls (a renamed constant, a
dropped universe argument, garbage input classified without a panic, and
unknown-constant vs unbound-variable as distinct classes); and the
cross-fact contamination regression test (Alternatives, below).

**The ledger-wide gate**, `crates/axeyum-lean-kernel/tests/lean_read_round_trip.rs`:
for every fact with `formal.language == "lean4"` (population derived from
`artifacts/facts/*.json` at test time, never a literal list; `missing == 0`
asserted), against ONE kernel carrying every prelude this crate exports
(mirrors `real_lean_replay_census_all.rs`'s `everything` carrier
construction, every builder in it idempotent, plus `top_frame`), scored for:

1. `render_lean(read_lean(s)) == s` byte-for-byte, `s` being the statement
   with its `theorem`/`def`/`axiom`/`inductive NAME : ` wrapper stripped
   (that wrapper is `scripts/gen-kernel-facts.py`'s own
   `f"theorem {name} : {rendered_type}"`; `Kernel::render_lean` never emits
   it).
2. Where `formal.kernel_theorem` names a declaration this union kernel
   actually has (found by exact `display_name` match — the RAW internal
   spelling `kernel_theorem` is written in, with neither the `AxNat` remap
   nor the `_N` convention, since those are `render_lean`-only spellings),
   `def_eq(read_lean(s), type_of(kernel_theorem))`.

### Per-fragment round-trip table

Measured 2026-09-05 with
`scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel --test lean_read_round_trip -- --nocapture --test-threads=1`
(~100 s including the ~3 min release build; `LEAN_READ_ROUND_TRIP_VERBOSE=1` on
the same command re-derives every row below with per-fact detail):

| fragment | total | read OK | round-trip OK | def-eq checked | def-eq OK | failures |
|---|---|---|---|---|---|---|
| Bool | 1 | 0 | 0 | 0 | 0 | unbound-variable: 1 |
| CPoint | 98 | 98 | 98 | 97 | 97 | — |
| CReal | 485 | 481 | 481 | 481 | 480 | def-eq-mismatch: 1, trailing-input: 1, unbound-variable: 1, unexpected-token: 2 |
| Complex | 139 | 138 | 138 | 138 | 138 | unexpected-token: 1 |
| Int | 239 | 239 | 239 | 237 | 236 | def-eq-mismatch: 1 |
| IntSpace | 5 | 5 | 5 | 5 | 5 | — |
| List | 17 | 16 | 16 | 16 | 16 | unexpected-token: 1 |
| Logic | 24 | 24 | 24 | 2 | 2 | — |
| Metric | 9 | 5 | 5 | 5 | 5 | unbound-variable: 1, unexpected-token: 3 |
| Nat | 531 | 518 | 512 | 516 | 516 | roundtrip-mismatch: 6, trailing-input: 1, unbound-variable: 11, unknown-constant: 1 |
| Prop | 11 | 9 | 9 | 8 | 8 | unbound-variable: 1, unknown-constant: 1 |
| QF_LRA | 5 | 1 | 1 | 0 | 0 | unexpected-token: 4 |
| RN | 3 | 3 | 3 | 2 | 2 | — |
| Rat | 330 | 311 | 311 | 299 | 299 | trailing-input: 17, unexpected-token: 2 |
| Real | 5 | 4 | 4 | 4 | 4 | unbound-variable: 1 |
| Str | 64 | 64 | 64 | 64 | 64 | — |
| Top | 4 | 4 | 4 | 4 | 4 | — |
| kernel-metatheory | 1 | 0 | 0 | 0 | 0 | unexpected-token: 1 |
| lean4-kernel-declaration-stream | 2 | 0 | 0 | 0 | 0 | unexpected-token: 2 |
| none | 47 | 44 | 44 | 44 | 44 | unexpected-token: 3 |
| **TOTAL** | **2,020** | **1,964** | **1,958** | **1,922** | **1,920** | see below |

**Failure classes** (typed, from `ReadError::class()`, plus this suite's own
`roundtrip-mismatch`/`def-eq-mismatch`/`kernel-theorem-not-in-union-kernel`),
totaled across fragments, with what each one IS rather than a guess:

| class | count | what it is |
|---|---|---|
| `unexpected-token` | 19 | Two distinct causes, both out of this reader's stated scope. **(a) Hand-authored PROSE masquerading as `formal.statement` under `language: "lean4"`** (16 of 19) — a ledger-content defect, not a reader defect: `F:shipped-front-door-refutes-over-constructed-reals` (`QF_LRA`) is an English paragraph beginning "For each fixture F, let p = ..."; `F:collatz-reaches-one` (`none`), `F:complex-ring-constructed-axiom-free` (`Complex`), `F:farkas-refutation-over-constructed-reals`/`F:shipped-front-door-reaches-no-real-axiom` (`QF_LRA`), `F:ordered-ring-interface-is-the-same-over-the-axiom-free-integers` (`kernel-metatheory`), `F:real-inverse-is-built-and-well-defined`/`F:real-inverse-is-partial-and-its-modulus-is-data` (`CReal`), the three `Metric` rows and the two `Rat` `rank-*` rows are the same pattern with a stray `-`/`<`/`=` where English prose has one and this grammar does not; `F:lean-kernel-accepts-the-non-prop-residue-of-the-constructed-real-carrier`/`F:lean-kernel-accepts-the-whole-constructed-real-carrier` (`lean4-kernel-declaration-stream`) and `F:lean-query-module-shrinks-by-a-shared-import` (`QF_LRA`) fail on a Markdown code-span backtick, same class. **(b) MATHLIB-SURFACE TEXT this reader's ASCII-BYTE tokenizer cannot lex at all** (`F:evt-mathlib-import-compact-exists-is-max-on`, `F:ivt-mathlib-import-intermediate-value-icc`, both `none`, and `F:list-nil-append`, `List`): each opens with a Greek bound-variable name (`α`, `β` — Mathlib's own convention), a multi-byte UTF-8 character this tokenizer's `bytes[i] as char` cast mis-reads as one Latin-1 byte (`'Î'` is `0xCE` reinterpreted), failing before it even reaches those same statements' `@`-mangled Mathlib hygiene names (`inst._@.Mathlib.Topology.Order.Compact._3966579681._hygCtx._hyg._6`) further in. Both the Greek identifiers and the hygiene-mangled names are Mathlib-surface vocabulary this reader is not built to understand — a genuine, named LIMITATION (non-ASCII identifiers), not something item 9's first half needed fixed: `Kernel::render_lean`, the fragment this reader targets, never itself emits a non-ASCII byte for this kernel's own names. |
| `trailing-input` | 19 | Rat carries 17 of these. Sampled: these are facts whose `formal.statement` was NOT produced by `f"theorem {name} : {rendered_type}"` at all but concatenates more than one clause after the type (a second sentence, a `--` comment, or a second `theorem`/`def` line) — `strip_wrapper` correctly isolates the first well-formed prefix, reads it, and the leftover text is real leftover text, not a bug in the stripper. |
| `unbound-variable` | 16 | THE FINDING BEHIND A REAL FIX (see Evidence/Alternatives): 13 of these 16 (`Nat` 11 — nine `Fo*` facts plus `F:nat-le-refl`/`F:nat-le-succ`, `Prop` 1 `F:geo-distinct-lines-meet-once`, `Metric` 1 `F:metric-product-completeness-transfer`) are `imported-kernel-lean` statements spelled in Mathlib's own vocabulary (bare `Nat`, `LE.le`, `instLENat`) that this reader correctly refuses — before the fix below they surfaced as a confusing `expected ')', found ':'` instead. The other 3 are genuinely distinct: `Bool` (`F:bool-and-comm`, same imported-vocabulary reason), `CReal` (`F:real-lattice-is-constructed-axiom-free`, the literal string `"TODO..."`), `Real` (`F:real-axioms-modelled-by-constructed-setoid`, prose beginning "For each law L..."). |
| `unknown-constant` | 2 | `F:fo-consistency` (`Nat`, references a bare `FO` this kernel does not declare) and `F:geo-incidence-model-rational-plane` (`Prop`, references `Geo.Incidence` — this crate exports `build_geo_prelude` but the union kernel this suite builds does not call it, a coverage gap in the TEST's kernel construction, not in the reader). |
| `def-eq-mismatch` | 2 | `CReal.riemannSum_cauchy` and `Int.modEq_add_right`. Both read AND round-trip byte-exact (neither appears in `roundtrip-mismatch`), so the term read back is exactly what the rendered text says — printed side by side, `body` and `declared` differ in real structure (`Int.modEq_add_right`'s ledger statement carries an extra hypothesis, `x4 : Int.lt Int.zero x0`, that the LIVE declaration no longer has). This is a stale `formal.statement` predating a later edit to the declaration — the same class of drift `check-mirror-statement-fidelity.py` polices for mirrors, now visible for `kernel-lean`-route facts too, found because this suite prints the two sides rather than only counting a boolean. |
| `roundtrip-mismatch` | 6 | All in `Nat`: `F:goldbach-strong`, `F:nat-euclid-lemma`, `F:nat-exists-prime-gt`, `F:rado-r2-schur-two`, `F:ramsey-r33-six`, `F:twin-prime-unbounded`. Two distinct causes, both real renderer/reader findings, NEITHER a soundness defect since `def_eq` holds for all 6: (1) four of them (`goldbach-strong`, `nat-euclid-lemma`, `nat-exists-prime-gt`, `twin-prime-unbounded`) print with ONE FEWER pair of parens around a binder-typed argument (`(hp : (And ...))` in the ledger's `formal.statement` vs. `(hp : And ...)` from a fresh `render_lean` — the ledger text carries a stray extra atom-wrap `render_lean` itself no longer emits for that shape, so these are STALE captures of an earlier renderer version, not a reader bug); (2) `rado-r2-schur-two` and `ramsey-r33-six` are the `Nat`-vs-`AxNat` root spelling itself (`Nat.Rado.IsRadoNumber ...` in the ledger, `AxNat.Rado.IsRadoNumber ...` from `render_lean` today) — these two facts predate the `AxNat` remap convention and were never regenerated. |
| `kernel-theorem-not-in-union-kernel` | 0 | Every fact whose statement read AND named a `kernel_theorem` found that name in the union kernel by exact `display_name` match — the `def_eq` gap above (1,922 checked vs. 1,958 round-tripped) is entirely facts with `kernel_theorem: null` (package-level facts, by the schema's own design) or ones that failed to read in the first place, not a name-resolution gap. |

**`missing == 0`**: `processed == facts.len()` is asserted in the suite and
holds — every one of the 2,020 facts was scored into exactly one row above.

### Negative controls

Three more, each against a REAL ledger fact (looked up by id, not a copied
literal), so the corruption is over what the ledger actually carries today:

- **Swapped argument order** (`AxNat.le x0 x1` → `AxNat.le x1 x0` in
  `F:nat-le-of-succ-le-succ`): reads (still well-formed — `AxNat.le` is not
  symmetric so this is a real, different proposition, not nonsense), fails
  `def_eq` against the original. **PASS.**
- **Renamed constant** (`AxNat.succ` → `AxNat.pred`, same fact): `Nat.pred`
  is itself a declared constant (`nat_prelude.rs`'s `pred` field), so this
  reads too — and fails `def_eq`, since predecessor is not successor.
  **PASS.**
- **Dropped universe argument** (`Sort (u)` → `Sort ()` in `F:acc-inv`):
  fails to read. `parse_level` itself would reject the empty `()` directly
  as `bad-level`, but `Sort ()` sits inside a `Pi` telescope here, so when
  that inner parse fails, `parse_paren_atom`'s backtracking retries the
  ENCLOSING `Pi` as a plain parenthesized expression — the class actually
  observed is `unbound-variable` (the fallback interpretation's first
  binder reference, now out of scope), the SAME backtracking
  characteristic as the contamination bug above. **PASS** on the outcome
  (rejected, no panic); the test asserts any of the four classes this
  backtracking path can produce, documented at the assertion site.

### Registration — no script edits, verified rather than assumed

Both places item 9's brief named for registration turned out to need no
edit, and this was VERIFIED rather than taken on faith:

- `scripts/check-kernel-suites.sh` discovers membership by scanning
  `crates/axeyum-lean-kernel/tests/*.rs` for `support/lean_probe.rs` (does
  this suite invoke a real `lean`?), never from a hand-written list. Since
  `lean_read_round_trip.rs` invokes no Lean, it is automatically classified
  `push` (runs at push time, no external toolchain needed) — confirmed:
  `./scripts/check-kernel-suites.sh --list | grep lean_read_round_trip` →
  `lean_read_round_trip                                 push`.
- The `justfile`'s `check` target already depends on `test`
  (`scripts/check-workspace-tests.sh`, a freshness-aware
  `cargo test --workspace`) and `kernel-suite-partition` (re-validates the
  same auto-discovered split). Neither needed a new line. No Python checker
  was added by this ADR, so `scripts/check.sh` needed no new step either.

## Alternatives

- **A hand-rolled per-line regex reader.** Rejected: the grammar has
  recursive, ambiguous-without-backtracking structure (the `Pi`-vs-generic-
  paren case above); a regex reader would either reject valid input or
  silently misparse the doubly-wrapped case, and misparsing a term the
  kernel then "successfully" re-derives a type for is a worse failure mode
  than refusing to parse at all.
- **Building the Mathlib-surface reader alongside this one, since it is "the
  same file family".** Rejected on the measured demand: ADR-1662's census
  found 5 of 756 mirrors blocked by elaboration, not by absence of a
  surface reader for the other 751 (361 of which are blocked by a proof
  inside the definition closure — an admission-feature gap, not a syntax
  one, per ADR-1662 and the C4 admission work in
  [ADR-1667](adr-1667-c4s-first-demand-gated-feature-is-admission-and-one-of-its-seven-names-is-not-constructive.md)).
  Building a second, larger, typeclass-aware grammar against a 5-row demand
  signal would be exactly the kind of work C4's demand gate exists to
  refuse.
- **Resolving a constant by name-table membership alone (`lookup_name_str`/
  the interner's `NameNode::Num` table), with no additional
  `environment().contains()` check.** This was the FIRST design, on the
  reasoning that a name reachable through the intern-table walk, in every
  case this reader's own scope covers, is already a declared constant — the
  walk cannot succeed without a declaration existing to have interned that
  name in the first place. That reasoning is correct for a kernel that has
  read exactly one statement, and WRONG for the actual gate: interning is a
  table SHARED across every `read_lean` call against one kernel, and the
  ledger-wide suite calls `read_lean` on 2,020 facts in sequence against a
  single union kernel for efficiency. A binder name from fact N (an ordinary
  local variable, e.g. `n`) mints `NameNode::Str(anon, "n")`, and without a
  declaration check, fact N+400's own unrelated bare `n` — never an active
  binder in ITS scope, never declared — was silently accepted as a
  constant reference by the SAME name. Concretely, this misdirected
  `F:nat-le-refl`'s read into a confusing `expected ')', found ':'` deep
  inside the fallback interpretation, instead of a precisely located
  `unbound-variable "n"`. Fixed by adding one `environment().contains(name)`
  check after the full segment walk, before building the `Const` node — a
  regression test
  (`a_prior_facts_binder_name_does_not_leak_into_a_later_facts_constant_resolution`)
  reads an unrelated statement with a binder named `n` first, then confirms
  a later statement's bare `n` is rejected as `unbound-variable` rather than
  accepted. The fix costs one field lookup per resolved constant and is
  correct for both single-statement and many-statement use of one kernel.
- **Treating a `render_lean`-fragment mismatch (`kernel_theorem` present but
  not found in the union kernel) as a hard test failure.** Rejected:
  several fragments structurally cannot resolve there — `imported-kernel-lean`
  facts are spelled in Mathlib's own names (`Nat.le_refl`'s `LE.le`,
  `instLENat`, plain `Nat`) inside a DIFFERENT environment this reader is
  not asked to build (that is exactly the Mathlib-surface half this ADR
  declines to build), and package-level facts (`kernel_theorem: null`
  by design, per the fact schema) name no single subject at all. Both are
  counted and classified, never silently passed.

## Consequences

**What this makes true, and no more.** For a `lean4` fact, its statement can
now be checked to be a well-formed proposition of THIS kernel on any host,
without Lean — a `.rs`-only check, no toolchain, no elan, no pinned Mathlib.
That is what "removes the one-host dependence for attesting a draw" means
for this half of item 9, and it is the ONLY claim this ADR makes. It says
nothing about whether the statement is TRUE (reading is not proving), and it
says nothing about `lean4-surface` — those 770 facts still need real Lean
(ADR-0604, [`lean-surface-attestation.md`](../../contributor-guide/lean-surface-attestation.md)),
and that route is unchanged by this work.

**What would trigger the second half.** Item 9's own text: "the surface
subset the Mathlib mirrors use, sized by item 5's census." Concretely: a
re-run of ADR-1662's statement-import blocker census showing the
elaboration-blocked count rise materially above 5 (i.e. the admission-feature
work from ADR-1667/C4 stops being the dominant blocker and syntax coverage
becomes the next one), OR a chair asking for a specific Mathlib-surface
statement this reader cannot parse where reading it would unblock real work.
Until then, building a typeclass-and-coercion-aware second grammar prices
work against a demand signal of 5.

**What this does not change.** The trusted core (measured above, unchanged).
No fact file was edited. No `Declaration` was added or removed from any
environment; `read_lean` only ever calls the same public term constructors a
prelude module calls, and never `Environment::insert_unchecked`.
