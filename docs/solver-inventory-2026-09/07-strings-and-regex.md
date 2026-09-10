# Strings and regular expressions — inventory (2026-09-09)

Scope: `crates/axeyum-strings/` (whole crate — the unbounded word-equation and
symbolic-derivative regex core); `crates/axeyum-solver/src/{strings,
string_theory, string_length_cert, word_reconstruct, regex_reconstruct,
word_alethe}.rs` and their `tests.rs` submodules; `crates/axeyum-smtlib/src/
{regex,regex_membership}.rs` (the SMT-LIB front-end regex surface, which
also embeds the bounded byte-string encoder); the four named integration
tests plus `corpus_regression.rs`. Base commit `ea8515407`.

**Baseline for the whole area**: every module in scope lives inside
`full_modules!()` (`crates/axeyum-solver/src/lib.rs:70`, invoked at
`lib.rs:251-252`), so it compiles only with `--features full`. This is stated
once and not repeated per row; the Reachability column below only calls out
gates *other than* `full` (none were found in this area) and otherwise uses
WIRED / TEST-ONLY / NO CALLER FOUND against the `full` baseline.

**The default (`qfbv`) build has no string surface and no SMT-LIB parser at
all.** `crates/axeyum-solver/Cargo.toml:37-40` sets `default = ["qfbv"]`,
`qfbv = []`; `axeyum-smtlib` (`Cargo.toml:29`) and `axeyum-strings`
(`Cargo.toml:30`) are both `optional = true`, pulled in only by
`full = [..., "dep:axeyum-smtlib", "dep:axeyum-strings", ...]`
(`Cargo.toml:51-58`). Since `axeyum-smtlib` (`crates/axeyum-smtlib/Cargo.toml:15-17`)
depends on `axeyum-strings` **unconditionally** (non-optional), pulling in the
parser at all pulls in the whole word-equation/regex core. A default-profile
consumer (`cargo build -p axeyum-solver`, no `--features`) has no `str.*`
support of any kind: no `Solver::check` route touches strings, and there is
no `parse_script`/`solve_smtlib` to even read `(set-logic QF_S)`.

## Summary

- Two independent regex engines exist in this codebase, not one:
  1. `crates/axeyum-smtlib/src/regex.rs` — a private (`enum Regex`, not
     `pub`) **byte**-alphabet NFA compiler feeding the bounded
     bit-vector string route (Thompson NFA simulated over bounded
     positions, `MAX_NFA_STATES = 256`, `MAX_LOOP_EXPANSION = 256`; `Inter`/
     `Comp`/`Diff` are **top-level only** and `Comp` requires DFA
     determinization).
  2. `crates/axeyum-strings/src/regex/*` — the unbounded **code-point**
     (`BitVec(18)`, ADR-0051) symbolic-derivative engine (Brzozowski/Veanes-
     Bjørner), with native `Loop`, and `Inter`/`Comp` decided directly by
     derivatives with no nesting restriction; state explosion is a
     `max_states` budget (`DEFAULT_MAX_STATES = 20_000`,
     `crates/axeyum-strings/src/regex/membership.rs:44`) that degrades to a
     sound `unknown` (`Closure::Budget`), never a wrong verdict.
  `re.diff` is not a native node in either engine's core AST: both front-end
  translators desugar it to `Inter(a, Comp(b))` before it reaches the engine
  (`crates/axeyum-smtlib/src/regex.rs:679-682` for the byte engine,
  `crates/axeyum-smtlib/src/regex_membership.rs:1295-1298` for the code-point
  engine).
- **`crates/axeyum-solver/src/strings.rs` (`BoundedString`/`StrTerm`, the
  bounded-bit-vector string-theory API, 1305 lines) is TEST-ONLY.** Its only
  callers in the whole workspace are its own module and
  `crates/axeyum-solver/tests/strings.rs`; no route in `smtlib.rs` calls it.
  The production bounded-string encoder is a **separate, independent
  reimplementation** of the same packed layout directly inside
  `crates/axeyum-smtlib/src/parse.rs` (`len_width`, `string_total`,
  `string_at_const`, `string_contains`, `string_to_code`, `string_from_int`,
  … at `parse.rs:8329-10249`), whose own comment says it "matches
  `BoundedString::len_width`" (`parse.rs:8330`) — i.e. the two encodings are
  kept in sync by convention/comment, not by one shared implementation. This
  is a real architectural duplication, not just an unused module.
- The decision procedure is a **seven-stage ladder** inside
  `solve_smtlib_at_string_bound` (`crates/axeyum-solver/src/smtlib.rs:2139`):
  word-only fallback → source-fingerprint prefix → source-string route →
  bounded bit-vector solve (+ `StringGate` confirm) → word-equation route →
  online CDCL(T) route → regex-membership route → lex-order route →
  length↔LIA route → bounded-completeness-unsat upgrade → (outer)
  string-bound ladder (24/32/48-byte rungs). Every stage after the first
  bounded solve may only turn an `Unknown` into a verdict; none can overturn
  a decided `sat`/`unsat`.
- Reachability tally for this lane's files: **20 WIRED**, **2 TEST-ONLY**
  (`strings.rs`/`BoundedString`, and one `#[cfg(test)]` use of
  `regex::matches` inside `regex_membership.rs` that is otherwise WIRED via
  `string_theory.rs:1211`), **0 FEATURE-GATED beyond `full`**, **0 NO CALLER
  FOUND**. See the Inventory tables for citations.
- Doc drift found and confirmed with a commit citation: the fuzz-coverage
  checklist (`docs/research/01-foundations/underspecified-operator-fuzz-coverage.md`,
  last updated 2026-07-07) still lists `str.from_code` of `128..=255` as
  **"P0 / GAP-S1"**, an open wrong-`sat`, with an `#[ignore]`d repro test. The
  fix landed in commit `6877c3657` ("str.from_code wrong-sat — byte model
  round-trips 0..=255 …", task #46) and the repro test
  (`from_code_out_of_range_p0_repro`,
  `crates/axeyum-solver/tests/string_differential_fuzz.rs:598-611`) is now a
  plain, passing `#[test]`, not `#[ignore]`.
- Partial operators (`str.at`, `str.substr`, `str.to_code`, `str.to_int`)
  each have a dedicated fuzz seed-class generating the degenerate argument;
  see §5 below and the checklist's String section
  (`docs/research/01-foundations/underspecified-operator-fuzz-coverage.md:102-122`).
- `str.indexof_re` is recognized syntax that is **declined at parse**,
  unconditionally, because it is a cvc5 extension outside SMT-LIB
  `UnicodeStrings` with no oracle to validate against
  (`crates/axeyum-smtlib/src/parse.rs:7581-7590`) — the clearest "parser
  accepts the token, nothing decides it" row in the operator table.
- The `:status` corpus sweep CLAUDE.md names as the pre-merge gate
  (`corpus_regression.rs`) is general-purpose (walks all of
  `corpus/regression/<logic>/`), not string-specific; its string coverage is
  `corpus/regression/cvc5/qf_s/` (20 `.smt2` files, all `QF_S`),
  `corpus/regression/cvc5/qf_slia/` (36 files, all `QF_SLIA` — added 2026-09-09,
  P2.5), and `corpus/regression/cvc5/seq/` (30 files, `Seq` theory — added
  2026-09-09, P2.5).

## Inventory

### `crates/axeyum-strings` (the unbounded word/regex core)

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `normal_form` | `src/normal_form.rs` | 309 | Flatten/drop-ε/fuse/push-len rewrite (ADR-0053 Phase B invariant) | WIRED | Used by `classes.rs`; `concat_components` re-exported and used at `string_theory.rs` (via `axeyum_strings::normal_form::concat_components`, seen in solver grep) |
| `classes` | `src/classes.rs` | 820 | Union-find over asserted `Seq` equalities → CAV-2014 normal forms per class, with premise-set tracking | WIRED | Consumed internally by `infer.rs`/`arrange.rs`/`refute.rs`; those are called from `string_theory.rs`/`smtlib.rs` (below) |
| `infer` | `src/infer.rs` | 946 | Budget-guarded fixpoint: `CycleEpsilon`/`InferUnify`/`InferEndpointEq`/`InferEndpointEmp` rules over `Classes`, emits `Fact`/`Conflict` | WIRED | Called from `arrange.rs` search and `refute.rs::refute_word_equations` (both WIRED, see below) |
| `arrange` | `src/arrange.rs` | 1089 | `F-Split`/`Len-Split` arrangement DFS → `solve_word_equations`, the only `sat`-model route (mandatory replay, no `Unsat` variant by type) | WIRED | `crates/axeyum-solver/src/string_theory.rs:1188`, `crates/axeyum-solver/src/smtlib.rs:166,453` |
| `refute` | `src/refute.rs` | 371 | `refute_word_equations`: runs `infer()` then re-checks the conflict from original premises via `check_derivation`; the only route to word-level `unsat` | WIRED | `string_theory.rs` doc + call inside `StringTheory` assert path (module doc `string_theory.rs:29-32`); re-exported and used by `smtlib.rs` word route |
| `check_derivation` | `src/check_derivation.rs` | 892 | Independent re-checker (`check_conflict`, `check_fact`, `check_equality`, `check_cycle_constant_conflict`) sharing no code with `infer.rs` | WIRED | `crates/axeyum-solver/src/refute.rs`-equivalent usage inside `crates/axeyum-strings/src/refute.rs`; `check_conflict`/`check_equality`/`check_cycle_constant_conflict`/`check_fact` imported directly by `crates/axeyum-solver/src/string_theory.rs` (grep: `axeyum_strings::check_conflict`, `check_cycle_constant_conflict`, `check_equality`, `check_fact`) |
| `lex_order` | `src/lex_order.rs` | 832 | `refute_lex`: certified-`unsat`-only refuter for `str.<`/`str.<=` (constant fold + transitivity/first-char clash) | WIRED | `crates/axeyum-solver/src/smtlib.rs:1235-1237` (`lex_order_verdict` → `apply_lex_order_route`) |
| `regex::ast` | `src/regex/ast.rs` | 179 | `Regex` AST: `Empty`/`None`/`Pred`/`Concat`/`Union`/`Inter`/`Comp`/`Star`/native `Loop` | WIRED | Root of the derivative engine, consumed throughout `derivative.rs`/`membership.rs` |
| `regex::predicate` | `src/regex/predicate.rs` | 254 | `CharPred` interval-set character-predicate algebra (∧/∨/¬, emptiness, witness, mintermization), `ALPHABET_MAX` | WIRED | Leaf of `ast.rs`/`derivative.rs`; `ALPHABET_MAX` imported by `crates/axeyum-smtlib/src/regex_membership.rs:20` |
| `regex::derivative` | `src/regex/derivative.rs` | 581 | `nullable`, `derivative`/`derivative_within`, `canon`, `derivative_closure`/`derivative_closure_within` (budgeted state-set closure) | WIRED | Called from `regex::membership` (`Membership::solve`/`refute_empty`), which is called from `string_theory.rs` |
| `regex::matcher` | `src/regex/matcher.rs` | 217 | Independent reference `matches()` — deliberately shares no code with the derivative engine (ADR-0054 trust anchor) | WIRED + TEST-ONLY use | WIRED: `crates/axeyum-solver/src/string_theory.rs:1211` (recomputes every membership atom's truth on the model, never trusted from search). Also used under `#[cfg(test)]` at `crates/axeyum-smtlib/src/regex_membership.rs:1381,1444` |
| `regex::membership` | `src/regex/membership.rs` | 1233 | `Membership`/`MembershipOutcome`, `Membership::solve` (witness) / `refute_empty` (re-checked emptiness cert), `recheck_empty`, `DEFAULT_MAX_STATES = 20_000` | WIRED | `crates/axeyum-solver/src/string_theory.rs` (`Membership`, `MembershipOutcome::Sat`) and `crates/axeyum-smtlib/src/regex_membership.rs` (`Membership` import) |

### `crates/axeyum-solver/src/` (string decision procedures and reconstruction)

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `strings` (`BoundedString`/`StrTerm`) | `src/strings.rs` | 1305 | Public bounded byte-string-by-BV-lowering API (length+content pair, `max_len ≤ 16`); full scalar op set incl. regex-via-NFA | **TEST-ONLY** | Only referenced by itself and `crates/axeyum-solver/tests/strings.rs`; `grep -rl BoundedString crates/axeyum-solver/src crates/axeyum-solver/tests` returns exactly those two files. Not called from `smtlib.rs`, `string_theory.rs`, or any dispatch table. |
| `string_theory` (`StringTheory`) | `src/string_theory.rs` | 1975 | Online CDCL(T) `TheorySolver` plugging the ADR-0053 word core into the generic `CdclT` driver; `check_qf_s_online_cdclt[_with_memberships]`, `check_qf_slia_length` | WIRED | `crates/axeyum-solver/src/smtlib.rs:806` (`check_qf_s_online_cdclt_with_memberships`), `smtlib.rs:1306` (`check_qf_slia_length`); both also re-exported at `lib.rs` `api::theories::strings` (`lib.rs:698-705`, `doc(hidden)`) |
| `string_length_cert` | `src/string_length_cert.rs` | 1820 | `StringLengthRefutationCertificate`, `check_string_length_refutation`, `string_length_refutation`: independently checkable `str.len`-coupled refutation certs | WIRED | `crates/axeyum-solver/src/evidence.rs:1366` (`check_string_length_refutation`), `evidence.rs:4107` (`string_length_refutation`) |
| `word_reconstruct` | `src/word_reconstruct.rs` | 889 | `is_word_equation_shape`, `reconstruct_word_clash_to_lean_module`: Lean-module proof reconstruction for a word clash | WIRED | `crates/axeyum-solver/src/reconstruct.rs:1687` (`is_word_equation_shape`), `reconstruct.rs:2876` (`reconstruct_word_clash_to_lean_module`) |
| `regex_reconstruct` | `src/regex_reconstruct.rs` | 696 | `reconstruct_regex_emptiness_to_lean_module`: Lean-module reconstruction for a certified regex-emptiness `unsat` | WIRED | `crates/axeyum-solver/src/smtlib.rs:1196`, `crates/axeyum-solver/src/evidence.rs:1346` |
| `word_alethe` | `src/word_alethe.rs` | 490 | `WordClashCertificate`, `word_conflict_alethe`: Alethe-proof emission for a re-checked word-level `unsat` (rule `axeyum_word_clash`, no native Alethe string-clash rule). **Lane L8 owns the Alethe evidence story overall; described here only for what this route emits.** | WIRED | `crates/axeyum-solver/src/evidence.rs:4098` (`word_conflict_alethe`) |

### `crates/axeyum-smtlib/src/` (front-end regex + string surfaces)

| Component | Path | LOC | Role | Reachability | Evidence |
|---|---|---|---|---|---|
| `regex.rs` | `src/regex.rs` | 1328 | Private byte-alphabet `enum Regex` + Thompson-NFA `compile`, feeding the bounded string route's `in_re`. `MAX_NFA_STATES=256`, `MAX_LOOP_EXPANSION=256`; `Inter`/`Comp`/`Diff` top-level only, `Comp` via `determinize_complete` (subset construction) | WIRED | Consumed by `parse.rs`'s bounded-string `in_re` handling (`string.rs` doc: "regex membership … via a Thompson NFA simulated over the bounded positions") |
| `regex_membership.rs` | `src/regex_membership.rs` | 1452 | The regex-membership **side channel**: translates a recognized conjunctive fragment straight into `axeyum_strings::regex::Regex` (code-point) `MembershipProblem`s, bypassing `regex.rs` entirely | WIRED | `crates/axeyum-solver/src/smtlib.rs` `apply_membership_route`/`membership_verdict` (§ Data flow) |
| `parse.rs` (bounded string ops) | `src/parse.rs:8329-10249` | (part of 22k-line file) | Independent reimplementation of the packed bit-vector string encoding: `string_prefixof`, `string_contains`, `string_suffixof`, `string_at_const`, `string_substr`, `string_replace[_all]`, `string_replace_re[_all]`, `string_indexof`, `string_to_code`, `string_from_code`, `string_to_int`, `string_from_int[_const]` | WIRED | Called from the SMT-LIB term-lowering dispatch inside `parse.rs` (`"str.at"`/`"str.substr"`/etc. match arms, e.g. `parse.rs:1784`, `3467`) |

## Data flow

**Front door**: `solve_smtlib`/`solve_smtlib_with_model`
(`crates/axeyum-solver/src/smtlib.rs:1954,1970`) → `solve_smtlib_at_string_bound`
(`smtlib.rs:2139`), one call per string-bound-ladder rung. Inside one rung, in
call order:

1. **Parse** — `axeyum_smtlib::parse_script_with_string_bound_within`
   (`smtlib.rs:2172`). String literals/`str.*`/`re.*` are lowered here,
   either into the packed bounded-BV encoding (`parse.rs:8329-10249`
   functions) or, for scripts the bounded encoder cannot represent, into an
   unbounded `Seq(BitVec(18))` word skeleton (`Script::word_skeleton`,
   `Script::word_only_fallback`).
2. **Word-only fallback** (T-B.4d) — if the bounded encoder declined at
   parse, `decide_word_only` (`smtlib.rs:2213`, calling
   `solve_word_equations`/word-only checked routes) decides from the
   source-level word view alone (`smtlib.rs:719`).
3. **Source-fingerprint prefix** / **source-string route** — fast exact-match
   and source-level word-skeleton routes (`source_fp_prefix_monotonic_result`,
   `source_string_route_verdict` at `smtlib.rs:686`) get first refusal on
   dense membership-heavy families (PyEx).
4. **Bounded solve** — `solve(&mut script.arena, &query.assertions, config)`
   (`smtlib.rs:2237`), the general `check_auto` dispatcher, decides the
   packed bit-vector encoding as ordinary BV constraints (no string-specific
   code runs here beyond what `parse.rs` already lowered).
5. **`StringGate::confirm`** (`smtlib.rs:2242`) — a soundness gate over the
   bounded result.
6. **`apply_source_string_semantic_unsat`** (`smtlib.rs:2249`).
7. **Word-equation route** (`apply_word_route` → `word_route_verdict`,
   `smtlib.rs:110,766`) — `solve_word_equations` over the flat top-level
   conjunction (sat-only second chance).
8. **Online CDCL(T) string route** (`apply_online_string_route` →
   `online_string_verdict` → `string_theory::check_qf_s_online_cdclt_with_memberships`,
   `smtlib.rs:790,862`, `string_theory.rs:1040`) — handles disjunctive/negated
   word problems the flat channel cannot represent; internally: collect `Seq`
   equality + `str.in_re` atoms → generic `CdclT` search →
   `refute_word_equations` (T-B.7) on each assert to certify conflicts →
   `Membership::refute_empty` for membership-class refutation → on a total
   assignment, `solve_word_equations` for the word model +
   `Membership::solve` per membership class + reference `matches()` recheck
   → `Model` replayed via the ground evaluator.
9. **Regex-membership route** (`apply_membership_route` → `membership_verdict`,
   `smtlib.rs:1017,1115`) — the `regex_membership.rs` side-channel
   `MembershipProblem`s decided by `Membership::solve`/`refute_empty`
   directly (bypasses word equations).
10. **Lex-order route** (`apply_lex_order_route` → `lex_order_verdict` →
    `axeyum_strings::refute_lex`, `smtlib.rs:1224,1265`).
11. **Length↔LIA route** (`apply_length_lia_route` → `length_lia_verdict` →
    `string_theory::check_qf_slia_length`, `smtlib.rs:1294,1339`).
12. **Source-string SAT probe**, **`bind_readable_string_values`**,
    **bounded-completeness-unsat upgrade** (`smtlib.rs:2323-2345`) — final
    second chances, sat-only / unsat-only respectively.
13. **String-bound ladder** (`apply_string_bound_ladder`, `smtlib.rs:2225`) —
    re-runs the whole 1-12 sequence at wider declared-string windows
    (24/32/48 bytes) only when the residual `Unknown` is specifically the
    bounded-window decline, and accepts only a `Sat`.

Every stage after step 4 is additive-only by construction (each `apply_*`
function takes the current `CheckResult` and only overwrites an `Unknown`).

## Entry points and public API

- `axeyum_solver::solve_smtlib` / `solve_smtlib_with_model` / `solve_smtlib_session` —
  the text front door; the only entry point that exercises every stage above.
- `axeyum_solver::api::theories::strings::{check_qf_s_online_cdclt,
  check_qf_s_online_cdclt_with_memberships, check_qf_slia_length,
  string_length_refutation, check_string_length_refutation}` — direct
  programmatic access to the online/length routes (`lib.rs:697-705`).
- `axeyum_solver::strings::BoundedString`/`StrTerm` (crate-root `pub mod
  strings;`, `lib.rs:226`) — the bounded bit-vector string-theory builder API.
  Public and callable by an external consumer, but not used by anything else
  in this crate (see TEST-ONLY finding above); a caller wanting bounded
  strings today gets them for free through `solve_smtlib`'s parser-level
  encoding instead.
- `axeyum_strings::{solve_word_equations, refute_word_equations, refute_lex,
  Membership, Regex, infer, Classes, check_conflict, check_fact,
  check_equality, check_cycle_constant_conflict}` — re-exported at
  `crates/axeyum-strings/src/lib.rs:113-120`; this is the crate's whole
  public surface (word core + regex core), reachable directly by any crate
  that takes `axeyum-strings` as a dependency (both `axeyum-solver` under
  `full` and `axeyum-smtlib` unconditionally do).
- `axeyum_smtlib::regex_membership::{MembershipProblem, translate_regex_with_defs, …}`
  and the private `regex.rs` NFA compiler are crate-internal to
  `axeyum-smtlib`; only `parse_script*`/`Script` surface their effects.

## Tests and gates

| Suite | Path | Feature gate | Covers |
|---|---|---|---|
| `strings.rs` (unit) | `crates/axeyum-solver/tests/strings.rs` | `full` (crate-level) | The only exerciser of `BoundedString`/`StrTerm` |
| `online_string_front_door.rs` | `crates/axeyum-solver/tests/online_string_front_door.rs` | `#![cfg(feature = "full")]` line 18 | Disjunctive/negated word problems (`or`/`ite`) through the text front door, decided by the online CDCL(T) route; `sat` replay + certified `unsat` |
| `word_first_fallback.rs` | `crates/axeyum-solver/tests/word_first_fallback.rs` | `#![cfg(feature = "full")]` line 28 | Scripts the bounded encoder rejects at parse (literal/concat-width cap overflow) falling back to the unbounded word-only path; reproduces cvc5-regress `issue6520`/`issue6681` shapes inline |
| `qf_slia_fixed_splice.rs` | `crates/axeyum-solver/tests/qf_slia_fixed_splice.rs` | `#![cfg(feature = "full")]` line 2 | Correlated-bound handling for generated fixed-position splice patterns (`PyExZ3`-style overwrite via two substrings around a literal) |
| `stoi_len_abstraction.rs` | `crates/axeyum-solver/tests/stoi_len_abstraction.rs` | `#![cfg(feature = "full")]` line 25 | `str.to_int`-aware length/value abstraction (P2.7 A.2), ground-int constant folding, semantic-suffix and `str.at`-over-`substr` parse-level normalizations, targeting the `2019-full_str_int` `QF_SLIA` family |
| `corpus_regression.rs` | `crates/axeyum-solver/tests/corpus_regression.rs` | `#![cfg(feature = "full")]` line 16 | The general oracle-free `:status` corpus sweep, **not string-specific** — walks every `*.smt2` under `corpus/regression/<logic>/` through `check_auto` and fails only on a verdict contradicting `:status`. Its string coverage is `corpus/regression/cvc5/qf_s/` (**20 files**, all `QF_S`), `corpus/regression/cvc5/qf_slia/` (**36 files**, all `QF_SLIA`), and `corpus/regression/cvc5/seq/` (**30 files**, `Seq` theory) — the latter two added 2026-09-09 (P2.5). Without `--features full` this compiles to zero tests (matches the CLAUDE.md warning). |
| `string_differential_fuzz.rs` | `crates/axeyum-solver/tests/string_differential_fuzz.rs` | needs `--features z3` (differential vs. the system Z3 binary) for the oracle arms; the module also carries self-checking arms | The bounded route's `str.++`/`str.at`/`str.substr`/`str.replace[_all]`/`str.from_code`/`str.to_code`/`str.to_int`/`str.from_int`/`str.indexof`/`str.<`; explicitly includes the `a946f925`-class degenerate-constant seed shapes (§5) |
| `regex_membership_differential_fuzz.rs` | `crates/axeyum-solver/tests/regex_membership_differential_fuzz.rs` | `--features z3` | Regex-membership route including `\u{...}`-escaped and astral-plane (`>0xFFFF`) literals against Z3 |
| `qf_slia_length_lia_differential_fuzz.rs`, `qf_slia_lex_order_differential_fuzz.rs` | `crates/axeyum-solver/tests/` | `--features z3` | Length↔LIA route and lex-order route, respectively, against Z3 |
| `word_equation_cvc5_crosscheck.rs`, `word_equation_differential_fuzz.rs` | `crates/axeyum-solver/tests/` | mixed (name suggests cvc5/z3 cross-check) | Word-equation route soundness — not read in full for this inventory; see Gaps |
| `evidence_regex_emptiness_certified.rs`, `regex_emptiness_lean_reconstruct.rs`, `evidence_string_length_cert.rs` | `crates/axeyum-solver/tests/` | `full` | Certificate/Lean-reconstruction coverage for the regex-emptiness and length-refutation certs |
| `word_alethe.rs` | `crates/axeyum-solver/tests/word_alethe.rs` | `full` | `word_conflict_alethe` Alethe emission (lane L8's area; not read in detail here) |

## Doc drift

Against `docs/research/01-foundations/underspecified-operator-fuzz-coverage.md`
(last updated 2026-07-07, "living checklist"):

- The checklist's String section (`:102-122`) still lists:
  > `str.from_code` | code point `128..=255` | TOTAL-BY-DEF | **WRONG** — folds
  > to "" | `from_code_out_of_range_p0_repro` (`#[ignore]`, failing) |
  > **P0 / GAP-S1**
  This is stale. The fix (commit `6877c3657`, "str.from_code wrong-sat — byte
  model round-trips 0..=255, decline unrepresentable code points instead of
  folding to empty (P0, task #46)") landed after the doc's last-updated date.
  `from_code_out_of_range_p0_repro`
  (`crates/axeyum-solver/tests/string_differential_fuzz.rs:598-611`) is now a
  plain passing `#[test]`, not `#[ignore]`, and `gen_sound_codepoint`
  (`string_differential_fuzz.rs:196-217`) now densely covers `0..=300`
  including the previously-wrong `128..=255` window. The rest of the
  checklist's String table (rows for `str.at`, `str.substr`, `str.to_code`,
  `str.to_int`, `str.from_code` negative/overflow) matches the current source
  and is not stale.
- No other drift found in the two docs this brief names as covering the
  area (this checklist and the CLAUDE.md Hard Rule it implements); the ADRs
  cited throughout (ADR-0029, ADR-0051, ADR-0053, ADR-0054) match current
  source behavior at every point checked (bounded-encoding caps,
  `Seq(BitVec(18))` code-point sort, the word-equation core's re-check
  discipline, and the derivative engine's native `Loop`/`Inter`/`Comp`).

## 1. Operator support table (parse / solve / model)

Parse = accepted by `axeyum_smtlib::parse_script*`. Solve = at least one
route in the ladder (§ Data flow) can decide a query using this operator.
Model = a `sat` witness including this operator's value is replayed against
the original assertion before being returned. "Bounded" = the packed-BV
route (`parse.rs` + `StringGate`); "Word" = `solve_word_equations`/online
CDCL(T); "Mem" = the regex-membership side channel; "LenLIA" = the
length↔LIA route.

| Operator | Parses | Solved by | Model/replay | Notes |
|---|---|---|---|---|
| `str.++` | yes | Bounded, Word, all downstream | yes | Widens packed bound on concat of non-constants; `STRING_BOUND_CAP=512` (`parse.rs:8325`) |
| `str.len` | yes | Bounded, Word (`normal_form::normalize` pushes `len` through `++`), LenLIA | yes | |
| `str.at` | yes | Bounded (`string_at_const`, `parse.rs:9178`) | yes | TOTAL-BY-DEF `""`/`0`-byte OOB, matches SMT-LIB (§5) |
| `str.substr` | yes | Bounded (`string_substr`, `parse.rs:9369`) | yes | TOTAL-BY-DEF OOB/negative handling (§5) |
| `str.contains` | yes | Bounded (`string_contains`, `parse.rs:9092`), Mem (via prefix/pattern translation) | yes | |
| `str.indexof` | yes | Bounded (`string_indexof`, `parse.rs:9766`) | yes | Negative start pinned to `-1` result per SMT-LIB |
| `str.indexof_re` | yes (recognized) | **no route — declined at parse** | n/a | `parse.rs:7581-7590`: cvc5 extension, no oracle, `Unsupported` unconditionally |
| `str.replace` | yes | Bounded (`string_replace`, `parse.rs:9602`) | yes | Symbolic-operand form declines to Unknown (fuzz doc note) |
| `str.replace_all` | yes | Bounded (`string_replace_all`, `parse.rs:9862`) | yes | Non-overlapping, left-to-right |
| `str.replace_re` / `str.replace_re_all` | yes | Bounded (`string_replace_re[_all]`, `parse.rs:9917,9970`) | yes | Regex-driven variants of the above |
| `str.update` | yes | Bounded (`string_update`, `parse.rs:9535`, dispatched from `apply_op` at `parse.rs:19308`) | yes | ADR-0029: overwrite `len(t)` bytes of `s` at index `i` with `t` (clipped to `s`; out-of-`[0, len(s))` index leaves `s` unchanged); result length always `len(s)` |
| `str.to_int` | yes | Bounded (`string_to_int`, `parse.rs:10126`), Mem (exact decimal-language translation) | yes | TOTAL-BY-DEF `-1` on non-numeral (§5) |
| `str.from_int` | yes | Bounded (`string_from_int[_const]`, `parse.rs:10180,10249`) | yes | `fits` flag guards out-of-window values |
| `str.to_code` | yes | Bounded (`string_to_code`, `parse.rs:10024`) | yes | TOTAL-BY-DEF `-1` on empty/multi-char (§5) |
| `str.from_code` | yes | Bounded (`string_from_code`, `parse.rs:10064`) | yes | Full `0..=255` round-trips exactly since task #46 (see Doc drift); `<0` or `>0x2FFFF` fold to `""`; `256..=0x2FFFF` declines to `Unknown` |
| `str.prefixof` | yes | Bounded (`string_prefixof`, `parse.rs:9061`), Mem | yes | |
| `str.suffixof` | yes | Bounded (`string_suffixof`, `parse.rs:9136`) | yes | |
| `str.is_digit` | yes (`parse.rs:1825`) | Bounded | yes | |
| `str.<` / `str.<=` | yes | Bounded (BV lex compare), LexOrder route (`refute_lex`, unsat-only) | yes | LexOrder only ever emits `Unsat`; `sat` still comes from Bounded/Word |
| `str.in_re` | yes | Bounded (byte NFA, `regex.rs`), Mem (code-point derivative engine) | yes | Two independent engines decide this operator depending on route (§3) |
| `re.none`/`re.all`/`re.allchar`/`re.range` | yes | both engines | n/a (regex, not a value) | |
| `re.++`/`re.union` | yes | both engines | n/a | |
| `re.inter` | yes | both engines | n/a | Byte engine: **top-level only**, nested declines (ADR-0029); code-point engine: no nesting restriction |
| `re.comp` | yes | both engines | n/a | Byte engine: DFA determinization + flip, top-level only; code-point engine: native derivative rule, any position |
| `re.diff` | yes | both engines | n/a | **Not a native AST node in either engine** — desugared to `Inter(a, Comp(b))` at the front end (`regex.rs:679-682`, `regex_membership.rs:1295-1298`) |
| `re.*` / `re.+` / `re.opt` | yes | both engines | n/a | |
| `re.loop` / `re.^` | yes | both engines | n/a | Byte engine: unrolled, capped at `MAX_LOOP_EXPANSION=256`; code-point engine: native `Regex::Loop`/`repeat`, no unrolling |

### 1a. The `seq.*` family (ADR-0029/ADR-0051, generic-element `(Seq E)`)

The operator tables above cover `String` (`Seq(BitVec(18))` fixed-element
strings) and its `str.*` spelling. A separate, generic-element `(Seq E)` sort
(`E` any registered element sort — `Bool`/`Int`/`BitVec`) is dispatched
through `apply_seq_op` (`parse.rs:18688-18987`) to the same packed-BV bounded
encoding family — `op.starts_with("seq.")` marks the bounded length
abstraction used (`parse.rs:18696`, P2.7 A.2), same as a `str.*` call. This
family was previously undocumented here:

| Operator | Site (`parse.rs`) | Notes |
|---|---|---|
| `seq.len` | `18707` | |
| `seq.++` / `seq.concat` | `18716` | |
| `seq.unit` | `18728` | Declines when the element width cannot be determined (no declared `(Seq E)` sort names it) |
| `seq.extract` | `18747` | |
| `seq.prefixof` | `18751` | |
| `seq.suffixof` | `18761` | |
| `seq.contains` | `18771` | |
| `seq.nth` | `18785` | |
| `seq.at` | `18797` | |
| `seq.update` | `18804` | |
| `seq.rev` | `18810` | |
| `seq.replace` | `18818` | |
| `seq.indexof` | `18827` | |
| `seq.replace_all` | `18839` | |
| `seq.nth_total` | `18844` | |

`seq.len`/`seq.++` on a `String`-sorted argument are also accepted as
synonyms for `str.len`/`str.++` in several term-shape matchers throughout
`parse.rs` (e.g. `length_int_expr` at `parse.rs:2643`); this table is about
the dedicated generic-`(Seq E)` dispatch, not that alias.

## 2. The decision procedure, in call order

See "Data flow" above for the full 13-stage ladder with file:line citations.
In one sentence: word equations are decided by a **union-find +
CAV-2014-normal-form substrate** (`classes.rs`) with a **budgeted inference
fixpoint** on top (`infer.rs`), fed to either a **DFS arrangement search**
for `sat` models (`arrange.rs::solve_word_equations`, no `Unsat` variant —
type-level soundness) or a **re-checked refutation** for `unsat`
(`refute.rs::refute_word_equations`, which re-derives `infer()`'s claimed
conflict from cited premises alone via `check_derivation.rs`, sharing no
code). Regex membership is decided by **Brzozowski/Veanes-Bjørner symbolic
derivatives** (`regex/derivative.rs`) with **witness search + matcher
replay** for `sat` (`Membership::solve`) and a **re-checked derivative-
emptiness certificate** for `unsat` (`Membership::refute_empty`,
`recheck_empty`). Neither `arrange.rs` nor `regex/membership.rs` ever emits
an untrusted `unsat`.

## 3. The regex engine(s)

Two engines, not one — see Summary and the operator table's `re.*` rows.

- **Byte engine** (`axeyum-smtlib/src/regex.rs`, bounded route): private
  `enum Regex` → Thompson NFA (`compile`), simulated over the bounded byte
  positions in `strings.rs`'s style. `Inter`/`Comp`/`Diff` are **top-level
  only** — nested inside another regex construct they decline
  (`"re.inter nested inside another regex construct is declined (ADR-0029)"`,
  `regex.rs:314`). `Comp` requires a **complete DFA** via subset-construction
  determinization (`determinize_complete`, `regex.rs:838`); an incomplete DFA
  would wrongly reject strings whose run falls off, so completion is
  mandatory before the flip. Size bound: `MAX_NFA_STATES = 256`
  (`regex.rs:75`); a regex whose NFA/DFA exceeds it is declined
  (`Unsupported`, sound `unknown`). Bounded repetition
  (`re.loop`/`re.^`) is **unrolled**, capped at `MAX_LOOP_EXPANSION = 256`
  (`regex.rs:732,744-753`); past the cap, declined.
- **Code-point derivative engine** (`axeyum-strings/src/regex/*`, membership
  route): Brzozowski derivatives + Veanes/Bjørner transition regexes over
  `CharPred` interval-set predicates on the `BitVec(18)` alphabet. `Inter`
  and `Comp` are decided **directly by derivative rules**
  (`derivative.rs:204-247`), no determinization, no nesting restriction.
  `Loop` is a **native** AST node, stepped one repetition at a time
  (`deriv_loop_within`, `derivative.rs:256`), never pre-unrolled. Size bound:
  `derivative_closure`/`derivative_closure_within` cap the distinct-residual
  set at `max_states` (`DEFAULT_MAX_STATES = 20_000`,
  `membership.rs:44`); exceeding it returns `Closure::Budget`, and emptiness
  reasoning **only concludes `unsat` on a `Complete` closure**
  (`derivative.rs:531-534`), so a budget overrun is always a sound
  `unknown`, never a wrong verdict.
- `re.diff` has no native representation in either engine; both translators
  desugar `R1 \ R2` to `R1 ∩ ¬R2` before their engine ever sees it.

## 4. Unicode and escapes

The 2026-07-06 incident (commit `ba0d9149`, "seed-215 — expand SMT-LIB
string-literal `\u` escapes"): both the byte-model encoder and the
code-point word/skeleton route decoded a `"..."` literal by only collapsing
`""`, never expanding `\u{h…}` (1-5 hex) / `\uhhhh` (4 hex) — so
`"\u{62}"` became six raw bytes instead of the character `b`, while the
regex-side decoder (`re.range`/`str.to_re`) *did* expand escapes, giving two
denotations for the same text and a fabricated `sat` (`s0 = "\u{62}" ∧ s0 ∈
(re.comp (re.range "a" "b"))`).

**Current state**: one shared decoder,
`decode_string_code_points` (`crates/axeyum-smtlib/src/parse.rs:8900`),
expands both escape forms on **every** literal route — confirmed by grep:
`word_literal` (`parse.rs:1448`), the constant-pattern translator
(`parse.rs:4070`), and the byte-model packer (`parse.rs:4931`,
`string_literal_bytes` at `parse.rs:8949`) all call it. A `\` not starting a
valid escape stays a literal backslash, matching Z3/cvc5
(`parse.rs:8900-8944`). `SMTLIB_MAX_CODE_POINT = 0x2_FFFF` (`parse.rs:8882`);
an escape naming a code point above it makes `decode_string_code_points`
return `None`, and the literal is declined (`Unsupported`) rather than
truncated — never a wrong verdict.

**Alphabet the solver reasons over**: the bounded byte-model route
(`strings.rs`/`parse.rs`'s packed encoding) is a **byte** model — a decoded
code point above `0xFF` has "no byte-model slot" and that literal's route is
declined (`string_literal_bytes`, `parse.rs:8949-8963`), pushing the query to
the word/membership routes instead. The unbounded word-equation core and the
regex-membership route both reason over `Seq(BitVec(18))` — the **full
Unicode scalar range up to `0x2FFFF`** (ADR-0051) — via
`axeyum_strings::regex::ALPHABET_MAX`.

**Fuzz coverage today**: `regex_membership_differential_fuzz.rs:70-99`
deliberately spans decimal digits, `\u{...}` escapes, and code points above
`0xFF` — its `LITERAL_POOL`-style constant array includes `"\\u{7f}"` (ASCII
boundary), `"\\u{e9}"` (above `0x7f`), and `"\\u{1d11e}"` (astral plane,
above `0xFFFF`), with an inline note that Z3 answers `unsat` correctly for
the astral-plane case. `string_literal_unicode_escape.rs` (present in
`crates/axeyum-solver/tests/`, not read in full — see Gaps) is a dedicated
end-to-end regression suite for this incident per the `ba0d9149` commit
message. The CLAUDE.md-recorded historical gap ("every generator omitted
escapes … hid for weeks") reads as closed for the generators inspected here;
I did not exhaustively audit every string-fuzz file in the crate (see Gaps).

## 5. Partial operators

| Operator | Degenerate input | Convention | Matches SMT-LIB? | Fuzz seed-class |
|---|---|---|---|---|
| `str.at` | index `<0` / `≥ len` | `""` (bounded route: `0`-byte via `char_at`/`string_at_const`) | yes (TOTAL-BY-DEF) | `string_differential_fuzz.rs` — `gen_int_expr` reaches `-1..` for the index (`rng.in_range(-1,4)` at depth 0), confirmed in the checklist row `:112` |
| `str.substr` | negative/OOB `off`/`n` | `""` / clamped | yes | `string_substr`'s off/len args both drawn from `gen_int_expr`, which reaches negative values; checklist row `:113` |
| `str.to_code` | empty or multi-char string | `-1` | yes | `gen_str_expr`'s literal length is `0..=3` (drives both empty and multi-char); checklist row `:115` |
| `str.to_int` | non-numeric string | `-1` | yes | Base `ALPHABET = "ab012"` naturally yields non-digit strings; a dedicated `gen_signed_numeric_literal` generator (task #42) additionally forces the `"-5"`/`"+3"`/`"1-2"` **looks-numeric-but-isn't** shape the base generator structurally under-samples (checklist rows `:116-117`) |
| `str.from_code` | code point `<0` | `""` | yes | `gen_sound_codepoint`'s `FIXED` array includes `-2,-1` (checklist `:121`) |
| `str.from_code` | code point `256..=0x2FFFF` | declines to `Unknown` | yes (sound-by-decline) | `gen_sound_codepoint` draw 1 densely sweeps `0..=300` |
| `str.from_code` | code point `128..=255` | round-trips exactly (fixed, task #46) | yes | `from_code_out_of_range_p0_repro`, now passing; see Doc drift |

All five listed partial operators satisfy the CLAUDE.md Hard Rule (a fuzz
seed-class deliberately emitting the degenerate/constant argument, not only
a variable form structurally unable to reach it) — this is a positive
finding, not a gap.

## 6. Reachability tally

| Reachability | Count | Members |
|---|---|---|
| WIRED | 20 | All of `axeyum-strings`'s 9 source-level modules (`normal_form`, `classes`, `infer`, `arrange`, `refute`, `check_derivation`, `lex_order`, `regex::{ast,predicate,derivative,matcher,membership}` — counted as one row each per the Inventory table, 9 rows there covering 13 files incl. `regex/mod.rs`); `string_theory.rs`, `string_length_cert.rs`, `word_reconstruct.rs`, `regex_reconstruct.rs`, `word_alethe.rs` (5); `axeyum-smtlib`'s `regex.rs`, `regex_membership.rs`, and the `parse.rs` bounded-op functions (3); the front-door dispatch functions themselves (`word_route_verdict`, `online_string_verdict`, `membership_verdict`, `lex_order_verdict`, `length_lia_verdict`, `decide_word_only`) reachable only via `smtlib.rs` internal call graph, re-exported `doc(hidden)` at `lib.rs:1444-1452` — not double counted, folded into the module rows above |
| TEST-ONLY | 2 | `crates/axeyum-solver/src/strings.rs` (`BoundedString`/`StrTerm`) — no caller outside itself and `tests/strings.rs`; `axeyum_strings::regex::matches` at `regex_membership.rs:1381,1444` specifically (its *other* call site, `string_theory.rs:1211`, is WIRED, so the type overall is WIRED — this is one test-only *use site*, not a test-only module) |
| FEATURE-GATED (beyond `full`) | 0 | None found — no `z3`/`bench-internals`/nested-`#[cfg]` gating inside this lane's files beyond the blanket `full` baseline |
| NO CALLER FOUND | 0 | None — every `pub fn`/`pub struct` surveyed in the Inventory tables above has at least one citable caller |

Search method for the TEST-ONLY finding: `grep -rln "BoundedString"
crates/axeyum-solver/src/*.rs crates/axeyum-solver/tests/*.rs
crates/axeyum-solver/examples/*.rs crates/axeyum-solver/benches/*.rs`
returns exactly `src/strings.rs` and `tests/strings.rs`; a second pass
(`grep -rn "strings::BoundedString\|strings::StrTerm"` over `lib.rs` and all
`src/*.rs`, excluding `src/strings.rs` itself) returns nothing.

## 7. The `:status` corpus sweep

`crates/axeyum-solver/tests/corpus_regression.rs`, `#![cfg(feature =
"full")]` at line 16 — compiles to zero tests without `--features full`
(confirmed by the `#![cfg(...)]` at file scope; no test function inside
survives without it). It is a **general** oracle-free sweep: it recursively
walks every `*.smt2` under `corpus/regression/<logic>/`
(`collect_smt2`, `corpus_regression.rs:39`), runs `check_auto`, and fails
**only** on a verdict that contradicts the file's `(set-info :status ...)` —
an `Unknown` or a parse failure is a skip, not a failure
(`corpus_regression.rs:6-13`). For this lane's scope, its coverage is
`corpus/regression/cvc5/qf_s/` — **20 `.smt2` files**, all bearing `(set-logic
QF_S)` — plus, as of 2026-09-09 (P2.5), `corpus/regression/cvc5/qf_slia/`
(**36 files**, all `(set-logic QF_SLIA)`) and `corpus/regression/cvc5/seq/`
(**30 files**, `Seq`-theory instances, mostly `(set-logic ALL)` upstream but
quantifier-free) — vendored from cvc5's own `test/regress/cli/*/strings` and
`*/seq` suites at clone commit `1689f13331f7543801f82d9dcbcaac2f70a26781`
(`find corpus/regression/cvc5/qf_s -iname "*.smt2" | wc -l` = 20;
`find corpus/regression/cvc5/qf_slia -iname "*.smt2" | wc -l` = 36;
`find corpus/regression/cvc5/seq -iname "*.smt2" | wc -l` = 30). Distinct
`str.*`/`seq.*`/`re.*` operators exercised rose from 16 (`qf_s/` alone) to 47
across all three directories; of the 66 newly vendored files, 57 decide
correctly against `:status` and 9 return `unknown` (never a wrong verdict) —
see `corpus/regression/cvc5/qf_slia/README.md` and
`corpus/regression/cvc5/seq/README.md` for the per-file/per-operator split.
QF_SLIA soundness is now exercised by both this vendored slice and the named
differential-fuzz suites (`qf_slia_length_lia_differential_fuzz.rs`,
`qf_slia_lex_order_differential_fuzz.rs`), the latter still needing
`--features z3` to compile any tests.

## Gaps and open questions

- I did not read `word_equation_cvc5_crosscheck.rs`,
  `word_equation_differential_fuzz.rs`, `qf_s_replace_fold_differential_fuzz.rs`,
  `qf_s_online_membership_differential_fuzz.rs`, `string_route_parity.rs`,
  `string_theory_online.rs`, `string_code_bridge.rs`, `string_bound_ladder.rs`,
  `string_update_reference_fuzz.rs`, `string_literal_unicode_escape.rs`,
  `word_int_coupling_sat.rs`, `bounded_string_replace_membership_deadline.rs`,
  `word_equation_route.rs`, or `evidence_string_front_door.rs` in full — the
  brief's scope did not name them individually and time did not allow a full
  pass. Each is present in `crates/axeyum-solver/tests/` per the directory
  listing; a follow-up pass should confirm each compiles only under `full`
  (spot checks above suggest this is universal in the crate) and catalog what
  each specifically covers.
- I did not verify by build that `corpus_regression.rs` and the four named
  integration tests actually pass at `ea8515407` — this inventory is
  source-reading only per the method brief; a `cargo test -p axeyum-solver
  --features full --test corpus_regression` (and the sibling `--test`
  invocations) would confirm current green/red status. `[unverified]`.
- The exact set of `str.replace`/`str.replace_all` symbolic-operand shapes
  that decline (vs. solve) was read from a fuzz-file comment
  (`string_differential_fuzz.rs:150-154`, "the wired-sound case; a fully-
  symbolic replace often declines") rather than traced through
  `string_replace`'s full branch structure in `parse.rs:9602-9765` (166
  lines not fully read); a precise "symbolic replace decides iff …"
  characterization would need that trace.
- Whether the online CDCL(T) route (`string_theory.rs`) is reachable from
  `Solver`/`check_with_*` facade methods beyond the SMT-LIB text front door
  was not traced — only the `smtlib.rs` call sites and the `doc(hidden)`
  `api::theories::strings` re-export were confirmed; a programmatic (non-text)
  caller path through `Solver` was not searched for.
