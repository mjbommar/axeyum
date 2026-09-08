# Bare integer literal guards, 2026-09-08

The class of admission limit **no name-keyed registry can ever see**: a numeric
comparison guarding a route, written as a literal, with no `const` definition
site to key an entry on. Found by the coverage sweep behind
[admission-limit-coverage-2026-09-08.md](admission-limit-coverage-2026-09-08.md);
none of these is registered in `crates/axeyum-solver/src/config_registry.rs`,
and inventing a name for one is a code change with its own review.

This table is the string/parser/rewrite group. Four further sites were found
elsewhere in the same sweep and are recorded in the companion document:
`maxsat.rs`'s `bits > 127` (hard `Err`, ends the MaxSAT route),
`bv2nat_blast.rs`'s `w >= 128` (an unlinked second copy of that file's own
`MAX_BLAST_WIDTH`), `qinst_egraph.rs`'s `attempts_since_clock_check >= 8192`
(which sets how often a shared deadline is polled at all), and `cas_poly.rs`'s
`ideal_limits()` struct literal (four Gröbner-basis budgets as anonymous
fields, backing the same search as the registered `MAX_IDEAL_*` constants).

Systematic sweep of the assigned files with
`grep -nE '[<>]=? ?[0-9_]{2,}|\.min\(|\.max\(|saturating_sub\('` plus a
second pass for single-digit comparisons, read by hand to exclude noise
(SMT-LIB n-ary arity checks like `items.len() >= 2` for `and`/`distinct`/etc,
sign checks like `n < 0`, enum discriminants, and `#[test]` bodies). These
have no name to register in `config_registry.rs` — that is exactly what makes
them invisible to a name-keyed registry.

| # | File:line(s) | Guard expression | Meters | On crossing | Observable to caller? | Suggested const name | Suggested doc comment |
|---|---|---|---|---|---|---|---|
| 1 | `crates/axeyum-smtlib/src/bounded_completeness.rs:436` | `if a.len() > 12` | decimal-digit count of an unparsed integer literal, in `integer_literal_too_large` | Decline (returns `true` = "too large", short-circuiting before `i128::parse`) | Yes, indirectly — feeds `has_unsafe_construct`, which makes `is_bounded_complete` return `false` (a `bool`, directly caller-visible) | `INT_LITERAL_DIGIT_PREFILTER` | Digit count above which an integer literal is rejected without parsing, so an absurd (e.g. 29-digit) literal can never overflow `i128::parse`; paired with `MAX_SAFE_INT_LITERAL`'s numeric threshold for literals that do parse. |
| 2 | `crates/axeyum-smtlib/src/parse.rs:1623` | `if depth > 256` in `SourceStringSatProblem::eval` | recursion depth of the bounded source-witness expression evaluator | Decline (`return None`) | Only indirectly — folds into the bounded source-witness probe's own SAT-only/replay-gated "leaves prior `unknown` untouched" behavior (see `SOURCE_WITNESS_*` entries) | `SOURCE_STRING_EVAL_MAX_DEPTH` | Recursion-depth guard for the bounded source-witness expression evaluator; a native-Rust-stack safety net, not a completeness policy. |
| 3 | `crates/axeyum-smtlib/src/parse.rs:2269` | `if conjuncts.len() > 2_048` | top-level conjuncts admitted into the word-only side-channel parse | Decline (`return None`); doc: "declining preserves the original bounded parse error as `unknown`" | Yes — the caller of the word-only route falls back to the pre-existing `SmtError`, itself surfaced to the top-level result | `WORD_ONLY_MAX_CONJUNCTS` | Cap on top-level conjuncts admitted into the word-only side-channel parse; keeps the downstream SAT driver's clause preparation off the pathological edge that can overflow the native call stack (doc measures real corpus rows at ~600 conjuncts, well under this). |
| 4 | `crates/axeyum-smtlib/src/parse.rs:2289` | `if assertions.len() > 2_048` | flattened word-only assertions (same route as #3, second gate) | Decline (`return None`), same fallback as #3 | Same as #3 | `WORD_ONLY_MAX_ASSERTIONS` | Second gate on the same word-only route as `WORD_ONLY_MAX_CONJUNCTS`, checked after conjuncts are flattened into individual word-boolean assertions. |
| 5 | `crates/axeyum-smtlib/src/parse.rs:4156` | `if depth > 16` in `regex_on_after_first_views` | recursion depth of the suffix-after-first-occurrence regex-view builder | Decline (`return None`) — this optional regex-view construction is simply not built | No — folds silently into "this content view is unavailable", one of several reasons the caller may not get a tightened view | `REGEX_VIEW_MAX_DEPTH` | Recursion-depth guard for building an after-first-occurrence regex view; declining only forgoes one optional narrowing, never a wrong verdict. |
| 6 | `crates/axeyum-smtlib/src/parse.rs:12875,14280,14337,14363,14406,14432,14546,15716,15740,15787,15850` (11 sites) | `if depth > 32` (identical value, same guard shape) in `exact_collect_affine`, `exact_string_length_le`, `exact_string_min_len`, `exact_string_max_len`, `exact_int_lower_bound`, `exact_int_upper_bound`, `exact_string_alphabet`, `eval_pinned_word`, `eval_pinned_word_semantics`, `eval_pinned_int`, `eval_guaranteed_pinned_word` | recursion depth, independently, in 11 different "exact reasoning" / "pinned word" helper functions | Decline (`return None`) in every case | No — each is an optional source-level fact-derivation helper; a `None` just means that fact/bound is not derived, no route is different at the top level | `EXACT_HELPER_MAX_DEPTH` (one shared name for what is currently 11 independent copies of the literal `32`) | Recursion-depth guard shared in spirit (not in code) by every `exact_*`/`eval_pinned_*` source-level fact helper; a native-stack safety net for deeply nested source terms. THIS IS THE LARGEST CLUSTER FOUND: 11 independent literal sites, same value, no shared name — a change to one would silently diverge from the other 10. |
| 7 | `crates/axeyum-smtlib/src/parse.rs:11791,11978,12309,13880` (4 sites) | `exact_ite_count(...).sum::<u32>() <= 6` / `> 6` in `exact_rewrite_app` (x3) and `exact_distribute_app_ite` | total nested-ITE count being distributed/compared during exact source-level rewriting | Decline (skip the ITE-aware rewrite branch / `return None`) | No — optional exact-rewrite shortcut only | `EXACT_ITE_DISTRIBUTE_CAP` | Total ITE count above which exact-rewrite ITE distribution/comparison is skipped; `2^6 = 64` matches this file's separate, named `EXACT_ITE_CASE_CAP`, suggesting the two are meant to agree but nothing pins them together. |
| 8 | `crates/axeyum-smtlib/src/parse.rs:13923,14006,14051,14085,14115,14145` (6 sites) | `parts.len() > 6` (with a `parts.len() < 2` structural lower-bound alongside at 4 of the 6) in `exact_rewrite_small_concat_equality`, `exact_rewrite_concat_at`, `exact_rewrite_concat_substr`, `exact_rewrite_concat_prefix`, `exact_rewrite_concat_suffix`, `exact_rewrite_concat_contains` | number of `str.++`/`seq.++` operands examined by each exact-rewrite concat helper | Decline (`return None`) | No — optional exact-rewrite shortcut only, six independent copies of the same literal | `EXACT_CONCAT_MAX_PARTS` | Operand-count cap shared in spirit by six sibling exact-rewrite concat helpers (`at`/`substr`/`prefix`/`suffix`/`contains`/small-equality); six independent literal sites, same value, no shared name. |
| 9 | `crates/axeyum-smtlib/src/parse.rs:13969` | `if word.len() > 4` in `exact_rewrite_fixed_word_language` | length of a candidate fixed word being matched against a regex language | Decline (`return None`) | No | `EXACT_FIXED_WORD_MAX_LEN` | Length above which `exact_rewrite_fixed_word_language` does not attempt to prove a fixed-word regex-language membership fact exactly. |
| 10 | `crates/axeyum-smtlib/src/parse.rs:8975,16482,16529,16590` and `:18549` | `total <= 128` / `width <= 128` / `ew >= 128` in `pack_string_literal`, `radix_bv_const`, `wide_decimal_bv_const`, `parse_indexed_constant`, `seq_pack_const` | bit-vector/packed-value width | NOT a decline — chooses between the narrow `u128`-packed representation and a `WideUint`/`wide_bv_const` multi-limb representation; both branches succeed | N/A (representation choice, not an admission/effort decision) | `NATIVE_LIMB_WIDTH_BITS` | Widest value representable in the native `u128` limb; at or under this width the narrow packed encoding is used directly, above it the wide multi-limb encoding is used instead — a structural fact about `u128`, not a policy knob. Five call sites, all consistent. |
| 11 | `crates/axeyum-solver/src/strings.rs:170,601,684` | `if rmax > 16` in `BoundedString::concat`, `::replace`, `::replace_all` | combined packed content length (bytes) after the operation | Hard `Err(IrError::InvalidWidth(rmax * 8))` — ends the route, no fallback in this module | Yes — `Err` is the return type | `BOUNDED_STRING_MAX_CONTENT_BYTES` | Hard cap on a `BoundedString`'s packed content length in this lower-level IR-facing module — `16` bytes = 128 bits is the `u128` packed-representation ceiling, and unlike the SMT-LIB front door's `STRING_BOUND_CAP`/wide representation, this module has no wide-limb fallback: crossing it is a hard error, not a decline-to-wide-mode. THE THREE SITES NAMED IN THE TASK BRIEFING. |
| 12 | `crates/axeyum-rewrite/src/canonical.rs:3043,3061` | `if width >= 128` (mask computation) | bit-vector width | NOT a decline — chooses `u128::MAX` vs `(1u128 << width) - 1` for an all-ones mask | N/A | `NATIVE_LIMB_WIDTH_BITS` (same structural fact as row 10) | See row 10. |
| 13 | `crates/axeyum-rewrite/src/inverter.rs:1271,1291` | `if width >= 128` (mask computation) | bit-vector width | NOT a decline — same all-ones-mask representation choice as row 12 | N/A | `NATIVE_LIMB_WIDTH_BITS` | See row 10. |
| 14 | `crates/axeyum-rewrite/src/functions.rs:1219` | `Sort::BitVec(width) if width <= 128 => ...` in `sample_value_of_sort` | bit-vector width of a sort being sampled for the Ackermann function-abstraction witness | Decline: falls to `_ => None`, i.e. the sample is *unavailable* | Yes — doc states explicitly this is "a reported coverage hole rather than a silent pass"; feeds `FunctionAbstractionWitness::unavailable`, which `FUNCTION_ABSTRACTION_WITNESS_SAMPLES`'s consumer reads | `WITNESS_SAMPLE_MAX_BV_WIDTH` | Widest `BitVec` sort `sample_value_of_sort` can sample; wider sorts make the function-abstraction witness sample unavailable rather than silently agree — unlike rows 10/12/13, there is no wide-limb fallback exercised here, so this is a real (if `u128`-shaped) coverage limit, not pure representation dispatch. |
| 15 | `crates/axeyum-solver/src/smtlib.rs:2446` | `if width >= 128` (mask computation, in multi-objective optimization pinning) | bit-vector width of an optimization objective being pinned at its optimum | NOT a decline — same all-ones-mask representation choice as rows 12/13 | N/A | `NATIVE_LIMB_WIDTH_BITS` | See row 10. |

## Notes

- Rows 10, 12, 13, 15 are the same structural fact (`128` = bits in a `u128`)
  reimplemented independently at nine call sites across three crates with no
  shared name. None of these are policy knobs — promoting them to a `const`
  would be for readability/consistency, not to make a governing value
  visible, so none of them belong in `config_registry.rs` even if named.
- Rows 6, 7, 8 are genuine "no name to register" clusters: real effort/depth
  budgets, repeated verbatim at 4-11 call sites each within one file, that a
  name-keyed registry structurally cannot see because no single definition
  site exists to key on.
- Not included: dozens of SMT-LIB n-ary operator arity checks
  (`items.len() >= 2` for `and`/`or`/`distinct`/`+`/`-`/`*`/`str.++`/etc, and
  the corresponding `Err(SmtError::Syntax("... expects >= N arguments"))`
  sites), sign/domain checks (`n < 0`, `offset < 0`), and `Theory::index`'s
  `0..=9` enum discriminants (structural, and already covered by the
  out-of-scope `Theory::COUNT` in the main report) — none of these meter an
  effort/resource budget or change how much work is done; they are
  well-formedness checks mandated by the SMT-LIB grammar or by the type
  itself.
