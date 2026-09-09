# Z3-Noodler and Mata — automata-based string solving (2026-09-09)

Scope: `references/z3-noodler/` (VeriFIT's Z3 fork, `src/smt/theory_str_noodler/`
is the added string theory, everything else is upstream Z3) and
`references/mata/` (VeriFIT's automata library, `include/mata/`, `src/`).

Clone SHAs (`git -C references/<x> log -1 --format=%H`):

- `z3-noodler`: `1ffd452c310e2b9ec27c63647c49598ea297ab57`
- `mata`: `e8c9310e389b1e62ece7080956550f70ceeed777`

Sizes and language:

- `mata` — 15M on disk, C++20. `include/mata` + `src`: 22,442 lines
  (`find references/mata/src references/mata/include -name "*.cc" -o -name
  "*.hh" | xargs wc -l`). Bundled 3rd-party: CUDD (BDDs), RE2 (regex parsing
  helper), simlib (`references/mata/3rdparty/`).
- `z3-noodler` — 50M on disk, C++17/20, a fork of the whole Z3 tree
  (740,270 lines under `src/*.{cpp,h,cc}`). The noodler-specific addition is
  `src/smt/theory_str_noodler/`: 29,113 lines across 49 files. license: MIT
  for both (`references/mata/LICENSE:1`, `references/z3-noodler/LICENSE.md:3`).

## Summary

- Z3-Noodler is a `theory` plugin bolted onto stock Z3's CDCL(T) loop
  (`theory_str_noodler : public theory`,
  `src/smt/theory_str_noodler/theory_str_noodler.h:58`). It intercepts
  `final_check_eh` (`theory_str_noodler_final_check.cpp:39`) and answers with
  ordinary theory lemmas (length formulas, blocking clauses) fed back into
  Z3's SAT core — string reasoning has no dedicated proof format of its own.
- The core algorithm is **stability/noodlification**: word equations and
  regex memberships become NFAs (`AutAssignment`, one Mata `Nfa` per
  string variable), the equation is turned into a segment automaton (chain of
  automata joined by ε-transitions, one segment per RHS variable), and
  `mata::applications::strings::seg_nfa::noodlify_for_equation`
  (`references/mata/include/mata/applications/strings.hh:402`) enumerates all
  ways to split it into "noodles" — this is the split step our own
  `arrange.rs` `F-Split`/`Len-Split` DFS also performs, but on explicit
  automata rather than symbolic classes.
- Mata itself is a general finite-automata library (explicit NFA/AFA over
  `Symbol = unsigned`, `references/mata/include/mata/alphabet.hh:16`), not a
  string-specific one: determinization, two minimization algorithms
  (Brzozowski, Hopcroft), inclusion/universality by naive complementation
  **and** by antichains, and a mintermization pass over symbolic (bitvector
  formula) transitions using CUDD BDDs
  (`references/mata/src/mintermization.cc`,
  `references/mata/include/mata/parser/mintermization.hh`).
- **The alphabet answer**: neither project materializes the ~200,000-code-point
  SMT-LIB Unicode range as explicit transitions. Noodler builds an explicit
  `Alphabet` from only the symbols that literally occur in the formula (string
  literals, regex character classes), plus one extra **dummy symbol**
  representing "everything else" (`util::get_dummy_symbol`,
  `src/smt/theory_str_noodler/util.h:35-42`) — a single minterm-style
  catch-all class, computed once per query, not once per problem instance's
  worst case. `zstring::max_char()` returns 196,607 = `0x2FFFF`
  (`src/util/zstring.h:36,42-51`) — **the identical SMT-LIB `UnicodeStrings`
  bound** axeyum uses (`SMTLIB_MAX_CODE_POINT = 0x2_FFFF`,
  `crates/axeyum-smtlib/src/parse.rs:8882`; `ALPHABET_MAX` in
  `crates/axeyum-strings/src/regex/predicate.rs`) — both are conforming to the
  same standard, not independently chosen.
- Length constraints are integrated by extracting Presburger (LIA) formulas
  from a solved noodle set — `DecisionProcedure::get_lengths`
  (`decision_procedure.cpp:559`) builds a `LenNode` tree, optionally via a
  **Parikh image** of a segment automaton
  (`src/smt/theory_str_noodler/parikh_image.{h,cpp}`, 1,435+433 lines) for
  disequalities/not-contains — then hands it to Z3's own arithmetic theory
  through `len_node_to_z3_formula` and `check_len_sat`
  (`theory_str_noodler_final_check.cpp:245-246`). This is Nelson-Oppen-style:
  the string theory produces a LIA formula, Z3's arithmetic solver decides it,
  the result gates whether noodlification continues.
- `str.replace_all` is handled by a dedicated automaton construction (a
  "prefix automaton" over the find/replace character sets,
  `src/smt/theory_str_noodler/regex.h:262-265`), not by unfolding into
  primitive equations. `str.to_int`/`str.from_int` go through
  `ConversionHandler` (`conversion_handler.h/.cpp`), which reasons over two
  auxiliary automata (`only_digits`, `non_number`) and derives sound value
  bounds (`get_to_int_value_bounds`, `conversion_handler.cpp:91`) that get
  folded into the LIA side rather than solved by string reasoning alone.
- Not-contains constraints reduce to **quantified LIA solved by Z3's own MBQI**
  (`quant_lia_solver`, `src/smt/theory_str_noodler/quant_lia_solver.h:14-40`,
  sets `p.set_bool("mbqi", true)`), which is explicitly incomplete — the code
  comment says so directly (`theory_str_noodler_final_check.cpp:364-365`,
  "using a solver with quantified instantiation that is incomplete and it
  might return `l_undef`").
- Incrementality is inherited from Z3's `theory` interface directly:
  `push_scope_eh`/`pop_scope_eh` push/pop nine separate `scoped_vector`s (word
  (dis)equations, memberships, not-contains, conversions, variable
  equivalences) plus a "loop protection" cache that memoizes solved instances'
  length formulas across `final_check_eh` calls
  (`theory_str_noodler.cpp:684-722`, `run_loop_protection` in
  `theory_str_noodler_final_check.cpp:110-117`).
- **Where each side degrades differs in kind, not just in constant.** Our
  code-point regex engine has a purpose-built structural budget
  (`DEFAULT_MAX_STATES = 20_000` distinct derivative residuals,
  `crates/axeyum-strings/src/regex/membership.rs:44`) that is deterministic,
  reproducible, and turns overrun into a typed `Closure::Budget` →
  sound `unknown`, never a wrong verdict. Noodler/Mata have **no equivalent
  structural cap on automaton or noodle-set size** in the code read for this
  lane; the only decline mechanism found is `util::check_limit`
  (`src/smt/theory_str_noodler/util.cc:33-37`), which checks Z3's *global*
  `ast_manager::limit().is_canceled()` — a wall-clock/step-count resource
  limit shared with the rest of the solve, not a string-specific,
  reproducible-by-construction budget. Both directions are sound-by-decline
  (Z3 catches the thrown exception and reports `unknown`,
  `src/smt/theory_str_noodler/util.cc:20-30`), but ours is quantized on a
  named structural measure and Noodler's is quantized on wall time.
- Nine other decision-procedure entry points exist besides the main
  worklist search, tried **in this order** inside `final_check_eh` before
  falling through to it (each only fires under a suitability predicate):
  loop-protection cache lookup, single-membership heuristic (universality/
  emptiness instead of full automaton construction), multi-membership
  heuristic, unary-alphabet length-only procedure, disequation-only length
  heuristic, Nielsen transformation, length-only decision procedure,
  underapproximation. This ladder-of-cheap-cases-before-the-general-solver
  structure is architecturally the same shape as axeyum's own seven-stage
  string ladder in `solve_smtlib_at_string_bound`
  (`crates/axeyum-solver/src/smtlib.rs:2139`,
  `docs/solver-inventory-2026-09/07-strings-and-regex.md:63-70`) — both
  projects converged on "try cheap special cases before the general
  procedure," independently.

## Schema

### A. Input front end

Inherited from Z3 wholesale — Noodler adds no new parser, only a new theory
plugin reachable once the input's sort/logic routes string terms to
`theory_str_noodler`. See lane C2 (`02-z3.md`) for the SMT-LIB parser itself.
Noodler-specific term recognition happens at the `expr`-tree level inside
`expr_cases.{h,cpp}` (pattern-matching helpers like `is_replace_indexof`,
`is_indexof_add`, `is_to_int_num_eq`, `expr_cases.h:11-84`) and
`ecma_regex.{h,cpp}` (2,633+1,125 lines — an ECMAScript-flavor regex parser
distinct from Z3's own `re.*` term constructors, used for the `re.derivative`-
style bisimulation front documented in `ast/rewriter/seq_regex_bisim.cpp`).

### B. Preprocessing (before search)

`DecisionProcedure::preprocess` (`decision_procedure.cpp:987`) runs a fixed,
named sequence of rewrite passes on the `Formula`/`AutAssignment` pair, in
this order (each a method on `FormulaPreprocessor`,
`formula_preprocess.h:412-430`): `remove_trivial` → `reduce_diseqalities` →
(optionally `underapprox_languages`) → `propagate_eps` → (conditionally,
twice) `refine_languages` → `generate_equiv` → `propagate_variables` →
`propagate_eps` → `infer_alignment` → `remove_regular` → (conditionally)
`skip_len_sat` → `generate_identities` → `propagate_variables` →
`refine_languages` → `reduce_diseqalities` → `remove_trivial` →
`reduce_regular_sequence(3)` → `remove_regular` → `generate_equiv` →
`common_prefix_propagation` → `common_suffix_propagation` →
`propagate_variables` → `generate_identities` → `remove_regular` →
`propagate_variables` → (underapprox branch) → `reduce_regular_sequence(1)` →
`generate_identities` → `propagate_variables` → `remove_regular` →
`conversions_validity` → `simplify_not_contains_to_equations` →
`replace_not_contains` (`decision_procedure.cpp:987-1080`, full sequence).
Each pass can independently detect unsat and short-circuit (`l_false`)
without ever reaching the main search. Model reconstruction: preprocessing
operates on the same `AutAssignment`/substitution-map structures the main
search consumes, so no separate reconstruction map is needed — variable
substitutions recorded in `init_substitution_map` are replayed by
`get_model` at the end (`theory_str_noodler_model.cpp`).

Before the general decision procedure is even constructed, `final_check_eh`
tries five cheaper special-case procedures gated by suitability checks
(`theory_str_noodler_final_check.cpp:127-215`): single-membership heuristic,
multi-membership heuristic, unary-alphabet procedure, disequation-length
heuristic, Nielsen transformation — see Summary.

### C. Core SAT engine

n/a for Noodler-the-string-theory — it is a passenger theory inside Z3's
DPLL(T) core. See lane C2 for that core.

### D. Inprocessing (during search)

n/a in the SAT-inprocessing sense; the theory-level analogue is the "loop
protection" cache (`run_loop_protection`,
`theory_str_noodler_final_check.cpp:110-117`): a map from a canonicalized
solving instance to a previously-derived length formula, checked before
launching (or re-launching) the noodlification search, avoiding recomputation
across `final_check_eh` re-entries at the same or deeper scope.

### E. Encoding / bit-blasting

n/a — no bit-blasting. The "encoding" here is term → automaton: every string
variable and literal becomes a Mata `Nfa` (`AutAssignment`,
`src/smt/theory_str_noodler/aut_assignment.h`); regex terms lower via
`regex::NfaConstructor` (`regex.h`) into Mata NFAs, using `re2parser.cc` /
`ecma_regex.cpp` for regex syntax. This is the fork point from axeyum: we
lower string constraints to term-level rewrites over word equations or to
byte/code-point bit-vectors; Noodler lowers to automata from the start.

### F. Theory solvers

The string theory itself, described in the Summary. Two other Noodler-side
theories worth naming: `lia_solver`/`quant_lia_solver`
(`src/smt/theory_str_noodler/lia_solver.h`, `quant_lia_solver.h`) wrap Z3's
own arithmetic solver (quantified, MBQI-based, for not-contains) rather than
implementing a new one; `ca_str_constr.{h,cpp}` (905 lines) implements
"counter automata" string constraints — read from the module name and the
`counter_automaton.h` (351 lines) header, not traced line-by-line for this
inventory (see Confidence).

### G. Theory combination

Nelson-Oppen-style, not model-based: the string theory produces `LenNode`
Presburger formulas from a candidate noodle solution and hands them to Z3's
arithmetic theory via `check_len_sat`
(`theory_str_noodler_final_check.cpp:245-246`, `303-306`); an unsatisfiable
length formula forces backtracking in the string search (blocking clause via
`block_curr_len`) rather than the two theories sharing a joint model
directly. Interface equalities between string- and non-string-sorted terms
are created explicitly: `mk_interface_eqs()`
(`theory_str_noodler_final_check.cpp:47-51`) runs first in every
`final_check_eh` call and forces `FC_CONTINUE` if it adds any, i.e. theory
combination is resolved to a fixpoint before string search ever starts.

### H. Quantifiers

Not-contains constraints only, via `quant_lia_solver` invoking Z3's own MBQI
with `mbqi=true` (`quant_lia_solver.h:38-40`) — acknowledged-incomplete in
the source comment (`theory_str_noodler_final_check.cpp:364-365`). No
quantified string reasoning otherwise; general first-order quantifiers over
string sorts are Z3's problem, not Noodler's (see lane C6 for axeyum's own
quantifier stack).

### I. Model production

`theory_str_noodler_model.cpp` builds three `model_value_proc` subclasses
(`noodler_var_value_proc`, `str_var_value_proc`, `concat_var_value_proc`,
lines 10/60/133) that call `dec_proc->get_model(str_var, arith_model)`
(`decision_procedure.h`, abstract method) to materialize a concrete string
per variable from the winning noodle/automaton assignment, threading in the
arithmetic model for length-coupled variables. No independent post-hoc model
check was found in the files read (contrast axeyum's mandatory replay —
every `sat` re-evaluates the term against the model,
`docs/solver-inventory-2026-09/07-strings-and-regex.md`, and the regex
engine's dedicated re-check via `regex::matcher`,
`crates/axeyum-strings/src/regex/matcher.rs:217`, called at
`crates/axeyum-solver/src/string_theory.rs:1211`). Whether Z3's own generic
model-checking machinery re-validates theory-produced model values was not
traced (`[undetermined]`; would need `src/model/model.cpp`).

### J. Proof / certificate production

None specific to string reasoning was found. Noodler emits ordinary theory
lemmas/blocking clauses (`block_curr_len`, `mk_interface_eqs`) that
participate in whatever proof-logging Z3's core does generically; no Alethe
rule, no automaton-level certificate (e.g. no emitted inclusion/emptiness
witness object) was found under `src/smt/theory_str_noodler/`. This is
n/a-by-absence, not a citation of a positive "no proofs" statement — see
lane C2 for Z3's general proof story, which this inherits.

### K. Proof checking

n/a for the same reason — no string-specific checker exists to describe.

### L. Interpolation

Not found under `src/smt/theory_str_noodler/`. Z3 itself has a general
interpolation framework (see lane C2); nothing in this lane's scope
specializes it for strings. `[undetermined beyond a targeted grep]`.

### M. Optimization

Not found in `theory_str_noodler` — no MaxSAT/objective-handling code in
this lane's scope. Z3's `opt` module is out of scope here (see lane C2).

### N. Incrementality

Full push/pop support inherited from the `theory` interface contract:
`push_scope_eh`/`pop_scope_eh` (`theory_str_noodler.cpp:684-722`) scope nine
separate `scoped_vector` todo-lists plus `var_eqs`; `last_run_was_sat` /
`scope_with_last_run_was_sat` cache a positive verdict across repeated
`final_check_eh` calls at the same scope (short-circuits to `FC_DONE` at
`theory_str_noodler_final_check.cpp:42-45`) and is invalidated on pop below
that scope (`theory_str_noodler.cpp:715-718`). The loop-protection cache
(Preprocessing/D above) is the cross-call memoization layer.

### O. Parallelism

None found in `theory_str_noodler`; the worklist search
(`compute_next_solution_with_len_checks`, `decision_procedure.cpp:20`) is a
single-threaded `while (!is_worklist_empty())` loop over a `std::deque`. Not
examined for whether Z3's own portfolio/parallel mode can run multiple
Noodler instances (`[undetermined]`).

### P. Resource limits and determinism

`util::check_limit(m)` (`util.cc:33-37`) checks Z3's global
`ast_manager::limit().is_canceled()` at each worklist-pop iteration
(`decision_procedure.cpp:35`) and throws, which Z3 catches and reports as
`unknown` (release builds; debug builds re-throw uncaught,
`util.cc:20-29` — a debug/release behavior split, not present on axeyum's
budget mechanism, which is the same code path in both profiles). No named
seed or explicit node/state cap specific to the string theory was found —
determinism, if any, is inherited from Z3's own single-threaded default
config and the deterministic iteration order of `std::deque`/`std::vector`
worklists.

## Gaps against axeyum

### They have, we do not

| Capability | Their implementation (cited) | Our status (cited) | Rough gap size |
|---|---|---|---|
| General explicit-automata NFA library with two minimization algorithms (Brzozowski, Hopcroft) and antichain-based inclusion/universality | `references/mata/include/mata/nfa/algorithms.hh:22-100` | No automata library at all; word equations are solved symbolically (union-find + arrangement DFS, `crates/axeyum-strings/src/classes.rs`, `arrange.rs`) and regex membership by derivatives, never by NFA construction/minimization | Large — a from-scratch dependency, not a patch; only worth building if a benchmark class shows the derivative engine losing specifically to automaton operations (not yet measured here) |
| Noodlification: enumerating all splits of a word equation as segment-automaton chains, giving a complete decision procedure for general word equations + regular constraints (the theory this fragment is complete for) | `references/mata/include/mata/applications/strings.hh:300-425`, driven from `decision_procedure.cpp` `push_to_worklist`/noodle loop | Our word core (`infer.rs`/`arrange.rs`) is a **budgeted** fixpoint + DFS, not proven complete for the general theory; ADR-0053 scopes it explicitly (see `docs/solver-inventory-2026-09/07-strings-and-regex.md` normal-form/Phase-B citation) | Medium-large — this is the actual algorithmic core, not a library call; adopting it would mean re-architecting the word-equation route, not adding a crate |
| LIA integration via Parikh images of segment automata for disequality/not-contains reasoning | `src/smt/theory_str_noodler/parikh_image.{h,cpp}` (1,868 lines combined) | We couple length and word constraints through a separate length↔LIA route and length-certificate module (`string_length_cert.rs`), not a Parikh-image-of-automaton construction | Medium — a specific, non-trivial construction; only relevant if our length↔LIA route is shown to be incomplete on a concrete benchmark class |
| `not-contains` handled generally via reduction to quantified LIA + MBQI | `theory_str_noodler_final_check.cpp:340-388`, `quant_lia_solver.h` | `not_contains`/`str.replace_all` support in axeyum was not traced exhaustively in `docs/solver-inventory-2026-09/07-strings-and-regex.md` (see that file's own Gaps section); no MBQI-equivalent quantifier instantiation route for strings exists | Medium — but note theirs is *acknowledged incomplete* (`l_undef` on some branches), so this is not an unqualified win for them |
| A battery of special-case fast-path procedures tried before the general solver (unary-alphabet, Nielsen transformation, disequation-length heuristic, membership-only heuristics) | `theory_str_noodler_final_check.cpp:127-215`, `nielsen_decision_procedure.{h,cpp}` (519+774 lines), `unary_decision_procedure.h` | axeyum's seven-stage ladder is architecturally the same idea but a shorter list of cases (word-only fallback, source-fingerprint, bounded BV, word-equation, online CDCL(T), regex-membership, lex-order, length↔LIA — `crates/axeyum-solver/src/smtlib.rs:2139`) | Small-medium — same design pattern, fewer specialized cases; incremental to extend rather than a new architecture |

### We have, they do not

This table is short for a real reason: most of axis A-P for Noodler is Z3's,
not Noodler's, so the honest comparison is "us vs. Z3" (lane C2), which has
its own larger table. What is genuinely specific to *our* strings stack
against *their* strings-specific code:

| Capability | Our implementation (cited) | Their status | Rough gap size |
|---|---|---|---|
| A structural, reproducible state/node budget for regex membership that degrades to a typed sound `unknown`, decoupled from wall-clock | `DEFAULT_MAX_STATES = 20_000`, `crates/axeyum-strings/src/regex/membership.rs:44`; `Closure::Budget`, `derivative.rs:531-534` | Only a global, wall-clock-based `ast_manager` resource limit was found (`util.cc:33-37`) — no string/automaton-specific structural cap in the files read | Small to build (we already have it); the gap is that Noodler's decline behavior is less reproducible across machines/loads, not that it is missing entirely — see Confidence |
| Two structurally independent regex/membership re-checkers with no shared code by design (ADR-0054) — a reference matcher for models, a separate re-derivation for emptiness certs | `crates/axeyum-strings/src/regex/matcher.rs:217`; `check_derivation.rs` (892 lines, shares no code with `infer.rs`) | No comparably-isolated re-checker for automaton-based string results was found in `theory_str_noodler` — Noodler's own worklist-produced result is the only evidence of the verdict | Small-medium — this is a design discipline, not a large algorithm; the gap is in *trust structure*, matching this project's "untrusted fast search, trusted small checking" identity, not in raw capability |
| Kernel-checkable Lean-module reconstruction for word-clash and regex-emptiness `unsat` | `crates/axeyum-solver/src/word_reconstruct.rs`, `regex_reconstruct.rs` (per `docs/solver-inventory-2026-09/07-strings-and-regex.md` Inventory table) | No proof/certificate production specific to strings found (Schema J) | Large in what it buys (an admitted-axiom-free trust chain), small in code footprint on their side to compare against because there is none |
| Dedicated fuzz seed-classes per underspecified operator (`str.at`, `str.substr`, `str.to_code`, `str.to_int`, `str.from_code`) deliberately emitting the degenerate/constant argument | `docs/solver-inventory-2026-09/07-strings-and-regex.md` §5 (all five satisfy CLAUDE.md's Hard Rule) | Not evaluated — Noodler's test corpus/fuzzing infrastructure was not read for this lane (see Confidence) | Not comparable without reading their tests; do not claim a gap either direction |

## Not comparable

- **Z3-Noodler is not a standalone solver in this comparison's sense — it is
  Z3 plus one theory plugin.** Roughly 96% of the fork by line count
  (711,157 of 740,270 total `src/*.{cpp,h,cc}` lines are outside
  `smt/theory_str_noodler/`, which is 29,113 lines) is unmodified-or-
  Z3-inherited code. Grading Noodler against axeyum on axes A, C, J, K, L, M,
  O, P as if they were Noodler-specific would silently be grading Z3 itself;
  every such axis above is marked n/a or cross-referenced to lane C2
  (`02-z3.md`) rather than filled from this lane's reading.
- **Mata is a general automata library, not a string solver.** Comparing its
  API surface (determinization, minimization, antichains) directly against
  axeyum's string-specific decision procedures is comparing a library to an
  application; the fairer comparison is Mata + Noodler's *use* of Mata
  (noodlification, mintermization-for-alphabet, Parikh images) against
  axeyum's word/regex core, which is what the Gaps tables above do.
  A feature-count table of raw Mata operations (e.g. "Mata has 6 reduction
  algorithms, we have 0") would be a category error: axeyum has no automaton
  IR to reduce in the first place, by design (ADR-0051 chose derivatives
  specifically to avoid building one).
- **The two systems' `unknown` verdicts are not directly comparable in
  frequency or cause without a shared benchmark run**, which this
  source-reading lane did not perform (CLAUDE.md forbids building either).
  This file states the *mechanism* difference (structural budget vs. global
  resource limit) as a documented finding, not a claim about which system
  times out more often in practice.
- **Noodlification's completeness claim (decidable fragment: word equations
  with regular constraints) versus axeyum's budgeted approach is a
  theoretical-completeness question, not a benchmark question**, and this
  lane did not verify Noodler's completeness claim against its own source —
  it is stated in VeriFIT's published papers (not read for this lane; see
  Confidence) and only partially corroborated here by reading the
  noodlification code itself compiles a case-complete-looking split
  enumeration.

## Confidence

Solid source reads, cited directly:

- The noodlification API shape and its role in `DecisionProcedure`
  (`decision_procedure.cpp:15-100`, `references/mata/include/mata/applications/strings.hh:300-425`).
- The full named preprocessing pass sequence and its order
  (`decision_procedure.cpp:987-1080`).
- The `final_check_eh` call-order ladder of special-case procedures
  (`theory_str_noodler_final_check.cpp:39-290`).
- The alphabet construction (`dummy_symbol`/minterm catch-all) and the
  `zstring::max_char()` = 196,607 = `0x2FFFF` match with axeyum's own bound
  (`util.h:35-42`, `zstring.h:36-51`).
- Mata's algorithm inventory (`algorithms.hh:22-198`) and mintermization via
  CUDD BDDs (`src/mintermization.cc:1-120`).
- Incrementality (`push_scope_eh`/`pop_scope_eh`, `theory_str_noodler.cpp:684-722`)
  and the resource-limit mechanism (`util.cc:33-37`, `20-29`).
- `str.to_int`/`str.from_int` bound derivation
  (`conversion_handler.h/.cpp`, cited above) and `str.replace_all`'s prefix-
  automaton construction (`regex.h:262-265`).

Inferences from naming/comments, not fully traced:

- `ca_str_constr.{h,cpp}` (905 lines) and `counter_automaton.h` (351 lines) —
  read the header comments and declarations only, not the full
  implementation; described from the module name and public interface, not
  from tracing every call site (Schema F).
- The claim that Noodler has "no structural, string-specific state/automaton
  size budget" is a **negative finding from a targeted grep** across
  `src/smt/theory_str_noodler/*.{h,cpp}` for `MAX_STATES`/`state limit`/
  `explosion`/`blow up`/`timeout` (see the two greps that produced this
  section) — it is possible a cap exists in a file this search missed or
  inside Mata itself as an opt-in parameter Noodler does not use; stated as
  "not found in the files read," not as "proven absent."
- Whether Noodler's noodlification is provably complete for the fragment it
  targets was not independently verified against source; it is presented as
  the algorithm's designed intent (visible in the code structure: full split
  enumeration, no arbitrary early cutoff other than the global resource
  limit) rather than a proof I checked.
- `ecma_regex.cpp` (2,633 lines) — its existence and role (an alternate,
  ECMAScript-flavored regex front distinct from Z3's native `re.*`
  constructors) is read from file naming, includes, and the
  `seq_regex_bisim.cpp` comment about minterms; not traced end to end.
- Model production's interaction with Z3's own generic model-checking
  machinery (whether Z3 re-validates `model_value_proc` outputs) is
  `[undetermined]` — would need `src/model/model.cpp`, out of this lane's
  scope.
- I did not read `nielsen_decision_procedure.cpp` (774 lines) or
  `length_decision_procedure.cpp` (1,098 lines) beyond their headers/call
  sites; their entries in the Gaps table are sized from what they claim to
  do (Nielsen transformation, length-only procedure), not from a full trace
  of their internals.
