//! SMT-LIB 2 script parser for the `QF_BV` benchmark slice.
//!
//! Scope (formats note): benchmarks-as-data — `set-logic`, `set-info`,
//! `declare-fun` (0-ary constants and n-ary uninterpreted functions, ADR-0013),
//! `declare-const`, `define-fun` (0-ary aliases and n-ary macros), `assert`,
//! `check-sat`, `exit`, plus `let` and `forall`/`exists` binders (ADR-0016).
//! Incremental scripting (`push`/`pop` with multiple `check-sat`) is recorded as
//! an ordered [`ScriptCommand`] sequence for scoped, per-`check-sat` solving
//! (ADR-0009 lifecycle). Term conversion is iterative, so deep benchmark terms
//! cannot overflow the stack.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use axeyum_fp::{FloatFormat, RoundingMode};
use axeyum_ir::{
    ArraySortKey, FuncId, MAX_BV_WIDTH, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode,
    WideUint,
};
use axeyum_strings::regex::Regex;

use crate::SmtError;
use crate::sexpr::{SExpr, read_all};

/// An ordered command from an (incremental) SMT-LIB script. Commands that affect
/// the assertion stack and its `check-sat` queries are recorded; declarations
/// mutate the shared arena directly (and stay global). A small number of output
/// commands are also recorded when their answer depends on the scoped assertion
/// stack at the command point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScriptCommand {
    /// `(assert t)` — push `t` onto the current assertion scope.
    Assert(TermId),
    /// `(push n)` — open `n` nested assertion scopes.
    Push(u32),
    /// `(pop n)` — close `n` scopes, dropping assertions made within them.
    Pop(u32),
    /// `(check-sat)` — decide the conjunction of the currently-active assertions.
    CheckSat,
    /// `(check-sat-assuming (l ...))` — decide the active assertions together with
    /// the assumption literals `l`, without retaining them afterwards.
    CheckSatAssuming(Vec<TermId>),
    /// `(reset-assertions)` — remove **all** assertions (and open scopes), keeping
    /// declarations and definitions. Modeled explicitly because treating it as a
    /// no-op would silently solve a *different* problem than the script asked.
    ResetAssertions,
    /// `(get-assertions)` — request the current assertion stack at this command
    /// point.
    GetAssertions,
}

/// A parsed benchmark script.
#[derive(Debug, Default)]
#[allow(clippy::struct_excessive_bools)] // Independent parser facts, not one state machine.
#[non_exhaustive]
pub struct Script {
    /// Arena holding all parsed terms.
    pub arena: TermArena,
    /// Every asserted formula, in script order (ignoring `push`/`pop` scoping —
    /// for the flat, non-incremental view). Use [`Script::commands`] for the
    /// scoped, incremental sequence.
    pub assertions: Vec<TermId>,
    /// `set-logic` value, if present.
    pub logic: Option<String>,
    /// `(set-info :status ...)` value, if present (benchmark ground truth).
    pub status: Option<String>,
    /// Script metadata from `(set-info :key value)`, keyed by `:key`.
    pub infos: BTreeMap<String, String>,
    /// Script options from `(set-option :key value)`, keyed by `:key`.
    pub options: BTreeMap<String, String>,
    /// Requested `(get-option :key)` queries, in script order.
    pub get_option_keys: Vec<String>,
    /// Requested `(get-info :key)` queries, in script order.
    pub get_info_keys: Vec<String>,
    /// Whether the script requested `(get-model)`.
    pub get_model: bool,
    /// User-declared 0-ary constants that should appear in a model, in
    /// declaration order. Quantifier locals and parser-introduced aliases are not
    /// recorded here.
    pub model_symbols: Vec<SymbolId>,
    /// User-declared n-ary uninterpreted functions that should appear in a model,
    /// in declaration order.
    pub model_functions: Vec<FuncId>,
    /// Number of `check-sat` commands seen.
    pub check_sats: u32,
    /// Per-assertion `:named` label (parallel to [`Script::assertions`]; `None`
    /// when the assertion was not named), for `(get-unsat-core)`.
    pub assertion_names: Vec<Option<String>>,
    /// Terms requested by `(get-value (t …))`, in script order, to be evaluated
    /// against a `sat` model.
    pub get_value_terms: Vec<TermId>,
    /// Optimization objectives `(maximize t)` / `(minimize t)`, in script order;
    /// the flag is `true` for `maximize`, `false` for `minimize` (ADR-pending OMT).
    pub objectives: Vec<(TermId, bool)>,
    /// The ordered `assert`/`push`/`pop`/`check-sat` sequence — the incremental
    /// view of the script (ADR-0009 lifecycle), for per-`check-sat` solving.
    pub commands: Vec<ScriptCommand>,
    /// Whether the script used the bounded string/sequence encoding (ADR-0029) —
    /// a declared `String`/`(Seq E)` symbol or any `str.*`/`seq.*` operator. When
    /// `true`, an `unsat` of the *lowered* query is only `unsat` **within the
    /// encoding bound**; the solver front door must confirm it bound-independent
    /// (see [`Script::len_abstraction_map`]) or report `unknown` (P2.7 A.2).
    pub uses_bounded_strings: bool,
    /// The script contains `PyEx`'s exact length-preserving split/replace/rejoin
    /// spelling. Its source-level routes were historically reached first through
    /// the bounded-cap fallback and can be much cheaper than the admitted packed
    /// encoding, so the solver front door preserves that route order.
    pub prefer_source_string_routes: bool,
    /// The unbounded length-abstraction rewrite map (P2.7 A.2): `original term →
    /// abstracted term` pairs, where a hooked string atom maps to `fresh_bool ∧
    /// implied_length_fact` and a string↔`Int` bridge term (`str.len`,
    /// `str.to_int`, …) maps to its unbounded integer abstraction (a shared
    /// length variable with the `len(x++y) = len(x)+len(y)` homomorphism, or a
    /// free integer). Rewriting an assertion through this map (root-first) yields
    /// a **relaxation** with *no encoding bound*: `unsat` of the rewritten active
    /// assertion stack (plus [`Script::len_abstraction_facts`]) transfers soundly
    /// to the real (unbounded) string semantics.
    pub len_abstraction_map: Vec<(TermId, TermId)>,
    /// Globally-true side facts for the abstraction variables (`len(v) ≥ 0`, a
    /// literal's exact length, …); conjoin with the rewritten assertions.
    pub len_abstraction_facts: Vec<TermId>,
    /// **Encoding-bound** facts (`len(v) ≤ max_len`) — true of the bounded
    /// encoding only, never of the real theory. For the solver's bound-bite
    /// detector: the abstraction being unsatisfiable *with* these while not
    /// provably unsatisfiable *without* them shows the encoding bound bit, so
    /// a bounded `unsat` must downgrade to `unknown`.
    pub len_abstraction_bounds: Vec<TermId>,
    /// A coarsely-abstracted string atom (`str.<`/`str.<=`/`str.in_re`) is
    /// present: the length abstraction may miss a bound bite, so only a
    /// confirmed (abstraction-refuted) `unsat` may pass the gate.
    pub len_abstraction_coarse: bool,
    /// The parser-side **word-equation dual build** (ADR-0053, T-B.4b): a
    /// first-class `Sort::Seq` translation of the script's string fragment,
    /// populated **only** when *every* asserted atom is a word equation /
    /// disequation over `str.++` / string literals / string variables (nothing
    /// else — no `str.len`, `substr`, regex, `contains`, `ite`, or negations
    /// deeper than a single disequality). It is the second-chance route the
    /// solver front door normally reaches after the ADR-0029 bounded pre-check
    /// and ADR-0052 gate return `unknown` (or first for a selectively admitted
    /// [`Script::prefer_source_string_routes`] pipeline): the word-level search
    /// may only ever *add* `sat`, never `unsat`, so a `None` (unrepresentable)
    /// side channel simply leaves the prior verdict untouched. Built into the
    /// same [`Script::arena`]; `String` = `Seq(BitVec(18))` with literals as the
    /// right-associated `seq.unit` code-point chain (matching `axeyum-strings`).
    pub word_problem: Option<WordProblem>,
    /// Set (to the original bounded-parse error's `Display`) when the script was
    /// parsed through the **word-first fallback** (T-B.4d): the bounded ADR-0029
    /// string encoder declined this script wholesale (a literal over
    /// `STRING_MAX_LEN`, a `str.++` result over `STRING_BOUND_CAP`, or another
    /// bounded-encoder capacity/unsupported limit), but the script *is* a pure
    /// word-equation problem, so only the unbounded [`Script::word_problem`] side
    /// channel is populated — [`Script::assertions`]/[`Script::commands`] are empty
    /// and no packed-BV terms exist. The solver front door decides such a script by
    /// the word route alone; on a word-route decline it reproduces this original
    /// error, so a previously-`unsupported` script never silently becomes a bare
    /// `unknown`/`sat`.
    pub word_only_fallback: Option<String>,
    /// The **Boolean-structured word skeleton** (P1.5b): one `Sort::Bool`-sorted
    /// term per top-level `assert`, translating the script's string fragment into
    /// first-class `Seq` equality atoms combined by arbitrary Boolean structure
    /// (`and`/`or`/`not`/`=>`/`xor`/`ite`, `distinct`, `true`/`false`). Where the
    /// flat [`Script::word_problem`] side channel is all-or-nothing over a *top-level
    /// conjunction*, this captures the `or`/negated shapes the conjunction cannot
    /// represent — it is what the online CDCL(T) route
    /// (`axeyum_solver::check_qf_s_online_cdclt`) decides at the front door,
    /// **strictly after** the flat word route declines.
    ///
    /// Populated all-or-nothing (mirroring [`Script::word_problem`]) whenever *every*
    /// asserted term is Boolean structure over `Seq` equalities/disequalities /
    /// `distinct`s (nothing else — no `str.len`, `substr`, regex, extended functions,
    /// or `ite` over strings); empty when any atom escapes that fragment. Built into
    /// the same [`Script::arena`] as `Seq(BitVec(18))` terms, sharing the
    /// `!weq!<name>` string-variable symbols with [`Script::word_problem`]. Carries
    /// no incremental scoping (declined wholesale, same soundness argument as
    /// [`Script::word_problem`]).
    pub word_skeleton: Vec<TermId>,
    /// The word skeleton contains structurally-interned opaque fixed-splice terms.
    /// Such a skeleton is a sound equality relaxation for proving `unsat`, but its
    /// `sat` models need not realize the omitted splice semantics and must be
    /// discarded by the solver front door.
    pub word_skeleton_opaque_terms: usize,
    /// A contradiction proved directly from guaranteed top-level string rewrite
    /// identities, fixed-splice equalities/disequalities, and exact constants.
    /// The proof is computed over the raw SMT-LIB expressions, before bounded
    /// packed-string lowering, so it is valid for unbounded source semantics.
    /// This side fact is
    /// independent of [`Script::word_skeleton`]: an unrelated unsupported atom may
    /// make that all-or-nothing skeleton empty while the source contradiction
    /// remains a valid refutation of the complete asserted conjunction. It is never
    /// populated for incremental or macro-bearing scripts.
    pub source_string_semantic_unsat: bool,
    /// The parser-side **regex-membership side channel** (P2.7 T-C.5, ADR-0054):
    /// a translation of the script's `str.in_re` fragment into single-variable
    /// [`MembershipProblem`](crate::MembershipProblem) constraints over the
    /// code-point symbolic-derivative regex engine. It retains supported asserted
    /// conjuncts (positive/negative `str.in_re` over variables or literals, length
    /// bounds, literal pins, exact `RegLan` aliases, and safe existential output
    /// concatenations) and records whether that subset is complete. The solver
    /// consults it as a second-chance route strictly after the bounded and word
    /// routes decline: a complete problem may add a checked `sat`; a complete or
    /// incomplete conjunctive subset may add `unsat` only behind re-checked
    /// emptiness. Otherwise the prior verdict is left untouched.
    pub membership_problem: Option<crate::MembershipProblem>,
    /// The **membership theory atoms** of the Boolean-structured word skeleton
    /// (P2.7 T-C.6): one entry per distinct `(str.in_re X R)` atom that appears
    /// inside [`Script::word_skeleton`], as `(proxy_atom_term, operand_symbol,
    /// regex)`. The `proxy_atom_term` is a fresh `Sort::Bool` symbol leaf standing
    /// for the atom in the skeleton's Boolean structure; `operand_symbol` is the
    /// `!weq!<name>` `Seq` symbol the membership constrains (shared with the
    /// equality atoms, so word equalities merge membership constraints across
    /// variables); `regex` is the code-point [`Regex`](axeyum_strings::Regex) the
    /// operand must (asserted `true`) or must not (asserted `false`) match.
    ///
    /// Populated in lockstep with [`Script::word_skeleton`] and only for the
    /// single-**variable**-operand fragment (a `str.++`/`substr`/literal operand
    /// collapses the whole skeleton to empty, same all-or-nothing discipline). The
    /// online CDCL(T) route consumes it to decide disjunctive/negated membership
    /// shapes: a per-variable regex-intersection emptiness is a certified theory
    /// conflict, and a `sat` branch is replayed by the reference matcher.
    pub word_skeleton_memberships: Vec<(TermId, SymbolId, axeyum_strings::regex::Regex)>,
    /// The parser-side **lexicographic-order side channel** (P2.7 T-C.6): a
    /// translation of the script's `str.<=` / `str.<` fragment into a Boolean
    /// skeleton over lex-order and word-equality atoms
    /// ([`LexProblem`](axeyum_strings::LexProblem)), populated all-or-nothing over
    /// the recognized fragment (Boolean structure over `str.<=`/`str.<`/`=`/`distinct`
    /// atoms whose operands are words — string literals, declared string variables,
    /// and `str.++` of those; nothing else). The solver consults it as a
    /// second-chance route strictly after the bounded, word, online, and membership
    /// routes decline: it may add a re-checked lexicographic `unsat` (a variable-
    /// independent constant fold or a transitivity + first-character clash), so a
    /// `None` (or an undecided problem) simply leaves the prior verdict untouched. It
    /// never adds `sat` — a satisfiable lex script is already decided by the bounded
    /// encoder (whose `sat` is a concrete short witness).
    pub lex_problem: Option<axeyum_strings::LexProblem>,
    /// The parser-side **length/LIA side channel** (P2.7 Phase A, `LenAbs` SAT
    /// bridge): a faithful, first-class `Seq`-level re-encoding of the script's
    /// `str.len`-coupled fragment — Boolean structure over `Seq` equality atoms
    /// (`=`/`distinct` of string words) and linear-`Int` atoms whose only string
    /// content is `str.len` of a word (`str.++`/literal/variable). Populated
    /// all-or-nothing over exactly that fragment (any regex, `substr`, `str.to_int`,
    /// extended function, or other string operator collapses the whole build to
    /// empty), and only when at least one `str.len` atom is present. The `Seq`
    /// variables share the `!weq!<name>` symbols with the word skeleton, and the
    /// terms use the first-class `Op::SeqLen`/`Op::SeqConcat` IR (so the ground
    /// evaluator replays them).
    ///
    /// The solver consults it as a second-chance route strictly after the bounded,
    /// word, online, membership, and lex routes decline: it links `str.len` to the
    /// LIA solver Nelson-Oppen-style over fresh length variables, and may add a
    /// `sat` — a concrete `Seq`-level witness (each string an `'a'`-fill of its
    /// solved length) that has **replayed against these very assertions through the
    /// ground evaluator** (the sole `sat` gate; a non-replay stays `unknown`). It
    /// never adds `unsat` (the bounded `unsat` gate / `StringGate` already owns the
    /// length-abstraction refutation), so a `None`/empty skeleton or a
    /// non-replaying candidate simply leaves the prior verdict untouched.
    pub length_skeleton: Vec<TermId>,
    /// Which floating-point operators (ADR-0023 `Fpa2Bv`) the script uses, for the
    /// per-query `Fpa2Bv` trust-step sub-case (task #69). FP → BV lowering happens
    /// eagerly at parse time (the `axeyum_fp::*` builder calls scattered through
    /// `parse_term`), so by the time the solver's `QF_BV` evidence path sees the
    /// query it is already bit-vector terms and the FP op-set is lost. This field
    /// preserves the op-set so the text front door
    /// (`axeyum_solver::produce_evidence_smtlib`) can record the fail-closed
    /// `Fpa2Bv` trust step and report which operator families were involved — see
    /// [`FpUsage::fpa2bv_simple_op_certified`]. Populated by a **conservative**
    /// allow-list scan of the raw s-expressions (see `scan_fp_usage`): it can only
    /// ever over-report a non-simple operator (→ certified `false`), never miss one.
    pub fp_usage: FpUsage,
}

/// Which floating-point operators (ADR-0023 `Fpa2Bv`) a parsed script uses.
/// The inventory is diagnostic and supports targeted regression coverage; it
/// does not certify the complete reduction. Both the per-run trust step and the
/// global `TrustId::Fpa2Bv` ledger entry remain uncertified.
///
/// The historical operator-local inventory distinguishes circuits validated at
/// every constructible width from rounding-bearing or otherwise incomplete
/// cases. That inventory is useful for testing, but it does **not** establish
/// faithfulness of the complete FP → BV reduction: quotient-domain equality,
/// congruence, arrays, quantifiers, and model lifting are also obligations. No
/// query currently qualifies for a certified `Fpa2Bv` trust step.
///
/// **Exact bit operations / predicates** (trivially faithful by inspection at any
/// width):
/// - `fp.neg` (flip the sign bit) and `fp.abs` (clear the sign bit);
/// - the five **mutually-exclusive category** predicates `fp.isNaN`,
///   `fp.isInfinite`, `fp.isZero`, `fp.isNormal`, `fp.isSubnormal` — exact
///   exponent/significand field-pattern tests;
/// - the **sign classification** predicates `fp.isNegative` (`sign bit set ∧ ¬NaN`)
///   and `fp.isPositive` (`sign bit clear ∧ ¬NaN`). Their SMT-LIB semantics is
///   *sign-bit* classification, not numeric `x < 0`, so `−0` is negative and `+0`
///   positive; both oracles (Z3, cvc5) agree (`af6c8bf`/GAP-F2 fix).
///
/// **Proven-faithful comparison circuits** `fp.eq`/`fp.lt`/`fp.leq`/`fp.gt`/`fp.geq`
/// — not bit-trivial, but faithful by a **width-independent** argument: `fp.eq` is
/// `¬NaN ∧ (bit-equal ∨ both-zero)`; `fp.lt` is `¬NaN ∧ ¬both-zero ∧ ult(order_key
/// x, order_key y)` where `order_key` is the sign-magnitude → monotone-unsigned
/// transform, correct at any width by the uniform IEEE `[sign][exp][sig]` layout
/// (`leq = lt ∨ eq`, `gt`/`geq` = argument-swapped). The whole comparison logic is
/// **exhaustively** cross-checked at `FP8_E5M2` (all 65 536 pairs vs `rustc_apfloat`,
/// `axeyum-fp/tests/fpa2bv_faithfulness.rs`) plus a second-width F16 witness — so
/// width-parametric code + a proven-monotone key + one exhaustive width ⇒ faithful
/// at every constructible width.
///
/// Every **other** FP operator carries rounding logic and is **not** certified
/// (`fp.add`/`sub`/`mul`/`div`/`rem`/`fma`/`sqrt`/`roundToIntegral`/`min`/`max` and
/// every conversion `to_fp` / `fp.to_ubv` / `fp.to_sbv` / `fp.to_real`). The
/// allow-list is not a block-list, so any unknown / future / rounding-bearing FP
/// operator is treated as non-certified and can never be silently certified.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FpUsage {
    /// The script uses the FP theory at all — an FP sort (`FloatingPoint` /
    /// `Float16`…`Float128`), an FP / rounding-mode literal, or any `fp.*` / `to_fp`
    /// operator — i.e. the `Fpa2Bv` reduction was actually invoked. `false` means no
    /// FP content, so no `Fpa2Bv` trust step applies.
    pub uses_fp: bool,
    /// The distinct FP operator head symbols seen (e.g. `"fp.neg"`, `"fp.add"`,
    /// `"to_fp"`), sorted. Empty when the script only *declares* FP sorts or uses
    /// core operators (`=`/`distinct`/`ite`) over FP terms.
    pub ops: BTreeSet<String>,
}

impl FpUsage {
    /// The operator-local FP validation allow-list (tested at every
    /// *constructible* width — FP formats are guarded to `≤ 128` bits, so the `u128`
    /// sign masks the circuits use never overflow). Any operator head symbol **not**
    /// in this set (including unknown / future `fp.*` operators and every
    /// rounding-bearing op / `to_fp`-style conversion) is treated as non-simple — an
    /// allow-list, not a block-list, so an unrecognized FP operator can never be
    /// mistaken for a validated local circuit. This does not grant whole-reduction
    /// certification. Two local-validation tiers are tracked:
    ///
    /// - **exact bit ops** — `fp.neg`/`fp.abs`, the five category predicates, and the
    ///   sign predicates `fp.isNegative`/`fp.isPositive` (trivially faithful by
    ///   inspection at any width);
    /// - **proven-faithful comparison / selection circuits** — the comparisons
    ///   `fp.eq`/`fp.lt`/`fp.leq`/`fp.gt`/`fp.geq` and the selections `fp.min`/`fp.max`.
    ///   Not bit-trivial, but faithful by a *width-independent* argument: they reduce
    ///   to `¬NaN` guards, the `±0` special-case, and the monotone `order_key`
    ///   (sign-magnitude → monotone-unsigned transform, correct at any width by the
    ///   IEEE `[sign][exp][sig]` layout), exhaustively cross-checked at `FP8_E5M2`
    ///   (all 65 536 pairs for each of `eq`/`lt`/`leq`/`min`/`max`,
    ///   `axeyum-fp/tests/fpa2bv_faithfulness.rs`); the comparisons additionally carry a
    ///   second-width F16 edge witness. `fp.min`/`fp.max` are exact selections (a
    ///   result verbatim, no
    ///   rounding); their SMT-LIB-*unspecified* opposite-sign-zero result uses
    ///   semantic selector bits minted in the **internal** symbol namespace
    ///   (`bv_var_internal`, task #72), so a user `declare` cannot alias them and
    ///   equal argument pairs remain congruent. Width-parametric code +
    ///   a proven-monotone key + an exhaustive width ⇒ faithful at every constructible
    ///   width.
    #[must_use]
    pub fn certified_faithful_op(op: &str) -> bool {
        matches!(
            op,
            "fp.neg"
                | "fp.abs"
                | "fp.isNaN"
                | "fp.isInfinite"
                | "fp.isZero"
                | "fp.isNormal"
                | "fp.isSubnormal"
                | "fp.isNegative"
                | "fp.isPositive"
                | "fp.eq"
                | "fp.lt"
                | "fp.leq"
                | "fp.gt"
                | "fp.geq"
                | "fp.min"
                | "fp.max"
        )
    }

    /// Whether an `Fpa2Bv` `unsat` over this script may carry `certified: true`.
    ///
    /// This is deliberately fail-closed.  Operator-local bit-blast validation is
    /// not a certificate for the complete SMT-LIB FP reduction: the theory has a
    /// single NaN value per format even though there are many IEEE NaN encodings,
    /// and core equality, functions, arrays, quantifiers, and model lifting must
    /// all respect that quotient.  Until the complete reduction has a small
    /// checker, every `Fpa2Bv` step remains an explicit trust hole.
    #[must_use]
    pub fn fpa2bv_simple_op_certified(&self) -> bool {
        false
    }
}

impl Script {
    /// The flat assertion view **only when it is a sound thing to solve directly**.
    ///
    /// Returns `Some(&self.assertions)` for an ordinary script, but **`None` for a
    /// word-first-fallback parse** ([`Script::word_only_fallback`] set) — a script
    /// the bounded encoder declined wholesale, whose [`Script::assertions`] view is
    /// **empty** and whose real content lives only in the parser side channels
    /// ([`Script::word_problem`] / [`Script::word_skeleton`] /
    /// [`Script::word_skeleton_memberships`]).
    ///
    /// # Why this matters (a soundness trap)
    ///
    /// Handing a fallback script's empty `assertions` slice straight to
    /// `check_auto` / `solve` decides the **empty conjunction**, i.e. a **vacuous
    /// `sat`** — a *wrong verdict* for a genuinely-unsat fallback script. This is
    /// exactly the P0 that shipped as `instance1079-re-loop-cong` (unsat, reported
    /// `sat`). Any consumer that parses **arbitrary** SMT-LIB text (a corpus reader,
    /// not a fixed embedded literal) and then solves the flat view must gate on this
    /// helper and route a `None` through the text front door
    /// (`axeyum_solver::solve_smtlib` / `decide_word_only_script`) instead.
    ///
    /// A `Some(view)` may still be empty for a *legitimately* assertion-free script
    /// (e.g. `(check-sat)` with no `assert`) — that empty conjunction really is
    /// `sat`; the hazard is *only* the fallback case, which this helper alone
    /// distinguishes.
    #[must_use]
    pub fn solvable_flat_view(&self) -> Option<&[TermId]> {
        if self.word_only_fallback.is_some() {
            None
        } else {
            Some(&self.assertions)
        }
    }

    /// The flat assertion view for a consumer whose input is **fixed, non-string
    /// text** that can never take the word-first fallback — with the "safe by
    /// construction" claim turned into an **enforced invariant**.
    ///
    /// Returns `&self.assertions`, but `debug_assert!`s that
    /// [`Script::word_only_fallback`] is unset first. This is the structural guard
    /// for the second half of the vacuous-`sat` P0 (`f5b00c72`): a consumer that
    /// parses embedded `QF_BV`/`QF_UF`/`QF_LIA`/`QF_ABV` text and hands the flat view
    /// to `check_auto`/`solve` is safe *only because* that text cannot regress into
    /// the string fallback (whose empty flat view solves to a vacuous `sat`). Reading
    /// the view through this accessor makes that latent assumption a checked one: if
    /// the consumer's text ever grows a string construct that trips the fallback, the
    /// `debug_assert` fires in any test/debug build **instead of silently shipping a
    /// wrong verdict**.
    ///
    /// Use [`Script::solvable_flat_view`] instead for consumers over **arbitrary**
    /// SMT-LIB text (corpus readers): those must *handle* the fallback (route a `None`
    /// through the text front door), not assert it away.
    ///
    /// # Panics
    ///
    /// In debug builds, panics if [`Script::word_only_fallback`] is set — i.e. this
    /// was a word-first-fallback parse and solving its (empty) flat view would be a
    /// vacuous `sat`.
    #[must_use]
    pub fn checked_flat_view(&self) -> &[TermId] {
        debug_assert!(
            self.word_only_fallback.is_none(),
            "checked_flat_view() on a word-first-fallback script: its flat view is EMPTY \
             and solving it directly is a vacuous `sat` (the f5b00c72 P0 class). A consumer \
             over arbitrary SMT-LIB text must use solvable_flat_view()/solve_smtlib and route \
             the word case; only fixed non-string-text consumers may use this accessor."
        );
        &self.assertions
    }
}

/// A first-class `Sort::Seq` word-equation problem accumulated as a side channel
/// while parsing a bounded-strings script (ADR-0053, T-B.4b).
///
/// Every field is over `Seq(BitVec(18))` (`Sort::string()`) terms interned in the
/// owning [`Script::arena`]. This is populated only for the pure word-equation
/// fragment (see [`Script::word_problem`]); the solver runs
/// [`axeyum_strings::solve_word_equations`](https://docs.rs/axeyum-strings) over
/// it and, on a replay-checked `Sat`, upgrades a prior `unknown` verdict to
/// `sat`. It carries **no** `unsat` capability by construction.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct WordProblem {
    /// Asserted equalities `l ≈ r` between `Seq`-sorted concatenations.
    pub equalities: Vec<(TermId, TermId)>,
    /// Asserted disequalities `l ≉ r` between `Seq`-sorted concatenations.
    pub disequalities: Vec<(TermId, TermId)>,
    /// The `Seq`-sorted symbols standing for the script's string variables (the
    /// symbols a returned model binds), in first-declaration order.
    pub seq_symbols: Vec<SymbolId>,
    /// Post-search inversion obligations (task #77). A `str.from_int` / `str.substr`
    /// subterm over a **symbolic** integer argument is replaced by a fresh `Seq`
    /// variable while building the word problem; after the arrangement search binds
    /// that variable to a concrete string, the solver inverts the string value back
    /// onto the integer argument (see [`WordObligation`]). Each obligation is
    /// *sat-implying*: the fresh variable stands for exactly the opaque term, so a
    /// successful inversion (`f(int) == word`) makes replacing the fresh variable by
    /// its defining term a model-preserving substitution. The flat word problem is
    /// built **only** when every assertion is a pure string atom (`build_word_problem`
    /// declines any non-string atom), so the inverted integer carries no competing
    /// arithmetic constraint. A failed inversion leaves the verdict `unknown`.
    pub obligations: Vec<WordObligation>,
    /// Linear integer bounds on the `str.from_int` argument variables (task #78).
    ///
    /// A `str.from_int(i)`-coupled script whose only *non-string* atoms are linear
    /// bounds `i ⋈ c` on the (declared `Int`) `from_int` argument is still decidable
    /// by the word route: the solver couples the `from_int` digit structure to these
    /// bounds by enumerating candidate integers in the bound-satisfying range, pinning
    /// the fresh `Seq` variable to the candidate's canonical decimal, and re-solving the
    /// residual word problem (see `axeyum_solver`'s coupled route). Every bound here is
    /// on a symbol that is *also* a [`WordObligation::FromInt`] `int_sym` — the builder
    /// declines any bound on an integer with no `from_int` coupling — so a chosen
    /// candidate that satisfies every bound and replays the word problem is a genuine
    /// model. A bound the route cannot satisfy leaves the verdict `unknown`; the route
    /// never emits `unsat`.
    pub int_bounds: Vec<IntBound>,
    /// Direct integer pins `sym = v` from folding `str.to_int` of a **constant string**
    /// (task #79). An atom `(= i (str.to_int <literal>))` binds the declared `Int`
    /// variable `i` to the exact SMT-LIB value of `str.to_int <literal>` — a closed,
    /// deterministic computation (all-digit decimal value, or `-1` for a non-digit /
    /// empty literal; leading zeros allowed). Because the string is constant the pin has
    /// no search: it is model-defining by construction, exactly like folding
    /// `str.from_int` of a constant into a string literal.
    ///
    /// The builder accepts a pin **only** when its variable carries no competing
    /// constraint the word route did not see: two pins on one variable must agree
    /// (else the script is declined → `unknown`, never `unsat`), and a pinned variable
    /// must not also be a `str.from_int`/`str.substr` obligation argument or an
    /// [`IntBound`] variable (else decline). Under those gates every pin is a sound,
    /// sat-implying binding the solver copies into the model after a replaying string
    /// arrangement.
    pub int_pins: Vec<(SymbolId, i128)>,
}

/// A relational operator for a linear integer bound `var ⋈ const` (task #78).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntBoundKind {
    /// `var >= const`.
    Ge,
    /// `var > const`.
    Gt,
    /// `var <= const`.
    Le,
    /// `var < const`.
    Lt,
    /// `var = const`.
    Eq,
}

/// A single linear integer bound `sym ⋈ bound` on a `str.from_int` argument
/// (task #78). Recorded by `build_word_problem` for the LIA-coupled word route;
/// `sym` is always a [`WordObligation::FromInt`] `int_sym`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntBound {
    /// The declared `Int` symbol the bound constrains (a `from_int` argument).
    pub sym: SymbolId,
    /// The bound's relational operator.
    pub kind: IntBoundKind,
    /// The integer literal the operator compares against.
    pub bound: i128,
}

/// A post-search integer-inversion obligation for the flat word route (task #77).
///
/// The `Seq`-producing extended function was replaced by a fresh `Seq` variable
/// while building the word problem; after the search assigns that variable a
/// concrete string value, the solver inverts the value to the integer argument the
/// original term requires and binds it in the model. Inversion is *exact* — it only
/// succeeds when the recovered integer reproduces the solved string under the
/// function's SMT-LIB semantics — so the returned `sat` model still replays against
/// the original assertions. A non-invertible value keeps the verdict `unknown`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WordObligation {
    /// The fresh `seq_sym` stands for `(str.from_int int_sym)`. Its solved string
    /// value must be a canonical decimal (`0` or a leading-digit-nonzero numeral) —
    /// inverted to that non-negative integer — or the empty string, inverted to any
    /// negative integer (`-1`). Anything else fails inversion.
    FromInt {
        /// The fresh `Seq` symbol the arrangement search binds.
        seq_sym: SymbolId,
        /// The `Int` symbol the recovered numeral is bound onto.
        int_sym: SymbolId,
    },
    /// The fresh `seq_sym` stands for `(str.substr literal offset len_sym)` with a
    /// constant string `literal` (its code points) and a constant `offset`. Its
    /// solved string value is inverted to the shortest non-negative `len` that
    /// reproduces it under SMT-LIB `str.substr` totality, bound onto `len_sym`.
    Substr {
        /// The fresh `Seq` symbol the arrangement search binds.
        seq_sym: SymbolId,
        /// The constant subject string's Unicode code points.
        literal: Vec<u32>,
        /// The constant offset argument.
        offset: i128,
        /// The `Int` symbol the recovered length is bound onto.
        len_sym: SymbolId,
    },
}

/// Parses an SMT-LIB script.
///
/// # Errors
///
/// [`SmtError::Syntax`] for malformed input, [`SmtError::Unsupported`] for
/// constructs outside the `QF_BV` benchmark slice, and sort errors surfaced
/// as [`SmtError::Ir`].
pub fn parse_script(input: &str) -> Result<Script, SmtError> {
    match parse_script_bounded(input) {
        Ok(script) => Ok(script),
        // Word-first parse fallback (T-B.4d). The bounded ADR-0029 string encoder
        // declined the script *wholesale* — a string literal over
        // `STRING_LITERAL_MAX_LEN`,
        // a `str.++` result over `STRING_BOUND_CAP`, a sequence element over the
        // packed-sort ceiling, or another bounded-encoder capacity/unsupported limit
        // (all surfaced as [`SmtError::Unsupported`], or an [`SmtError::Ir`] width
        // error from packing). These caps are an artifact of the *bounded* encoding,
        // not of the string theory: a pure word-equation problem is decidable
        // unbounded regardless of literal length or concat width. So retry with a
        // word-level-only parse that builds **only** the unbounded
        // [`Script::word_problem`] side channel (no packed-BV terms, no flat
        // assertions). On success the front door decides it by the word route; on
        // failure (not a pure word-equation fragment) the original bounded error is
        // returned unchanged, so bench/consumer classification stays honest.
        //
        // A [`SmtError::Syntax`] is malformed input — never a capacity decline — so
        // it is propagated as-is (no fallback).
        Err(error @ (SmtError::Unsupported(_) | SmtError::Ir(_)))
            if !word_only_fallback_within_stack_budget(input) =>
        {
            Err(error)
        }
        Err(error @ (SmtError::Unsupported(_) | SmtError::Ir(_))) => {
            let allow_semantic_refuter = bounded_capacity_decline(&error);
            match parse_word_only(input, allow_semantic_refuter) {
                Some(mut script) => {
                    script.word_only_fallback = Some(error.to_string());
                    Ok(script)
                }
                None => Err(error),
            }
        }
        Err(error) => Err(error),
    }
}

/// Maximum source nesting reparsed by the optional word-only fallback. The bounded
/// parser has already declined at this point; reparsing much deeper generated terms
/// can exhaust the native stack while recursively translating or destroying their
/// S-expression tree. Returning the original bounded error is fail-closed. The scan
/// ignores parentheses in comments, strings, and quoted symbols.
fn word_only_fallback_within_stack_budget(input: &str) -> bool {
    const MAX_DEPTH: u32 = 2_048;
    let bytes = input.as_bytes();
    let mut depth = 0_u32;
    let mut i = 0_usize;
    let mut string = false;
    let mut quoted = false;
    let mut comment = false;
    while i < bytes.len() {
        let byte = bytes[i];
        if comment {
            comment = byte != b'\n';
        } else if string {
            if byte == b'"' {
                if bytes.get(i + 1) == Some(&b'"') {
                    i += 1;
                } else {
                    string = false;
                }
            }
        } else if quoted {
            quoted = byte != b'|';
        } else {
            match byte {
                b';' => comment = true,
                b'"' => string = true,
                b'|' => quoted = true,
                b'(' => {
                    depth = depth.saturating_add(1);
                    if depth > MAX_DEPTH {
                        return false;
                    }
                }
                b')' => depth = depth.saturating_sub(1),
                _ => {}
            }
        }
        i += 1;
    }
    true
}

/// The bounded ADR-0029 parse: the full slice parser (string literals ≤
/// `STRING_LITERAL_MAX_LEN`, concats ≤ `STRING_BOUND_CAP`, packed-BV model).
/// A capacity/unsupported decline here is what triggers the word-first fallback in
/// [`parse_script`].
fn parse_script_bounded(input: &str) -> Result<Script, SmtError> {
    let mut exprs = read_all(input)?;
    // Finite-set theory: model every `(Set E)` as a `BitVec(W)` over the finite
    // element domain and rewrite the sound subset of set operations to bit-vector
    // operations *in place* on the s-expression tree, before any term is built.
    // A no-op (and no allocation) for scripts that use no sets; an
    // [`SmtError::Unsupported`] for a script whose set usage falls outside the
    // provably-sound subset (see [`desugar_sets`]).
    desugar_sets(&mut exprs)?;
    // Constant-array elimination: a `(select ((as const A) v) i)` always denotes
    // `v` (a const array maps *every* index to `v`), so const-array formulas can be
    // decided without an `Int`-array IR sort by rewriting them away on the
    // s-expression tree, before any term is built. Sound and **sort-agnostic** (the
    // index/element sorts may be `Int`/`Bool`/`BV`); a no-op (and no allocation) for
    // scripts that use no const arrays, and a clean [`SmtError::Unsupported`] for the
    // const-array shapes outside the provably-sound subset (see
    // [`desugar_const_arrays`]).
    desugar_const_arrays(&mut exprs);
    // Bounded finite-sequence theory: build the packed-width → element-width
    // registry for every `(Seq E)` over a fixed-width element sort, once, up front.
    // The map is then immutable for the parse; an empty table is the fast path for
    // sequence-free scripts. A `(Seq E)` over an unsupported element sort makes
    // this a clean [`SmtError::Unsupported`].
    let seq = build_seq_info(&exprs)?;
    // Keep the ordinary 12-byte symbolic window unless a declaration is compared
    // directly with a representable 13-byte literal. This avoids making every
    // unrelated string variable/CNF one byte wider just because one path names a
    // protocol token such as "cache-control".
    let string_symbol_bounds = inferred_string_symbol_bounds(&exprs);
    // Finite fields (QF_FF): build the modeled-width → prime registry for every
    // `(_ FiniteField p)` sort (directly and via `define-sort`), once, up front
    // (mirroring [`build_seq_info`]). A modulus over the bit-width cap, a non-prime
    // "field", or a width collision makes the whole script a clean `Unsupported`.
    let ff = build_ff_info(&exprs)?;
    let split_replace_rejoin_count = count_split_replace_rejoin(&exprs);
    // The unbounded length-abstraction builder (P2.7 A.2): string/sequence
    // operator hooks record abstraction twins as terms are built; exported on
    // the Script at the end. Interior-mutable so it threads as `&LenAbs`
    // (mirroring `SeqInfo`); a no-op for string-free scripts.
    let lenabs = LenAbs {
        admit_split_replace_rejoin: split_replace_rejoin_count <= SPLIT_REPLACE_REJOIN_PACKED_LIMIT,
        ..LenAbs::default()
    };
    let mut script = Script::default();
    let mut aliases: HashMap<String, TermId> = HashMap::new();
    let mut macros: HashMap<String, MacroDef<'_>> = HashMap::new();
    let mut sort_aliases: HashMap<String, Sort> = HashMap::new();
    // `:named` term annotations: `(! t :named foo)` binds `foo` as an alias for
    // the term `t` (SMT-LIB `:named` attribute). The binding is script-global
    // (not lexically scoped), so the map persists across commands; a later bare
    // reference to `foo` resolves to `t`. Declared symbols take precedence (see
    // `parse_atom`), so a real declaration never gets shadowed by a `:named`.
    let mut named: HashMap<String, TermId> = HashMap::new();

    for command in &exprs {
        parse_command(
            &mut script,
            &mut aliases,
            &mut macros,
            &mut sort_aliases,
            &mut named,
            &seq,
            &ff,
            &lenabs,
            &string_symbol_bounds,
            command,
        )?;
    }
    let (len_map, len_facts, len_bounds, len_coarse, ops_used) = lenabs.export();
    script.len_abstraction_map = len_map;
    script.len_abstraction_facts = len_facts;
    script.len_abstraction_bounds = len_bounds;
    script.len_abstraction_coarse = len_coarse;
    script.uses_bounded_strings |= ops_used;
    // Floating-point op-set scan (task #69): record which FP operators the script
    // used so the text front door can decide whether an `Fpa2Bv` `unsat` may carry
    // a certified trust step. Conservative over the raw (already set/const-array
    // desugared) s-expressions — see [`scan_fp_usage`].
    script.fp_usage = scan_fp_usage(&exprs);
    // Eager `seq.nth` Ackermann congruence (ADR-0029 slice 2): two `seq.nth`
    // applications with provably-equal sequence and index operands must return the
    // same (otherwise-unconstrained) out-of-bounds value. The constraints only pin
    // the **fresh** out-of-bounds symbols, so appending them globally is monotone
    // and sound (never turns a genuine `sat` into `unsat`). Added to the flat
    // `assertions` view and, for the incremental view, as an `Assert` before the
    // first `check-sat` so every query sees the function property.
    if let Some(cong) = seq.drain_nth_congruence(&mut script.arena)? {
        script.assertions.push(cong);
        script.assertion_names.push(None);
        let at = script
            .commands
            .iter()
            .position(|c| {
                matches!(
                    c,
                    ScriptCommand::CheckSat | ScriptCommand::CheckSatAssuming(_)
                )
            })
            .unwrap_or(script.commands.len());
        script.commands.insert(at, ScriptCommand::Assert(cong));
    }
    // Parser-side word-equation dual build (ADR-0053, T-B.4b). A minimal,
    // all-or-nothing side channel: only populated for the pure word-equation
    // fragment, and only when the script has no incremental scoping (so the
    // active query at every `check-sat` is a subset of the accumulated
    // assertions — a model of the whole is a model of any subset, keeping the
    // "only ever add sat" invariant sound). `parse_sort`/`(Seq E)` are untouched.
    if script.uses_bounded_strings {
        let source_facts = source_string_semantic_facts(&exprs);
        script.source_string_semantic_unsat = source_facts.conflict;
        script.prefer_source_string_routes =
            split_replace_rejoin_count > 0 || script.source_string_semantic_unsat;
        // The complete bounded parse above has already syntax- and sort-checked
        // every command. Once the exact source analysis proves the active
        // conjunction contradictory, no optional word/membership/lex/length side
        // channel can change that verdict. Return the validated flat script now so
        // the front door consumes the source certificate immediately instead of
        // spending the remaining budget constructing fallback machinery.
        if source_facts.eager_boolean_path_conflict {
            return Ok(script);
        }
        script.word_problem = build_word_problem(&mut script.arena, &exprs);
        // Parser-side Boolean-structured word skeleton (P1.5b): the superset the
        // online CDCL(T) route decides — `or`/negated word problems the flat
        // conjunction side channel above cannot represent. Same all-or-nothing
        // discipline and same shared `!weq!` symbols.
        if let Some(skeleton) = build_word_skeleton(&mut script.arena, &exprs) {
            script.word_skeleton = skeleton.assertions;
            script.word_skeleton_memberships = skeleton.memberships;
            script.word_skeleton_opaque_terms = skeleton.opaque_terms;
        }
        // Parser-side regex-membership side channel (P2.7 T-C.5): the `str.in_re`
        // fragment translated to code-point membership problems for the
        // symbolic-derivative sub-solver (ADR-0054). Same all-or-nothing discipline
        // and shared `!weq!` symbols.
        script.membership_problem = crate::MembershipProblem::build(&mut script.arena, &exprs);
        // Parser-side lexicographic-order side channel (P2.7 T-C.6): the
        // `str.<=`/`str.<` fragment translated to a Boolean skeleton over lex/word-eq
        // atoms for the certified lex-order refuter. Same all-or-nothing discipline.
        script.lex_problem = build_lex_problem(&exprs);
        // Parser-side length/LIA side channel (P2.7 Phase A, `LenAbs` SAT bridge): the
        // `str.len`-coupled fragment re-encoded at the first-class `Seq` level for the
        // length↔LIA route. Same all-or-nothing discipline and shared `!weq!` symbols.
        if let Some(skeleton) = build_length_skeleton(&mut script.arena, &exprs) {
            script.length_skeleton = skeleton;
        }
    }
    Ok(script)
}

/// Conservatively scans the raw s-expressions for floating-point (ADR-0023
/// `Fpa2Bv`) usage and records the operator op-set (task #69).
///
/// FP → BV lowering is eager (at parse time), so the op-set is otherwise lost by
/// the time the solver's `QF_BV` evidence path runs. This walk over the s-expression
/// *tokens* recovers it for the per-query `Fpa2Bv` trust-step decision.
///
/// # Why a token walk is sound-conservative
///
/// Every FP operator appears in the source as a head atom (`fp.add`, `fp.neg`, …)
/// or an indexed head (`(_ fp.to_ubv m)`, `(_ to_fp e s)`). Walking **all** atoms
/// of **all** commands — including `define-fun` / `let` bodies — therefore *sees
/// every FP operator that could ever be built*. The only imprecision is the
/// harmless direction: a `define-fun` body that is never applied still contributes
/// its operator tokens, which can only *add* to [`FpUsage::ops`] and so can only
/// turn a certified `true` into a conservative `false`, never the reverse. Hence
/// [`FpUsage::fpa2bv_simple_op_certified`] never over-certifies.
///
/// FP sorts / literals / rounding modes set [`FpUsage::uses_fp`] (the reduction was
/// invoked) without contributing an operator, so a script that only declares FP
/// vars and uses core `=`/`distinct`/`ite` is still certifiable (sound by the
/// over-approximation argument on [`FpUsage::fpa2bv_simple_op_certified`]).
fn scan_fp_usage(exprs: &[SExpr]) -> FpUsage {
    let mut usage = FpUsage::default();
    // Iterative (no recursion — adversarially deep inputs must not overflow the
    // stack, mirroring the s-expression reader's discipline).
    let mut stack: Vec<&SExpr> = exprs.iter().collect();
    while let Some(node) = stack.pop() {
        match node {
            SExpr::Atom(a) => classify_fp_atom(a, &mut usage),
            SExpr::List(items) => stack.extend(items.iter()),
        }
    }
    usage
}

/// Per-declaration string bounds justified by a direct literal comparison.
fn inferred_string_symbol_bounds(exprs: &[SExpr]) -> BTreeMap<String, u32> {
    let declared: BTreeSet<&str> = exprs.iter().filter_map(declared_string_var).collect();
    let mut bounds = BTreeMap::new();
    let mut stack: Vec<&SExpr> = exprs
        .iter()
        .filter_map(|expression| {
            let [head, body] = expression.list()? else {
                return None;
            };
            (head.atom() == Some("assert")).then_some(body)
        })
        .collect();
    while let Some(expression) = stack.pop() {
        let Some(items) = expression.list() else {
            continue;
        };
        if items.first().and_then(SExpr::atom) == Some("=") {
            for left in 1..items.len() {
                for right in left + 1..items.len() {
                    for (symbol, literal) in
                        [(&items[left], &items[right]), (&items[right], &items[left])]
                    {
                        if let Some(name) = symbol.atom().filter(|name| declared.contains(name))
                            && let Some(length) = adaptive_string_literal_len(literal)
                        {
                            bounds.insert(name.to_owned(), length);
                        }
                    }
                }
            }
        }
        stack.extend(items);
    }
    bounds
}

fn adaptive_string_literal_len(expression: &SExpr) -> Option<u32> {
    let value = literal_pattern_cps(expression)?;
    let length = u32::try_from(value.len()).ok()?;
    (length > STRING_MAX_LEN
        && length <= STRING_LITERAL_MAX_LEN
        && value
            .iter()
            .all(|&code_point| u8::try_from(code_point).is_ok()))
    .then_some(length)
}

/// Classifies a single atom for [`scan_fp_usage`]: records an FP operator into
/// `usage.ops` (and marks `uses_fp`), or marks `uses_fp` for an FP sort / literal /
/// rounding-mode token, or does nothing for a non-FP atom.
fn classify_fp_atom(atom: &str, usage: &mut FpUsage) {
    // Any `fp.*` operator (`fp.add`, `fp.neg`, `fp.isNaN`, `fp.to_ubv`, …). The
    // `fp` literal constructor is a *value* (`(fp #b0 …)`), not an operator, and
    // does not carry the trailing dot — it falls through to the `uses_fp` markers.
    if let Some(rest) = atom.strip_prefix("fp.") {
        debug_assert!(!rest.is_empty());
        usage.uses_fp = true;
        usage.ops.insert(atom.to_owned());
        return;
    }
    match atom {
        // FP-producing conversions that are NOT spelled `fp.*`: `(_ to_fp e s)` and
        // `(_ to_fp_unsigned e s)`. They round, so they are non-simple operators.
        "to_fp" | "to_fp_unsigned" => {
            usage.uses_fp = true;
            usage.ops.insert(atom.to_owned());
        }
        // FP sorts, value literals, and rounding modes: the reduction was invoked,
        // but these contribute no operator to the op-set.
        "FloatingPoint"
        | "Float16"
        | "Float32"
        | "Float64"
        | "Float128"
        | "RoundingMode"
        | "fp"
        | "+zero"
        | "-zero"
        | "+oo"
        | "-oo"
        | "NaN"
        | "roundNearestTiesToEven"
        | "RNE"
        | "roundNearestTiesToAway"
        | "RNA"
        | "roundTowardPositive"
        | "RTP"
        | "roundTowardNegative"
        | "RTN"
        | "roundTowardZero"
        | "RTZ" => {
            usage.uses_fp = true;
        }
        _ => {}
    }
}

/// The word-first fallback parse (T-B.4d): build **only** the unbounded
/// [`WordProblem`] side channel, with no bounded caps (any literal length, any
/// concat width — the `Seq(BitVec(18))` IR is unbounded). Returns `Some(script)`
/// only when the script is the pure word-equation fragment that
/// [`build_word_problem`] recognizes; otherwise `None`, so [`parse_script`] can
/// surface the original bounded error unchanged.
///
/// The returned [`Script`] carries an **empty** flat/incremental assertion view
/// (no packed-BV terms are ever built) and the populated [`Script::word_problem`];
/// `logic`/`status` are recovered by a light scan so the front door still reports
/// the benchmark's own `:status`. [`Script::word_only_fallback`] is set by the
/// caller.
fn parse_word_only(input: &str, allow_semantic_refuter: bool) -> Option<Script> {
    // Re-tokenize and re-run the same s-expression desugars the bounded parse
    // applies before term construction. A set/const-array desugar failure means
    // the script is not a pure word-equation problem, so decline (bounded error
    // stands). `desugar_const_arrays` is infallible.
    let mut exprs = read_all(input).ok()?;
    desugar_sets(&mut exprs).ok()?;
    desugar_const_arrays(&mut exprs);

    let mut script = Script::default();
    // Preserve whole-conjunction semantic contradictions across the bounded-parser
    // decline. The ordinary parse records this flag before solving; the fallback
    // used to rebuild the word routes but silently dropped the same exact fact.
    // Dense PyEx paths can then spend their whole budget in a weaker side channel
    // despite already requiring both `T = U` and `T != U`.
    script.source_string_semantic_unsat =
        allow_semantic_refuter && source_string_semantic_facts(&exprs).conflict;
    // The flat conjunction side channel (may decline on `or`/negation) and the
    // Boolean-structured skeleton (P1.5b, decides the `or`/negated shapes). The
    // fallback is accepted when **either** is representable — a purely disjunctive
    // word problem whose *bounded* parse declined at a length/width cap is still
    // decidable by the online route. The skeleton shares the `!weq!` symbols the flat
    // build declared (`TermArena::declare` is idempotent).
    script.word_problem = build_word_problem(&mut script.arena, &exprs);
    if let Some(skeleton) = build_word_skeleton(&mut script.arena, &exprs) {
        script.word_skeleton = skeleton.assertions;
        script.word_skeleton_memberships = skeleton.memberships;
        script.word_skeleton_opaque_terms = skeleton.opaque_terms;
    }
    // Regex-membership side channel (P2.7 T-C.5): a script whose *bounded* parse
    // declined at a length/loop cap may still be a pure `str.in_re` membership
    // problem the unbounded symbolic-derivative sub-solver decides.
    script.membership_problem = crate::MembershipProblem::build(&mut script.arena, &exprs);
    // Length/LIA side channel (P2.7 Phase A): a script whose *bounded* parse declined
    // at a length/width cap may still be a `str.len`-coupled fragment the length↔LIA
    // route decides (a `sat` witness whose strings exceed the bounded length cap).
    if let Some(skeleton) = build_length_skeleton(&mut script.arena, &exprs) {
        script.length_skeleton = skeleton;
    }
    if script.word_problem.is_none()
        && script.word_skeleton.is_empty()
        && script.membership_problem.is_none()
        && script.length_skeleton.is_empty()
        && !script.source_string_semantic_unsat
    {
        // No decision route recognizes the script — not a word-equation/membership
        // problem and no exact whole-conjunction contradiction; decline so the
        // original bounded error stands.
        return None;
    }
    // The word channel *is* the bounded-string surface for this script; flag it so
    // downstream string-aware code paths recognize it (the front door special-cases
    // `word_only_fallback` before any bounded gate, so this is informational).
    script.uses_bounded_strings = true;

    // Recover `set-logic` / `(set-info :status …)` so `SmtLibOutcome` still carries
    // the script's declared logic and ground-truth status.
    for e in &exprs {
        let Some(items) = e.list() else { continue };
        match items.first().and_then(SExpr::atom) {
            Some("set-logic") => {
                if let Some(logic) = items.get(1).and_then(SExpr::atom) {
                    script.logic = Some(logic.to_owned());
                }
            }
            Some("set-info") => {
                if items.get(1).and_then(SExpr::atom) == Some(":status")
                    && let Some(status) = items.get(2).and_then(SExpr::atom)
                {
                    script.status = Some(status.to_owned());
                }
            }
            _ => {}
        }
    }
    Some(script)
}

/// Whether the bounded parser failed only because a represented string/sequence
/// exceeded a deliberate packing cap. In that case, exact source-level semantic
/// refutation is a valid fallback even when no partial word route accepts the rest
/// of the formula. Other unsupported or IR errors must retain their parse decline:
/// the fallback has not type-checked their terms.
fn bounded_capacity_decline(error: &SmtError) -> bool {
    let SmtError::Unsupported(message) = error else {
        return false;
    };
    message.starts_with("string literal longer than the bounded length")
        || message.contains("result of bounded max length") && message.contains("exceeds the cap")
}

// --- word-equation dual build (ADR-0053, T-B.4b) -----------------------------
//
// Walks the (post-desugar) top-level command s-expressions a *second* time,
// translating the string fragment into first-class `Sort::Seq` terms in the same
// arena. It never touches `parse_sort` or the bounded packed-BV representation —
// it is a strictly additive side channel. The recognized fragment is exactly:
//
//   * string variables: `(declare-const x String)` / `(declare-fun x () String)`;
//   * string expressions: a string literal, a string variable, or `(str.++ …)`
//     over string expressions;
//   * atoms (under top-level `assert` and nested `and`): `(= s t …)` (chained
//     equality), `(distinct s t …)` (pairwise disequality), and `(not (= s t))`
//     (a single disequality), all over string expressions;
//   * **positive-polarity extended-function atoms** (T-B.4c) — each an atom in a
//     top-level conjunction position, reduced to fresh-variable word equations
//     that are *equisatisfiable* with the atom in the real string theory:
//
//         (str.prefixof p x)   →   x = p ++ k          (fresh k)
//         (str.suffixof s x)   →   x = k ++ s          (fresh k)
//         (str.contains x c)   →   x = k1 ++ c ++ k2   (fresh k1, k2)
//
//     Each reduction is *sat-implying*: any witness for the reduced equality
//     makes the original atom true (`(str.prefixof p x)` holds iff `∃k. x=p++k`,
//     etc.), so a replay-checked `Sat` of the reduced problem is a genuine `Sat`
//     of the original script. The fresh `k`/`k1`/`k2` are never added to
//     `seq_symbols`, so they never surface in a returned model.
//
// Anything else — `str.len`, `substr`, regex, `str.at`/anything length-dependent,
// `ite` over strings, a negation deeper than a single disequality, an atom over a
// non-string sort, or any incremental command
// (`push`/`pop`/`check-sat-assuming`/`reset-assertions`) or `define-fun` —
// collapses the whole side channel to `None`. All-or-nothing: a partial
// translation could let a model of the represented subset violate a dropped atom,
// so an unrepresentable atom forbids the whole problem.
//
// **Polarity is tracked conservatively.** The extended-function reductions above
// are sound *only in a positive (top-level-conjunction) position*: under a `not`
// (or any `or`/`ite`/`=>`/iff — none of which the dual build recognizes at all)
// the reduction would be *sat-admitting* rather than sat-implying and could
// fabricate a wrong `sat`. So `word_atom` reaches the extended-function cases only
// on the positive-conjunction recursion (`assert` bodies and the arms of a
// top-level `and`); the `not` branch accepts a single word *disequality* and
// nothing else, and a `(not (str.contains …))` / `(not (str.prefixof …))` — or an
// extended-function atom nested under any unrecognized connective — falls through
// to a wholesale `None`. When in doubt, decline.

/// Builds the [`WordProblem`] side channel from the command s-expressions, or
/// `None` when the script is outside the pure word-equation fragment (see the
/// module comment above).
fn build_word_problem(arena: &mut TermArena, exprs: &[SExpr]) -> Option<WordProblem> {
    // Incremental scoping or macros put the "active subset ⊆ all asserts"
    // soundness argument out of reach — decline wholesale.
    for e in exprs {
        if let Some(
            "push" | "pop" | "check-sat-assuming" | "reset-assertions" | "define-fun"
            | "define-fun-rec" | "define-funs-rec" | "define-sort",
        ) = e.list().and_then(|l| l.first()).and_then(SExpr::atom)
        {
            return None;
        }
    }

    // Collect declared string variables → one fresh `Seq`-sorted symbol each.
    let mut vars: BTreeMap<String, (SymbolId, TermId)> = BTreeMap::new();
    let mut order: Vec<SymbolId> = Vec::new();
    for e in exprs {
        if let Some(name) = declared_string_var(e)
            && !vars.contains_key(name)
        {
            let sym = arena
                .declare_internal(&format!("!weq!{name}"), Sort::string())
                .ok()?;
            let term = arena.var(sym);
            vars.insert(name.to_owned(), (sym, term));
            order.push(sym);
        }
    }

    // Collect declared `Int` variables → their own `Int` symbols. These name the
    // integer arguments of any `str.from_int`/`str.substr` opaque subterm (task #77);
    // an obligation binds the recovered numeral onto exactly these symbols. Sharing
    // the real name keeps a returned model's integer bindings aligned with the script.
    let mut int_vars: BTreeMap<String, SymbolId> = BTreeMap::new();
    for e in exprs {
        if let Some(name) = declared_int_var(e)
            && !int_vars.contains_key(name)
        {
            let sym = arena.declare(name, Sort::Int).ok()?;
            int_vars.insert(name.to_owned(), sym);
        }
    }

    // Translate every assertion; a single unrepresentable atom aborts the whole.
    // `next_k` names the fresh `Seq` variables introduced by the positive-polarity
    // extended-function reductions (prefixof/suffixof/contains); it threads across
    // all assertions so every fresh symbol is globally unique.
    let mut wp = WordProblem::default();
    let mut next_k: u32 = 0;
    let mut opaque = OpaqueCtx {
        int_vars: &int_vars,
        intern: BTreeMap::new(),
        next: 0,
    };
    for e in exprs {
        let Some(items) = e.list() else { continue };
        if items.first().and_then(SExpr::atom) == Some("assert") {
            let [_, body] = items else { return None };
            if !word_atom(arena, body, &vars, &mut wp, &mut next_k, &mut opaque) {
                return None;
            }
        }
    }

    if wp.equalities.is_empty() && wp.disequalities.is_empty() {
        return None;
    }

    // Task #78 soundness gate: an integer bound is only sound to *accept* (rather than
    // decline the whole script on) when its variable is a `str.from_int` argument the
    // coupled word route can drive. A bound on an integer with no `from_int` coupling
    // has no string channel to enforce it, so admitting it would risk a wrong `sat` —
    // decline the whole word problem instead (the bounded parse error stands → unknown).
    if !wp.int_bounds.is_empty() {
        let from_int_args: BTreeSet<SymbolId> = wp
            .obligations
            .iter()
            .filter_map(|ob| match ob {
                WordObligation::FromInt { int_sym, .. } => Some(*int_sym),
                WordObligation::Substr { .. } => None,
            })
            .collect();
        if !wp.int_bounds.iter().all(|b| from_int_args.contains(&b.sym)) {
            return None;
        }
    }

    // Task #79 soundness gates for constant `str.to_int` pins. A pin `i = to_int(lit)` is
    // model-defining only when `i` carries no competing constraint the word route did not
    // model: (1) two pins on one variable must agree — a disagreement makes the script
    // unsat, which this route never claims, so decline to `unknown`; (2) a pinned variable
    // must not also be a `str.from_int`/`str.substr` obligation argument or an integer-bound
    // variable, or the recovered/bounded integer could contradict the pin. Any overlap or
    // conflict declines the whole word problem (the bounded parse error stands → `unknown`).
    if !wp.int_pins.is_empty() {
        let mut pinned: BTreeMap<SymbolId, i128> = BTreeMap::new();
        for &(sym, val) in &wp.int_pins {
            match pinned.insert(sym, val) {
                Some(prev) if prev != val => return None, // conflicting pins → unknown
                _ => {}
            }
        }
        let obligation_ints: BTreeSet<SymbolId> = wp
            .obligations
            .iter()
            .map(|ob| match ob {
                WordObligation::FromInt { int_sym, .. } => *int_sym,
                WordObligation::Substr { len_sym, .. } => *len_sym,
            })
            .collect();
        let bound_ints: BTreeSet<SymbolId> = wp.int_bounds.iter().map(|b| b.sym).collect();
        if pinned
            .keys()
            .any(|s| obligation_ints.contains(s) || bound_ints.contains(s))
        {
            return None;
        }
    }

    wp.seq_symbols = order;
    Some(wp)
}

/// Builds the [`Script::word_skeleton`] (P1.5b): the Boolean-structured superset of
/// [`build_word_problem`]. Each top-level `assert` body is translated into one
/// `Sort::Bool`-sorted term over first-class `Seq` equality atoms, preserving the
/// full Boolean structure (`and`/`or`/`not`/`=>`/`xor`/`ite`, `distinct`,
/// `true`/`false`) that the flat conjunction side channel flattens away. Returns
/// `None` (all-or-nothing) when the script falls outside the fragment — any
/// non-string atom, an `ite`/read over strings, `str.len`/`substr`/regex/extended
/// functions, or any incremental scoping. Declared Boolean symbols are retained
/// exactly, including Boolean equalities used as aliases for string atoms.
///
/// **Soundness.** The online route only ever *adds* a verdict (a certified theory
/// `unsat` or a replay-checked `sat`, see `axeyum_solver::check_qf_s_online_cdclt`),
/// so a `None` skeleton simply leaves the prior verdict untouched. Unlike
/// [`build_word_problem`], the *sat-implying* fresh-variable word reductions of
/// `prefixof`/`suffixof`/`contains` are **not** performed here — those are sound
/// only in a positive (top-level-conjunction) position. Instead, a `prefixof` /
/// `suffixof` / `contains` atom whose **pattern is a string constant** and whose
/// **subject is a single declared variable** is translated into an *exact regex
/// membership* (`P·Σ*` / `Σ*·S` / `Σ*·C·Σ*`); a membership atom is
/// polarity-symmetric (the online route complements the language for the negative
/// literal), so this is sound in any Boolean context (P2.7 Phase D). A
/// variable/compound pattern or a compound subject still collapses the skeleton to
/// `None`. Incremental scoping is declined for the same reason as
/// [`build_word_problem`] (the active query at a `check-sat` would be a subset, so a
/// whole-conjunction `unsat` need not transfer).
fn build_word_skeleton(arena: &mut TermArena, exprs: &[SExpr]) -> Option<WordSkeleton> {
    // Incremental scoping / macros put the "active subset ⊆ all asserts" soundness
    // argument out of reach — decline wholesale (mirrors `build_word_problem`).
    for e in exprs {
        if let Some(
            "push" | "pop" | "check-sat-assuming" | "reset-assertions" | "define-fun"
            | "define-fun-rec" | "define-funs-rec" | "define-sort",
        ) = e.list().and_then(|l| l.first()).and_then(SExpr::atom)
        {
            return None;
        }
    }

    // A generated path can assert both that one exact string view is empty and
    // that the same view contains a non-empty literal. This is a complete,
    // source-level contradiction independent of the view's construction. Catch it
    // before compiling hundreds of overlapping regular languages: the dense PyEx
    // `entry-disposition` family otherwise spends the full query budget rediscovering
    // this two-atom conflict through general derivative intersection.
    if guaranteed_empty_contains_conflict(exprs) {
        let empty = arena.seq_empty(ArraySortKey::BitVec(Sort::STRING_ELEM_WIDTH));
        let reflexive = arena.eq(empty, empty).ok()?;
        let contradiction = arena.not(reflexive).ok()?;
        return Some(WordSkeleton {
            assertions: vec![contradiction],
            memberships: Vec::new(),
            opaque_terms: 0,
        });
    }

    // Declared string variables → the shared fresh `Seq`-sorted symbols (idempotent
    // with `build_word_problem`: `TermArena::declare` returns the existing symbol for
    // a matching name+sort, so the two builds share `!weq!<name>`).
    let mut vars: BTreeMap<String, (SymbolId, TermId)> = BTreeMap::new();
    for e in exprs {
        if let Some(name) = declared_string_var(e)
            && !vars.contains_key(name)
        {
            let sym = arena
                .declare_internal(&format!("!weq!{name}"), Sort::string())
                .ok()?;
            let term = arena.var(sym);
            vars.insert(name.to_owned(), (sym, term));
        }
    }

    // Declared Boolean variables stay first-class Boolean skeleton leaves. Kaluza
    // and similar symbolic-execution corpora name string predicates through chains
    // such as `(= T_1 (not (= x "")))` followed by `(assert T_1)`. Retaining the
    // aliases is an exact Boolean re-encoding; the online route still treats only
    // the nested Seq equalities as theory atoms and replay-checks the whole skeleton.
    let mut bool_vars: BTreeMap<String, TermId> = BTreeMap::new();
    for e in exprs {
        if let Some(name) = declared_bool_var(e)
            && !bool_vars.contains_key(name)
        {
            let sym = arena.declare(name, Sort::Bool).ok()?;
            bool_vars.insert(name.to_owned(), arena.var(sym));
        }
    }

    // Translate every `assert` body into a Bool term over `Seq` equality and
    // `str.in_re` membership atoms; a single unrepresentable atom aborts the whole
    // skeleton. `mem` accumulates the membership theory atoms (deduplicated).
    let semantic_facts = source_string_semantic_facts(exprs);
    let mut assertions: Vec<TermId> = Vec::new();
    let mut saw_seq_atom = semantic_facts.conflict;
    if semantic_facts.conflict {
        assertions.push(arena.bool_const(false));
    }
    let mut mem = MembershipCollector {
        intern: BTreeMap::new(),
        memberships: Vec::new(),
        next: 0,
        concat_defs: Vec::new(),
        next_concat: 0,
        opaque_words: Vec::new(),
        next_opaque: 0,
        pinned_words: semantic_facts.pinned_words,
    };
    for (left, right) in semantic_facts.derived_equalities {
        let [left, right] = word_terms_with_opaque(arena, &[left, right], &vars, &mut mem)?[..]
        else {
            return None;
        };
        mem.concat_defs.push(arena.eq(left, right).ok()?);
        saw_seq_atom = true;
    }
    let conjuncts = guaranteed_top_level_conjuncts(exprs);
    if conjuncts.len() > 2_048 {
        return None;
    }
    for body in conjuncts {
        let t = word_bool(arena, body, &vars, &bool_vars, &mut saw_seq_atom, &mut mem)?;
        assertions.push(t);
    }

    // Conjoin the definitional equations minted for `str.in_re` over `str.++`
    // subjects (`!inre_arg!k = <concat>`) as unconditional top-level assertions —
    // they name the concatenation the membership constrains and must hold in the
    // model the online route replays.
    assertions.extend(mem.concat_defs.iter().copied());

    // Keep pathological generated conjunctions below the depth at which the
    // downstream SAT driver can overflow the native call stack while preparing
    // clauses. This route is optional: declining preserves the original bounded
    // parse error as `unknown`, whereas admitting an unsafe skeleton can abort the
    // competition process. Dense PyEx rows that move the population are well below
    // this ceiling (roughly 600 conjuncts in the measured family).
    if assertions.len() > 2_048 {
        return None;
    }

    // Require at least one genuine `Seq` equality atom **or** a membership atom —
    // otherwise this is not a string problem the online route can decide.
    if assertions.is_empty() || (!saw_seq_atom && mem.memberships.is_empty()) {
        return None;
    }
    Some(WordSkeleton {
        assertions,
        memberships: mem.memberships,
        opaque_terms: mem.opaque_words.len(),
    })
}

/// The result of [`build_word_skeleton`]: the Boolean-structured assertions plus
/// the membership theory atoms they reference (see
/// [`Script::word_skeleton_memberships`]).
struct WordSkeleton {
    assertions: Vec<TermId>,
    memberships: Vec<(TermId, SymbolId, axeyum_strings::regex::Regex)>,
    opaque_terms: usize,
}

/// The declared name of a 0-ary `Int`-sorted symbol, if `e` is such a declaration
/// (`(declare-const n Int)` or `(declare-fun n () Int)`). The `Int` counterpart of
/// [`declared_string_var`], for the length/LIA skeleton's linear-integer variables.
fn declared_int_var(e: &SExpr) -> Option<&str> {
    let items = e.list()?;
    match items.first().and_then(SExpr::atom)? {
        "declare-const" if items.len() == 3 => {
            (items[2].atom() == Some("Int")).then(|| items[1].atom())?
        }
        "declare-fun" if items.len() == 4 => {
            let empty_params = items[2].list().is_some_and(<[SExpr]>::is_empty);
            (empty_params && items[2].list().is_some() && items[3].atom() == Some("Int"))
                .then(|| items[1].atom())?
        }
        _ => None,
    }
}

/// The declared name of a 0-ary `Bool`-sorted symbol, if `e` is such a
/// declaration (`(declare-const p Bool)` or `(declare-fun p () Bool)`).
fn declared_bool_var(e: &SExpr) -> Option<&str> {
    let items = e.list()?;
    match items.first().and_then(SExpr::atom)? {
        "declare-const" if items.len() == 3 => {
            (items[2].atom() == Some("Bool")).then(|| items[1].atom())?
        }
        "declare-fun" if items.len() == 4 => {
            let empty_params = items[2].list().is_some_and(<[SExpr]>::is_empty);
            (empty_params && items[2].list().is_some() && items[3].atom() == Some("Bool"))
                .then(|| items[1].atom())?
        }
        _ => None,
    }
}

/// Builds the [`Script::length_skeleton`] (P2.7 Phase A, `LenAbs` SAT bridge): a
/// faithful first-class `Seq`-level re-encoding of the script's `str.len`-coupled
/// fragment, so the length↔LIA route can add a `sat` witness that the bounded
/// packed encoder (length-capped at [`STRING_MAX_LEN`]) cannot represent.
///
/// Each top-level `assert` body is translated into one `Sort::Bool` term over
/// **`Seq` equality atoms** (`=`/`distinct` of string words — literals, declared
/// string variables, `str.++` of those) and **linear-`Int` atoms** (`=`/`distinct`/
/// `<`/`<=`/`>`/`>=` over `Int` expressions whose only string content is
/// `str.len`/`seq.len` of a word, alongside `Int` literals, declared `Int`
/// variables, and `+`/`-`/`*`), preserving the full Boolean structure
/// (`and`/`or`/`not`/`=>`/`xor`/`ite`). Returns `None` (all-or-nothing) on any atom
/// outside that fragment — regex, `substr`, `str.to_int`/`to_code`, `str.at`,
/// `indexof`, extended functions, a non-`Seq`/non-`Int` atom, a bare Boolean leaf,
/// or any incremental scoping — and also when **no** `str.len` atom is present (a
/// pure word or pure LIA problem is left to those routes).
///
/// **Soundness.** The terms use the first-class `Op::SeqLen`/`Op::SeqConcat`/`Seq`
/// symbols, so the ground evaluator replays them exactly; the skeleton is a
/// *faithful* re-encoding of the assert bodies (same models), so replaying it
/// equals replaying the original assertions. The length↔LIA route only ever *adds*
/// a replay-checked `sat` (never `unsat`, never overriding a decided verdict), so a
/// `None` skeleton simply leaves the prior verdict untouched. Incremental scoping
/// is declined for the same "active subset ⊆ all asserts" reason as
/// [`build_word_skeleton`].
fn build_length_skeleton(arena: &mut TermArena, exprs: &[SExpr]) -> Option<Vec<TermId>> {
    for e in exprs {
        if let Some(
            "push" | "pop" | "check-sat-assuming" | "reset-assertions" | "define-fun"
            | "define-fun-rec" | "define-funs-rec" | "define-sort",
        ) = e.list().and_then(|l| l.first()).and_then(SExpr::atom)
        {
            return None;
        }
    }

    // Declared string variables → the shared fresh `!weq!<name>` `Seq` symbols
    // (idempotent with the word skeleton via `TermArena::declare`).
    let mut seq_vars: BTreeMap<String, (SymbolId, TermId)> = BTreeMap::new();
    for e in exprs {
        if let Some(name) = declared_string_var(e)
            && !seq_vars.contains_key(name)
        {
            let sym = arena
                .declare_internal(&format!("!weq!{name}"), Sort::string())
                .ok()?;
            let term = arena.var(sym);
            seq_vars.insert(name.to_owned(), (sym, term));
        }
    }
    // Declared `Int` variables → the script's own `Int` symbols (idempotent
    // `declare`; the length skeleton is solved and replayed in isolation, so
    // sharing the real symbol is harmless and keeps the model bindings aligned).
    let mut int_vars: BTreeMap<String, (SymbolId, TermId)> = BTreeMap::new();
    for e in exprs {
        if let Some(name) = declared_int_var(e)
            && !int_vars.contains_key(name)
        {
            let sym = arena.declare(name, Sort::Int).ok()?;
            let term = arena.var(sym);
            int_vars.insert(name.to_owned(), (sym, term));
        }
    }

    let mut assertions: Vec<TermId> = Vec::new();
    let mut saw_len = false;
    for e in exprs {
        let Some(items) = e.list() else { continue };
        if items.first().and_then(SExpr::atom) == Some("assert") {
            let [_, body] = items else { return None };
            let t = length_bool(arena, body, &seq_vars, &int_vars, &mut saw_len)?;
            assertions.push(t);
        }
    }
    // Require at least one `str.len` atom — otherwise this is not the length-coupled
    // fragment this route targets (a pure word/LIA problem is left to those routes).
    if assertions.is_empty() || !saw_len {
        return None;
    }
    Some(assertions)
}

/// Translates a Boolean body into a `Sort::Bool` term over `Seq` equality and
/// linear-`Int` atoms for [`build_length_skeleton`]. Returns `None` on anything
/// outside the length-coupled fragment (aborting the whole all-or-nothing build).
/// Sets `saw_len` when a `str.len`/`seq.len` atom is encountered.
fn length_bool(
    arena: &mut TermArena,
    e: &SExpr,
    seq_vars: &BTreeMap<String, (SymbolId, TermId)>,
    int_vars: &BTreeMap<String, (SymbolId, TermId)>,
    saw_len: &mut bool,
) -> Option<TermId> {
    match e.atom() {
        Some("true") => return Some(arena.bool_const(true)),
        Some("false") => return Some(arena.bool_const(false)),
        _ => {}
    }
    let items = e.list()?;
    let head = items.first().and_then(SExpr::atom)?;
    match head {
        "and" | "or" | "xor" if items.len() >= 2 => {
            let mut acc = length_bool(arena, &items[1], seq_vars, int_vars, saw_len)?;
            for it in &items[2..] {
                let next = length_bool(arena, it, seq_vars, int_vars, saw_len)?;
                acc = match head {
                    "and" => arena.and(acc, next).ok()?,
                    "or" => arena.or(acc, next).ok()?,
                    _ => arena.xor(acc, next).ok()?,
                };
            }
            Some(acc)
        }
        "=>" if items.len() >= 3 => {
            let mut acc = length_bool(arena, items.last()?, seq_vars, int_vars, saw_len)?;
            for it in items[1..items.len() - 1].iter().rev() {
                let ante = length_bool(arena, it, seq_vars, int_vars, saw_len)?;
                acc = arena.implies(ante, acc).ok()?;
            }
            Some(acc)
        }
        "not" if items.len() == 2 => {
            let inner = length_bool(arena, &items[1], seq_vars, int_vars, saw_len)?;
            arena.not(inner).ok()
        }
        "ite" if items.len() == 4 => {
            let c = length_bool(arena, &items[1], seq_vars, int_vars, saw_len)?;
            let t = length_bool(arena, &items[2], seq_vars, int_vars, saw_len)?;
            let f = length_bool(arena, &items[3], seq_vars, int_vars, saw_len)?;
            arena.ite(c, t, f).ok()
        }
        // `(= a b …)` — a chained equality that is **either** all `Seq` words or all
        // `Int` expressions. Try the `Seq` reading first (word operands), then `Int`.
        "=" if items.len() >= 3 => length_equality(arena, &items[1..], seq_vars, int_vars, saw_len),
        // `(distinct a b …)` — pairwise disequality over `Seq` words or `Int` exprs.
        "distinct" if items.len() >= 3 => {
            let terms = match word_terms(arena, &items[1..], seq_vars) {
                Some(terms) => terms,
                None => length_int_terms(arena, &items[1..], seq_vars, int_vars, saw_len)?,
            };
            let mut acc: Option<TermId> = None;
            for i in 0..terms.len() {
                for &t in &terms[i + 1..] {
                    let atom = arena.eq(terms[i], t).ok()?;
                    let diseq = arena.not(atom).ok()?;
                    acc = Some(match acc {
                        None => diseq,
                        Some(prev) => arena.and(prev, diseq).ok()?,
                    });
                }
            }
            acc
        }
        // Linear-`Int` order comparisons — chained (`(< a b c)` ⇒ `a<b ∧ b<c`).
        "<" | "<=" | ">" | ">=" if items.len() >= 3 => {
            let terms = length_int_terms(arena, &items[1..], seq_vars, int_vars, saw_len)?;
            let mut acc: Option<TermId> = None;
            for w in terms.windows(2) {
                let atom = match head {
                    "<" => arena.int_lt(w[0], w[1]),
                    "<=" => arena.int_le(w[0], w[1]),
                    ">" => arena.int_gt(w[0], w[1]),
                    _ => arena.int_ge(w[0], w[1]),
                }
                .ok()?;
                acc = Some(match acc {
                    None => atom,
                    Some(prev) => arena.and(prev, atom).ok()?,
                });
            }
            acc
        }
        _ => None,
    }
}

fn length_equality(
    arena: &mut TermArena,
    operands: &[SExpr],
    seq_vars: &BTreeMap<String, (SymbolId, TermId)>,
    int_vars: &BTreeMap<String, (SymbolId, TermId)>,
    saw_len: &mut bool,
) -> Option<TermId> {
    if let [left, right] = operands {
        if let Some(indicator) =
            length_int_ite_const_equality(arena, left, right, seq_vars, int_vars, saw_len)
        {
            return Some(indicator);
        }
        if let Some(indicator) =
            length_int_ite_const_equality(arena, right, left, seq_vars, int_vars, saw_len)
        {
            return Some(indicator);
        }
    }
    let terms = match word_terms(arena, operands, seq_vars) {
        Some(terms) => terms,
        None => length_int_terms(arena, operands, seq_vars, int_vars, saw_len)?,
    };
    let mut acc: Option<TermId> = None;
    for &term in &terms[1..] {
        let atom = arena.eq(terms[0], term).ok()?;
        acc = Some(match acc {
            None => atom,
            Some(previous) => arena.and(previous, atom).ok()?,
        });
    }
    acc
}

/// Inverts an integer-valued Boolean indicator for the length/LIA side channel.
/// This is the S-expression counterpart of [`int_ite_const_equality`]: generated
/// scripts commonly wrap a length predicate as `(ite p 1 0)` and immediately
/// compare it with a constant. Exact constant branches reduce the equality to
/// `true`, `false`, `p`, or `not p`, preserving the original Boolean formula.
fn length_int_ite_const_equality(
    arena: &mut TermArena,
    candidate: &SExpr,
    target: &SExpr,
    seq_vars: &BTreeMap<String, (SymbolId, TermId)>,
    int_vars: &BTreeMap<String, (SymbolId, TermId)>,
    saw_len: &mut bool,
) -> Option<TermId> {
    let target_value = parse_int_literal(target)?;
    let ite = candidate.list()?;
    if ite.len() != 4 || ite[0].atom() != Some("ite") {
        return None;
    }
    let then_value = parse_int_literal(&ite[2])?;
    let else_value = parse_int_literal(&ite[3])?;
    let condition = length_bool(arena, &ite[1], seq_vars, int_vars, saw_len)?;
    match (then_value == target_value, else_value == target_value) {
        (true, true) => Some(arena.bool_const(true)),
        (false, false) => Some(arena.bool_const(false)),
        (true, false) => Some(condition),
        (false, true) => arena.not(condition).ok(),
    }
}

/// Translates every element of `exprs` as a linear-`Int` expression for
/// [`length_bool`], returning `None` if any is not one.
fn length_int_terms(
    arena: &mut TermArena,
    exprs: &[SExpr],
    seq_vars: &BTreeMap<String, (SymbolId, TermId)>,
    int_vars: &BTreeMap<String, (SymbolId, TermId)>,
    saw_len: &mut bool,
) -> Option<Vec<TermId>> {
    exprs
        .iter()
        .map(|e| length_int_expr(arena, e, seq_vars, int_vars, saw_len))
        .collect()
}

/// Translates one `Int`-sorted expression for the length skeleton: an `Int`
/// literal, a declared `Int` variable, `str.len`/`seq.len` of a word (the only
/// string content allowed), or `+`/`-`/`*` over such expressions. Returns `None`
/// for anything else. Sets `saw_len` on a length atom.
fn length_int_expr(
    arena: &mut TermArena,
    e: &SExpr,
    seq_vars: &BTreeMap<String, (SymbolId, TermId)>,
    int_vars: &BTreeMap<String, (SymbolId, TermId)>,
    saw_len: &mut bool,
) -> Option<TermId> {
    match e {
        SExpr::Atom(a) => {
            if let Ok(n) = a.parse::<i128>() {
                Some(arena.int_const(n))
            } else {
                int_vars.get(a).map(|&(_, term)| term)
            }
        }
        SExpr::List(items) => {
            let head = items.first().and_then(SExpr::atom)?;
            match head {
                "str.len" | "seq.len" if items.len() == 2 => {
                    let s = word_str_expr(arena, &items[1], seq_vars)?;
                    *saw_len = true;
                    arena.seq_len(s).ok()
                }
                "+" if items.len() >= 2 => {
                    let mut acc = length_int_expr(arena, &items[1], seq_vars, int_vars, saw_len)?;
                    for it in &items[2..] {
                        let next = length_int_expr(arena, it, seq_vars, int_vars, saw_len)?;
                        acc = arena.int_add(acc, next).ok()?;
                    }
                    Some(acc)
                }
                // Unary `(- a)` is negation; `(- a b …)` is left-folded subtraction.
                "-" if items.len() == 2 => {
                    let a = length_int_expr(arena, &items[1], seq_vars, int_vars, saw_len)?;
                    arena.int_neg(a).ok()
                }
                "-" if items.len() >= 3 => {
                    let mut acc = length_int_expr(arena, &items[1], seq_vars, int_vars, saw_len)?;
                    for it in &items[2..] {
                        let next = length_int_expr(arena, it, seq_vars, int_vars, saw_len)?;
                        acc = arena.int_sub(acc, next).ok()?;
                    }
                    Some(acc)
                }
                "*" if items.len() >= 2 => {
                    let mut acc = length_int_expr(arena, &items[1], seq_vars, int_vars, saw_len)?;
                    for it in &items[2..] {
                        let next = length_int_expr(arena, it, seq_vars, int_vars, saw_len)?;
                        acc = arena.int_mul(acc, next).ok()?;
                    }
                    Some(acc)
                }
                _ => None,
            }
        }
    }
}

/// Builds the [`Script::lex_problem`] (P2.7 T-C.6): the Boolean skeleton over
/// `str.<=` / `str.<` and word-equality atoms that the certified lexicographic-order
/// refuter decides.
///
/// All-or-nothing (mirroring [`build_word_skeleton`]): every `assert` body must be
/// Boolean structure (`and`/`or`/`not`/`=>`/`xor`/`ite`/`true`/`false`) over lex-order
/// atoms (`str.<`/`str.<=`), word equalities (`=`), and word disequalities
/// (`distinct`/`not =`), whose operands are **words** — string literals, declared
/// string variables, and `str.++` of those. Any other atom (`str.len`, `substr`,
/// regex, extended functions, a non-string `=`, incremental scoping) declines the
/// whole build (`None`). Requires at least one genuine lex-order atom — a pure
/// word-equation problem is left to the word/online routes.
///
/// **Soundness.** The refuter only ever *adds* a re-checked `unsat` to an `unknown`
/// (never `sat`, never overriding a decided verdict), so a `None` skeleton simply
/// leaves the prior verdict untouched. Incremental scoping is declined for the same
/// reason as [`build_word_skeleton`].
fn build_lex_problem(exprs: &[SExpr]) -> Option<axeyum_strings::LexProblem> {
    // Incremental scoping / macros put the "active subset ⊆ all asserts" soundness
    // argument out of reach — decline wholesale (mirrors `build_word_skeleton`).
    for e in exprs {
        if let Some(
            "push" | "pop" | "check-sat-assuming" | "reset-assertions" | "define-fun"
            | "define-fun-rec" | "define-funs-rec" | "define-sort",
        ) = e.list().and_then(|l| l.first()).and_then(SExpr::atom)
        {
            return None;
        }
    }

    // Declared string variables (identity keys for the word segments).
    let mut vars: BTreeSet<String> = BTreeSet::new();
    for e in exprs {
        if let Some(name) = declared_string_var(e) {
            vars.insert(name.to_owned());
        }
    }

    let mut atoms: Vec<axeyum_strings::LexAtom> = Vec::new();
    let mut assertions: Vec<axeyum_strings::LexFormula> = Vec::new();
    let mut saw_lex = false;
    for e in exprs {
        let Some(items) = e.list() else { continue };
        if items.first().and_then(SExpr::atom) == Some("assert") {
            let [_, body] = items else { return None };
            let f = lex_bool(body, &vars, &mut atoms, &mut saw_lex)?;
            assertions.push(f);
        }
    }
    if assertions.is_empty() || !saw_lex {
        return None;
    }
    Some(axeyum_strings::LexProblem { atoms, assertions })
}

/// Interns a lex/equality atom into `atoms`, returning its index (structural
/// deduplication so a repeated atom shares one entry / one folded valuation).
fn intern_lex_atom(
    atoms: &mut Vec<axeyum_strings::LexAtom>,
    atom: axeyum_strings::LexAtom,
) -> usize {
    if let Some(i) = atoms.iter().position(|a| *a == atom) {
        return i;
    }
    atoms.push(atom);
    atoms.len() - 1
}

/// The flattened word of `e` (a `Vec` of literal code points and variable spans),
/// or `None` if `e` is outside the word fragment.
fn lex_word_full(e: &SExpr, vars: &BTreeSet<String>) -> Option<Vec<axeyum_strings::Seg>> {
    use axeyum_strings::Seg;
    if let Some(a) = e.atom() {
        if a.len() >= 2 && a.starts_with('"') && a.ends_with('"') {
            let cps = literal_pattern_cps(e)?;
            return Some(cps.into_iter().map(Seg::Lit).collect());
        }
        if vars.contains(a) {
            return Some(vec![Seg::Var(a.to_owned())]);
        }
        return None;
    }
    let items = e.list()?;
    match items.first().and_then(SExpr::atom)? {
        "str.++" if items.len() >= 2 => {
            let mut word = Vec::new();
            for it in &items[1..] {
                word.extend(lex_word_full(it, vars)?);
            }
            Some(word)
        }
        _ => None,
    }
}

/// Translates a Boolean `e` into a [`LexFormula`](axeyum_strings::LexFormula) over
/// interned lex/equality atoms, or `None` on anything outside the lex fragment.
/// Sets `saw_lex` when a genuine `str.<`/`str.<=` atom is produced.
fn lex_bool(
    e: &SExpr,
    vars: &BTreeSet<String>,
    atoms: &mut Vec<axeyum_strings::LexAtom>,
    saw_lex: &mut bool,
) -> Option<axeyum_strings::LexFormula> {
    use axeyum_strings::{LexAtom, LexFormula};
    match e.atom() {
        Some("true") => return Some(LexFormula::Const(true)),
        Some("false") => return Some(LexFormula::Const(false)),
        _ => {}
    }
    let items = e.list()?;
    let head = items.first().and_then(SExpr::atom)?;
    match head {
        "and" | "or" if items.len() >= 2 => {
            let mut children = Vec::with_capacity(items.len() - 1);
            for it in &items[1..] {
                children.push(lex_bool(it, vars, atoms, saw_lex)?);
            }
            Some(if head == "and" {
                LexFormula::And(children)
            } else {
                LexFormula::Or(children)
            })
        }
        "xor" if items.len() >= 2 => {
            let mut acc = lex_bool(&items[1], vars, atoms, saw_lex)?;
            for it in &items[2..] {
                let next = lex_bool(it, vars, atoms, saw_lex)?;
                acc = LexFormula::Xor(Box::new(acc), Box::new(next));
            }
            Some(acc)
        }
        "=>" if items.len() >= 3 => {
            let mut acc = lex_bool(items.last()?, vars, atoms, saw_lex)?;
            for it in items[1..items.len() - 1].iter().rev() {
                let ante = lex_bool(it, vars, atoms, saw_lex)?;
                acc = LexFormula::Implies(Box::new(ante), Box::new(acc));
            }
            Some(acc)
        }
        "not" if items.len() == 2 => {
            let inner = lex_bool(&items[1], vars, atoms, saw_lex)?;
            Some(LexFormula::Not(Box::new(inner)))
        }
        "ite" if items.len() == 4 => {
            let c = lex_bool(&items[1], vars, atoms, saw_lex)?;
            let t = lex_bool(&items[2], vars, atoms, saw_lex)?;
            let f = lex_bool(&items[3], vars, atoms, saw_lex)?;
            Some(LexFormula::Ite(Box::new(c), Box::new(t), Box::new(f)))
        }
        "str.<" | "str.<=" if items.len() == 3 => {
            let left = lex_word_full(&items[1], vars)?;
            let right = lex_word_full(&items[2], vars)?;
            *saw_lex = true;
            let idx = intern_lex_atom(
                atoms,
                LexAtom::Lex {
                    left,
                    right,
                    strict: head == "str.<",
                },
            );
            Some(LexFormula::Atom(idx))
        }
        "=" if items.len() >= 3 => lex_eq_chain(&items[1..], vars, atoms),
        "distinct" if items.len() >= 3 => lex_distinct(&items[1..], vars, atoms),
        _ => None,
    }
}

/// Left-folds a list of [`LexFormula`]s into an `And`, or `None` if empty.
fn lex_and_fold(children: Vec<axeyum_strings::LexFormula>) -> Option<axeyum_strings::LexFormula> {
    let mut acc: Option<axeyum_strings::LexFormula> = None;
    for c in children {
        acc = Some(match acc {
            None => c,
            Some(prev) => axeyum_strings::LexFormula::And(vec![prev, c]),
        });
    }
    acc
}

/// `(= a b …)` over words → a conjunction of `(= a_0 a_i)` equality atoms.
fn lex_eq_chain(
    operands: &[SExpr],
    vars: &BTreeSet<String>,
    atoms: &mut Vec<axeyum_strings::LexAtom>,
) -> Option<axeyum_strings::LexFormula> {
    use axeyum_strings::{LexAtom, LexFormula};
    let words: Vec<_> = operands
        .iter()
        .map(|it| lex_word_full(it, vars))
        .collect::<Option<_>>()?;
    let children = words[1..]
        .iter()
        .map(|w| {
            let idx = intern_lex_atom(
                atoms,
                LexAtom::Eq {
                    left: words[0].clone(),
                    right: w.clone(),
                },
            );
            LexFormula::Atom(idx)
        })
        .collect();
    lex_and_fold(children)
}

/// `(distinct a b …)` over words → a conjunction of pairwise `(not (= a_i a_j))`.
fn lex_distinct(
    operands: &[SExpr],
    vars: &BTreeSet<String>,
    atoms: &mut Vec<axeyum_strings::LexAtom>,
) -> Option<axeyum_strings::LexFormula> {
    use axeyum_strings::{LexAtom, LexFormula};
    let words: Vec<_> = operands
        .iter()
        .map(|it| lex_word_full(it, vars))
        .collect::<Option<_>>()?;
    let mut children = Vec::new();
    for i in 0..words.len() {
        for w in &words[i + 1..] {
            let idx = intern_lex_atom(
                atoms,
                LexAtom::Eq {
                    left: words[i].clone(),
                    right: w.clone(),
                },
            );
            children.push(LexFormula::Not(Box::new(LexFormula::Atom(idx))));
        }
    }
    lex_and_fold(children)
}

/// Interns the `str.in_re` membership atoms of a word skeleton into fresh
/// `Sort::Bool` proxy symbols, so a repeated `(str.in_re X R)` shares one theory
/// atom (and hence one skeleton variable).
struct MembershipCollector {
    /// Distinct `(operand, regex)` → its proxy atom term.
    intern: BTreeMap<(SymbolId, axeyum_strings::regex::Regex), TermId>,
    /// The accumulated `(proxy_atom_term, operand_symbol, regex)` triples, in
    /// first-encounter order.
    memberships: Vec<(TermId, SymbolId, axeyum_strings::regex::Regex)>,
    /// Fresh-proxy-symbol counter.
    next: u32,
    /// Definitional word equations `!inre_arg!k = <concat operand>` minted when a
    /// `str.in_re` subject is a `str.++` (or other word expression) rather than a
    /// single variable — see [`MembershipCollector::concat_operand`]. Each is a
    /// **top-level, unconditional** `Seq` equality the skeleton conjoins alongside
    /// the asserted formulas, tying the fresh operand symbol to the concatenation so
    /// the online CDCL(T) route composes the membership with the word part.
    concat_defs: Vec<TermId>,
    /// Fresh-concat-operand-symbol counter (disjoint from the `!weq!<name>` user
    /// symbols and the `!inre!k` proxy symbols).
    next_concat: u32,
    /// Structurally interned opaque fixed-splice expressions. They preserve
    /// equality congruence but intentionally omit splice semantics, making the
    /// resulting word skeleton UNSAT-only.
    opaque_words: Vec<(SExpr, TermId)>,
    /// Fresh opaque-word symbol counter.
    next_opaque: u32,
    /// Exact constants implied by guaranteed top-level equality paths. Replacing
    /// one of these expressions by its value is equivalence-preserving within the
    /// asserted conjunction.
    pinned_words: Vec<(SExpr, Vec<u32>)>,
}

impl MembershipCollector {
    /// Returns the exact guaranteed constant for `expression`, if one was derived.
    fn pinned_word(&self, expression: &SExpr) -> Option<Vec<u32>> {
        eval_guaranteed_pinned_word(expression, &self.pinned_words, 0)
    }

    /// Returns one shared `Seq` symbol for a structurally identical opaque word.
    fn opaque_word(&mut self, arena: &mut TermArena, expression: &SExpr) -> Option<TermId> {
        if let Some((_, term)) = self
            .opaque_words
            .iter()
            .find(|(candidate, _)| candidate == expression)
        {
            return Some(*term);
        }
        let sym = arena
            .declare_internal(
                &format!("!opaque_word!{}", self.next_opaque),
                Sort::string(),
            )
            .ok()?;
        self.next_opaque += 1;
        let term = arena.var(sym);
        self.opaque_words.push((expression.clone(), term));
        Some(term)
    }

    /// Introduces a fresh `Seq`-sorted operand symbol `w` for a `str.in_re` whose
    /// subject is a compound word expression `concat` (a `str.++` of variables and
    /// literals), records the definitional equation `w = concat`, and returns `w`'s
    /// symbol. The caller then asserts the membership on `w` via
    /// [`MembershipCollector::atom`]. `None` on an arena declaration/build failure.
    ///
    /// The definitional equation is **unconditional** (it is not gated by any
    /// enclosing `or`/`ite`/`not`): `w` simply *names* the concatenation, so it holds
    /// in every branch. This is what lets a `str.in_re (str.++ …) R` atom reuse the
    /// single-variable membership machinery — the atom becomes `w ∈ R` with `w`
    /// pinned to the concatenation by the equation — while the mandatory Seq-level
    /// replay against the skeleton (which carries both the equation and the
    /// membership) remains the sole gate on any `sat`.
    fn concat_operand(&mut self, arena: &mut TermArena, concat: TermId) -> Option<SymbolId> {
        let sym = arena
            .declare_internal(&format!("!inre_arg!{}", self.next_concat), Sort::string())
            .ok()?;
        self.next_concat += 1;
        let w = arena.var(sym);
        let def = arena.eq(w, concat).ok()?;
        self.concat_defs.push(def);
        Some(sym)
    }

    /// Returns the `Sort::Bool` proxy atom term for `(str.in_re operand R)`,
    /// minting a fresh `!inre!<k>` symbol on first encounter. `None` on an arena
    /// declaration failure (never expected).
    fn atom(
        &mut self,
        arena: &mut TermArena,
        operand: SymbolId,
        regex: axeyum_strings::regex::Regex,
    ) -> Option<TermId> {
        if let Some(&t) = self.intern.get(&(operand, regex.clone())) {
            return Some(t);
        }
        let sym = arena
            .declare_internal(&format!("!inre!{}", self.next), Sort::Bool)
            .ok()?;
        self.next += 1;
        let term = arena.var(sym);
        self.intern.insert((operand, regex.clone()), term);
        self.memberships.push((term, operand, regex));
        Some(term)
    }
}

/// Translates one Boolean term into a `Sort::Bool` [`TermId`] over `Seq` equality
/// atoms, or `None` on anything outside the skeleton fragment. Recurses through
/// every Boolean connective; leaves are `Seq` equalities (`=`), `Seq` disequalities
/// (`not (= …)` / `distinct`), declared Boolean symbols, and the Boolean constants.
/// Boolean equality is retained as exact equivalence. Sets `saw_seq_atom` when a
/// genuine `Seq` equality atom is produced.
///
/// **No polarity tracking is needed** because — unlike [`word_atom`] — this build
/// performs *no* sat-implying reductions: every leaf is either an exact `Seq`
/// equality/disequality or an exact regex-membership atom (a `str.in_re`, or a
/// constant-pattern `prefixof`/`suffixof`/`contains` translated to `P·Σ*` / `Σ*·S`
/// / `Σ*·C·Σ*`), or an exact content predicate (`len(X)=0`,
/// `indexof(X,C,0)=-1`, first/last-character `str.at` equality), each sound in any
/// Boolean position. The same predicates are retained over the exact suffix view
/// `substr(X,n,len(X)-n)`. Other `str.len`/`substr`/`to_int` shapes, a compound
/// pattern, or any non-string construct returns `None` (all-or-nothing).
fn word_bool(
    arena: &mut TermArena,
    e: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    bool_vars: &BTreeMap<String, TermId>,
    saw_seq_atom: &mut bool,
    mem: &mut MembershipCollector,
) -> Option<TermId> {
    match e.atom() {
        Some("true") => return Some(arena.bool_const(true)),
        Some("false") => return Some(arena.bool_const(false)),
        Some(name) => return bool_vars.get(name).copied(),
        None => {}
    }
    let items = e.list()?;
    let head = items.first().and_then(SExpr::atom)?;
    match head {
        // Boolean connectives: fold the (≥1) operands.
        "and" | "or" | "xor" if items.len() >= 2 => {
            let mut acc = word_bool(arena, &items[1], vars, bool_vars, saw_seq_atom, mem)?;
            for it in &items[2..] {
                let next = word_bool(arena, it, vars, bool_vars, saw_seq_atom, mem)?;
                acc = match head {
                    "and" => arena.and(acc, next).ok()?,
                    "or" => arena.or(acc, next).ok()?,
                    _ => arena.xor(acc, next).ok()?,
                };
            }
            Some(acc)
        }
        "=>" if items.len() >= 3 => {
            // Right-associative implication chain `a => b => … => z`.
            let mut acc = word_bool(arena, items.last()?, vars, bool_vars, saw_seq_atom, mem)?;
            for it in items[1..items.len() - 1].iter().rev() {
                let ante = word_bool(arena, it, vars, bool_vars, saw_seq_atom, mem)?;
                acc = arena.implies(ante, acc).ok()?;
            }
            Some(acc)
        }
        "not" if items.len() == 2 => {
            let inner = word_bool(arena, &items[1], vars, bool_vars, saw_seq_atom, mem)?;
            word_boolean_not(arena, inner)
        }
        // `(str.in_re X R)`: a membership theory atom (negative polarity is expressed
        // by the enclosing `not`, never here — the atom itself is always positive).
        //
        // * A single declared string variable `X` → a membership on `X`.
        // * A `str.++` (or other word expression) subject → introduce a fresh operand
        //   `w`, define `w = <subject>` unconditionally (a top-level `Seq` equality),
        //   and assert the membership on `w`. This routes a membership-over-concat
        //   into the same online CDCL(T) composition as a variable membership: the
        //   equation ties `w` to the concatenation, and the mandatory Seq-level model
        //   replay against this skeleton (equation + membership) is the sole `sat`
        //   gate. An unsupported regex, or a subject outside the word fragment,
        //   declines the whole skeleton.
        "str.in_re" if items.len() == 3 => word_in_re_atom(arena, items, vars, saw_seq_atom, mem),
        // Constant-pattern extended-function atoms as **regex memberships** (P2.7
        // Phase D). Each is *exactly* a regex-language membership when its pattern is
        // a string constant and its subject is a single declared string variable —
        // and, unlike the sat-implying fresh-variable word reductions in
        // [`word_extended_fn`], a membership atom is **polarity-symmetric** (the
        // online route complements the language natively for the negative literal),
        // so these are sound in *any* Boolean position:
        //
        //   * `(str.prefixof P X)` ⟺ `X ∈ L(P·Σ*)`   (P a constant prefix)
        //   * `(str.suffixof S X)` ⟺ `X ∈ L(Σ*·S)`   (S a constant suffix)
        //   * `(str.contains X C)` ⟺ `X ∈ L(Σ*·C·Σ*)` (C a constant infix)
        //
        // A subject may also be the exact constant-offset suffix view
        // `substr(X,n,len(X)-n)`: prefixing the language with exactly `n` arbitrary
        // characters gives its exact reading over `X`. Other compound subjects and
        // variable patterns decline the whole skeleton.
        "str.prefixof" if items.len() == 3 => {
            let cps = literal_pattern_cps(&items[1])?;
            if cps.is_empty() {
                return Some(arena.bool_const(true));
            }
            let view = content_view_skeleton(&items[2], vars, &cps)?;
            mem.atom(
                arena,
                view.operand,
                around_exact_view(view, prefix_pattern_regex(&cps)),
            )
        }
        "str.suffixof" if items.len() == 3 => {
            let cps = literal_pattern_cps(&items[1])?;
            if cps.is_empty() {
                return Some(arena.bool_const(true));
            }
            let view = content_view_skeleton(&items[2], vars, &cps)?;
            mem.atom(
                arena,
                view.operand,
                around_exact_view(view, suffix_pattern_regex(&cps)),
            )
        }
        "str.contains" if items.len() == 3 => word_contains_atom(arena, items, vars, mem),
        // Boolean `ite` only (the branches must themselves be skeleton Booleans; an
        // `ite` over *strings* is not a `word_str_expr` and is declined below).
        "ite" if items.len() == 4 => {
            let c = word_bool(arena, &items[1], vars, bool_vars, saw_seq_atom, mem)?;
            let t = word_bool(arena, &items[2], vars, bool_vars, saw_seq_atom, mem)?;
            let f = word_bool(arena, &items[3], vars, bool_vars, saw_seq_atom, mem)?;
            word_boolean_ite(arena, c, t, f)
        }
        // A **trivially-true length guard** (`(<= 0 (str.len W))` / `(>= (str.len W)
        // 0)`) is a tautology — replaced by `true` so the redundant `norn-*` guard does
        // not collapse the skeleton. Exact constant-offset substring length guards
        // are memberships; any other length comparison still declines.
        "<" | "<=" | ">" | ">=" if items.len() == 3 => {
            exact_word_int_comparison(arena, head, &items[1], &items[2], vars, mem)
        }
        // `(= a b …)` — either chained equality over `Seq` expressions, or exact
        // Boolean equivalence over skeleton formulas. Boolean equality is expanded
        // to `(a => b) ∧ (b => a)` so it remains Boolean structure rather than a
        // non-Seq theory atom.
        "=" if items.len() >= 3 => {
            word_equality(arena, &items[1..], vars, bool_vars, saw_seq_atom, mem)
        }
        // `(distinct a b …)` — pairwise disequality → conjunction of `(not (= …))`.
        "distinct" if items.len() >= 3 => {
            let terms = word_terms_with_opaque(arena, &items[1..], vars, mem)?;
            let mut acc: Option<TermId> = None;
            for i in 0..terms.len() {
                for &t in &terms[i + 1..] {
                    let atom = arena.eq(terms[i], t).ok()?;
                    *saw_seq_atom = true;
                    let diseq = arena.not(atom).ok()?;
                    acc = Some(match acc {
                        None => diseq,
                        Some(prev) => arena.and(prev, diseq).ok()?,
                    });
                }
            }
            acc
        }
        // Anything else (extended functions, `str.len`, non-string atoms, …) is
        // outside the skeleton fragment — decline the whole build.
        _ => None,
    }
}

/// Builds negation inside the exact word skeleton while eliminating the Boolean
/// aliases emitted by symbolic-execution front ends. This is only structural
/// simplification: every returned term is equivalent to `not term`.
fn word_boolean_not(arena: &mut TermArena, term: TermId) -> Option<TermId> {
    match arena.node(term) {
        TermNode::BoolConst(value) => Some(arena.bool_const(!value)),
        TermNode::App {
            op: Op::BoolNot,
            args,
        } => Some(args[0]),
        _ => arena.not(term).ok(),
    }
}

/// Builds a Boolean conditional inside the exact word skeleton, folding only
/// identities whose branches are constants or structurally identical. `PyEx` uses
/// integer conditionals as Boolean aliases; after [`constant_int_ite_equality`]
/// translates those aliases, this keeps the SAT driver from searching through a
/// fresh conditional for every underlying string predicate.
fn word_boolean_ite(
    arena: &mut TermArena,
    condition: TermId,
    when_true: TermId,
    when_false: TermId,
) -> Option<TermId> {
    if when_true == when_false {
        return Some(when_true);
    }
    if let TermNode::BoolConst(value) = arena.node(condition) {
        return Some(if *value { when_true } else { when_false });
    }
    match (arena.node(when_true), arena.node(when_false)) {
        (TermNode::BoolConst(true), TermNode::BoolConst(false)) => Some(condition),
        (TermNode::BoolConst(false), TermNode::BoolConst(true)) => {
            word_boolean_not(arena, condition)
        }
        _ => arena.ite(condition, when_true, when_false).ok(),
    }
}

fn word_contains_atom(
    arena: &mut TermArena,
    items: &[SExpr],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    mem: &mut MembershipCollector,
) -> Option<TermId> {
    let cps = literal_pattern_cps(&items[2])?;
    if cps.is_empty() {
        return Some(arena.bool_const(true));
    }
    if let Some((base, delimiter)) = before_first_occurrence_parts(&items[1]) {
        let [delimiter] = delimiter[..] else {
            return None;
        };
        let [target] = cps[..] else { return None };
        if delimiter == target {
            return Some(arena.bool_const(false));
        }
        let view = content_view_skeleton(base, vars, &[delimiter, target])?;
        let not_delimiter =
            || Regex::inter(Regex::any_char(), Regex::comp(Regex::character(delimiter)));
        let before_delimiter = Regex::concat(
            Regex::concat(
                Regex::concat(Regex::star(not_delimiter()), Regex::character(target)),
                Regex::star(not_delimiter()),
            ),
            Regex::concat(Regex::character(delimiter), Regex::star(Regex::any_char())),
        );
        return mem.atom(
            arena,
            view.operand,
            around_exact_view(view, before_delimiter),
        );
    }
    let (operand, regex) =
        regex_on_after_first_views(&items[1], vars, &cps, contains_pattern_regex(&cps), 0)?;
    mem.atom(arena, operand, regex)
}

/// Translates a chained word equality or Boolean equivalence for [`word_bool`].
fn word_equality(
    arena: &mut TermArena,
    items: &[SExpr],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    bool_vars: &BTreeMap<String, TermId>,
    saw_seq_atom: &mut bool,
    mem: &mut MembershipCollector,
) -> Option<TermId> {
    // Common symbolic-execution content predicates have exact regular-language
    // readings. Retain those before trying ordinary Seq/Boolean equality so they
    // remain available under arbitrary Boolean structure and constant-ITE aliases.
    if items.len() == 2
        && let Some(content) = exact_content_equality(arena, items, vars, mem)
    {
        return Some(content);
    }
    // PyEx materializes a Boolean predicate as an integer-valued conditional,
    // typically `(= (ite C 1 0) 0)`. Constant branches make this an exact Boolean
    // formula over C, so retain it in the word skeleton before trying Seq equality.
    if items.len() == 2
        && let Some(booleanized) =
            constant_int_ite_equality(arena, items, vars, bool_vars, saw_seq_atom, mem)
    {
        return Some(booleanized);
    }
    if let Some(terms) = word_terms_with_opaque(arena, items, vars, mem) {
        let mut acc: Option<TermId> = None;
        for &term in &terms[1..] {
            let atom = arena.eq(terms[0], term).ok()?;
            *saw_seq_atom = true;
            acc = Some(match acc {
                None => atom,
                Some(prev) => arena.and(prev, atom).ok()?,
            });
        }
        return acc;
    }

    let terms: Vec<TermId> = items
        .iter()
        .map(|term| word_bool(arena, term, vars, bool_vars, saw_seq_atom, mem))
        .collect::<Option<_>>()?;
    let mut acc: Option<TermId> = None;
    for &term in &terms[1..] {
        let forward = arena.implies(terms[0], term).ok()?;
        let backward = arena.implies(term, terms[0]).ok()?;
        let iff = arena.and(forward, backward).ok()?;
        acc = Some(match acc {
            None => iff,
            Some(prev) => arena.and(prev, iff).ok()?,
        });
    }
    acc
}

/// Translates word operands for the Boolean skeleton, allowing an exact
/// fixed-position splice to stand for one structurally-interned opaque `Seq` term.
/// This is a relaxation: every real model assigns that symbol the splice's value.
/// The enclosing skeleton is marked UNSAT-only so a model of the relaxation is
/// never reported as a model of the original string formula.
fn word_terms_with_opaque(
    arena: &mut TermArena,
    expressions: &[SExpr],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    collector: &mut MembershipCollector,
) -> Option<Vec<TermId>> {
    expressions
        .iter()
        .map(|expression| {
            // Preserve every directly representable word expression in the
            // skeleton. In particular, do not replace a declared variable by a
            // constant inferred from an asserted equality: doing so would turn
            // `s = "literal"` into `"literal" = "literal"` and erase the model
            // binding that membership atoms on `s` must share. Constant propagation
            // is needed only to give an exact meaning to a fixed-splice expression
            // that the ordinary word translator cannot represent.
            if let Some(term) = word_str_expr(arena, expression, vars) {
                return Some(term);
            }
            // Equality-class pins may only give a source-level meaning to the
            // one compound form this relaxation explicitly models. Applying a
            // pin to an arbitrary unsupported expression would erase the very
            // equality being checked (`at("abc",1) = "x"` became `"x" = "x"`).
            fixed_splice_split(expression.list()?)?;
            if let Some(value) = collector.pinned_word(expression) {
                return seq_from_code_points(arena, &value);
            }
            collector.opaque_word(arena, expression)
        })
        .collect()
}

/// Exactly translates regular string-content equalities used heavily by `PyEx`:
///
/// * `len(W) = 0` iff the underlying variable has length at most its dropped prefix;
/// * `indexof(W, C, 0) = -1` iff suffix/before-first view `W` lacks `C`;
/// * `at(W, 0) = C` / `at(W, len(W)-1) = C` as prefix/suffix languages.
///
/// Here `W` is `X`, an exact constant-offset suffix view, or the exact prefix
/// before the first occurrence of a one-code-point delimiter. Both equality
/// orientations are accepted. The `str.at` result is either empty or one code
/// point, so a multi-code-point right side is exactly `false`; equality to the
/// empty word holds exactly when `len(X) <= n`. Every non-constant, other
/// compound-subject, or other-index shape declines.
fn exact_content_equality(
    arena: &mut TermArena,
    items: &[SExpr],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    mem: &mut MembershipCollector,
) -> Option<TermId> {
    let [left, right] = items else { return None };
    exact_content_equality_ordered(arena, left, right, vars, mem)
        .or_else(|| exact_content_equality_ordered(arena, right, left, vars, mem))
}

/// One oriented half of [`exact_content_equality`]: `subject = constant`.
fn exact_content_equality_ordered(
    arena: &mut TermArena,
    subject: &SExpr,
    constant: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    mem: &mut MembershipCollector,
) -> Option<TermId> {
    let app = subject.list()?;
    let head = app.first().and_then(SExpr::atom)?;
    match head {
        "str.len" | "seq.len" if app.len() == 2 && parse_int_literal(constant) == Some(0) => {
            if let Some((operand, regex)) = first_occurrence_empty_view(&app[1], vars) {
                return mem.atom(arena, operand, regex);
            }
            let view = suffix_view_skeleton(&app[1], vars)?;
            mem.atom(
                arena,
                view.operand,
                at_most_length_regex(view.total_dropped()?),
            )
        }
        "str.indexof"
            if app.len() == 4
                && parse_int_literal(&app[3]) == Some(0)
                && parse_int_literal(constant) == Some(-1) =>
        {
            let needle = literal_pattern_cps(&app[2])?;
            if needle.is_empty() {
                return Some(arena.bool_const(false));
            }
            if let Some((base, delimiter)) = before_first_occurrence_parts(&app[1]) {
                let [delimiter] = delimiter[..] else {
                    return None;
                };
                let [needle] = needle[..] else { return None };
                if delimiter == needle {
                    return Some(arena.bool_const(true));
                }
                let view = content_view_skeleton(base, vars, &[delimiter, needle])?;
                let safe_character = Regex::inter(
                    Regex::any_char(),
                    Regex::comp(Regex::union(
                        Regex::character(delimiter),
                        Regex::character(needle),
                    )),
                );
                let safe_prefix = Regex::star(safe_character);
                // When the delimiter is absent, `indexof = -1` and SMT-LIB's
                // total `substr(base, 0, -1)` is empty, so the predicate is true
                // regardless of whether `needle` occurs in `base`. When the
                // delimiter is present, only the prefix before its first
                // occurrence must avoid the needle.
                let no_delimiter = Regex::comp(contains_pattern_regex(&[delimiter]));
                let no_needle_before_first_delimiter = Regex::union(
                    no_delimiter,
                    Regex::concat(
                        Regex::concat(safe_prefix, Regex::character(delimiter)),
                        Regex::star(Regex::any_char()),
                    ),
                );
                return mem.atom(
                    arena,
                    view.operand,
                    around_exact_view(view, no_needle_before_first_delimiter),
                );
            }
            let no_needle = Regex::comp(contains_pattern_regex(&needle));
            let (operand, regex) =
                regex_on_after_first_views(&app[1], vars, &needle, no_needle, 0)?;
            mem.atom(arena, operand, regex)
        }
        "str.at" if app.len() == 3 => {
            let value = literal_pattern_cps(constant)?;
            if value.len() > 1 {
                return Some(arena.bool_const(false));
            }
            if let Some((operand, regex)) = first_occurrence_at_view(&app[1], &app[2], &value, vars)
            {
                return mem.atom(arena, operand, regex);
            }
            let (view, first) = at_boundary_view(&app[1], &app[2], vars, &value)?;
            let regex = match value.as_slice() {
                [] => at_most_length_regex(view.total_dropped()?),
                [c] if first => around_exact_view(view, prefix_pattern_regex(&[*c])),
                [c] => around_exact_view(view, suffix_pattern_regex(&[*c])),
                _ => unreachable!("multi-code-point str.at equality returned above"),
            };
            mem.atom(arena, view.operand, regex)
        }
        _ => None,
    }
}

/// Exact language for a before/after-first-occurrence view being empty.
fn first_occurrence_empty_view(
    expression: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
) -> Option<(SymbolId, Regex)> {
    if let Some((base, needle)) = before_first_occurrence_parts(expression) {
        let view = content_view_skeleton(base, vars, &needle)?;
        let empty_prefix = if needle.is_empty() {
            Regex::star(Regex::any_char())
        } else {
            Regex::union(
                Regex::comp(contains_pattern_regex(&needle)),
                prefix_pattern_regex(&needle),
            )
        };
        return Some((view.operand, around_exact_view(view, empty_prefix)));
    }
    let (base, needle) = after_first_occurrence_parts(expression)?;
    let view = content_view_skeleton(base, vars, &[needle])?;
    let not_needle = Regex::inter(Regex::any_char(), Regex::comp(Regex::character(needle)));
    let first_at_end = Regex::concat(Regex::star(not_needle), Regex::character(needle));
    Some((
        view.operand,
        around_exact_view(view, Regex::union(Regex::empty(), first_at_end)),
    ))
}

/// Exact first/last-character language for before/after-first-occurrence views.
fn first_occurrence_at_view(
    expression: &SExpr,
    index: &SExpr,
    value: &[u32],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
) -> Option<(SymbolId, Regex)> {
    let first = parse_int_literal(index) == Some(0);
    let last = index.list().is_some_and(|index| {
        index.len() == 3
            && index[0].atom() == Some("-")
            && parse_int_literal(&index[2]) == Some(1)
            && index[1]
                .list()
                .is_some_and(|len| len.len() == 2 && len[1] == *expression)
    });
    if !first && !last {
        return None;
    }
    if let Some((base, delimiter)) = after_first_occurrence_parts(expression) {
        let view = content_view_skeleton(base, vars, &[delimiter])?;
        let not_delimiter =
            || Regex::inter(Regex::any_char(), Regex::comp(Regex::character(delimiter)));
        let no_delimiter = Regex::comp(contains_pattern_regex(&[delimiter]));
        let regex = match value {
            [] => Regex::union(
                Regex::empty(),
                Regex::concat(Regex::star(not_delimiter()), Regex::character(delimiter)),
            ),
            [c] if first => Regex::union(
                Regex::inter(no_delimiter, prefix_pattern_regex(&[*c])),
                Regex::concat(
                    Regex::concat(
                        Regex::concat(Regex::star(not_delimiter()), Regex::character(delimiter)),
                        Regex::character(*c),
                    ),
                    Regex::star(Regex::any_char()),
                ),
            ),
            [c] => Regex::union(
                Regex::inter(no_delimiter, suffix_pattern_regex(&[*c])),
                Regex::concat(
                    Regex::concat(
                        Regex::concat(Regex::star(not_delimiter()), Regex::character(delimiter)),
                        Regex::star(Regex::any_char()),
                    ),
                    Regex::character(*c),
                ),
            ),
            _ => return None,
        };
        return Some((view.operand, around_exact_view(view, regex)));
    }
    let (base, needle) = before_first_occurrence_parts(expression)?;
    let view = content_view_skeleton(base, vars, &needle)?;
    let regex = match value {
        [] if needle.is_empty() => Regex::star(Regex::any_char()),
        [] => Regex::union(
            Regex::comp(contains_pattern_regex(&needle)),
            prefix_pattern_regex(&needle),
        ),
        [c] if first => Regex::inter(
            Regex::inter(
                contains_pattern_regex(&needle),
                Regex::comp(prefix_pattern_regex(&needle)),
            ),
            prefix_pattern_regex(&[*c]),
        ),
        [c] => {
            let [needle] = needle[..] else { return None };
            if *c == needle {
                Regex::none()
            } else {
                let not_needle =
                    Regex::inter(Regex::any_char(), Regex::comp(Regex::character(needle)));
                Regex::concat(
                    Regex::concat(
                        Regex::concat(Regex::star(not_needle), Regex::character(*c)),
                        Regex::character(needle),
                    ),
                    Regex::star(Regex::any_char()),
                )
            }
        }
        _ => return None,
    };
    Some((view.operand, around_exact_view(view, regex)))
}

/// A declared string variable viewed after dropping exactly `dropped` leading
/// characters. `substr(X,dropped,len(X)-dropped)` denotes this view exactly,
/// including its empty result when `len(X) <= dropped`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SuffixView {
    operand: SymbolId,
    dropped: u32,
    dropped_suffix: u32,
}

impl SuffixView {
    fn total_dropped(self) -> Option<u32> {
        self.dropped.checked_add(self.dropped_suffix)
    }
}

/// Recognizes either a bare declared string variable or its exact constant-offset
/// suffix view `substr(W,n,len(W)-n)`, where `W` may itself be a supported suffix
/// view. Nested views compose by adding their dropped-prefix lengths.
fn suffix_view_skeleton(
    e: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
) -> Option<SuffixView> {
    content_view_skeleton(e, vars, &[])
}

/// Recognizes a constant slice of a declared string, optionally through
/// length-preserving first-occurrence replacements that cannot affect any code
/// point in `protected`. This captures `PyEx`'s generated lowercase pipeline: while
/// checking for `"O"`, earlier `"A"→"a"`, … replacements preserve both positions
/// and every occurrence of `"O"` exactly.
fn content_view_skeleton(
    e: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    protected: &[u32],
) -> Option<SuffixView> {
    if let Some(name) = variable_name_skeleton(e, vars) {
        let (operand, _) = *vars.get(&name)?;
        return Some(SuffixView {
            operand,
            dropped: 0,
            dropped_suffix: 0,
        });
    }

    if let Some(base) = preserved_replace_base(e, protected) {
        return content_view_skeleton(base, vars, protected);
    }

    let app = e.list()?;
    if app.len() != 4 || !matches!(app[0].atom(), Some("str.substr" | "seq.extract")) {
        return None;
    }
    let base = content_view_skeleton(&app[1], vars, protected)?;
    let additionally_dropped = u32::try_from(parse_int_literal(&app[2])?).ok()?;
    let total_removed = len_minus_constant(&app[3], &app[1])?;
    if total_removed < additionally_dropped {
        return None;
    }
    Some(SuffixView {
        operand: base.operand,
        dropped: base.dropped.checked_add(additionally_dropped)?,
        dropped_suffix: base
            .dropped_suffix
            .checked_add(total_removed - additionally_dropped)?,
    })
}

/// Returns `k` when `e` is syntactically `len(subject) - k`, accepting a nested
/// chain of subtracted non-negative integer literals. `PyEx` emits the same slice as
/// `(- (- (str.len s) right_drop) left_drop)` rather than folding the constants.
fn len_minus_constant(e: &SExpr, subject: &SExpr) -> Option<u32> {
    let items = e.list()?;
    if items.len() == 2
        && matches!(items[0].atom(), Some("str.len" | "seq.len"))
        && items[1] == *subject
    {
        return Some(0);
    }
    if items.len() != 3 || items[0].atom() != Some("-") {
        return None;
    }
    let removed = u32::try_from(parse_int_literal(&items[2])?).ok()?;
    len_minus_constant(&items[1], subject)?.checked_add(removed)
}

fn len_subject_minus_constant(e: &SExpr) -> Option<(&SExpr, u32)> {
    let items = e.list()?;
    if items.len() == 2 && matches!(items[0].atom(), Some("str.len" | "seq.len")) {
        return Some((&items[1], 0));
    }
    if items.len() != 3 || items[0].atom() != Some("-") {
        return None;
    }
    let removed = u32::try_from(parse_int_literal(&items[2])?).ok()?;
    let (subject, prior) = len_subject_minus_constant(&items[1])?;
    Some((subject, prior.checked_add(removed)?))
}

/// Peels a length-preserving first-occurrence replacement that cannot change any
/// code point in `protected`. Besides ordinary `str.replace`, recognizes `PyEx`'s
/// exact split/rejoin spelling:
///
/// `replace(substr(s,0,indexof(s,n,0)+1),n,r) ++ substr(s,indexof(s,n,0)+1,...)`.
fn preserved_replace_base<'a>(e: &'a SExpr, protected: &[u32]) -> Option<&'a SExpr> {
    let items = e.list()?;
    if items.len() == 4 && items[0].atom() == Some("str.replace") {
        let needle = literal_pattern_cps(&items[2])?;
        let replacement = literal_pattern_cps(&items[3])?;
        if replacement_preserves(&needle, &replacement, protected) {
            return Some(&items[1]);
        }
        return None;
    }

    split_replace_rejoin_base(items, protected)
}

/// The base word of `PyEx`'s exact split/replace/rejoin spelling of a
/// first-occurrence replacement. The needle and replacement must have equal
/// length, so the reconstructed word has exactly the base word's length.
fn split_replace_rejoin_base<'a>(items: &'a [SExpr], protected: &[u32]) -> Option<&'a SExpr> {
    if items.len() != 3 || items[0].atom() != Some("str.++") {
        return None;
    }
    let replace = items[1].list()?;
    if replace.len() != 4 || replace[0].atom() != Some("str.replace") {
        return None;
    }
    let needle = literal_pattern_cps(&replace[2])?;
    let replacement = literal_pattern_cps(&replace[3])?;
    // The generated split point is `index + 1`, hence this exact reconstruction is
    // specifically the one-code-point replacement used by Python lower/upper.
    if needle.len() != 1
        || replacement.len() != 1
        || !replacement_preserves(&needle, &replacement, protected)
    {
        return None;
    }

    let prefix = replace[1].list()?;
    if prefix.len() != 4
        || prefix[0].atom() != Some("str.substr")
        || parse_int_literal(&prefix[2]) != Some(0)
    {
        return None;
    }
    let base = &prefix[1];
    let split = strip_subtracted_zero(&prefix[3]);
    if !is_index_plus_one(split, base, &replace[2]) {
        return None;
    }

    let suffix = items[2].list()?;
    if suffix.len() != 4 || suffix[0].atom() != Some("str.substr") || suffix[1] != *base {
        return None;
    }
    let suffix_start = strip_subtracted_zero(&suffix[2]);
    if suffix_start != split {
        return None;
    }
    let suffix_len = suffix[3].list()?;
    if suffix_len.len() != 3
        || suffix_len[0].atom() != Some("-")
        || strip_subtracted_zero(&suffix_len[2]) != split
    {
        return None;
    }
    let len = suffix_len[1].list()?;
    if len.len() != 2 || !matches!(len[0].atom(), Some("str.len" | "seq.len")) || len[1] != *base {
        return None;
    }
    Some(base)
}

/// Maximum number of split/replace/rejoin terms admitted into one packed query.
/// Above this, even the correlated-width encoding creates a very large term DAG;
/// preserving the existing source-level fallback is both faster and more robust.
const SPLIT_REPLACE_REJOIN_PACKED_LIMIT: usize = 64;

fn count_split_replace_rejoin(exprs: &[SExpr]) -> usize {
    let mut stack: Vec<&SExpr> = exprs.iter().collect();
    let mut count = 0;
    while let Some(expression) = stack.pop() {
        let Some(items) = expression.list() else {
            continue;
        };
        if split_replace_rejoin_base(items, &[]).is_some() {
            count += 1;
        }
        stack.extend(items);
    }
    count
}

/// Recognizes the exact suffix strictly after the first occurrence of `needle`:
/// `substr(s, indexof(s,needle,0)+1, len(s)-(indexof(...)+1))`. For a one-code-point
/// needle, asking whether this suffix contains the same needle is exactly asking
/// whether `s` contains at least two occurrences.
fn after_first_occurrence_base<'a>(e: &'a SExpr, needle: &SExpr) -> Option<&'a SExpr> {
    let suffix = e.list()?;
    if suffix.len() != 4 || suffix[0].atom() != Some("str.substr") {
        return None;
    }
    let base = &suffix[1];
    let split = strip_subtracted_zero(&suffix[2]);
    if !is_index_plus_one(split, base, needle) {
        return None;
    }
    let length = suffix[3].list()?;
    if length.len() != 3
        || length[0].atom() != Some("-")
        || strip_subtracted_zero(&length[2]) != split
    {
        return None;
    }
    let len = length[1].list()?;
    (len.len() == 2 && matches!(len[0].atom(), Some("str.len" | "seq.len")) && len[1] == *base)
        .then_some(base)
}

/// The base and one-code-point needle of an exact suffix strictly after its first
/// occurrence. This is the self-describing counterpart of
/// [`after_first_occurrence_base`].
fn after_first_occurrence_parts(e: &SExpr) -> Option<(&SExpr, u32)> {
    let suffix = e.list()?;
    if suffix.len() != 4 || suffix[0].atom() != Some("str.substr") {
        return None;
    }
    let split = strip_subtracted_zero(&suffix[2]).list()?;
    if split.len() != 3 || split[0].atom() != Some("+") {
        return None;
    }
    let index = if parse_int_literal(&split[1]) == Some(1) {
        &split[2]
    } else if parse_int_literal(&split[2]) == Some(1) {
        &split[1]
    } else {
        return None;
    };
    let index = index.list()?;
    if index.len() != 4
        || index[0].atom() != Some("str.indexof")
        || index[1] != suffix[1]
        || parse_int_literal(&index[3]) != Some(0)
    {
        return None;
    }
    let [needle] = literal_pattern_cps(&index[2])?[..] else {
        return None;
    };
    let base = after_first_occurrence_base(e, &index[2])?;
    Some((base, needle))
}

/// The base and constant needle of the exact prefix before its first occurrence:
/// `substr(s, 0, indexof(s, needle, 0))` (allowing generated `- 0` wrappers).
fn before_first_occurrence_parts(e: &SExpr) -> Option<(&SExpr, Vec<u32>)> {
    let prefix = e.list()?;
    if prefix.len() != 4
        || prefix[0].atom() != Some("str.substr")
        || parse_int_literal(&prefix[2]) != Some(0)
    {
        return None;
    }
    let index = strip_subtracted_zero(&prefix[3]).list()?;
    if index.len() != 4
        || index[0].atom() != Some("str.indexof")
        || index[1] != prefix[1]
        || parse_int_literal(&index[3]) != Some(0)
    {
        return None;
    }
    Some((&prefix[1], literal_pattern_cps(&index[2])?))
}

fn replacement_preserves(needle: &[u32], replacement: &[u32], protected: &[u32]) -> bool {
    needle.len() == replacement.len()
        && needle
            .iter()
            .chain(replacement)
            .all(|c| !protected.contains(c))
}

fn strip_subtracted_zero(mut e: &SExpr) -> &SExpr {
    while let Some(items) = e.list()
        && items.len() == 3
        && items[0].atom() == Some("-")
        && parse_int_literal(&items[2]) == Some(0)
    {
        e = &items[1];
    }
    e
}

fn is_index_plus_one(e: &SExpr, subject: &SExpr, needle: &SExpr) -> bool {
    let Some(plus) = e.list() else { return false };
    if plus.len() != 3 || plus[0].atom() != Some("+") {
        return false;
    }
    let index = if parse_int_literal(&plus[1]) == Some(1) {
        &plus[2]
    } else if parse_int_literal(&plus[2]) == Some(1) {
        &plus[1]
    } else {
        return false;
    };
    let Some(index) = index.list() else {
        return false;
    };
    index.len() == 4
        && index[0].atom() == Some("str.indexof")
        && index[1] == *subject
        && index[2] == *needle
        && parse_int_literal(&index[3]) == Some(0)
}

fn is_any_index_plus_one(e: &SExpr) -> bool {
    let Some(plus) = e.list() else { return false };
    if plus.len() != 3 || plus[0].atom() != Some("+") {
        return false;
    }
    let index = if parse_int_literal(&plus[1]) == Some(1) {
        &plus[2]
    } else if parse_int_literal(&plus[2]) == Some(1) {
        &plus[1]
    } else {
        return false;
    };
    let Some(index) = index.list() else {
        return false;
    };
    index.len() == 4
        && index[0].atom() == Some("str.indexof")
        && parse_int_literal(&index[3]) == Some(0)
}

fn is_remaining_after_first_nonnegative(e: &SExpr) -> bool {
    let Some(difference) = e.list() else {
        return false;
    };
    if difference.len() != 3 || difference[0].atom() != Some("-") {
        return false;
    }
    let Some(len) = difference[1].list() else {
        return false;
    };
    if len.len() != 2 || !matches!(len[0].atom(), Some("str.len" | "seq.len")) {
        return false;
    }
    let split = strip_subtracted_zero(&difference[2]);
    let Some(plus) = split.list() else {
        return false;
    };
    if plus.len() != 3 || plus[0].atom() != Some("+") {
        return false;
    }
    let index = if parse_int_literal(&plus[1]) == Some(1) {
        &plus[2]
    } else if parse_int_literal(&plus[2]) == Some(1) {
        &plus[1]
    } else {
        return false;
    };
    let Some(index) = index.list() else {
        return false;
    };
    index.len() == 4
        && index[0].atom() == Some("str.indexof")
        && index[1] == len[1]
        && literal_pattern_cps(&index[2]).is_some_and(|needle| !needle.is_empty())
        && parse_int_literal(&index[3]) == Some(0)
}

/// Recognizes `str.at(W, 0)` (`true`) or `str.at(W, len(W)-1)` (`false`) for a
/// supported [`SuffixView`] `W`.
fn at_boundary_view(
    subject: &SExpr,
    index: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    protected: &[u32],
) -> Option<(SuffixView, bool)> {
    let view = content_view_skeleton(subject, vars, protected)?;
    if parse_int_literal(index) == Some(0) {
        return Some((view, true));
    }
    let minus = index.list()?;
    if minus.len() != 3 || minus[0].atom() != Some("-") || parse_int_literal(&minus[2]) != Some(1) {
        return None;
    }
    let len = minus[1].list()?;
    if len.len() != 2 || !matches!(len[0].atom(), Some("str.len" | "seq.len")) {
        return None;
    }
    (content_view_skeleton(&len[1], vars, protected)? == view).then_some((view, false))
}

/// Exactly folds `(= (ite C a b) k)` (or its symmetric orientation) when `a`,
/// `b`, and `k` are integer literals, leaving `C` as Boolean skeleton structure.
fn constant_int_ite_equality(
    arena: &mut TermArena,
    items: &[SExpr],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    bool_vars: &BTreeMap<String, TermId>,
    saw_seq_atom: &mut bool,
    mem: &mut MembershipCollector,
) -> Option<TermId> {
    let (ite, expected) = match (items[0].list(), parse_int_literal(&items[1])) {
        (Some(ite), Some(expected)) => (ite, expected),
        _ => (items[1].list()?, parse_int_literal(&items[0])?),
    };
    if ite.len() != 4 || ite[0].atom() != Some("ite") {
        return None;
    }
    let then_value = parse_int_literal(&ite[2])?;
    let else_value = parse_int_literal(&ite[3])?;
    let condition = word_bool(arena, &ite[1], vars, bool_vars, saw_seq_atom, mem)?;
    let when_true = arena.bool_const(then_value == expected);
    let when_false = arena.bool_const(else_value == expected);
    word_boolean_ite(arena, condition, when_true, when_false)
}

/// Translates a `(str.in_re X R)` atom into its membership proxy for [`word_bool`]
/// (negative polarity is expressed by the enclosing `not`, never here).
///
/// * A single declared string variable `X` → a membership on `X`.
/// * A `str.++` (or other word expression) subject → introduce a fresh operand `w`,
///   define `w = <subject>` unconditionally (a top-level `Seq` equality), and assert
///   the membership on `w`. This routes a membership-over-concat into the same online
///   CDCL(T) composition as a variable membership: the equation ties `w` to the
///   concatenation, and the mandatory Seq-level replay against this skeleton
///   (equation + membership) is the sole `sat` gate. An unsupported regex, or a
///   subject outside the word fragment, declines the whole skeleton (`None`).
fn word_in_re_atom(
    arena: &mut TermArena,
    items: &[SExpr],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    saw_seq_atom: &mut bool,
    mem: &mut MembershipCollector,
) -> Option<TermId> {
    let regex = crate::regex_membership::translate_regex(&items[2])?;
    if let Some(name) = variable_name_skeleton(&items[1], vars) {
        let (operand, _) = *vars.get(&name)?;
        mem.atom(arena, operand, regex)
    } else {
        let concat = word_str_expr(arena, &items[1], vars)?;
        let operand = mem.concat_operand(arena, concat)?;
        // The definitional equation `w = concat` is a genuine `Seq` equality atom the
        // online route must see (it grounds the word part).
        *saw_seq_atom = true;
        mem.atom(arena, operand, regex)
    }
}

/// Decodes an SMT-LIB string-literal `SExpr` atom (quotes included, `""`-escaped
/// quotes, `\u{…}`/`\uhhhh` escapes) to its Unicode code points, or `None` when `e`
/// is not a string literal (or a code point exceeds the alphabet — the shared
/// [`decode_string_code_points`] bound). Used to translate the **constant pattern**
/// of a `str.prefixof`/`str.suffixof`/`str.contains` atom into a regex membership.
fn literal_pattern_cps(e: &SExpr) -> Option<Vec<u32>> {
    let a = e.atom()?;
    if a.len() < 2 || !a.starts_with('"') || !a.ends_with('"') {
        return None;
    }
    let inner = a[1..a.len() - 1].replace("\"\"", "\"");
    decode_string_code_points(&inner)
}

/// A literal code-point sequence as a `Regex` (concat of single-character
/// predicates; the empty sequence is `ε`). Mirrors
/// `regex_membership::literal_regex`.
fn literal_pattern_regex(cps: &[u32]) -> axeyum_strings::regex::Regex {
    use axeyum_strings::regex::Regex;
    let mut acc: Option<Regex> = None;
    for &c in cps {
        let ch = Regex::character(c);
        acc = Some(match acc {
            None => ch,
            Some(prev) => Regex::concat(prev, ch),
        });
    }
    acc.unwrap_or(Regex::Empty)
}

/// `L(P·Σ*)` — the strings with constant prefix `P` (`str.prefixof P X`).
fn prefix_pattern_regex(cps: &[u32]) -> axeyum_strings::regex::Regex {
    use axeyum_strings::regex::Regex;
    Regex::concat(literal_pattern_regex(cps), Regex::star(Regex::any_char()))
}

/// `L(Σ*·S)` — the strings with constant suffix `S` (`str.suffixof S X`).
fn suffix_pattern_regex(cps: &[u32]) -> axeyum_strings::regex::Regex {
    use axeyum_strings::regex::Regex;
    Regex::concat(Regex::star(Regex::any_char()), literal_pattern_regex(cps))
}

/// `L(Σ*·C·Σ*)` — the strings containing the constant infix `C`
/// (`str.contains X C`).
fn contains_pattern_regex(cps: &[u32]) -> axeyum_strings::regex::Regex {
    use axeyum_strings::regex::Regex;
    let any = || Regex::star(Regex::any_char());
    Regex::concat(Regex::concat(any(), literal_pattern_regex(cps)), any())
}

/// Prefixes `tail` with exactly `count` arbitrary characters.
fn after_exact_prefix(
    count: u32,
    tail: axeyum_strings::regex::Regex,
) -> axeyum_strings::regex::Regex {
    use axeyum_strings::regex::Regex;
    if count == 0 {
        tail
    } else {
        Regex::concat(Regex::repeat(Regex::any_char(), count, Some(count)), tail)
    }
}

/// Wraps the exact language of a constant slice with the arbitrary characters
/// removed from its left and right edges.
fn around_exact_view(
    view: SuffixView,
    middle: axeyum_strings::regex::Regex,
) -> axeyum_strings::regex::Regex {
    use axeyum_strings::regex::Regex;
    let with_prefix = after_exact_prefix(view.dropped, middle);
    if view.dropped_suffix == 0 {
        with_prefix
    } else {
        Regex::concat(
            with_prefix,
            Regex::repeat(
                Regex::any_char(),
                view.dropped_suffix,
                Some(view.dropped_suffix),
            ),
        )
    }
}

/// Pulls a regular-language predicate backwards through one or more generated
/// `suffix-after-first-occurrence` views. If the delimiter is absent, SMT-LIB's
/// total `indexof = -1` makes the generated split zero and the view is the whole
/// base; if present, the view is the suffix following the first delimiter.
fn regex_on_after_first_views(
    expression: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    protected: &[u32],
    language: axeyum_strings::regex::Regex,
    depth: u32,
) -> Option<(SymbolId, axeyum_strings::regex::Regex)> {
    use axeyum_strings::regex::Regex;
    if depth > 16 {
        return None;
    }
    if let Some(view) = content_view_skeleton(expression, vars, protected) {
        return Some((view.operand, around_exact_view(view, language)));
    }
    if let Some(base) = preserved_replace_base(expression, protected) {
        return regex_on_after_first_views(base, vars, protected, language, depth + 1);
    }
    let (base, delimiter) = after_first_occurrence_parts(expression)?;
    let no_delimiter = Regex::comp(contains_pattern_regex(&[delimiter]));
    let not_delimiter = Regex::inter(Regex::any_char(), Regex::comp(Regex::character(delimiter)));
    let preimage = Regex::union(
        Regex::inter(no_delimiter, language.clone()),
        Regex::concat(
            Regex::concat(Regex::star(not_delimiter), Regex::character(delimiter)),
            language,
        ),
    );
    // A replacement outside the view may be discarded only when it preserves both
    // the downstream predicate and this split delimiter. Otherwise changing the
    // first delimiter could change where the suffix begins.
    let mut protected = protected.to_vec();
    if !protected.contains(&delimiter) {
        protected.push(delimiter);
    }
    regex_on_after_first_views(base, vars, &protected, preimage, depth + 1)
}

/// The exact language of words whose length is at most `maximum`.
fn at_most_length_regex(maximum: u32) -> axeyum_strings::regex::Regex {
    use axeyum_strings::regex::Regex;
    Regex::repeat(Regex::any_char(), 0, Some(maximum))
}

/// The exact language of words whose length is at least `minimum`.
fn at_least_length_regex(minimum: u32) -> axeyum_strings::regex::Regex {
    use axeyum_strings::regex::Regex;
    Regex::repeat(Regex::any_char(), minimum, None)
}

/// Folds literal integer comparisons and the exact `PyEx` substring guards
/// `(>= (- (str.len W) n) 0)`. For a suffix view that drops `d` characters, the
/// latter is `len(X) >= d+n` when `n > 0` and a tautology when `n <= 0`.
/// The symmetric tautology `(<= 0 (str.len W))` is retained as well. All other
/// integer comparisons decline the word skeleton.
fn exact_word_int_comparison(
    arena: &mut TermArena,
    head: &str,
    left: &SExpr,
    right: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    mem: &mut MembershipCollector,
) -> Option<TermId> {
    if let (Some(a), Some(b)) = (
        parse_int_literal(strip_subtracted_zero(left)),
        parse_int_literal(strip_subtracted_zero(right)),
    ) {
        let value = match head {
            "<" => a < b,
            "<=" => a <= b,
            ">" => a > b,
            ">=" => a >= b,
            _ => return None,
        };
        return Some(arena.bool_const(value));
    }

    if head == "<=" && parse_int_literal(left) == Some(0) {
        let len = right.list()?;
        if len.len() == 2
            && matches!(len[0].atom(), Some("str.len" | "seq.len"))
            && suffix_view_skeleton(&len[1], vars).is_some()
        {
            return Some(arena.bool_const(true));
        }
    }

    if head == "<=" && parse_int_literal(right) == Some(0) {
        let len = left.list()?;
        if len.len() == 2 && matches!(len[0].atom(), Some("str.len" | "seq.len")) {
            let view = suffix_view_skeleton(&len[1], vars)?;
            return mem.atom(
                arena,
                view.operand,
                at_most_length_regex(view.total_dropped()?),
            );
        }
    }

    if head != ">=" || parse_int_literal(right) != Some(0) {
        return None;
    }
    if is_any_index_plus_one(strip_subtracted_zero(left)) {
        // SMT-LIB `indexof` is at least -1, so `indexof(...)+1 >= 0`.
        return Some(arena.bool_const(true));
    }
    if is_remaining_after_first_nonnegative(strip_subtracted_zero(left)) {
        // For a non-empty needle, a found index plus one never exceeds the
        // haystack length; absence gives -1 + 1 = 0.
        return Some(arena.bool_const(true));
    }
    // `indexof(W, C, 0) >= 0` is exactly `contains(W, C)`. PyEx emits this
    // redundant well-formedness guard around every dynamically sliced word; keep
    // its exact regular-language reading instead of dropping the whole skeleton.
    if let Some(indexof) = strip_subtracted_zero(left).list()
        && indexof.len() == 4
        && indexof[0].atom() == Some("str.indexof")
        && parse_int_literal(&indexof[3]) == Some(0)
    {
        let needle = literal_pattern_cps(&indexof[2])?;
        if needle.is_empty() {
            return Some(arena.bool_const(true));
        }
        let view = content_view_skeleton(&indexof[1], vars, &needle)?;
        return mem.atom(
            arena,
            view.operand,
            around_exact_view(view, contains_pattern_regex(&needle)),
        );
    }
    if let Some(len) = left.list()
        && len.len() == 2
        && matches!(len[0].atom(), Some("str.len" | "seq.len"))
        && suffix_view_skeleton(&len[1], vars).is_some()
    {
        return Some(arena.bool_const(true));
    }
    let (subject, threshold) = len_subject_minus_constant(left)?;
    let view = suffix_view_skeleton(subject, vars)?;
    if threshold == 0 {
        return Some(arena.bool_const(true));
    }
    let minimum = view.total_dropped()?.checked_add(threshold)?;
    mem.atom(arena, view.operand, at_least_length_regex(minimum))
}

/// The declared string-variable name if `e` is a bare atom naming one of the
/// skeleton's `vars` (a single-variable membership operand). A `str.++`/`substr`/
/// literal operand is not an atom in `vars`, so returns `None` (⇒ decline).
fn variable_name_skeleton(
    e: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
) -> Option<String> {
    let a = e.atom()?;
    vars.contains_key(a).then(|| a.to_owned())
}

/// The declared name of a 0-ary `String`-sorted symbol, if `e` is such a
/// declaration (`(declare-const x String)` or `(declare-fun x () String)`).
fn declared_string_var(e: &SExpr) -> Option<&str> {
    let items = e.list()?;
    match items.first().and_then(SExpr::atom)? {
        "declare-const" if items.len() == 3 => {
            (items[2].atom() == Some("String")).then(|| items[1].atom())?
        }
        "declare-fun" if items.len() == 4 => {
            let empty_params = items[2].list().is_some_and(<[SExpr]>::is_empty);
            (empty_params && items[2].list().is_some() && items[3].atom() == Some("String"))
                .then(|| items[1].atom())?
        }
        _ => None,
    }
}

/// Declares a fresh `Seq`-sorted variable term for an extended-function reduction
/// (the `k`/`k1`/`k2` above), bumping `next_k`. The name prefix `!weqk!` is
/// **disjoint** from the `!weq!<user-name>` string-variable symbols (a user var
/// derived name always has `!` as its fifth byte, this one has `k`), so a fresh
/// variable can never alias a user string variable or a previously-minted `k`.
/// Deliberately **not** recorded in `wp.seq_symbols`, so it never surfaces in a
/// returned model.
fn fresh_seq_k(arena: &mut TermArena, next_k: &mut u32) -> Option<TermId> {
    let n = *next_k;
    *next_k += 1;
    let sym = arena
        .declare_internal(&format!("!weqk!{n}"), Sort::string())
        .ok()?;
    Some(arena.var(sym))
}

/// Translates a Boolean atom into `wp`, returning `false` (abort) on anything
/// outside the pure word-equation fragment. Recurses through top-level `and`.
///
/// **Every call is a positive (top-level-conjunction) position**: the caller only
/// invokes this on `assert` bodies and, via the `and` recursion, on the arms of a
/// top-level `and`. The `not` branch consumes its operand as a *disequality* and
/// never recurses positively, so the sat-implying extended-function reductions
/// (prefixof/suffixof/contains) are only ever reached in a sound positive context.
fn word_atom(
    arena: &mut TermArena,
    e: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    wp: &mut WordProblem,
    next_k: &mut u32,
    opaque: &mut OpaqueCtx,
) -> bool {
    // `true` is a trivial conjunct.
    if e.atom() == Some("true") {
        return true;
    }
    let Some(items) = e.list() else {
        return false;
    };
    let Some(head) = items.first().and_then(SExpr::atom) else {
        return false;
    };
    // Task #78: a linear integer bound `i ⋈ c` on a declared `Int` variable (the
    // `str.from_int` argument channel). Recognized *before* the string `=` case so an
    // integer equality `(= i 420)` is captured as a bound rather than mis-parsed as a
    // (failing) string equality. The build-time soundness gate in `build_word_problem`
    // rejects the whole script if any bound's variable is not a `from_int` argument.
    if let Some(bound) = int_bound_atom(head, items, opaque.int_vars) {
        wp.int_bounds.push(bound);
        return true;
    }
    // Task #79: a constant-string `str.to_int` pin `(= i (str.to_int <literal>))` on a
    // declared `Int` variable. Recognized *before* the string `=` case (its right side
    // is not a string expression, so the string translator would reject it). The value
    // is the exact SMT-LIB `str.to_int` of the constant literal — pure constant folding,
    // no obligation. Build-time gates in `build_word_problem` reject a conflicting or
    // over-constrained pin (→ `unknown`, never `unsat`).
    if let Some(pin) = to_int_const_pin_atom(head, items, opaque.int_vars) {
        wp.int_pins.push(pin);
        return true;
    }
    match head {
        "and" => items[1..]
            .iter()
            .all(|c| word_atom(arena, c, vars, wp, next_k, opaque)),
        // `(= a b …)` — chained equality over ≥2 string expressions.
        "=" if items.len() >= 3 => {
            let Some(terms) = word_terms_flat(arena, &items[1..], vars, wp, opaque) else {
                return false;
            };
            for &t in &terms[1..] {
                wp.equalities.push((terms[0], t));
            }
            true
        }
        // `(distinct a b …)` — pairwise disequality over ≥2 string expressions.
        "distinct" if items.len() >= 3 => {
            let Some(terms) = word_terms_flat(arena, &items[1..], vars, wp, opaque) else {
                return false;
            };
            for i in 0..terms.len() {
                for &t in &terms[i + 1..] {
                    wp.disequalities.push((terms[i], t));
                }
            }
            true
        }
        // `(not (= a b))` — a single disequality (exactly two operands: a deeper
        // negation `¬(a=b=c)` is a *disjunction*, not representable, so decline).
        "not" if items.len() == 2 => {
            let Some(inner) = items[1].list() else {
                return false;
            };
            if inner.first().and_then(SExpr::atom) == Some("=") && inner.len() == 3 {
                let Some(terms) = word_terms_flat(arena, &inner[1..], vars, wp, opaque) else {
                    return false;
                };
                wp.disequalities.push((terms[0], terms[1]));
                true
            } else {
                false
            }
        }
        // Positive-polarity extended-function reductions (T-B.4c): prefixof /
        // suffixof / contains. Each is equisatisfiable with the atom *in this
        // positive position* (see `word_extended_fn`). Negative/disjunctive
        // contexts never reach here — see the `word_atom` / module polarity notes.
        _ => word_extended_fn(arena, head, items, vars, wp, next_k, opaque),
    }
}

/// Reduces a positive-polarity extended-function atom (`str.prefixof` /
/// `str.suffixof` / `str.contains`) to a fresh-variable word equation, pushed
/// into `wp`. Returns `false` (abort the whole side channel) for any other head
/// or an unrepresentable operand.
///
/// Each reduction is *sat-implying* in this positive position — a witness for the
/// fresh-variable equality makes the original atom true — so the route stays
/// sound (never sat-admitting):
///
///   * `(str.prefixof p x)` ⟺ `∃k.     x = p ++ k`
///   * `(str.suffixof s x)` ⟺ `∃k.     x = k ++ s`
///   * `(str.contains x c)` ⟺ `∃k1,k2. x = k1 ++ c ++ k2`
///
/// The fresh `k`/`k1`/`k2` are never recorded in `wp.seq_symbols`, so they never
/// surface in a returned model.
fn word_extended_fn(
    arena: &mut TermArena,
    head: &str,
    items: &[SExpr],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    wp: &mut WordProblem,
    next_k: &mut u32,
    opaque: &mut OpaqueCtx,
) -> bool {
    if items.len() != 3 {
        return false;
    }
    let (Some(a), Some(b)) = (
        word_str_expr_flat(arena, &items[1], vars, wp, opaque),
        word_str_expr_flat(arena, &items[2], vars, wp, opaque),
    ) else {
        return false;
    };
    // Build the equisatisfiable right-hand side; `?`-style bail on any arena error
    // or unrecognized head collapses the whole side channel (all-or-nothing).
    let equality = match head {
        // (str.prefixof p x): a = p, b = x  ⇒  x = p ++ k.
        "str.prefixof" => fresh_seq_k(arena, next_k)
            .and_then(|k| arena.seq_concat(a, k).ok())
            .map(|rhs| (b, rhs)),
        // (str.suffixof s x): a = s, b = x  ⇒  x = k ++ s.
        "str.suffixof" => fresh_seq_k(arena, next_k)
            .and_then(|k| arena.seq_concat(k, a).ok())
            .map(|rhs| (b, rhs)),
        // (str.contains x c): a = x, b = c  ⇒  x = k1 ++ c ++ k2.
        "str.contains" => {
            let k1 = fresh_seq_k(arena, next_k);
            let k2 = fresh_seq_k(arena, next_k);
            match (k1, k2) {
                (Some(k1), Some(k2)) => arena
                    .seq_concat(b, k2)
                    .and_then(|tail| arena.seq_concat(k1, tail))
                    .ok()
                    .map(|rhs| (a, rhs)),
                _ => None,
            }
        }
        _ => return false,
    };
    match equality {
        Some(eq) => {
            wp.equalities.push(eq);
            true
        }
        None => false,
    }
}

/// Translates every element of `exprs` as a string expression, returning `None`
/// if any is not one.
fn word_terms(
    arena: &mut TermArena,
    exprs: &[SExpr],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
) -> Option<Vec<TermId>> {
    exprs
        .iter()
        .map(|e| word_str_expr(arena, e, vars))
        .collect()
}

/// The flat-word-problem context for the opaque `str.from_int`/`str.substr` subterms
/// (task #77): the declared `Int` variables (name → symbol) and the intern table +
/// counter for the fresh `Seq` variables that stand in for symbolic occurrences.
struct OpaqueCtx<'a> {
    /// Declared integer variables (`name → Int symbol`) — the inversion targets.
    int_vars: &'a BTreeMap<String, SymbolId>,
    /// Structurally-identical opaque subterms → the one fresh `Seq` variable term
    /// standing for them (so `(str.from_int i)` written twice shares one obligation).
    intern: BTreeMap<String, TermId>,
    /// Monotonic counter for unique `!weqop!<n>` fresh-variable names.
    next: u32,
}

/// The flat-path [`word_terms`]: translates each element as a string expression
/// **with** `str.from_int`/`str.substr` support (see [`word_str_expr_flat`]).
fn word_terms_flat(
    arena: &mut TermArena,
    exprs: &[SExpr],
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    wp: &mut WordProblem,
    opaque: &mut OpaqueCtx,
) -> Option<Vec<TermId>> {
    exprs
        .iter()
        .map(|e| word_str_expr_flat(arena, e, vars, wp, opaque))
        .collect()
}

/// The flat-path [`word_str_expr`] (task #77). Identical to [`word_str_expr`] except
/// it also recognizes two integer-coupled `Seq`-producing functions:
///
///   * `(str.from_int n)` / `(str.substr lit off n)` with a **ground** integer
///     argument fold directly to their literal value (pure constant folding, exactly
///     like an inline string literal — no obligation);
///   * `(str.from_int i)` / `(str.substr lit off i)` over a **declared `Int`
///     variable** are replaced by a fresh `Seq` variable and recorded as a
///     [`WordObligation`], so the solver inverts the solved string value back onto the
///     integer argument after the arrangement search (see [`WordProblem::obligations`]).
///
/// Every other shape delegates to [`word_str_expr`] (literal / variable / `str.++`
/// recursion carries the opaque support inward / constant-folded `str.replace`).
fn word_str_expr_flat(
    arena: &mut TermArena,
    e: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
    wp: &mut WordProblem,
    opaque: &mut OpaqueCtx,
) -> Option<TermId> {
    if let SExpr::List(items) = e {
        match items.first().and_then(SExpr::atom) {
            // `(str.++ …)` — recurse with the flat translator so a nested
            // `str.from_int`/`str.substr` operand is still recognized.
            Some("str.++") if items.len() >= 2 => {
                let mut acc = word_str_expr_flat(arena, &items[1], vars, wp, opaque)?;
                for it in &items[2..] {
                    let next = word_str_expr_flat(arena, it, vars, wp, opaque)?;
                    acc = arena.seq_concat(acc, next).ok()?;
                }
                return Some(acc);
            }
            // `(str.from_int n)`.
            Some("str.from_int") if items.len() == 2 => {
                // Ground argument → fold to the canonical decimal literal.
                if let Some(n) = parse_int_literal(&items[1]) {
                    return seq_from_code_points(arena, &decimal_code_points(n));
                }
                // Symbolic argument → fresh `Seq` variable + inversion obligation.
                let int_sym = *items[1].atom().and_then(|nm| opaque.int_vars.get(nm))?;
                let (term, seq_sym) = opaque_fresh(arena, e, opaque)?;
                if let Some(sym) = seq_sym {
                    wp.obligations.push(WordObligation::FromInt {
                        seq_sym: sym,
                        int_sym,
                    });
                }
                return Some(term);
            }
            // `(str.substr lit off n)` with a **constant string subject** and a
            // **constant offset**.
            Some("str.substr") if items.len() == 4 => {
                let literal = literal_pattern_cps(&items[1])?;
                let offset = parse_int_literal(&items[2])?;
                // Ground length → fold to the exact substring literal.
                if let Some(len) = parse_int_literal(&items[3]) {
                    return seq_from_code_points(arena, &substr_code_points(&literal, offset, len));
                }
                // Symbolic length → fresh `Seq` variable + inversion obligation.
                let len_sym = *items[3].atom().and_then(|nm| opaque.int_vars.get(nm))?;
                let (term, seq_sym) = opaque_fresh(arena, e, opaque)?;
                if let Some(sym) = seq_sym {
                    wp.obligations.push(WordObligation::Substr {
                        seq_sym: sym,
                        literal,
                        offset,
                        len_sym,
                    });
                }
                return Some(term);
            }
            _ => {}
        }
    }
    // Everything else: the base string-expression fragment.
    word_str_expr(arena, e, vars)
}

/// Returns the interned fresh `Seq` variable term for the opaque subterm `e`, plus
/// its symbol **only when freshly minted** (so the caller records exactly one
/// obligation per structurally-distinct opaque term). A re-encountered opaque term
/// reuses the existing fresh variable and yields `None` for the symbol.
fn opaque_fresh(
    arena: &mut TermArena,
    e: &SExpr,
    opaque: &mut OpaqueCtx,
) -> Option<(TermId, Option<SymbolId>)> {
    let key = sexpr_key(e);
    if let Some(&term) = opaque.intern.get(&key) {
        return Some((term, None));
    }
    let n = opaque.next;
    opaque.next += 1;
    // `!weqop!<n>` is disjoint from the `!weq!<name>` user variables and the
    // `!weqk!<n>` extended-function skolems (distinct fifth byte), so a fresh opaque
    // variable can never alias any of them.
    let sym = arena
        .declare_internal(&format!("!weqop!{n}"), Sort::string())
        .ok()?;
    let term = arena.var(sym);
    opaque.intern.insert(key, term);
    Some((term, Some(sym)))
}

/// A structural key for interning identical opaque subterms.
fn sexpr_key(e: &SExpr) -> String {
    match e {
        SExpr::Atom(a) => a.clone(),
        SExpr::List(items) => {
            let mut s = String::from("(");
            for (i, it) in items.iter().enumerate() {
                if i > 0 {
                    s.push(' ');
                }
                s.push_str(&sexpr_key(it));
            }
            s.push(')');
            s
        }
    }
}

/// Recognizes a linear integer bound atom `(⋈ var lit)` or `(⋈ lit var)` where `var`
/// is a **declared `Int` variable** (in `int_vars`), `lit` an integer literal, and
/// `⋈ ∈ {>=, >, <=, <, =}` (task #78). Returns the normalized [`IntBound`] on the
/// variable's symbol, or `None` for any other shape (two variables, two literals, a
/// compound arithmetic operand, a non-relational head, or the wrong arity). The
/// `(lit ⋈ var)` orientation flips the relation so the bound is always `var ⋈ lit`.
fn int_bound_atom(
    head: &str,
    items: &[SExpr],
    int_vars: &BTreeMap<String, SymbolId>,
) -> Option<IntBound> {
    let kind = match head {
        ">=" => IntBoundKind::Ge,
        ">" => IntBoundKind::Gt,
        "<=" => IntBoundKind::Le,
        "<" => IntBoundKind::Lt,
        "=" => IntBoundKind::Eq,
        _ => return None,
    };
    if items.len() != 3 {
        return None;
    }
    let lhs = &items[1];
    let rhs = &items[2];
    // `(⋈ var lit)`.
    if let (Some(&sym), Some(bound)) = (
        lhs.atom().and_then(|n| int_vars.get(n)),
        parse_int_literal(rhs),
    ) {
        return Some(IntBound { sym, kind, bound });
    }
    // `(⋈ lit var)` — flip the relation so the bound reads `var ⋈ lit`.
    if let (Some(bound), Some(&sym)) = (
        parse_int_literal(lhs),
        rhs.atom().and_then(|n| int_vars.get(n)),
    ) {
        let flipped = match kind {
            IntBoundKind::Ge => IntBoundKind::Le,
            IntBoundKind::Gt => IntBoundKind::Lt,
            IntBoundKind::Le => IntBoundKind::Ge,
            IntBoundKind::Lt => IntBoundKind::Gt,
            IntBoundKind::Eq => IntBoundKind::Eq,
        };
        return Some(IntBound {
            sym,
            kind: flipped,
            bound,
        });
    }
    None
}

/// Recognizes a constant-string `str.to_int` pin atom `(= var (str.to_int <literal>))`
/// or `(= (str.to_int <literal>) var)`, where `var` is a **declared `Int` variable**
/// (in `int_vars`) and `<literal>` is a string constant (task #79). Returns the pin
/// `(var-symbol, str.to_int value)` — the exact SMT-LIB `str.to_int` of the literal —
/// or `None` for any other shape (a `str.to_int` over a *symbolic* string, a non-int
/// left/right operand, the wrong head/arity, or a literal whose all-digit value
/// overflows `i128`, which is declined so the value is never truncated to a wrong
/// integer).
///
/// The pin is **exact**: `str.to_int` of a constant string is a closed function value,
/// so binding `var` to it is model-defining with no search — the mirror of folding
/// `str.from_int` of a constant into a string literal.
fn to_int_const_pin_atom(
    head: &str,
    items: &[SExpr],
    int_vars: &BTreeMap<String, SymbolId>,
) -> Option<(SymbolId, i128)> {
    if head != "=" || items.len() != 3 {
        return None;
    }
    // Extract the `(str.to_int <literal>)` value from whichever side is that shape.
    let to_int_val = |e: &SExpr| -> Option<i128> {
        let sub = e.list()?;
        if sub.len() != 2 || sub[0].atom() != Some("str.to_int") {
            return None;
        }
        let cps = literal_pattern_cps(&sub[1])?;
        to_int_of_code_points(&cps)
    };
    let var_sym =
        |e: &SExpr| -> Option<SymbolId> { e.atom().and_then(|n| int_vars.get(n)).copied() };
    // `(= var (str.to_int lit))`.
    if let (Some(sym), Some(v)) = (var_sym(&items[1]), to_int_val(&items[2])) {
        return Some((sym, v));
    }
    // `(= (str.to_int lit) var)`.
    if let (Some(v), Some(sym)) = (to_int_val(&items[1]), var_sym(&items[2])) {
        return Some((sym, v));
    }
    None
}

/// The exact SMT-LIB `UnicodeStrings` `str.to_int` value of a constant string given by
/// its Unicode code points (task #79): the decimal value when **every** code point is
/// an ASCII digit `'0'..='9'` (leading zeros allowed — `to_int("01") = 1`), and `-1`
/// for the empty string or any string containing a non-digit code point (a `'-'` sign,
/// letters, wide code points, …). Returns `None` — decline, never a wrong pin — when an
/// all-digit value overflows `i128`, since the exact value cannot then be represented.
fn to_int_of_code_points(cps: &[u32]) -> Option<i128> {
    if cps.is_empty() {
        return Some(-1);
    }
    let mut acc: i128 = 0;
    for &c in cps {
        if !(0x30..=0x39).contains(&c) {
            return Some(-1);
        }
        let digit = i128::from(c - 0x30);
        acc = acc.checked_mul(10)?.checked_add(digit)?;
    }
    Some(acc)
}

/// Parses an SMT-LIB integer literal: a bare numeral atom, or `(- n)` for a negative
/// numeral. Returns `None` for any other (compound / symbolic) integer expression.
fn parse_int_literal(e: &SExpr) -> Option<i128> {
    match e {
        SExpr::Atom(a) => a.parse::<i128>().ok(),
        SExpr::List(items) => {
            if items.len() == 2 && items[0].atom() == Some("-") {
                let n = items[1].atom()?.parse::<i128>().ok()?;
                n.checked_neg()
            } else {
                None
            }
        }
    }
}

/// The Unicode code points of `str.from_int(n)` (SMT-LIB `UnicodeStrings`): the
/// canonical decimal digits of a non-negative `n` (no leading zeros; `0` → "0"), or
/// the empty sequence for a negative `n`.
fn decimal_code_points(n: i128) -> Vec<u32> {
    if n < 0 {
        return Vec::new();
    }
    n.to_string().chars().map(|c| c as u32).collect()
}

/// The Unicode code points of `str.substr(s, offset, len)` (SMT-LIB totality): the
/// maximal substring of `s` starting at `offset` of length at most `len`, or empty
/// when `offset` is out of `0..|s|` or `len ≤ 0`.
fn substr_code_points(s: &[u32], offset: i128, len: i128) -> Vec<u32> {
    if offset < 0 || len <= 0 {
        return Vec::new();
    }
    let Ok(off) = usize::try_from(offset) else {
        return Vec::new();
    };
    if off >= s.len() {
        return Vec::new();
    }
    let take = usize::try_from(len)
        .unwrap_or(usize::MAX)
        .min(s.len() - off);
    s[off..off + take].to_vec()
}

/// Translates one string expression into a `Seq`-sorted term: a string literal,
/// a declared string variable, `(str.++ …)` over string expressions, or a
/// **constant-folded** `(str.replace H N R)` whose haystack `H` and needle `N` are
/// string constants (the replacement `R` may be any string expression). Returns
/// `None` for anything else.
fn word_str_expr(
    arena: &mut TermArena,
    e: &SExpr,
    vars: &BTreeMap<String, (SymbolId, TermId)>,
) -> Option<TermId> {
    match e {
        SExpr::Atom(a) => {
            if a.len() >= 2 && a.starts_with('"') && a.ends_with('"') {
                word_literal(arena, a)
            } else {
                vars.get(a).map(|&(_, term)| term)
            }
        }
        SExpr::List(items) => match items.first().and_then(SExpr::atom) {
            Some("str.++") if items.len() >= 2 => {
                let mut acc = word_str_expr(arena, &items[1], vars)?;
                for it in &items[2..] {
                    let next = word_str_expr(arena, it, vars)?;
                    acc = arena.seq_concat(acc, next).ok()?;
                }
                Some(acc)
            }
            // `(str.replace H N R)` with **constant** `H` and `N`: the first
            // occurrence of `N` in `H` is fixed at translation time, so the whole
            // term reduces to `H[..i] ++ R ++ H[i+|N|..]` (or `H` if `N ∉ H`) — an
            // *exact*, value-preserving rewrite (verified against the SMT-LIB
            // first-occurrence semantics, including the empty-needle case
            // `replace(H,ε,R) = R ++ H` where `i = 0`). `R` itself may be any string
            // expression, so a variable replacement stays symbolic.
            Some("str.replace") if items.len() == 4 => {
                let haystack = literal_pattern_cps(&items[1])?;
                let needle = literal_pattern_cps(&items[2])?;
                let replacement = word_str_expr(arena, &items[3], vars)?;
                match first_occurrence(&haystack, &needle) {
                    Some(i) => {
                        // `H[..i] ++ R ++ H[i+|N|..]`, but skip an *empty* prefix or
                        // suffix segment so the folded term interns identically to a
                        // written `(str.++ …)` (no stray leading/trailing `ε` concat,
                        // which the flat refuter would not normalize away).
                        let pre = &haystack[..i];
                        let suf = &haystack[i + needle.len()..];
                        let mut acc = replacement;
                        if !pre.is_empty() {
                            let pre_t = seq_from_code_points(arena, pre)?;
                            acc = arena.seq_concat(pre_t, acc).ok()?;
                        }
                        if !suf.is_empty() {
                            let suf_t = seq_from_code_points(arena, suf)?;
                            acc = arena.seq_concat(acc, suf_t).ok()?;
                        }
                        Some(acc)
                    }
                    // Needle absent ⇒ the string is unchanged.
                    None => seq_from_code_points(arena, &haystack),
                }
            }
            _ => None,
        },
    }
}

/// The start index of the **first** occurrence of `needle` in `haystack` (an empty
/// needle occurs at index 0), or `None` when `needle` does not occur.
fn first_occurrence(haystack: &[u32], needle: &[u32]) -> Option<usize> {
    if needle.is_empty() {
        return Some(0);
    }
    if needle.len() > haystack.len() {
        return None;
    }
    (0..=haystack.len() - needle.len()).find(|&i| haystack[i..i + needle.len()] == *needle)
}

/// Builds the `Seq(BitVec(18))` term for a string literal atom (quotes included,
/// `""`-escaped quotes) as the right-associated `seq.unit` chain of its Unicode
/// code points — matching the `axeyum-strings` constant convention. The empty
/// literal `""` is `seq.empty`.
fn word_literal(arena: &mut TermArena, atom: &str) -> Option<TermId> {
    let inner = atom[1..atom.len() - 1].replace("\"\"", "\"");
    // Expand `\u{…}` / `\uhhhh` escapes to code points (shared with the byte-model
    // route, so `"\u{62}"` is the one character `b` on every route).
    let code_points = decode_string_code_points(&inner)?;
    seq_from_code_points(arena, &code_points)
}

/// Builds the `Seq(BitVec(18))` term for a Unicode code-point sequence as the
/// right-associated `seq.unit` chain (matching the `axeyum-strings` constant
/// convention). The empty sequence is `seq.empty`.
fn seq_from_code_points(arena: &mut TermArena, code_points: &[u32]) -> Option<TermId> {
    let key = ArraySortKey::BitVec(Sort::STRING_ELEM_WIDTH);
    if code_points.is_empty() {
        return Some(arena.seq_empty(key));
    }
    // Right-associate: unit(c0) ++ (unit(c1) ++ (… ++ unit(cn))).
    let mut acc: Option<TermId> = None;
    for &cp in code_points.iter().rev() {
        let elem = arena
            .bv_const(Sort::STRING_ELEM_WIDTH, u128::from(cp))
            .ok()?;
        let unit = arena.seq_unit(elem).ok()?;
        acc = Some(match acc {
            None => unit,
            Some(rest) => arena.seq_concat(unit, rest).ok()?,
        });
    }
    acc
}

// --- constant arrays: `(select ((as const A) v) i)` → `v` --------------------
//
// A *constant array* `((as const (Array I E)) v)` is the function that maps every
// index to the single value `v`. The defining identity is therefore
//
//     ∀ i.  (select ((as const A) v) i) = v
//
// which is **sort-agnostic**: it holds for any index sort `I` and element sort `E`
// (`Int`, `Bool`, `BitVec`, …). This lets us decide const-array formulas — e.g.
// the cvc5 `QF_ALIA` `constarr` family, `(Array Int Int)` / `(Array Int Bool)` —
// entirely by an s-expression rewrite even before the generic non-BV array
// solver/model-projection route is complete.
//
// # The sound subset (everything else is declined)
//
// A symbol `s` is treated as a *const-array alias* when the script binds it,
// **exactly once**, with a top-level assertion `(= s ca)` (or `(= ca s)`) whose
// right side `ca` is a const-array expression: either a literal
// `((as const A) v)` or a `store`-chain over one. We then:
//
//   * substitute every *other* use of `s` by `ca` (so all reads/equalities see
//     the concrete const array), and
//   * drop both the defining assertion and `s`'s `declare-const`/`declare-fun`,
//     so the residual query no longer needs a model for that array symbol.
//
// With the aliases inlined, the remaining const-array operators are reduced
// bottom-up by [`reduce_const_array_sexpr`]:
//
//   * `(select ca i)` with `ca` a literal const array → its value `v`. Sound by
//     the identity above, for *any* index term `i`.
//   * `(select (store arr j w) i)` → `(ite (= i j) w (select arr i))`
//     (read-over-write, SMT-LIB array axiom), recursing until it bottoms out at a
//     const array. The `=` over the index sort and the `ite` over the element sort
//     are ordinary terms axeyum already decides.
//   * `(= ca1 ca2)` with **both** sides const arrays → `(= v1 v2)` (two constant
//     arrays are extensionally equal iff their values are equal — the index sort
//     is non-empty, so the universally-quantified pointwise equality collapses to
//     the single value equality).
//
// Anything outside this subset is left for the ordinary IR/solver route and may
// still return a sound `unknown`, never a wrong verdict:
//
//   * A `select`/`store` over a *free* (non-const-derived) `Int`-array variable —
//     the general `Int`-array decision procedure is represented in IR but not
//     model-producing yet.
//   * A `store`-chain equality connecting two *different* const arrays
//     (`constarr3`) — `(= ca1 ca2)` where the sides are `store`-derived, not bare
//     const arrays — is not reduced (cvc5 itself errors on this), so the residual
//     non-BV `Array` equality is left for the downstream array route.
//   * A const array of a non-modelable element sort declines when its value `v`
//     reaches term conversion.
//
// Soundness rests only on the array axioms (read-over-write and constant-array
// extensionality), so no wrong `sat`/`unsat` is possible: every rewrite step is a
// denotation-preserving equality.

/// Constant-array elimination over the whole script's s-expression tree
/// (in place), before any term is built. See the module note above for the
/// sound subset; out-of-subset const-array shapes are left for the existing sort
/// machinery to decline (never given a wrong verdict).
///
/// Fast path: a script that mentions no `as const` form is left untouched (and
/// unallocated). This pass never fails — unsupported residual array forms are
/// declined later by [`parse_sort`]/term conversion — so it returns `()` rather
/// than a `Result` (unlike the fallible [`desugar_sets`]).
fn desugar_const_arrays(exprs: &mut Vec<SExpr>) {
    // Fast path: nothing const-array-related anywhere.
    if !exprs.iter().any(mentions_const_array) {
        return;
    }
    // Phase A — collect const-array aliases: symbols bound *exactly once* by a
    // top-level `(assert (= s ca))` / `(assert (= ca s))` whose `ca` is a
    // const-array expression. A symbol bound more than once, or also used as a
    // store target in a way we cannot inline, is left un-aliased (so its uses
    // decline through the normal path rather than risk an unsound substitution).
    let mut alias_value: HashMap<String, SExpr> = HashMap::new();
    let mut alias_disqualified: HashSet<String> = HashSet::new();
    for e in exprs.iter() {
        if let Some((sym, ca)) = const_array_definition(e) {
            if alias_value.contains_key(sym) || alias_disqualified.contains(sym) {
                // Seen twice: a single concrete const-array binding is required for
                // a sound inline, so disqualify the symbol entirely.
                alias_value.remove(sym);
                alias_disqualified.insert(sym.to_owned());
            } else {
                alias_value.insert(sym.to_owned(), ca.clone());
            }
        }
    }
    if alias_value.is_empty() {
        // No safely-inlinable const-array alias; only literal const-array forms (if
        // any) remain, which `reduce_const_array_sexpr` handles directly below.
        for e in exprs.iter_mut() {
            reduce_const_array_sexpr(e);
        }
        return;
    }
    // Phase B — rewrite the command list:
    //   * drop the `declare-const`/`declare-fun` of every aliased symbol,
    //   * drop each aliased symbol's defining `(assert (= s ca))`,
    //   * inline `s → ca` everywhere else, then reduce const-array operators.
    let mut rewritten: Vec<SExpr> = Vec::with_capacity(exprs.len());
    for e in exprs.drain(..) {
        if is_alias_declaration(&e, &alias_value) || is_alias_definition(&e, &alias_value) {
            continue;
        }
        let mut e = e;
        inline_aliases(&mut e, &alias_value);
        reduce_const_array_sexpr(&mut e);
        rewritten.push(e);
    }
    *exprs = rewritten;
}

/// Whether `e` mentions an `(as const …)` constant-array head anywhere.
fn mentions_const_array(e: &SExpr) -> bool {
    match e {
        SExpr::Atom(_) => false,
        SExpr::List(items) => {
            (items.first().and_then(SExpr::atom) == Some("as")
                && items.get(1).and_then(SExpr::atom) == Some("const"))
                || items.iter().any(mentions_const_array)
        }
    }
}

/// Whether `e` is a constant-array *expression*: a literal `((as const A) v)`, or
/// a `store`-chain whose base is one. (A bare symbol is *not* — alias inlining
/// turns symbols into these before reduction.)
fn is_const_array_expr(e: &SExpr) -> bool {
    let Some(items) = e.list() else { return false };
    if is_const_array_literal(e) {
        return true;
    }
    // `(store arr j w)` over a const-array base.
    items.len() == 4 && items[0].atom() == Some("store") && is_const_array_expr(&items[1])
}

/// Whether `e` is a *literal* constant array `((as const A) v)` whose array sort
/// `A` is **not** purely bit-vector-indexed/valued — a list whose head is the
/// `(as const A)` qualified identifier with one argument (the value).
///
/// The bit-vector-array case (`(Array (_ BitVec i) (_ BitVec e))`) is deliberately
/// *excluded*: those const arrays are already handled by the IR
/// `arena.const_array` and `eliminate_arrays` path (ADR-0010, `QF_ABV`), and this
/// pass must leave that working path untouched (no regression). Non-BV-array
/// const arrays (`(Array Int Int)`, `(Array Int Bool)`, …) are still simplified
/// here because it avoids requiring a generic array model for those symbols.
fn is_const_array_literal(e: &SExpr) -> bool {
    let Some(items) = e.list() else { return false };
    if items.len() != 2 {
        return false;
    }
    let Some(head) = items[0].list() else {
        return false;
    };
    head.first().and_then(SExpr::atom) == Some("as")
        && head.len() == 3
        && head[1].atom() == Some("const")
        && !is_bv_array_sort(&head[2])
}

/// Whether the sort s-expr `s` is `(Array (_ BitVec i) (_ BitVec e))` — a purely
/// bit-vector-indexed/valued array, which the existing IR array path handles. Used
/// to *exclude* BV const arrays from the s-expression const-array rewrite so the
/// `QF_ABV` path is left untouched.
fn is_bv_array_sort(s: &SExpr) -> bool {
    let Some(items) = s.list() else { return false };
    items.len() == 3
        && items[0].atom() == Some("Array")
        && is_bv_sort_sexpr(&items[1])
        && is_bv_sort_sexpr(&items[2])
}

/// Whether the sort s-expr `s` is `(_ BitVec n)`.
fn is_bv_sort_sexpr(s: &SExpr) -> bool {
    s.list().is_some_and(|items| {
        items.len() == 3 && items[0].atom() == Some("_") && items[1].atom() == Some("BitVec")
    })
}

/// If `e` is `(assert (= s ca))` or `(assert (= ca s))` with `s` a symbol and
/// `ca` a const-array expression, return `(s, ca)`. Used to collect const-array
/// aliases; only the **defining** equality is matched (a single value binding).
fn const_array_definition(e: &SExpr) -> Option<(&str, &SExpr)> {
    let items = e.list()?;
    if items.len() != 2 || items[0].atom() != Some("assert") {
        return None;
    }
    let eq = items[1].list()?;
    if eq.len() != 3 || eq[0].atom() != Some("=") {
        return None;
    }
    // `(= s ca)` or `(= ca s)`.
    if let Some(s) = eq[1].atom()
        && is_const_array_expr(&eq[2])
    {
        return Some((s, &eq[2]));
    }
    if let Some(s) = eq[2].atom()
        && is_const_array_expr(&eq[1])
    {
        return Some((s, &eq[1]));
    }
    None
}

/// Whether `e` is `(declare-const s …)` / `(declare-fun s () …)` for a symbol `s`
/// in `aliases` (so the declaration of an inlined const-array alias is dropped).
fn is_alias_declaration(e: &SExpr, aliases: &HashMap<String, SExpr>) -> bool {
    let Some(items) = e.list() else { return false };
    let head = items.first().and_then(SExpr::atom);
    if head != Some("declare-const") && head != Some("declare-fun") {
        return false;
    }
    items
        .get(1)
        .and_then(SExpr::atom)
        .is_some_and(|s| aliases.contains_key(s))
}

/// Whether `e` is the defining `(assert (= s ca))` of an aliased symbol `s`
/// (dropped after inlining: the binding is captured in the alias map).
fn is_alias_definition(e: &SExpr, aliases: &HashMap<String, SExpr>) -> bool {
    const_array_definition(e).is_some_and(|(s, _)| aliases.contains_key(s))
}

/// Replace every *atom* use of an aliased const-array symbol by its const-array
/// value expression, recursively. Inlining a definition-free term position is
/// sound: the alias map holds exactly the const array the symbol was asserted
/// equal to.
fn inline_aliases(e: &mut SExpr, aliases: &HashMap<String, SExpr>) {
    match e {
        SExpr::Atom(a) => {
            if let Some(ca) = aliases.get(a) {
                *e = ca.clone();
            }
        }
        SExpr::List(items) => {
            for child in items.iter_mut() {
                inline_aliases(child, aliases);
            }
        }
    }
}

/// Reduce constant-array operators bottom-up (in place):
///
/// * `(select ca i)` with `ca` a literal const array → its value `v`;
/// * `(select (store arr j w) i)` → `(ite (= i j) w (select arr i))`, recursing
///   until it bottoms out at a const array;
/// * `(= ca1 ca2)` with both sides literal const arrays → `(= v1 v2)`.
///
/// Forms outside this subset are left untouched (and decline through the normal
/// sort machinery). Every step is denotation-preserving (the array axioms).
fn reduce_const_array_sexpr(e: &mut SExpr) {
    let SExpr::List(items) = e else { return };
    // Bottom-up: reduce children first so a `select` over a freshly-reduced
    // store-chain still sees the const array underneath.
    for child in items.iter_mut() {
        reduce_const_array_sexpr(child);
    }
    let Some(head) = items.first().and_then(SExpr::atom) else {
        return;
    };
    match head {
        // `(select arr i)`.
        "select" if items.len() == 3 => {
            if let Some(v) = const_array_value(&items[1]) {
                // `(select ((as const A) v) i)` = `v` for any `i`.
                *e = v.clone();
            } else if let Some(items1) = items[1].list()
                && items1.len() == 4
                && items1[0].atom() == Some("store")
            {
                // Read-over-write: `(select (store arr j w) i)`
                //   → `(ite (= i j) w (select arr i))`.
                let arr = items1[1].clone();
                let j = items1[2].clone();
                let w = items1[3].clone();
                let i = items[2].clone();
                let mut inner = SExpr::List(vec![atom("select"), arr, i.clone()]);
                reduce_const_array_sexpr(&mut inner);
                *e = SExpr::List(vec![
                    atom("ite"),
                    SExpr::List(vec![atom("="), i, j]),
                    w,
                    inner,
                ]);
            }
        }
        // `(= a b)` between two literal const arrays → value equality.
        "=" if items.len() == 3 => {
            if let (Some(v1), Some(v2)) =
                (const_array_value(&items[1]), const_array_value(&items[2]))
            {
                *e = SExpr::List(vec![atom("="), v1.clone(), v2.clone()]);
            }
        }
        _ => {}
    }
}

/// The value `v` of a *literal* constant array `((as const A) v)`, or `None`.
fn const_array_value(e: &SExpr) -> Option<&SExpr> {
    if is_const_array_literal(e) {
        e.list().map(|items| &items[1])
    } else {
        None
    }
}

// --- finite-set theory: `(Set E)` modeled as `BitVec(W)` ---------------------
//
// SMT-LIB's finite-set theory (cvc5 `set.*`) over a finite element domain is
// isomorphic to the powerset of the domain, which is exactly a bit-set. We model
// `(Set E)` as a `BitVec(W)` where each bit position is a distinct element of the
// modeled domain, and rewrite the **denotation-preserving subset** of the set
// operators to bit-vector operators, entirely at the s-expression level (so no IR
// `Sort`/`Op` change is needed — just like uninterpreted sorts, `79a0679`).
//
// # The modeled element domain and its bit positions
//
// The only set elements a quantifier-free formula can *name* are the terms that
// appear as the element argument of `set.singleton`/`set.member`. We give each
// **distinct** such element term its own bit index `0..D` (`D` distinct element
// terms), plus a `MARGIN` of extra high "junk" bits standing for elements the
// formula never names. The width is `W = D + MARGIN` (at least `1`).
//
// # Soundness — when is this denotation-preserving?
//
// The encoding is exact (isomorphic to the real powerset semantics) provided two
// conditions hold, which [`scan_set_ops`] enforces by **declining** (leaving the
// whole script [`SmtError::Unsupported`]) otherwise:
//
//  1. **Distinct element terms denote distinct elements.** We only accept element
//     terms that are *constant literals* (numerals, decimals, `#b`/`#x`/`(_ bvN
//     W)` bit-vectors, `true`/`false`). Two syntactically-distinct literals are
//     two distinct values, so giving them distinct bits introduces no spurious
//     (dis)equality. (Arithmetic element terms such as `(* v0 7)` can *alias*
//     another element term — `(* 7 v0)` — so a per-term bit would be unsound
//     without congruence constraints; those files are declined for a later
//     slice.)
//
//  2. **Only finite-domain-safe operators.** `set.empty`, `set.singleton`,
//     `set.member`, `set.union`, `set.inter`, `set.minus`, `set.subset`, and set
//     `=`/`distinct` are all pointwise over the membership function, so they
//     commute with projecting onto the modeled domain: `union=bvor`,
//     `inter=bvand`, `minus=bvand-bvnot`, `member=bit test`, `subset=(a = a&b)`.
//     The `MARGIN` junk bits let a *free* set variable differ from another set on
//     unnamed elements (so `(not (= x y))` over two free sets is `sat`, and an
//     equality never wrongly forces two free sets equal on the unnamed tail).
//     `set.complement` and `set.universe` are **not** pointwise on a finite
//     projection — they quantify over the *whole* (possibly infinite) element
//     sort — so they are declined (a `BitVec` complement over the modeled domain
//     would give a *wrong* complement for the unnamed tail).
//     `set.comprehension`/`set.choose`/`set.insert`/etc. are likewise declined.
//
// Under (1) and (2) every set term denotes a subset of the modeled domain and
// every operator is computed exactly on that domain, so a model of the `BitVec`
// encoding lifts to a set model (map bit `i` to element `i`, and realize the
// junk bits with that many fresh distinct unnamed elements) and vice-versa: the
// encoding is **equisatisfiable**, so neither a wrong `sat` nor a wrong `unsat`
// is possible.
//
// # Cardinality over a slack universe
//
// `set.card S` is the *count* of elements in `S`. Naive popcount over the
// `D + MARGIN` named-element width above would be **wrong**: a free set ranges
// over the infinite element sort, so its true cardinality includes the unnamed
// tail, which the few junk bits cannot represent. Instead, when (and only when) a
// script uses `set.card`, we **widen the modeled universe** to a *slack universe*
// of `N` abstract element slots, where
//
//   `N = D + (sum of every numeric literal in the script)
//          + (number of `set.card` occurrences) + MARGIN`.
//
// At this width each `(Set E)` free variable is a free `BitVec(N)`, every set
// operator is the same pointwise `bv*` as above, and
//
//   `set.card S` → `Σ_{i<N} bv2nat((_ extract i i) S)`  (an `Int` popcount).
//
// **Soundness (no wrong sat, no wrong unsat).** This is exactly the theory of
// *subsets of an `N`-element universe* — sound and complete for that theory. The
// only question is whether restricting from arbitrary subsets of the infinite
// sort down to subsets of `N` slots can change satisfiability:
//
//  * **No wrong sat (encoding ⇒ real).** Any satisfying bit assignment lifts to a
//    real set model: pick `N` distinct elements of the (infinite) sort, one per
//    slot; every `bv*` operator then *is* the corresponding set operator and
//    popcount *is* cardinality, so every satisfied constraint is a true statement
//    about genuine finite sets.
//
//  * **No wrong unsat (real ⇒ encoding).** A real satisfying model can be
//    *compressed* to use at most `N` distinct elements. Because the accepted
//    subset has **no complement/universe** and only **distinct-literal** elements,
//    two unnamed elements sharing the same Venn region (w.r.t. the set variables)
//    are indistinguishable, so any unnamed element not needed to *meet a
//    cardinality lower bound* can be deleted without violating any constraint
//    (deletion only lowers cardinalities; it never breaks an upper bound, a set
//    equality/subset, or a named-literal membership). The total unnamed elements a
//    minimal model needs is therefore at most the sum of the cardinality
//    lower-bound constants, each of which is a numeric literal of the script. So
//    `N`, summing *all* literals (plus one slot per `set.card` to absorb any
//    strict `>` bound's `k+1` demand, plus `D` and the margin), is a *conservative
//    over-approximation* of the slots any minimal model needs — never too small.
//
// Cardinality is supported **only** when the element-soundness conditions (1)
// above still hold; in particular a `set.member`/`set.singleton` with a
// *non-literal* element (a free element variable, e.g. `(set.member x s)` with `x`
// of sort `E`) combined with cardinality would need an element-index/select model
// and is **declined** by [`scan_set_ops`] (the non-literal-element rule), never
// guessed.

/// Operators that quantify over the *entire* element sort (not just the modeled
/// finite projection) or otherwise fall outside the sound `BitVec` subset; any
/// occurrence makes [`desugar_sets`] decline the whole script.
///
/// `set.card` is **not** here: it is soundly modeled as a popcount over a
/// *slack universe* large enough to realize any model the formula's cardinality
/// constants demand (see [`set_card_universe_width`] and the module note,
/// "Cardinality over a slack universe").
const UNSUPPORTED_SET_OPS: &[&str] = &[
    "set.complement",
    "set.universe",
    "set.comprehension",
    "set.choose",
    "set.insert",
    "set.filter",
    "set.map",
    "set.fold",
];

/// Margin of extra high "junk" bits added beyond the `D` named-element bits, so a
/// free set variable can differ from another set on elements the formula never
/// names. See the module-level soundness note.
const SET_MARGIN_BITS: u32 = 2;

/// Cap on the modeled set width. The single-bit `set.singleton` constant is
/// emitted as `(_ bv(1<<i) W)`, whose value must fit a `u128`, so more than 127
/// distinct element terms is declined (rare; these benchmarks have a handful).
const MAX_SET_WIDTH: u32 = 128;

/// Rewrites the sound subset of finite-set operations to bit-vector operations,
/// in place on the whole s-expression script `exprs`, modeling every `(Set E)` as
/// a `BitVec(W)` (see the module-level soundness note).
///
/// Fast path: a script that mentions no set sort or `set.*` operator is left
/// untouched (and unallocated).
///
/// # Errors
///
/// [`SmtError::Unsupported`] if the script's set usage falls outside the
/// provably-sound subset (an unsupported operator, a non-literal element term, or
/// a modeled width over [`MAX_SET_WIDTH`]). Declining is *sound*: an unsupported
/// file is reported as such rather than risking a wrong verdict.
fn desugar_sets(exprs: &mut [SExpr]) -> Result<(), SmtError> {
    // Fast path: nothing set-related anywhere.
    if !exprs.iter().any(mentions_sets) {
        return Ok(());
    }
    // Collect the distinct (literal) element terms, in first-appearance order, and
    // validate the sound-subset conditions.
    let mut element_keys: Vec<String> = Vec::new();
    scan_set_ops(exprs, &mut element_keys)?;
    let d = u32::try_from(element_keys.len()).unwrap_or(u32::MAX);
    // Cardinality mode: if the script uses `set.card`, widen to a *slack universe*
    // large enough to realize any model the cardinality constants demand (see the
    // module note, "Cardinality over a slack universe"). Otherwise the named-domain
    // width `D + MARGIN` is exact for the pointwise operators.
    let width = if exprs.iter().any(uses_set_card) {
        set_card_universe_width(exprs, d)?
    } else {
        d.checked_add(SET_MARGIN_BITS)
            .filter(|&w| w <= MAX_SET_WIDTH)
            .ok_or_else(|| {
                SmtError::Unsupported(format!(
                    "finite-set modeling needs {d} element bits, over the {MAX_SET_WIDTH}-bit cap"
                ))
            })?
            .max(1)
    };
    let bit_index: HashMap<String, u32> = element_keys
        .into_iter()
        .enumerate()
        .map(|(i, k)| (k, u32::try_from(i).expect("index fits (width capped)")))
        .collect();
    for e in exprs.iter_mut() {
        rewrite_set_sexpr(e, width, &bit_index);
    }
    Ok(())
}

/// Whether `e` mentions the `Set` sort head or any `set.*` operator anywhere.
fn mentions_sets(e: &SExpr) -> bool {
    match e {
        SExpr::Atom(a) => a.starts_with("set."),
        SExpr::List(items) => {
            items.first().and_then(SExpr::atom) == Some("Set") || items.iter().any(mentions_sets)
        }
    }
}

/// Whether `e` uses the `(set.card ...)` operator anywhere.
fn uses_set_card(e: &SExpr) -> bool {
    match e {
        SExpr::Atom(_) => false,
        SExpr::List(items) => {
            items.first().and_then(SExpr::atom) == Some("set.card")
                || items.iter().any(uses_set_card)
        }
    }
}

/// The slack-universe width `N` for a script that uses `set.card` (see the module
/// note, "Cardinality over a slack universe"):
///
///   `N = D + Σ(numeric literals) + (#`set.card` occurrences) + MARGIN`,
///
/// a conservative over-approximation of the distinct element slots any minimal
/// model can need, capped at [`MAX_SET_WIDTH`]. Summing **all** numeric literals
/// (not just cardinality lower bounds) only over-allocates; the per-`set.card`
/// slot absorbs any strict `>` bound's `k+1` demand. Never under-allocates, so
/// no wrong `unsat`.
///
/// # Errors
///
/// [`SmtError::Unsupported`] if the demanded universe exceeds [`MAX_SET_WIDTH`]
/// (the popcount stays exact but the singleton one-hot constant must fit `u128`).
fn set_card_universe_width(exprs: &[SExpr], d: u32) -> Result<u32, SmtError> {
    let mut literal_sum: u64 = 0;
    let mut card_count: u64 = 0;
    for e in exprs {
        accumulate_card_budget(e, &mut literal_sum, &mut card_count);
    }
    let demand = u64::from(d)
        .saturating_add(literal_sum)
        .saturating_add(card_count)
        .saturating_add(u64::from(SET_MARGIN_BITS))
        .max(1);
    if demand > u64::from(MAX_SET_WIDTH) {
        return Err(SmtError::Unsupported(format!(
            "finite-set cardinality needs a {demand}-slot universe, over the \
             {MAX_SET_WIDTH}-bit cap"
        )));
    }
    Ok(u32::try_from(demand).expect("demand <= MAX_SET_WIDTH fits u32"))
}

/// Sums every non-negative integer numeric literal in `e` into `literal_sum` and
/// counts `set.card` occurrences into `card_count` (both saturating). Decimals and
/// bit-vector literals do not contribute to the cardinality budget (only integer
/// cardinality bounds drive element demand).
fn accumulate_card_budget(e: &SExpr, literal_sum: &mut u64, card_count: &mut u64) {
    match e {
        SExpr::Atom(a) => {
            // A bare non-negative integer numeral.
            if !a.is_empty() && a.bytes().all(|c| c.is_ascii_digit()) {
                *literal_sum = literal_sum.saturating_add(a.parse::<u64>().unwrap_or(u64::MAX));
            }
        }
        SExpr::List(items) => {
            if items.first().and_then(SExpr::atom) == Some("set.card") {
                *card_count = card_count.saturating_add(1);
            }
            for child in items {
                accumulate_card_budget(child, literal_sum, card_count);
            }
        }
    }
}

/// Validates the sound-subset conditions and collects the distinct literal element
/// terms (first-appearance order) into `element_keys`.
///
/// # Errors
///
/// [`SmtError::Unsupported`] for an [`UNSUPPORTED_SET_OPS`] operator or a
/// non-literal `set.singleton`/`set.member` element term.
fn scan_set_ops(exprs: &[SExpr], element_keys: &mut Vec<String>) -> Result<(), SmtError> {
    for e in exprs {
        if let SExpr::List(items) = e {
            if let Some(head) = items.first().and_then(SExpr::atom) {
                if UNSUPPORTED_SET_OPS.contains(&head) {
                    return Err(SmtError::Unsupported(format!(
                        "finite-set operator `{head}` is outside the sound BitVec subset \
                         (it ranges over the whole element sort, not the named finite domain)"
                    )));
                }
                if (head == "set.singleton" || head == "set.member") && items.len() >= 2 {
                    // The element is the LAST argument: `(set.singleton e)` and
                    // `(set.member e S)`.
                    let elem = &items[items.len() - if head == "set.member" { 2 } else { 1 }];
                    let key = set_element_key(elem).ok_or_else(|| {
                        SmtError::Unsupported(format!(
                            "finite-set element `{elem:?}` is not a constant literal; only \
                             literal elements are soundly modeled (non-literal elements may \
                             alias and need congruence — a later slice)"
                        ))
                    })?;
                    if !element_keys.contains(&key) {
                        element_keys.push(key);
                    }
                }
            }
            scan_set_ops(items, element_keys)?;
        }
    }
    Ok(())
}

/// The canonical bit-position key for a set element term, or `None` if the term is
/// not a constant literal (so giving it its own bit could be unsound; see the
/// module note, condition 1).
///
/// Accepts numerals (`7`), decimals (`1.5`), `#b`/`#x` bit-vector literals,
/// indexed bit-vector constants `(_ bvN W)`, and the booleans `true`/`false`. The
/// key is the literal's normalized text, so two syntactically-equal literals share
/// a bit and two distinct literals get distinct bits.
fn set_element_key(e: &SExpr) -> Option<String> {
    match e {
        SExpr::Atom(a) => is_set_element_literal_atom(a).then(|| a.clone()),
        SExpr::List(items) => {
            // `(_ bvN W)` indexed bit-vector constant.
            if items.len() == 3
                && items[0].atom() == Some("_")
                && items[1].atom().is_some_and(|n| n.starts_with("bv"))
                && items[2].atom().is_some_and(|w| w.parse::<u32>().is_ok())
            {
                let n = items[1].atom().expect("checked");
                let w = items[2].atom().expect("checked");
                Some(format!("(_ {n} {w})"))
            } else {
                None
            }
        }
    }
}

/// Whether an atom is a constant literal usable as a finite-set element bit key:
/// a numeral, a decimal, a `#b`/`#x` bit-vector literal, or `true`/`false`.
fn is_set_element_literal_atom(a: &str) -> bool {
    if a == "true" || a == "false" {
        return true;
    }
    if let Some(rest) = a.strip_prefix("#b") {
        return !rest.is_empty() && rest.bytes().all(|c| c == b'0' || c == b'1');
    }
    if let Some(rest) = a.strip_prefix("#x") {
        return !rest.is_empty() && rest.bytes().all(|c| c.is_ascii_hexdigit());
    }
    // Numeral or decimal: digits with at most one `.`.
    let mut seen_dot = false;
    let mut seen_digit = false;
    for c in a.bytes() {
        match c {
            b'0'..=b'9' => seen_digit = true,
            b'.' if !seen_dot => seen_dot = true,
            _ => return false,
        }
    }
    seen_digit
}

/// Recursively rewrites every finite-set sort/operator in `e` (in place) to its
/// bit-vector encoding at width `width`, using `bit_index` for element positions.
fn rewrite_set_sexpr(e: &mut SExpr, width: u32, bit_index: &HashMap<String, u32>) {
    let SExpr::List(items) = e else { return };
    // Direct cardinality comparison `(CMP (set.card S) k)` / `(CMP k (set.card S))`
    // with `k` a numeric literal → a **pure-BV** popcount comparison, kept entirely
    // in `QF_BV` (a bit-blasted adder tree compared with a BV constant) so the
    // backend decides it *completely* — the `Int`/BV combined path is incomplete
    // for the multi-set cardinality shapes (`card`/`card-3`/`card-6`). This must run
    // **before** the bottom-up recursion below turns the inner `set.card` into an
    // `Int` popcount. Other `set.card` positions (e.g. inside a `+`) still fall
    // through to the sound `Int` popcount.
    if let Some(rewritten) = try_card_compare_bv(items, width, bit_index) {
        *e = rewritten;
        return;
    }
    let SExpr::List(items) = e else {
        unreachable!("e is a List (matched above)")
    };
    // Rewrite children first (bottom-up), so set sub-terms become BV before the
    // parent operator consumes them.
    for child in items.iter_mut() {
        rewrite_set_sexpr(child, width, bit_index);
    }
    // `(Set E)` in a sort position → `(_ BitVec W)`.
    if items.len() == 2 && items[0].atom() == Some("Set") {
        *e = bitvec_sort(width);
        return;
    }
    let Some(head) = items.first().and_then(SExpr::atom) else {
        return;
    };
    match head {
        // `(as set.empty (Set E))` and the bare `set.empty` (handled as an atom
        // elsewhere) → the all-zeros bit-set. The `(Set E)` argument has already
        // been rewritten to `(_ BitVec W)` above; we ignore it.
        "as" if items.len() == 3 && items[1].atom() == Some("set.empty") => {
            *e = bv_zero(width);
        }
        "set.empty" => *e = bv_zero(width),
        "set.singleton" if items.len() == 2 => {
            *e = singleton_sexpr(&items[1], width, bit_index);
        }
        "set.member" if items.len() == 3 => {
            // `(set.member e S)` → bit `i` of `S` is set:
            //   `(= ((_ extract i i) S) #b1)`.
            *e = member_sexpr(&items[1], &items[2], bit_index);
        }
        "set.union" if items.len() >= 2 => {
            *e = fold_set_sexpr("bvor", &items[1..]);
        }
        "set.inter" if items.len() >= 2 => {
            *e = fold_set_sexpr("bvand", &items[1..]);
        }
        "set.minus" if items.len() == 3 => {
            // `a \ b` = `a & ~b`.
            *e = SExpr::List(vec![
                atom("bvand"),
                items[1].clone(),
                SExpr::List(vec![atom("bvnot"), items[2].clone()]),
            ]);
        }
        "set.subset" if items.len() == 3 => {
            // `a ⊆ b` ⇔ `a = a & b`.
            let a = items[1].clone();
            let b = items[2].clone();
            *e = SExpr::List(vec![
                atom("="),
                a.clone(),
                SExpr::List(vec![atom("bvand"), a, b]),
            ]);
        }
        "set.card" if items.len() == 2 => {
            // `(set.card S)` → the `Int` popcount over the slack universe:
            //   `(+ (bv2nat ((_ extract 0 0) S)) … (bv2nat ((_ extract N-1 N-1) S)))`.
            // Each bit's `bv2nat` is `0` or `1`, so the sum is exactly `|S|` over the
            // modeled universe (see the module note, "Cardinality over a slack
            // universe").
            *e = card_popcount_sexpr(&items[1], width);
        }
        _ => {}
    }
}

/// `(_ BitVec width)` sort s-expr.
fn bitvec_sort(width: u32) -> SExpr {
    SExpr::List(vec![atom("_"), atom("BitVec"), atom(&width.to_string())])
}

/// `(_ bv0 width)` — the empty bit-set / all-zeros constant.
fn bv_zero(width: u32) -> SExpr {
    SExpr::List(vec![atom("_"), atom("bv0"), atom(&width.to_string())])
}

/// `(set.singleton e)` → the one-hot constant `(_ bv(1<<i) W)` for `e`'s bit `i`.
/// An element with no registered bit (impossible after [`scan_set_ops`]) maps to
/// the empty set, which is sound (it can only under-constrain, never wrong-`unsat`
/// — but the scan guarantees every singleton element is registered).
fn singleton_sexpr(elem: &SExpr, width: u32, bit_index: &HashMap<String, u32>) -> SExpr {
    let value = set_element_key(elem)
        .and_then(|k| bit_index.get(&k).copied())
        .map_or(0u128, |i| 1u128 << i);
    SExpr::List(vec![
        atom("_"),
        atom(&format!("bv{value}")),
        atom(&width.to_string()),
    ])
}

/// `(set.member e S)` → `(= ((_ extract i i) S) #b1)`, the bit-`i` membership test.
/// A `set.member` whose element has no bit (impossible after [`scan_set_ops`])
/// becomes `false` (the element is in no modeled set), which is sound here.
fn member_sexpr(elem: &SExpr, set: &SExpr, bit_index: &HashMap<String, u32>) -> SExpr {
    let Some(i) = set_element_key(elem).and_then(|k| bit_index.get(&k).copied()) else {
        return atom("false");
    };
    let extract = SExpr::List(vec![
        SExpr::List(vec![
            atom("_"),
            atom("extract"),
            atom(&i.to_string()),
            atom(&i.to_string()),
        ]),
        set.clone(),
    ]);
    SExpr::List(vec![atom("="), extract, atom("#b1")])
}

/// Folds a set operator `op` (`bvor`/`bvand`) over `args` (≥ 1), left-associating.
fn fold_set_sexpr(op: &str, args: &[SExpr]) -> SExpr {
    let mut acc = args[0].clone();
    for next in &args[1..] {
        acc = SExpr::List(vec![atom(op), acc, next.clone()]);
    }
    acc
}

/// If `items` is a direct cardinality comparison `(CMP (set.card S) k)` or
/// `(CMP k (set.card S))` with `CMP` one of `>= <= = > <` and `k` a non-negative
/// integer literal, returns the equivalent **pure-BV** comparison
/// `(bv-cmp (popcount_bv S) (_ bv k CW))` at a popcount width `CW` wide enough to
/// hold the universe size `width`. The set expression `S` is itself recursively
/// set-rewritten. Returns `None` for any other shape (the caller then uses the
/// generic bottom-up rewrite, which routes a non-comparison `set.card` to the
/// sound `Int` popcount).
///
/// Soundness: popcount and `k` are both non-negative and fit in `CW` bits, so the
/// unsigned BV comparison is exact and equals the `Int` comparison.
fn try_card_compare_bv(
    items: &[SExpr],
    width: u32,
    bit_index: &HashMap<String, u32>,
) -> Option<SExpr> {
    if items.len() != 3 {
        return None;
    }
    let cmp = items[0].atom()?;
    let bv_cmp = match cmp {
        ">=" => "bvuge",
        "<=" => "bvule",
        ">" => "bvugt",
        "<" => "bvult",
        "=" => "=",
        _ => return None,
    };
    // Identify which side is `(set.card S)` and which is the literal `k`.
    let (card_arg, lit) = match (card_inner(&items[1]), card_inner(&items[2])) {
        (Some(s), None) => (s, &items[2]),
        (None, Some(s)) => (s, &items[1]),
        // `(= (set.card a) (set.card b))` and the like are not the literal-compare
        // shape; fall through to the generic `Int` popcount path.
        _ => return None,
    };
    let k = lit
        .atom()
        .filter(|a| !a.is_empty() && a.bytes().all(|c| c.is_ascii_digit()))
        .and_then(|a| a.parse::<u128>().ok())?;
    // Popcount width: enough to hold `width` (the max popcount) and `k`. By
    // construction `cw >= bits_for(k)`, so the `(_ bv k cw)` constant is exact (no
    // truncation), and `cw >= bits_for(width)`, so the popcount adder cannot
    // overflow.
    let cw = popcount_bv_width(width).max(bits_for(k));
    // Recursively set-rewrite the inner set expression `S` to its `BitVec(width)`.
    let mut set_expr = card_arg.clone();
    rewrite_set_sexpr(&mut set_expr, width, bit_index);
    let pc = popcount_bv_sexpr(&set_expr, width, cw);
    let kbv = SExpr::List(vec![
        atom("_"),
        atom(&format!("bv{k}")),
        atom(&cw.to_string()),
    ]);
    Some(SExpr::List(vec![atom(bv_cmp), pc, kbv]))
}

/// `Some(S)` if `e` is `(set.card S)`, else `None`.
fn card_inner(e: &SExpr) -> Option<&SExpr> {
    match e {
        SExpr::List(items) if items.len() == 2 && items[0].atom() == Some("set.card") => {
            Some(&items[1])
        }
        _ => None,
    }
}

/// Number of bits needed to represent the value `n` (at least 1).
fn bits_for(n: u128) -> u32 {
    (128 - n.leading_zeros()).max(1)
}

/// Popcount-result BV width for a `width`-bit universe: enough to hold the value
/// `width` (the maximum possible popcount).
fn popcount_bv_width(width: u32) -> u32 {
    bits_for(u128::from(width))
}

/// `popcount_bv(S)` as a `BitVec(cw)` adder tree: zero-extend each of the `width`
/// single-bit extracts of `S` to `cw` bits and sum them with `bvadd`. The result
/// is the exact cardinality on the modeled universe (no overflow: `cw` holds
/// `width`).
fn popcount_bv_sexpr(set: &SExpr, width: u32, cw: u32) -> SExpr {
    let bit_bv = |i: u32| -> SExpr {
        // `((_ zero_extend cw-1) ((_ extract i i) S))` — a `0`/`1` `BitVec(cw)`.
        let one_bit = SExpr::List(vec![
            SExpr::List(vec![
                atom("_"),
                atom("extract"),
                atom(&i.to_string()),
                atom(&i.to_string()),
            ]),
            set.clone(),
        ]);
        SExpr::List(vec![
            SExpr::List(vec![
                atom("_"),
                atom("zero_extend"),
                atom(&(cw - 1).to_string()),
            ]),
            one_bit,
        ])
    };
    let mut acc = bit_bv(0);
    for i in 1..width {
        acc = SExpr::List(vec![atom("bvadd"), acc, bit_bv(i)]);
    }
    acc
}

/// `(set.card S)` → the `Int` popcount over the `width`-bit slack universe:
///   `(+ (bv2nat ((_ extract 0 0) S)) … (bv2nat ((_ extract w-1 w-1) S)))`.
///
/// `set` is the already-rewritten `BitVec(width)` set term. Each summand is the
/// `Int` `0`/`1` of one bit, so the total is exactly the cardinality on the
/// modeled universe. A single bit (`width == 1`) is the lone `bv2nat`-extract (no
/// `+`), and `width >= 1` always holds (the universe is `.max(1)`).
fn card_popcount_sexpr(set: &SExpr, width: u32) -> SExpr {
    let bit_int = |i: u32| -> SExpr {
        // `(bv2nat ((_ extract i i) S))` — a `0`/`1` `Int`.
        SExpr::List(vec![
            atom("bv2nat"),
            SExpr::List(vec![
                SExpr::List(vec![
                    atom("_"),
                    atom("extract"),
                    atom(&i.to_string()),
                    atom(&i.to_string()),
                ]),
                set.clone(),
            ]),
        ])
    };
    if width <= 1 {
        return bit_int(0);
    }
    let mut sum = vec![atom("+")];
    sum.extend((0..width).map(bit_int));
    SExpr::List(sum)
}

/// A borrowed-free atom s-expr.
fn atom(s: &str) -> SExpr {
    SExpr::Atom(s.to_owned())
}

fn smtlib_metadata_value(value: &SExpr) -> String {
    match value {
        SExpr::Atom(atom) => atom.clone(),
        SExpr::List(items) => {
            let rendered = items
                .iter()
                .map(smtlib_metadata_value)
                .collect::<Vec<_>>()
                .join(" ");
            format!("({rendered})")
        }
    }
}

/// Whether `root` contains a quantifier. Assertion-local encoding guards are
/// free-variable restrictions and cannot be hoisted across a quantifier whose
/// bound symbol they may mention, so that combination is declined rather than
/// silently changing scope.
fn contains_quantifier(arena: &TermArena, root: TermId) -> bool {
    let mut seen = HashSet::new();
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if matches!(op, Op::Forall(_) | Op::Exists(_)) {
                return true;
            }
            pending.extend(args.iter().copied());
        }
    }
    false
}

/// Conjoin the bounded-representation guards created while parsing one
/// assertion. This keeps guards under the same `push`/`pop` lifetime as the
/// sequence term that needs them.
fn attach_encoding_guards(
    arena: &mut TermArena,
    mut term: TermId,
    guards: &[TermId],
    context: &str,
) -> Result<TermId, SmtError> {
    if guards.is_empty() {
        return Ok(term);
    }
    if contains_quantifier(arena, term) {
        return Err(SmtError::Unsupported(format!(
            "symbolic bounded-sequence element guard inside `{context}` quantifier"
        )));
    }
    for &guard in guards {
        term = arena.and(term, guard)?;
    }
    Ok(term)
}

/// Output/definition contexts have no assertion scope in which an encoding
/// guard can live. Decline them instead of applying a global restriction that
/// would survive or disappear incorrectly across incremental commands.
fn reject_new_encoding_guards(
    lenabs: &LenAbs,
    checkpoint: usize,
    context: &str,
) -> Result<(), SmtError> {
    if lenabs.encoding_guard_checkpoint() == checkpoint {
        Ok(())
    } else {
        Err(SmtError::Unsupported(format!(
            "symbolic bounded-sequence element in `{context}` has no assertion scope"
        )))
    }
}

// A flat dispatch over the SMT-LIB command keywords; one match arm per command.
#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
fn parse_command<'a>(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &mut HashMap<String, MacroDef<'a>>,
    sort_aliases: &mut HashMap<String, Sort>,
    named: &mut HashMap<String, TermId>,
    seq: &SeqInfo,
    ff: &FfInfo,
    lenabs: &LenAbs,
    string_symbol_bounds: &BTreeMap<String, u32>,
    command: &'a SExpr,
) -> Result<(), SmtError> {
    let items = command
        .list()
        .ok_or_else(|| SmtError::Syntax("top-level atom".to_owned()))?;
    let head = items
        .first()
        .and_then(SExpr::atom)
        .ok_or_else(|| SmtError::Syntax("empty command".to_owned()))?;
    match head {
        "set-logic" => {
            exact_len(items, 2, head)?;
            script.logic = items.get(1).and_then(SExpr::atom).map(str::to_owned);
        }
        "set-info" => {
            exact_len(items, 3, head)?;
            let key = items
                .get(1)
                .and_then(SExpr::atom)
                .ok_or_else(|| SmtError::Syntax("set-info key".to_owned()))?
                .to_owned();
            let value = smtlib_metadata_value(sexpr_at(items, 2)?);
            if key == ":status" {
                script.status = items.get(2).and_then(SExpr::atom).map(str::to_owned);
            }
            script.infos.insert(key, value);
        }
        "set-option" => {
            exact_len(items, 3, head)?;
            let key = items
                .get(1)
                .and_then(SExpr::atom)
                .ok_or_else(|| SmtError::Syntax("set-option key".to_owned()))?
                .to_owned();
            script
                .options
                .insert(key, smtlib_metadata_value(sexpr_at(items, 2)?));
        }
        // Output/query commands: accepted as no-ops at parse time. The core is
        // produced by the solver (`solve_smtlib_unsat_core`), the model by the
        // `sat` result — the parser just records a well-formed script.
        "get-model" => {
            exact_len(items, 1, head)?;
            script.get_model = true;
        }
        "exit"
        | "get-unsat-core"
        | "get-proof"
        | "get-assignment"
        | "get-unsat-assumptions"
        | "get-objectives" => exact_len(items, 1, head)?,
        "get-assertions" => {
            exact_len(items, 1, head)?;
            script.commands.push(ScriptCommand::GetAssertions);
        }
        // `(reset-assertions)` clears assertions but keeps declarations — modeled
        // explicitly (a no-op here would silently keep stale assertions across the
        // reset, solving a different problem than the script asked).
        "reset-assertions" => {
            exact_len(items, 1, head)?;
            script.commands.push(ScriptCommand::ResetAssertions);
        }
        // `(reset)` is a FULL reset (assertions + declarations + options back to the
        // initial state). In this parse-then-execute model declarations are interned
        // into a single shared arena, so clearing them mid-script is not soundly
        // supported — reject explicitly rather than silently ignore (which would
        // leave stale declarations/assertions in effect).
        "reset" => {
            exact_len(items, 1, head)?;
            return Err(SmtError::Unsupported(
                "reset (full reset of declarations + assertions); use reset-assertions, or run \
                 each benchmark in a fresh solver instance"
                    .to_owned(),
            ));
        }
        // Optimization objectives (OMT): `(maximize t)` / `(minimize t)`.
        "maximize" | "minimize" => {
            exact_len(items, 2, head)?;
            let guard_checkpoint = lenabs.encoding_guard_checkpoint();
            let t = parse_term(
                &mut script.arena,
                sexpr_at(items, 1)?,
                aliases,
                macros,
                named,
                seq,
                ff,
                lenabs,
            )?;
            reject_new_encoding_guards(lenabs, guard_checkpoint, head)?;
            script.objectives.push((t, head == "maximize"));
        }
        // `(get-option k)` and `(get-info k)` record the requested key;
        // `(echo "string")` is accepted as a well-formed output command and
        // otherwise ignored.
        "get-option" => {
            exact_len(items, 2, head)?;
            script.get_option_keys.push(
                sexpr_at(items, 1)?
                    .atom()
                    .ok_or_else(|| SmtError::Syntax("get-option key".to_owned()))?
                    .to_owned(),
            );
        }
        "get-info" => {
            exact_len(items, 2, head)?;
            script.get_info_keys.push(
                sexpr_at(items, 1)?
                    .atom()
                    .ok_or_else(|| SmtError::Syntax("get-info key".to_owned()))?
                    .to_owned(),
            );
        }
        "echo" => exact_len(items, 2, head)?,
        "get-value" => {
            exact_len(items, 2, head)?;
            let list = items
                .get(1)
                .and_then(SExpr::list)
                .ok_or_else(|| SmtError::Syntax("get-value expects (t …)".to_owned()))?;
            let guard_checkpoint = lenabs.encoding_guard_checkpoint();
            for t in list {
                let term = parse_term(
                    &mut script.arena,
                    t,
                    aliases,
                    macros,
                    named,
                    seq,
                    ff,
                    lenabs,
                )?;
                script.get_value_terms.push(term);
            }
            reject_new_encoding_guards(lenabs, guard_checkpoint, head)?;
        }
        "check-sat-assuming" => {
            exact_len(items, 2, head)?;
            let list = items
                .get(1)
                .and_then(SExpr::list)
                .ok_or_else(|| SmtError::Syntax("check-sat-assuming expects (l ...)".to_owned()))?;
            let guard_checkpoint = lenabs.encoding_guard_checkpoint();
            let mut assumptions = Vec::with_capacity(list.len());
            for lit in list {
                assumptions.push(parse_term(
                    &mut script.arena,
                    lit,
                    aliases,
                    macros,
                    named,
                    seq,
                    ff,
                    lenabs,
                )?);
            }
            let guards = lenabs.encoding_guards_since(guard_checkpoint);
            if !guards.is_empty()
                && assumptions
                    .iter()
                    .any(|&term| contains_quantifier(&script.arena, term))
            {
                return Err(SmtError::Unsupported(
                    "symbolic bounded-sequence element guard inside `check-sat-assuming` \
                     quantifier"
                        .to_owned(),
                ));
            }
            assumptions.extend(guards);
            script.check_sats += 1;
            script
                .commands
                .push(ScriptCommand::CheckSatAssuming(assumptions));
        }
        "check-sat" => {
            exact_len(items, 1, head)?;
            script.check_sats += 1;
            script.commands.push(ScriptCommand::CheckSat);
        }
        "declare-fun" => {
            parse_declare_fun(script, sort_aliases, ff, string_symbol_bounds, items)?;
        }
        "declare-const" => {
            parse_declare_const(script, sort_aliases, ff, string_symbol_bounds, items)?;
        }
        "declare-datatype" => parse_declare_datatype(script, sort_aliases, items)?,
        "declare-datatypes" => parse_declare_datatypes(script, sort_aliases, items)?,
        "define-fun" => {
            parse_define_fun(
                script,
                aliases,
                macros,
                sort_aliases,
                named,
                seq,
                ff,
                lenabs,
                items,
            )?;
        }
        // `(define-const c S body)` is exact sugar for `(define-fun c () S body)`
        // (SMT-LIB §3.7.2 abbreviation): a nullary definition. We reuse the
        // no-args alias path verbatim, so soundness is identical to `define-fun`.
        "define-const" => {
            parse_define_const(
                script,
                aliases,
                macros,
                sort_aliases,
                named,
                seq,
                ff,
                lenabs,
                items,
            )?;
        }
        "define-sort" => parse_define_sort(script, sort_aliases, items)?,
        // `(declare-sort U 0)` — an arity-0 uninterpreted sort. Arity ≥ 1
        // (parametric, e.g. `(declare-sort List 1)`) is out of scope.
        "declare-sort" => parse_declare_sort(script, sort_aliases, items)?,
        "assert" => {
            exact_len(items, 2, head)?;
            let body = sexpr_at(items, 1)?;
            let name = named_label(body);
            let guard_checkpoint = lenabs.encoding_guard_checkpoint();
            let t = parse_term(
                &mut script.arena,
                body,
                aliases,
                macros,
                named,
                seq,
                ff,
                lenabs,
            )?;
            let guards = lenabs.encoding_guards_since(guard_checkpoint);
            let t = attach_encoding_guards(&mut script.arena, t, &guards, head)?;
            // `:named` terms are script-global aliases in this parser. Point a
            // later reference at the guarded bounded assertion, not at the
            // pre-guard term recorded while parsing the annotation; otherwise
            // `push`/`pop` followed by `(assert name)` could resurrect the lossy
            // `int2bv` term without its injectivity guard.
            if let Some(label) = &name {
                named.insert(label.clone(), t);
            }
            script.assertions.push(t);
            script.assertion_names.push(name);
            script.commands.push(ScriptCommand::Assert(t));
        }
        // Incremental scoping (ADR-0009): `(push)`/`(pop)` default to one scope.
        "push" | "pop" => {
            let count = match items.get(1) {
                None => 1,
                Some(e) => e
                    .atom()
                    .and_then(|s| s.parse::<u32>().ok())
                    .ok_or_else(|| SmtError::Syntax(format!("`{head}` count")))?,
            };
            if items.len() > 2 {
                return Err(SmtError::Syntax(format!(
                    "`{head}` takes at most one count"
                )));
            }
            script.commands.push(if head == "push" {
                ScriptCommand::Push(count)
            } else {
                ScriptCommand::Pop(count)
            });
        }
        other => return Err(SmtError::Unsupported(format!("command `{other}`"))),
    }
    Ok(())
}

/// The `:named` attribute value of an attributed term `(! t :attr v … :named
/// name …)`, returned as a borrowed name to bind script-globally as an alias for
/// the inner term `t`. `items` is the full `!` application list. Scans the
/// `:attr value` pairs after the term (index 2 onward), mirroring
/// [`named_label`] but yielding the borrowed `&str` the iterative parser needs.
fn attribute_named_name(items: &[SExpr]) -> Option<&str> {
    let mut i = 2;
    while i + 1 < items.len() {
        if items[i].atom() == Some(":named") {
            return items[i + 1].atom();
        }
        i += 2;
    }
    None
}

/// The `:named` label of an attributed assertion `(! t :named name …)`, if any.
fn named_label(body: &SExpr) -> Option<String> {
    let items = body.list()?;
    if items.first().and_then(SExpr::atom) != Some("!") {
        return None;
    }
    // Scan `:attr value` pairs after the term for `:named`.
    let mut i = 2;
    while i + 1 < items.len() {
        if items[i].atom() == Some(":named") {
            return items[i + 1].atom().map(str::to_owned);
        }
        i += 2;
    }
    None
}

fn parse_declare_fun(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    ff: &FfInfo,
    string_symbol_bounds: &BTreeMap<String, u32>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 4, "declare-fun")?;
    let name = atom_at(items, 1)?;
    let args = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("declare-fun args".to_owned()))?;
    // A 0-ary `String` constant is the packed bounded-string bit-vector plus its
    // canonical well-formedness constraint (ADR-0029), exactly like
    // `declare-const ... String`. Detected syntactically (not by the resolved
    // `BitVec(STRING_TOTAL)` sort) so a genuine `(_ BitVec 68)` constant is never
    // forced into the string well-formedness shape.
    if args.is_empty() && sexpr_at(items, 3)?.atom() == Some("String") {
        declare_string_symbol(
            script,
            name,
            string_symbol_bounds
                .get(name)
                .copied()
                .unwrap_or(STRING_MAX_LEN),
        )?;
        return Ok(());
    }
    // A 0-ary `RoundingMode` constant: a `BitVec(3)` plus its `≤ 4` constraint,
    // exactly like `declare-const … RoundingMode`.
    if args.is_empty() && sexpr_at(items, 3)?.atom() == Some("RoundingMode") {
        declare_rounding_mode_symbol(script, name)?;
        return Ok(());
    }
    // A 0-ary finite-field constant `(_ FiniteField p)` (directly or via a
    // `define-sort` alias): a `BitVec(ff_width(p))` plus a `bvult var p`
    // well-formedness constraint, so the modeled domain is exactly `GF(p)`.
    if args.is_empty()
        && let Some(p) = ff_decl_prime(ff, sexpr_at(items, 3)?)
    {
        declare_ff_symbol(script, name, p)?;
        return Ok(());
    }
    // A 0-ary `(Seq E)` constant: packed sequence + well-formedness (ADR-0029),
    // exactly like `declare-const ... (Seq E)`.
    if args.is_empty()
        && let Some(ew) = seq_decl_elem_width(sexpr_at(items, 3)?)
    {
        declare_seq_symbol(script, name, ew)?;
        return Ok(());
    }
    let result = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 3)?)?;
    if args.is_empty() {
        // 0-ary: a plain constant symbol.
        let symbol = script.arena.declare(name, result)?;
        record_model_symbol(script, symbol);
    } else {
        // n-ary: an uninterpreted function (ADR-0013).
        let params = args
            .iter()
            .map(|s| parse_sort(&script.arena, sort_aliases, s))
            .collect::<Result<Vec<Sort>, SmtError>>()?;
        let func = script.arena.declare_fun(name, &params, result)?;
        record_model_function(script, func);
    }
    Ok(())
}

/// Adds the constructors `(cname (sel sort) …)` of one datatype `dt` to the
/// arena. Sorts resolve through `parse_sort`, so a field may reference any
/// already-declared datatype (the sorts in a `declare-datatypes` group are all
/// declared before their constructors, supporting (mutual) recursion).
fn add_datatype_constructors(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    dt: axeyum_ir::DatatypeId,
    ctors: &[SExpr],
) -> Result<(), SmtError> {
    for ctor in ctors {
        let parts = ctor
            .list()
            .filter(|p| !p.is_empty())
            .ok_or_else(|| SmtError::Syntax("datatype constructor".to_owned()))?;
        let cname = parts[0]
            .atom()
            .ok_or_else(|| SmtError::Syntax("constructor name".to_owned()))?
            .to_owned();
        let mut fields = Vec::with_capacity(parts.len() - 1);
        for field in &parts[1..] {
            let fp = field
                .list()
                .filter(|p| p.len() == 2)
                .ok_or_else(|| SmtError::Syntax("(selector sort)".to_owned()))?;
            let sname = fp[0]
                .atom()
                .ok_or_else(|| SmtError::Syntax("selector name".to_owned()))?
                .to_owned();
            let fsort = parse_sort(&script.arena, sort_aliases, &fp[1])?;
            fields.push((sname, fsort));
        }
        script.arena.add_constructor(dt, &cname, &fields);
    }
    Ok(())
}

/// `(declare-datatype Name (ctor …))` — a single (non-parametric) datatype.
fn parse_declare_datatype(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 3, "declare-datatype")?;
    let name = atom_at(items, 1)?;
    let ctors = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("datatype constructor list".to_owned()))?;
    let dt = script.arena.declare_datatype(name);
    add_datatype_constructors(script, sort_aliases, dt, ctors)
}

/// `(declare-datatypes ((Name 0) …) ((ctors) …))` (SMT-LIB 2.6) — one or more
/// non-parametric datatypes (mutual recursion supported; parametric `arity > 0`
/// is rejected). All sorts are declared first, then their constructors, so a
/// field sort may reference any datatype in the group.
fn parse_declare_datatypes(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 3, "declare-datatypes")?;
    let sort_decls = items
        .get(1)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("datatype sort declarations".to_owned()))?;
    let groups = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("datatype constructor groups".to_owned()))?;
    if sort_decls.len() != groups.len() {
        return Err(SmtError::Syntax(
            "declare-datatypes: sort and constructor lists differ in length".to_owned(),
        ));
    }
    // First pass: declare every datatype sort (so constructor fields can recurse).
    let mut ids = Vec::with_capacity(sort_decls.len());
    for decl in sort_decls {
        let pair = decl
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("(Name arity)".to_owned()))?;
        let name = pair[0]
            .atom()
            .ok_or_else(|| SmtError::Syntax("datatype name".to_owned()))?;
        let arity = pair[1].atom().and_then(|s| s.parse::<u32>().ok());
        if arity != Some(0) {
            return Err(SmtError::Unsupported(
                "parametric datatypes (arity > 0)".to_owned(),
            ));
        }
        ids.push(script.arena.declare_datatype(name));
    }
    // Second pass: add each datatype's constructors.
    for (dt, group) in ids.into_iter().zip(groups) {
        let ctors = group
            .list()
            .ok_or_else(|| SmtError::Syntax("datatype constructor list".to_owned()))?;
        add_datatype_constructors(script, sort_aliases, dt, ctors)?;
    }
    Ok(())
}

fn parse_declare_const(
    script: &mut Script,
    sort_aliases: &HashMap<String, Sort>,
    ff: &FfInfo,
    string_symbol_bounds: &BTreeMap<String, u32>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 3, "declare-const")?;
    let name = atom_at(items, 1)?;
    // String front-end (ADR-0029, first slice): a String constant is a packed
    // bit-vector plus its canonical well-formedness constraint, asserted in both
    // the flat and incremental views so equality/disequality decide via the BV path.
    if sexpr_at(items, 2)?.atom() == Some("String") {
        return declare_string_symbol(
            script,
            name,
            string_symbol_bounds
                .get(name)
                .copied()
                .unwrap_or(STRING_MAX_LEN),
        );
    }
    // A `RoundingMode` constant: a `BitVec(3)` plus its `≤ 4` well-formedness
    // constraint, so it can only take one of the 5 SMT-LIB rounding-mode tokens.
    if sexpr_at(items, 2)?.atom() == Some("RoundingMode") {
        return declare_rounding_mode_symbol(script, name);
    }
    // A finite-field constant `(_ FiniteField p)` (directly or via a `define-sort`
    // alias): a `BitVec(ff_width(p))` plus a `bvult var p` well-formedness
    // constraint, so the modeled domain is exactly `GF(p)`.
    if let Some(p) = ff_decl_prime(ff, sexpr_at(items, 2)?) {
        return declare_ff_symbol(script, name, p);
    }
    // A `(Seq E)` constant: the packed sequence bit-vector plus its canonical
    // well-formedness constraint (ADR-0029), exactly like a `String` symbol.
    if let Some(ew) = seq_decl_elem_width(sexpr_at(items, 2)?) {
        return declare_seq_symbol(script, name, ew);
    }
    let sort = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 2)?)?;
    let symbol = script.arena.declare(name, sort)?;
    record_model_symbol(script, symbol);
    Ok(())
}

fn record_model_symbol(script: &mut Script, symbol: SymbolId) {
    if !script.model_symbols.contains(&symbol) {
        script.model_symbols.push(symbol);
    }
}

fn record_model_function(script: &mut Script, func: FuncId) {
    if !script.model_functions.contains(&func) {
        script.model_functions.push(func);
    }
}

/// The element width of a syntactic `(Seq E)` declaration sort, or `None` if the
/// sort is not a soundly-packable sequence (so a non-sequence declaration falls
/// through to the normal sort path).
fn seq_decl_elem_width(sort: &SExpr) -> Option<u32> {
    let items = sort.list()?;
    if items.len() == 2 && items[0].atom() == Some("Seq") {
        seq_elem_width(&items[1])
    } else {
        None
    }
}

/// Declares a 0-ary `(Seq E)` symbol: the packed sequence bit-vector (max length
/// [`SEQ_MAX_LEN`], element width `ew`) plus its canonical well-formedness
/// constraint (length ≤ max; padding elements zero), asserted in both the flat and
/// incremental views so `=`/`distinct` and the `seq.*` operators decide via the
/// BV path (ADR-0029). Shared by `declare-const`/0-ary `declare-fun` of `(Seq E)`.
fn declare_seq_symbol(script: &mut Script, name: &str, ew: u32) -> Result<(), SmtError> {
    script.uses_bounded_strings = true;
    let m = seq_max_len_for(ew).ok_or_else(|| {
        SmtError::Unsupported(format!(
            "sequence element width {ew} exceeds the packed-sort bit ceiling (ADR-0029)"
        ))
    })?;
    let total = seq_total(ew, m);
    let sym = script.arena.declare(name, Sort::BitVec(total))?;
    record_model_symbol(script, sym);
    let v = script.arena.var(sym);
    let wf = seq_wellformed(&mut script.arena, v, m, ew)?;
    script.assertions.push(wf);
    script.assertion_names.push(None);
    script.commands.push(ScriptCommand::Assert(wf));
    Ok(())
}

/// Declares a 0-ary `String` symbol: a packed bounded-string bit-vector plus its
/// canonical well-formedness constraint (length ≤ max, padding bytes zero),
/// asserted in both the flat and incremental views so equality/disequality and
/// the `str.*` operators decide via the BV path (ADR-0029). Shared by
/// `declare-const ... String` and 0-ary `declare-fun ... String`.
fn declare_string_symbol(script: &mut Script, name: &str, max_len: u32) -> Result<(), SmtError> {
    script.uses_bounded_strings = true;
    let sym = script
        .arena
        .declare(name, Sort::BitVec(string_total(max_len)))?;
    record_model_symbol(script, sym);
    let v = script.arena.var(sym);
    let wf = string_wellformed_m(&mut script.arena, v, max_len)?;
    script.assertions.push(wf);
    script.assertion_names.push(None);
    script.commands.push(ScriptCommand::Assert(wf));
    Ok(())
}

/// Declares a 0-ary value of the first-class five-element `RoundingMode` sort.
/// Its three-bit lowering canonicalizes unused codes at every origin, including
/// function results and quantified binders, so no declaration-local side
/// constraint is needed.
fn declare_rounding_mode_symbol(script: &mut Script, name: &str) -> Result<(), SmtError> {
    let sym = script.arena.declare(name, Sort::RoundingMode)?;
    record_model_symbol(script, sym);
    Ok(())
}

/// The prime modulus of a declaration sort s-expr if it is a finite field
/// `(_ FiniteField p)` — directly or via a registered `define-sort` alias — and
/// `None` otherwise (so a non-field declaration falls through to the normal
/// sort path). A malformed/over-cap/non-prime finite-field sort would have already
/// made [`build_ff_info`] decline the whole script, so this is a clean lookup.
fn ff_decl_prime(ff: &FfInfo, sort: &SExpr) -> Option<u128> {
    if is_ff_sort_sexpr(sort) {
        return parse_ff_modulus(sort.list().expect("checked is_ff_sort_sexpr")).ok();
    }
    sort.atom().and_then(|n| ff.alias_to_prime.get(n).copied())
}

/// Declares a 0-ary finite-field symbol of `GF(p)`: a `BitVec(ff_width(p))` plus
/// a `bvult var p` well-formedness constraint (asserted in both the flat and
/// incremental views), so the symbol can only take a canonical residue `< p` —
/// making the modeled domain exactly the `p` field elements. Shared by
/// `declare-const`/0-ary `declare-fun` of `(_ FiniteField p)`.
fn declare_ff_symbol(script: &mut Script, name: &str, p: u128) -> Result<(), SmtError> {
    let w = ff_width(p);
    let sym = script.arena.declare(name, Sort::BitVec(w))?;
    record_model_symbol(script, sym);
    let v = script.arena.var(sym);
    let pw = script.arena.bv_const(w, p)?;
    let wf = script.arena.bv_ult(v, pw)?;
    script.assertions.push(wf);
    script.assertion_names.push(None);
    script.commands.push(ScriptCommand::Assert(wf));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn parse_define_fun<'a>(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &mut HashMap<String, MacroDef<'a>>,
    sort_aliases: &HashMap<String, Sort>,
    named: &mut HashMap<String, TermId>,
    seq: &SeqInfo,
    ff: &FfInfo,
    lenabs: &LenAbs,
    items: &'a [SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 5, "define-fun")?;
    let name = atom_at(items, 1)?;
    let args = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("define-fun args".to_owned()))?;
    let declared_sort = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 3)?)?;
    let body_expr = sexpr_at(items, 4)?;
    if args.is_empty() {
        parse_define_fun_alias(
            script,
            aliases,
            macros,
            named,
            seq,
            ff,
            lenabs,
            name,
            declared_sort,
            body_expr,
        )
    } else {
        macros.insert(
            name.to_owned(),
            MacroDef {
                params: parse_params(&script.arena, sort_aliases, args)?,
                result_sort: declared_sort,
                body: body_expr,
            },
        );
        Ok(())
    }
}

/// `(define-const c S body)` — the nullary `define-fun` abbreviation
/// (SMT-LIB §3.7.2). Items are `[define-const, c, S, body]` (length 4), versus
/// `define-fun`'s `[define-fun, c, (), S, body]`. We parse the same pieces and
/// dispatch straight to [`parse_define_fun_alias`], so the binding semantics
/// (sort check + `aliases` insertion) are byte-for-byte identical to a no-args
/// `define-fun`.
#[allow(clippy::too_many_arguments)]
fn parse_define_const<'a>(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &mut HashMap<String, MacroDef<'a>>,
    sort_aliases: &HashMap<String, Sort>,
    named: &mut HashMap<String, TermId>,
    seq: &SeqInfo,
    ff: &FfInfo,
    lenabs: &LenAbs,
    items: &'a [SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 4, "define-const")?;
    let name = atom_at(items, 1)?;
    let declared_sort = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 2)?)?;
    let body_expr = sexpr_at(items, 3)?;
    parse_define_fun_alias(
        script,
        aliases,
        macros,
        named,
        seq,
        ff,
        lenabs,
        name,
        declared_sort,
        body_expr,
    )
}

#[allow(clippy::too_many_arguments)]
fn parse_define_fun_alias(
    script: &mut Script,
    aliases: &mut HashMap<String, TermId>,
    macros: &HashMap<String, MacroDef<'_>>,
    named: &mut HashMap<String, TermId>,
    seq: &SeqInfo,
    ff: &FfInfo,
    lenabs: &LenAbs,
    name: &str,
    declared_sort: Sort,
    body_expr: &SExpr,
) -> Result<(), SmtError> {
    let guard_checkpoint = lenabs.encoding_guard_checkpoint();
    let body = parse_term(
        &mut script.arena,
        body_expr,
        aliases,
        macros,
        named,
        seq,
        ff,
        lenabs,
    )?;
    reject_new_encoding_guards(lenabs, guard_checkpoint, "define-fun/define-const")?;
    let body_sort = script.arena.sort_of(body);
    // Int→Real coercion for a Real-declared nullary constant whose body is an
    // integer literal/term: SMT-LIB admits `(define-fun x () Real 0)` (a numeral
    // denotes a Real in a Reals context). Fold an integer constant to the exact
    // real constant, or embed a non-constant Int term via the exact `to_real`
    // operator — denotation-preserving, matching Z3/cvc5. Any other sort mismatch
    // is still a genuine error.
    let body =
        if body_sort != declared_sort && declared_sort == Sort::Real && body_sort == Sort::Int {
            match *script.arena.node(body) {
                TermNode::IntConst(value) => script.arena.real_const(Rational::integer(value)),
                _ => script.arena.int_to_real(body)?,
            }
        } else if body_sort != declared_sort {
            return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
                declared_sort,
                body_sort,
            )));
        } else {
            body
        };
    aliases.insert(name.to_owned(), body);
    Ok(())
}

#[derive(Clone, Copy)]
struct Param<'a> {
    name: &'a str,
    sort: Sort,
}

struct MacroDef<'a> {
    params: Vec<Param<'a>>,
    result_sort: Sort,
    body: &'a SExpr,
}

fn parse_params<'a>(
    arena: &TermArena,
    sort_aliases: &HashMap<String, Sort>,
    args: &'a [SExpr],
) -> Result<Vec<Param<'a>>, SmtError> {
    let mut params = Vec::with_capacity(args.len());
    for arg in args {
        let pair = arg
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("define-fun parameter".to_owned()))?;
        let name = pair[0]
            .atom()
            .ok_or_else(|| SmtError::Syntax("define-fun parameter name".to_owned()))?;
        if params.iter().any(|p: &Param<'_>| p.name == name) {
            return Err(SmtError::Syntax(format!(
                "duplicate define-fun parameter `{name}`"
            )));
        }
        params.push(Param {
            name,
            sort: parse_sort(arena, sort_aliases, &pair[1])?,
        });
    }
    Ok(params)
}

fn exact_len(items: &[SExpr], expected: usize, head: &str) -> Result<(), SmtError> {
    if items.len() == expected {
        Ok(())
    } else {
        Err(SmtError::Syntax(format!(
            "`{head}` expects {} arguments, got {}",
            expected.saturating_sub(1),
            items.len().saturating_sub(1)
        )))
    }
}

fn atom_at(items: &[SExpr], i: usize) -> Result<&str, SmtError> {
    items
        .get(i)
        .and_then(SExpr::atom)
        .ok_or_else(|| SmtError::Syntax(format!("expected atom at position {i}")))
}

fn sexpr_at(items: &[SExpr], i: usize) -> Result<&SExpr, SmtError> {
    items
        .get(i)
        .ok_or_else(|| SmtError::Syntax(format!("expected argument at position {i}")))
}

fn parse_sort(
    arena: &TermArena,
    sort_aliases: &HashMap<String, Sort>,
    e: &SExpr,
) -> Result<Sort, SmtError> {
    match e {
        SExpr::Atom(a) if a == "Bool" => Ok(Sort::Bool),
        SExpr::Atom(a) if a == "Int" => Ok(Sort::Int),
        SExpr::Atom(a) if a == "Real" => Ok(Sort::Real),
        // Floating-point sorts are first-class `Sort::Float` (ADR-0026), lowered
        // structurally to `BitVec(exp + sig)`; the distinct sort lets conversions
        // tell a float operand from a plain bit-vector.
        SExpr::Atom(a) if a == "Float16" => Ok(Sort::Float { exp: 5, sig: 11 }),
        SExpr::Atom(a) if a == "Float32" => Ok(Sort::Float { exp: 8, sig: 24 }),
        SExpr::Atom(a) if a == "Float64" => Ok(Sort::Float { exp: 11, sig: 53 }),
        SExpr::Atom(a) if a == "Float128" => Ok(Sort::Float { exp: 15, sig: 113 }),
        // The `String` sort is the bounded-model fragment (ADR-0029): a string of
        // up to `STRING_MAX_LEN` bytes is one bit-vector packing a length (low) and
        // the content bytes (above). The sort resolves to that `BitVec`; declared
        // string symbols additionally carry a canonical well-formedness constraint
        // (asserted at `declare-*` time) so equal strings share one bit pattern and
        // `=`/`distinct` decide via the BV path. `Seq` (unbounded sequences) has no
        // sound bounded lowering yet, so it stays a scoped `Unsupported`.
        SExpr::Atom(a) if a == "String" => Ok(Sort::BitVec(STRING_TOTAL)),
        // The `RoundingMode` sort is the 5-element FP rounding-mode enumeration,
        // modeled as a [`BitVec(ROUNDING_MODE_BITS)`] (8 patterns, the 5 SMT-LIB
        // modes mapped by [`rounding_mode_value`]). A declared `RoundingMode`
        // symbol additionally carries a `≤ 4` well-formedness constraint (asserted
        // at declare time, see [`declare_rounding_mode_symbol`]) so the sort has
        // exactly its 5 inhabitants. The 5 literal mode keywords still parse as
        // concrete [`RoundingMode`] values (a fast single-mode path); this sort
        // path only fires when `RoundingMode` is named as a *sort*.
        SExpr::Atom(a) if a == "RoundingMode" => Ok(Sort::RoundingMode),
        SExpr::Atom(a) if a == "Seq" => Err(SmtError::Unsupported(format!(
            "the bare `{a}` sort head needs an element sort `(Seq E)` (ADR-0029)"
        ))),
        SExpr::List(items) => {
            // `(Seq E)` over a fixed-width element sort → the packed `BitVec`
            // (ADR-0029 generalization of the bounded-string layout). The
            // width→element-width mapping was registered by `build_seq_info`.
            if items.len() == 2 && items[0].atom() == Some("Seq") {
                return seq_sort(items);
            }
            if items.len() == 4
                && items[0].atom() == Some("_")
                && items[1].atom() == Some("FloatingPoint")
                && let (Some(eb), Some(sb)) = (
                    items[2].atom().and_then(|s| s.parse::<u32>().ok()),
                    items[3].atom().and_then(|s| s.parse::<u32>().ok()),
                )
            {
                if eb <= 1 || sb <= 1 {
                    return Err(SmtError::Syntax(format!(
                        "FloatingPoint parameters must both be greater than 1, got ({eb}, {sb})"
                    )));
                }
                let total = eb
                    .checked_add(sb)
                    .ok_or_else(|| SmtError::Syntax("FloatingPoint width overflow".to_owned()))?;
                if total > MAX_BV_WIDTH {
                    return Err(SmtError::Syntax(format!(
                        "FloatingPoint width {total} exceeds implementation cap {MAX_BV_WIDTH}"
                    )));
                }
                return Ok(Sort::Float { exp: eb, sig: sb });
            }
            if items.len() == 3
                && items[0].atom() == Some("_")
                && items[1].atom() == Some("BitVec")
                && let Some(w) = items[2].atom().and_then(|s| s.parse::<u32>().ok())
            {
                return Ok(Sort::BitVec(w));
            }
            // `(_ FiniteField p)` — a prime field `GF(p)` modeled as `BitVec(w)`
            // with `w = ff_width(p)` (QF_FF). The prime `p` is carried directly, so
            // resolution is pure; the modulus is validated (prime, ≤ the bit cap)
            // by the up-front [`build_ff_info`] scan, which would have declined the
            // whole script otherwise — so re-validating here only re-derives the
            // width and surfaces the same `Unsupported` reason on the unusual path
            // where a finite-field sort appears outside a declaration/`as`.
            if is_ff_sort_sexpr(e) {
                let p = parse_ff_modulus(items)?;
                return Ok(Sort::BitVec(ff_width(p)));
            }
            if items.len() == 3 && items[0].atom() == Some("Array") {
                let index = parse_sort(arena, sort_aliases, &items[1])?;
                let element = parse_sort(arena, sort_aliases, &items[2])?;
                let index = ArraySortKey::from_sort(index).ok_or_else(|| {
                    SmtError::Unsupported(format!("nested array index sort is unsupported: {e:?}"))
                })?;
                let element = ArraySortKey::from_sort(element).ok_or_else(|| {
                    SmtError::Unsupported(format!(
                        "nested array element sort is unsupported: {e:?}"
                    ))
                })?;
                return Ok(Sort::Array { index, element });
            }
            Err(SmtError::Unsupported(format!("sort {e:?}")))
        }
        // A declared datatype sort (ADR-0022), referenced by name, or a
        // `define-sort` alias (looked up after builtins/datatypes so a builtin
        // sort name can never be shadowed).
        SExpr::Atom(a) => arena
            .find_datatype(a)
            .map(Sort::Datatype)
            .or_else(|| arena.find_uninterpreted_sort(a).map(Sort::Uninterpreted))
            .or_else(|| sort_aliases.get(a).copied())
            .ok_or_else(|| SmtError::Unsupported(format!("sort `{a}`"))),
    }
}

/// `(define-sort name () body)` — a 0-arity sort alias (ADR-pending command
/// parity): `name` resolves to `body` wherever a sort is expected. The body is
/// parsed through [`parse_sort`], so an alias may reference an earlier alias.
/// Parametric aliases (`(define-sort Pair (X) …)`) are not supported.
///
/// # Errors
///
/// [`SmtError::Unsupported`] for a parametric (non-empty parameter list) alias,
/// and [`SmtError::Syntax`] for a malformed form, a name that is a builtin sort,
/// or a duplicate alias.
fn parse_define_sort(
    script: &mut Script,
    sort_aliases: &mut HashMap<String, Sort>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 4, "define-sort")?;
    let name = atom_at(items, 1)?;
    let params = items
        .get(2)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("define-sort parameter list".to_owned()))?;
    if !params.is_empty() {
        return Err(SmtError::Unsupported("parametric define-sort".to_owned()));
    }
    if is_builtin_sort_name(name) || script.arena.find_datatype(name).is_some() {
        return Err(SmtError::Syntax(format!(
            "define-sort: `{name}` is a builtin or declared sort"
        )));
    }
    if sort_aliases.contains_key(name) {
        return Err(SmtError::Syntax(format!(
            "define-sort: duplicate sort alias `{name}`"
        )));
    }
    let body = parse_sort(&script.arena, sort_aliases, sexpr_at(items, 3)?)?;
    sort_aliases.insert(name.to_owned(), body);
    Ok(())
}

/// `(declare-sort U n)` — an uninterpreted sort.
///
/// The arity-0 case `(declare-sort U 0)` is the common `QF_UF`/`QF_UFLIA` shape:
/// `U` is registered as a first-class [`Sort::Uninterpreted`] id in the arena and
/// in the shared `sort_aliases` map. Later uses in `declare-fun` parameter/result
/// positions, `=`, `distinct`, `ite`, and quantifier binders remain many-sorted
/// EUF instead of being collapsed to a fixed-width bit-vector.
///
/// Parametric declared sorts (`(declare-sort List 1)` and higher) would model a
/// *family* of sorts, which the scalar BV encoding cannot express, so they are
/// rejected as [`SmtError::Unsupported`] (rare in practice).
///
/// # Errors
///
/// [`SmtError::Unsupported`] for a parametric (arity ≥ 1) sort; [`SmtError::Syntax`]
/// for a malformed form, a non-numeric arity, a name that is a builtin sort, or a
/// duplicate sort name (mirroring [`parse_define_sort`]).
fn parse_declare_sort(
    script: &mut Script,
    sort_aliases: &mut HashMap<String, Sort>,
    items: &[SExpr],
) -> Result<(), SmtError> {
    exact_len(items, 3, "declare-sort")?;
    let name = atom_at(items, 1)?;
    let arity = atom_at(items, 2)?
        .parse::<u32>()
        .map_err(|_| SmtError::Syntax("declare-sort arity must be a numeral".to_owned()))?;
    if arity != 0 {
        return Err(SmtError::Unsupported(format!(
            "parametric/arity-{arity} declared sort `{name}` (only arity-0 \
             uninterpreted sorts are supported)"
        )));
    }
    if is_builtin_sort_name(name)
        || script.arena.find_datatype(name).is_some()
        || script.arena.find_uninterpreted_sort(name).is_some()
    {
        return Err(SmtError::Syntax(format!(
            "declare-sort: `{name}` is a builtin or declared sort"
        )));
    }
    if sort_aliases.contains_key(name) {
        return Err(SmtError::Syntax(format!(
            "declare-sort: duplicate sort name `{name}`"
        )));
    }
    let id = script.arena.declare_uninterpreted_sort(name);
    sort_aliases.insert(name.to_owned(), Sort::Uninterpreted(id));
    Ok(())
}

/// Whether `name` is a builtin (atom-named) sort keyword, so a `define-sort`
/// alias may not redefine it. Indexed/compound sort heads (`BitVec`, `Array`,
/// `FloatingPoint`) only ever appear inside a list, never as a bare alias name,
/// so they are covered by the parser, not this guard.
fn is_builtin_sort_name(name: &str) -> bool {
    matches!(
        name,
        "Bool"
            | "Int"
            | "Real"
            | "Float16"
            | "Float32"
            | "Float64"
            | "Float128"
            | "String"
            | "RoundingMode"
            | "Seq"
    )
}

/// One frame of the iterative term converter.
enum Frame<'a> {
    /// Evaluate this expression (pushing children first when needed).
    Eval(&'a SExpr),
    /// After the inner term of `(! t :named name)` is on the result stack, bind
    /// `name → t` in the script-global `:named` map (the term itself stays on
    /// the stack as the attributed term's value).
    RegisterNamed { name: &'a str },
    /// Pop `argc` results and apply the operator list.
    Apply { items: &'a [SExpr], argc: usize },
    /// Pop the evaluated string operand of `(str.in_re s R)` and encode the
    /// bounded regex match against the regex s-expression `re_expr` (which is
    /// **not** a term and so is compiled, not evaluated, by [`crate::regex`]).
    ApplyInRe { re_expr: &'a SExpr },
    /// Pop the two evaluated string operands `s` and `t` of
    /// `(str.replace_re s R t)` / `(str.replace_re_all s R t)` and apply the
    /// regex-driven replace against the regex s-expression `re_expr` (the middle
    /// `RegLan` argument, which is **compiled**, not evaluated as a term).
    /// `all` selects `str.replace_re_all` over `str.replace_re`.
    ApplyReplaceRe { re_expr: &'a SExpr, all: bool },
    /// Pop `argc` results and apply a rounding-mode FP op. When `mode` is
    /// `Some(m)` the mode is a literal `RoundingMode` value parsed before queueing
    /// (the single-mode fast path) and only the operand children were queued. When
    /// `mode` is `None` the mode is a **symbolic** `RoundingMode` term: it was
    /// queued as the *first* operand (so the top-of-stack ordering is `[rm, ops…]`)
    /// and the op expands to the 5-way `ite` ([`apply_fp_rounded_symbolic`]).
    ApplyFpRounded {
        items: &'a [SExpr],
        mode: Option<RoundingMode>,
        argc: usize,
    },
    /// Like [`Frame::ApplyFpRounded`] but for an *indexed* head, e.g.
    /// `((_ to_fp 8 24) RM x)` or `((_ fp.to_sbv 32) RM x)`. The same `mode`
    /// literal-vs-symbolic convention applies.
    ApplyFpRoundedIndexed {
        items: &'a [SExpr],
        mode: Option<RoundingMode>,
        argc: usize,
    },
    /// Pop `argc` results and expand a parameterized `define-fun` body.
    ApplyMacro { name: &'a str, argc: usize },
    /// Check the sort of the most recent result.
    CheckSort { expected: Sort, context: &'a str },
    /// Pop one binding scope after a `let` body finishes.
    PopScope,
    /// Pop `count` evaluated binding values, bind them, then queue the body.
    BindLet {
        names: Vec<&'a str>,
        body: &'a SExpr,
    },
    /// Enter a quantifier scope (bound names → fresh symbol vars), then queue
    /// the body, scope pop, and the quantifier wrap.
    BindQuantifier {
        bindings: Vec<(&'a str, TermId)>,
        syms: Vec<axeyum_ir::SymbolId>,
        is_forall: bool,
        body: &'a SExpr,
    },
    /// Pop the quantifier body and wrap it in `forall`/`exists` over `syms`.
    ApplyQuantifier {
        syms: Vec<axeyum_ir::SymbolId>,
        is_forall: bool,
    },
    /// Pop the just-evaluated scrutinee `e` and set up the `match` desugaring
    /// (ADR-pending datatype `match`): plan per-case testers and binding scopes,
    /// queue each case body's evaluation under its scope, then a [`Frame::CombineMatch`]
    /// to fold the case results into a right-nested `ite`.
    MatchScrutinee { cases: &'a [SExpr] },
    /// Push a precomputed binding scope (a `match` case's pattern variables →
    /// selector terms); paired with a later [`Frame::PopScope`].
    PushScope(HashMap<&'a str, TermId>),
    /// Pop the `n = testers.len()` evaluated case-result terms and fold them into
    /// a right-nested `ite`: each `Some(t)` is the `is-C` guard for that case, and
    /// the final (innermost else) case carries `None` (unconditional, exhaustive).
    CombineMatch { testers: Vec<Option<TermId>> },
}

#[allow(clippy::too_many_lines)]
#[allow(clippy::too_many_arguments)]
fn parse_term<'a>(
    arena: &mut TermArena,
    root: &'a SExpr,
    aliases: &HashMap<String, TermId>,
    macros: &HashMap<String, MacroDef<'a>>,
    named: &mut HashMap<String, TermId>,
    seq: &SeqInfo,
    ff: &FfInfo,
    lenabs: &LenAbs,
) -> Result<TermId, SmtError> {
    let mut frames: Vec<Frame> = vec![Frame::Eval(root)];
    let mut results: Vec<TermId> = Vec::new();
    let mut scopes: Vec<HashMap<&'a str, TermId>> = Vec::new();

    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Eval(e) => queue_eval(
                arena,
                e,
                aliases,
                macros,
                named,
                ff,
                lenabs,
                &scopes,
                &mut frames,
                &mut results,
            )?,
            Frame::RegisterNamed { name } => {
                // The just-evaluated `(! t :named name)` inner term is on top of
                // the stack; bind `name → t` script-globally (it stays on the
                // stack as the attributed term's value).
                let t = *results
                    .last()
                    .ok_or_else(|| SmtError::Syntax("`:named` term".to_owned()))?;
                named.insert(name.to_owned(), t);
            }
            Frame::Apply { items, argc } => {
                let args = results.split_off(results.len() - argc);
                results.push(apply_op(arena, seq, ff, lenabs, items, &args)?);
            }
            Frame::ApplyInRe { re_expr } => {
                let s = results
                    .pop()
                    .ok_or_else(|| SmtError::Syntax("str.in_re string operand".to_owned()))?;
                lenabs.mark_used();
                let atom = crate::regex::encode_in_re(arena, s, re_expr)?;
                // P2.7 A.2: `s ∈ R ⟹ min(R) ≤ len(s) [≤ max(R)]` — the regex's
                // match-length interval feeds the unbounded length abstraction,
                // so a long-forcing regex (e.g. a 10-char literal concat over an
                // 8-bounded variable) trips the bound-bite detector instead of
                // surfacing a bound-induced `unsat`.
                let mut fact: Option<TermId> = None;
                if let Some((min, max)) = crate::regex::in_re_length_interval(re_expr) {
                    let ls = lenabs.len_expr_string(arena, s)?;
                    if min > 0 {
                        let c = arena.int_const(i128::from(min));
                        fact = Some(arena.int_le(c, ls)?);
                    }
                    if let Some(mx) = max {
                        let c = arena.int_const(i128::from(mx));
                        let ub = arena.int_le(ls, c)?;
                        fact = Some(match fact {
                            Some(lb) => arena.and(lb, ub)?,
                            None => ub,
                        });
                    }
                }
                // The atom must enter the abstraction map even fact-less —
                // kept verbatim it would smuggle the encoding bound back in.
                // A symbolic regex atom is always *coarse*: its interval
                // cannot see union gaps (e.g. `ab | a^9`), so an unconfirmed
                // bounded `unsat` on such a script must downgrade. A ground
                // atom (literal string operand) or a constant-folded one is
                // exact at every bound and stays verbatim.
                if !packed_const(arena, s) && !matches!(arena.node(atom), TermNode::BoolConst(_)) {
                    lenabs.coarse.set(true);
                    match fact {
                        Some(f) => {
                            lenabs.note_atom_fact(arena, atom, f)?;
                        }
                        None => lenabs.note_atom_free(arena, atom)?,
                    }
                }
                results.push(atom);
            }
            Frame::ApplyReplaceRe { re_expr, all } => {
                // Operands were queued `s` then `t`, so the stack top is `t`.
                let t = results
                    .pop()
                    .ok_or_else(|| SmtError::Syntax("str.replace_re replacement".to_owned()))?;
                let s = results
                    .pop()
                    .ok_or_else(|| SmtError::Syntax("str.replace_re string operand".to_owned()))?;
                lenabs.mark_used();
                let out = if all {
                    string_replace_re_all(arena, s, re_expr, t)?
                } else {
                    string_replace_re(arena, s, re_expr, t)?
                };
                results.push(out);
            }
            Frame::ApplyFpRounded { items, mode, argc } => {
                let args = results.split_off(results.len() - argc);
                let out = if let Some(m) = mode {
                    apply_fp_rounded(arena, items, m, &args)?
                } else {
                    // Symbolic mode: the first queued operand is the `rm` term.
                    let (rm, ops) = args
                        .split_first()
                        .ok_or_else(|| SmtError::Syntax("missing rounding mode".to_owned()))?;
                    apply_fp_rounded_symbolic(arena, items, *rm, ops)?
                };
                results.push(out);
            }
            Frame::ApplyFpRoundedIndexed { items, mode, argc } => {
                let args = results.split_off(results.len() - argc);
                let out = if let Some(m) = mode {
                    apply_fp_rounded_indexed(arena, items, m, &args)?
                } else {
                    // Symbolic mode: the first queued operand is the `rm` term.
                    let (rm, ops) = args
                        .split_first()
                        .ok_or_else(|| SmtError::Syntax("missing rounding mode".to_owned()))?;
                    apply_fp_rounded_indexed_symbolic(arena, items, *rm, ops)?
                };
                results.push(out);
            }
            Frame::ApplyMacro { name, argc } => {
                queue_macro_expansion(
                    arena,
                    macros,
                    &mut scopes,
                    &mut frames,
                    &mut results,
                    name,
                    argc,
                )?;
            }
            Frame::CheckSort { expected, context } => {
                check_recent_sort(arena, &results, expected, context)?;
            }
            Frame::BindLet { names, body } => {
                bind_let_scope(&mut scopes, &mut results, names);
                frames.push(Frame::PopScope);
                frames.push(Frame::Eval(body));
            }
            Frame::BindQuantifier {
                bindings,
                syms,
                is_forall,
                body,
            } => {
                let mut scope = HashMap::new();
                for (name, term) in bindings {
                    scope.insert(name, term);
                }
                scopes.push(scope);
                frames.push(Frame::ApplyQuantifier { syms, is_forall });
                frames.push(Frame::PopScope);
                frames.push(Frame::Eval(body));
            }
            Frame::ApplyQuantifier { syms, is_forall } => {
                let mut acc = results
                    .pop()
                    .ok_or_else(|| SmtError::Syntax("quantifier body".to_owned()))?;
                for &sym in syms.iter().rev() {
                    acc = if is_forall {
                        arena.forall(sym, acc)?
                    } else {
                        arena.exists(sym, acc)?
                    };
                }
                results.push(acc);
            }
            Frame::PopScope => {
                scopes.pop();
            }
            Frame::MatchScrutinee { cases } => {
                let scrutinee = results
                    .pop()
                    .ok_or_else(|| SmtError::Syntax("match scrutinee".to_owned()))?;
                queue_match(arena, scrutinee, cases, &mut frames)?;
            }
            Frame::PushScope(scope) => {
                scopes.push(scope);
            }
            Frame::CombineMatch { testers } => {
                combine_match(arena, &mut results, &testers)?;
            }
        }
    }
    if results.len() == 1 {
        Ok(results.pop().expect("one result"))
    } else {
        Err(SmtError::Syntax(format!(
            "term conversion produced {} results",
            results.len()
        )))
    }
}

#[allow(clippy::too_many_arguments)]
fn queue_eval<'a>(
    arena: &mut TermArena,
    expr: &'a SExpr,
    aliases: &HashMap<String, TermId>,
    macros: &HashMap<String, MacroDef<'a>>,
    named: &HashMap<String, TermId>,
    ff: &FfInfo,
    lenabs: &LenAbs,
    scopes: &[HashMap<&'a str, TermId>],
    frames: &mut Vec<Frame<'a>>,
    results: &mut Vec<TermId>,
) -> Result<(), SmtError> {
    match expr {
        SExpr::Atom(a) => results.push(parse_atom(arena, a, aliases, named, scopes)?),
        SExpr::List(items) => queue_list_eval(arena, items, macros, ff, lenabs, frames, results)?,
    }
    Ok(())
}

#[allow(clippy::too_many_lines)]
fn queue_list_eval<'a>(
    arena: &mut TermArena,
    items: &'a [SExpr],
    macros: &HashMap<String, MacroDef<'a>>,
    ff: &FfInfo,
    lenabs: &LenAbs,
    frames: &mut Vec<Frame<'a>>,
    results: &mut Vec<TermId>,
) -> Result<(), SmtError> {
    let head = items
        .first()
        .ok_or_else(|| SmtError::Syntax("empty application".to_owned()))?;
    if head.atom() == Some("_") {
        results.push(parse_indexed_constant(arena, items)?);
    } else if head.atom() == Some("!") {
        // Attributed term `(! t :attr v ...)` denotes `t`. Non-`:named`
        // annotations (`:pattern` triggers, …) are hints we drop. A `:named foo`
        // attribute additionally binds `foo` as a script-global alias for `t`,
        // so later bare references to `foo` resolve — we queue a
        // [`Frame::RegisterNamed`] to record the binding once `t` is evaluated.
        let inner = items
            .get(1)
            .ok_or_else(|| SmtError::Syntax("`!` expects a term".to_owned()))?;
        if let Some(name) = attribute_named_name(items) {
            frames.push(Frame::RegisterNamed { name });
        }
        frames.push(Frame::Eval(inner));
    } else if head.atom() == Some("let") {
        queue_let(items, frames)?;
    } else if head.atom() == Some("match") {
        queue_match_scrutinee(items, frames)?;
    } else if head.atom() == Some("forall") || head.atom() == Some("exists") {
        let is_forall = head.atom() == Some("forall");
        queue_quantifier(arena, items, is_forall, frames)?;
    } else if head.atom() == Some("as") && items.len() == 3 && items[1].atom() == Some("seq.empty")
    {
        // `(as seq.empty (Seq E))` — the empty sequence (length 0, zero content)
        // in the max-length-`SEQ_MAX_LEN` packed layout for element width `ew`,
        // taken from the `(Seq E)` ascription (ADR-0029). The element width is on
        // the ascription, so it needs no `seq` table; a non-fixed-width element
        // declines cleanly.
        let ew = seq_decl_elem_width(&items[2]).ok_or_else(|| {
            SmtError::Unsupported(format!(
                "`(as seq.empty {:?})` has no sound fixed-width element packing (ADR-0029)",
                items[2]
            ))
        })?;
        // P2.7 A.2: the empty sequence has length exactly 0.
        lenabs.mark_used();
        let empty = seq_empty(arena, ew)?;
        let zero = arena.int_const(0);
        lenabs.note_len(empty, zero);
        results.push(empty);
    } else if head.atom() == Some("as")
        && items.len() == 3
        && !ff.is_empty()
        && is_ff_literal_name(items[1].atom())
    {
        // `(as ffK Sort)` — a finite-field literal whose value is `K` and whose
        // modulus is the ascribed field sort `(_ FiniteField p)` (directly or via a
        // `define-sort` alias). Resolved to a canonical residue `BitVec` constant
        // (QF_FF). The leading `ffK` is not a bare term, so it must be handled here,
        // before the generic ascription branch evaluates `items[1]`.
        results.push(parse_ff_as_literal(
            arena,
            ff,
            items[1].atom().expect("checked is_ff_literal_name"),
            &items[2],
        )?);
    } else if head.atom() == Some("as") && items.len() == 3 {
        // Sort ascription `(as t S)` denotes `t` — it only annotates the sort of
        // an otherwise-determined term (SMT-LIB §3.6, "qualified identifier").
        // Quantifier-free axeyum already infers every term's sort, so the
        // ascription is an identity we drop: evaluate the inner term and ignore
        // the trailing sort s-expr (which is a *sort*, not a term, so it must
        // not be queued for term evaluation). The `((as const S) v)` constant-
        // array form is an *application* whose head is itself `(as const S)`;
        // it has a list head and is handled in [`apply_op`], not here.
        frames.push(Frame::Eval(&items[1]));
    } else if head.atom() == Some("str.in_re") && items.len() == 3 {
        // `(str.in_re s R)`: the second argument `R` is a `RegLan` regex, which
        // has no term sort — it must be **compiled** (Thompson NFA → bounded
        // match), not evaluated as a term. Queue only the string operand for
        // evaluation, then a [`Frame::ApplyInRe`] that pops it and encodes the
        // bounded regex match against `R` (ADR-0029 slice 5).
        frames.push(Frame::ApplyInRe { re_expr: &items[2] });
        frames.push(Frame::Eval(&items[1]));
    } else if let Some(name @ ("str.replace_re" | "str.replace_re_all")) = head.atom()
        && items.len() == 4
    {
        // `(str.replace_re s R t)` / `(str.replace_re_all s R t)`: the middle
        // argument `R` is a `RegLan` regex (no term sort) — compiled, not
        // evaluated. Queue the string operands `s` (items[1]) and `t` (items[3]),
        // then a [`Frame::ApplyReplaceRe`] that pops them and applies the
        // regex-driven replace against `R` (items[2]). Evals push in reverse so the
        // stack ends with `t` on top (ADR-0029).
        frames.push(Frame::ApplyReplaceRe {
            re_expr: &items[2],
            all: name == "str.replace_re_all",
        });
        frames.push(Frame::Eval(&items[3]));
        frames.push(Frame::Eval(&items[1]));
    } else if head.atom() == Some("str.indexof_re") {
        // `str.indexof_re` is **not** in the SMT-LIB `UnicodeStrings` theory (it is
        // a cvc5 extension) and is unsupported by the Z3 differential oracle, so
        // there is no ground truth to validate an encoding against. Decline cleanly
        // (a sound `unknown`) rather than risk a wrong verdict (ADR-0029). The
        // regex argument is never queued for term evaluation.
        return Err(SmtError::Unsupported(
            "str.indexof_re is not in the SMT-LIB UnicodeStrings theory (a cvc5 extension, \
             unsupported by the oracle); declined (ADR-0029)"
                .to_owned(),
        ));
    } else if let Some(name) = head.atom()
        && is_fp_rounded_op(name)
    {
        // Rounding-mode FP ops `(fp.add RM x y)`: the first argument is the
        // rounding mode. A *literal* mode is parsed here (single-mode fast path,
        // byte-identical); a *symbolic* mode (e.g. a declared `RoundingMode`
        // symbol or a `define-fun` alias) is queued as the first operand and
        // expands to the 5-way `ite` in [`apply_fp_rounded_symbolic`].
        let mode_expr = items
            .get(1)
            .ok_or_else(|| SmtError::Syntax(format!("{name} expects a rounding mode")))?;
        let mode = parse_rounding_mode(mode_expr);
        // Queue the rounding-mode subterm too when it is symbolic.
        let queued = if mode.is_some() {
            &items[2..]
        } else {
            &items[1..]
        };
        frames.push(Frame::ApplyFpRounded {
            items,
            mode,
            argc: queued.len(),
        });
        for child in queued.iter().rev() {
            frames.push(Frame::Eval(child));
        }
    } else if let Some(idx) = head.list()
        && idx.first().and_then(SExpr::atom) == Some("_")
        && idx
            .get(1)
            .and_then(SExpr::atom)
            .is_some_and(is_fp_indexed_conversion)
        && items.len() == 3
    {
        // Indexed rounding-mode FP conversions `((_ to_fp eb sb) RM x)`,
        // `((_ fp.to_sbv m) RM x)`, …: the leading `RM` precedes a single operand
        // (`items.len() == 3` = head + RM + operand). A *literal* RM takes the
        // single-mode fast path; a *symbolic* RM is queued as the first operand and
        // expands to the 5-way `ite`. (The mode-free bit-reinterpret
        // `((_ to_fp eb sb) x)` has only one argument — `items.len() == 2` — so it
        // falls through to the generic indexed-application path; `to_fp_unsigned` /
        // `fp.to_sbv` / `fp.to_ubv` always carry a mandatory RM, so they match here.)
        let mode = parse_rounding_mode(&items[1]);
        let queued = if mode.is_some() {
            &items[2..]
        } else {
            &items[1..]
        };
        frames.push(Frame::ApplyFpRoundedIndexed {
            items,
            mode,
            argc: queued.len(),
        });
        for child in queued.iter().rev() {
            frames.push(Frame::Eval(child));
        }
    } else if let Some(name) = head.atom()
        && macros.contains_key(name)
    {
        queue_children(
            items,
            frames,
            Frame::ApplyMacro {
                name,
                argc: items.len() - 1,
            },
        );
    } else {
        queue_children(
            items,
            frames,
            Frame::Apply {
                items,
                argc: items.len() - 1,
            },
        );
    }
    Ok(())
}

fn queue_children<'a>(items: &'a [SExpr], frames: &mut Vec<Frame<'a>>, apply: Frame<'a>) {
    frames.push(apply);
    for child in items[1..].iter().rev() {
        frames.push(Frame::Eval(child));
    }
}

/// Queues a quantifier `(forall ((x T) ..) body)`: each bound variable becomes
/// a fresh arena symbol (uniquely named to avoid capture), scoped to `body`,
/// and the body is wrapped in `forall`/`exists` over those symbols (ADR-0016).
fn queue_quantifier<'a>(
    arena: &mut TermArena,
    items: &'a [SExpr],
    is_forall: bool,
    frames: &mut Vec<Frame<'a>>,
) -> Result<(), SmtError> {
    let keyword = if is_forall { "forall" } else { "exists" };
    exact_len(items, 3, keyword)?;
    let binding_list = items
        .get(1)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax(format!("{keyword} bindings")))?;
    if binding_list.is_empty() {
        return Err(SmtError::Syntax(format!(
            "{keyword} needs >= 1 bound variable"
        )));
    }
    let body = sexpr_at(items, 2)?;

    let mut bindings = Vec::with_capacity(binding_list.len());
    let mut syms = Vec::with_capacity(binding_list.len());
    for binding in binding_list {
        let pair = binding
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax(format!("{keyword} binding pair")))?;
        let name = pair[0]
            .atom()
            .ok_or_else(|| SmtError::Syntax(format!("{keyword} binding name")))?;
        // Quantifier binder sorts are parsed in term-conversion context; sort
        // aliases are resolved at declaration sites, not threaded here.
        let no_aliases: HashMap<String, Sort> = HashMap::new();
        let sort = parse_sort(arena, &no_aliases, &pair[1])?;
        let sym = fresh_quantifier_symbol(arena, name, sort)?;
        bindings.push((name, arena.var(sym)));
        syms.push(sym);
    }
    frames.push(Frame::BindQuantifier {
        bindings,
        syms,
        is_forall,
        body,
    });
    Ok(())
}

/// Declares a uniquely-named fresh symbol for a quantifier's bound variable, so
/// it cannot capture a free symbol or another binder's variable.
fn fresh_quantifier_symbol(
    arena: &mut TermArena,
    base: &str,
    sort: Sort,
) -> Result<axeyum_ir::SymbolId, SmtError> {
    let mut index = 0u32;
    loop {
        let candidate = format!("!q.{base}.{index}");
        if arena.find_symbol(&candidate).is_none() {
            return Ok(arena.declare(&candidate, sort)?);
        }
        index += 1;
    }
}

/// Application of a reduction-internal total function interpreting the
/// SMT-LIB-unspecified result of an out-of-domain FP→int conversion.  A real UF,
/// rather than a syntax-keyed fresh symbol, is required: semantically equal FP
/// operands (including the single NaN value) must receive the same result.
fn unspecified_conversion_value(
    arena: &mut TermArena,
    tag: &str,
    operand: TermId,
    width: u32,
    mode: RoundingMode,
) -> Result<TermId, SmtError> {
    let operand_sort = arena.sort_of(operand);
    let Sort::Float { exp, sig } = operand_sort else {
        return Err(SmtError::Syntax(format!(
            "unspecified FP conversion operand must be Float, got {operand_sort:?}"
        )));
    };
    let name = format!("!fp.{tag}.{exp}.{sig}.{width}.{mode:?}");
    let func = match arena.find_internal_function(&name) {
        Some(func) => func,
        None => arena.declare_internal_fun(&name, &[operand_sort], Sort::BitVec(width))?,
    };
    Ok(arena.apply(func, &[operand])?)
}

fn unspecified_to_real_value(arena: &mut TermArena, operand: TermId) -> Result<TermId, SmtError> {
    let operand_sort = arena.sort_of(operand);
    let Sort::Float { exp, sig } = operand_sort else {
        return Err(SmtError::Syntax(format!(
            "fp.to_real operand must be Float, got {operand_sort:?}"
        )));
    };
    let name = format!("!fp.to_real.{exp}.{sig}");
    let func = match arena.find_internal_function(&name) {
        Some(func) => func,
        None => arena.declare_internal_fun(&name, &[operand_sort], Sort::Real)?,
    };
    Ok(arena.apply(func, &[operand])?)
}

fn queue_let<'a>(items: &'a [SExpr], frames: &mut Vec<Frame<'a>>) -> Result<(), SmtError> {
    exact_len(items, 3, "let")?;
    let bindings = items
        .get(1)
        .and_then(SExpr::list)
        .ok_or_else(|| SmtError::Syntax("let bindings".to_owned()))?;
    let body = sexpr_at(items, 2)?;
    let names = parse_let_names(bindings)?;
    frames.push(Frame::BindLet { names, body });
    for b in bindings.iter().rev() {
        frames.push(Frame::Eval(&b.list().expect("checked")[1]));
    }
    Ok(())
}

fn parse_let_names(bindings: &[SExpr]) -> Result<Vec<&str>, SmtError> {
    let mut names = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let pair = binding
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("let binding pair".to_owned()))?;
        names.push(
            pair[0]
                .atom()
                .ok_or_else(|| SmtError::Syntax("let name".to_owned()))?,
        );
    }
    for (i, name) in names.iter().enumerate() {
        if names[..i].contains(name) {
            return Err(SmtError::Syntax(format!("duplicate let binding `{name}`")));
        }
    }
    Ok(names)
}

fn queue_macro_expansion<'a>(
    arena: &TermArena,
    macros: &HashMap<String, MacroDef<'a>>,
    scopes: &mut Vec<HashMap<&'a str, TermId>>,
    frames: &mut Vec<Frame<'a>>,
    results: &mut Vec<TermId>,
    name: &'a str,
    arity: usize,
) -> Result<(), SmtError> {
    let actuals = results.split_off(results.len() - arity);
    let def = macros
        .get(name)
        .ok_or_else(|| SmtError::Unsupported(format!("operator `{name}`")))?;
    if actuals.len() != def.params.len() {
        return Err(SmtError::Syntax(format!(
            "`{name}` expects {} arguments, got {}",
            def.params.len(),
            actuals.len()
        )));
    }
    let mut scope = HashMap::new();
    for (param, arg) in def.params.iter().zip(actuals) {
        let actual = arena.sort_of(arg);
        if actual != param.sort {
            return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
                param.sort, actual,
            )));
        }
        scope.insert(param.name, arg);
    }
    scopes.push(scope);
    frames.push(Frame::PopScope);
    frames.push(Frame::CheckSort {
        expected: def.result_sort,
        context: name,
    });
    frames.push(Frame::Eval(def.body));
    Ok(())
}

fn check_recent_sort(
    arena: &TermArena,
    results: &[TermId],
    expected: Sort,
    context: &str,
) -> Result<(), SmtError> {
    let Some(&term) = results.last() else {
        return Err(SmtError::Syntax(format!(
            "`{context}` body produced no result"
        )));
    };
    let actual = arena.sort_of(term);
    if actual != expected {
        return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
            expected, actual,
        )));
    }
    Ok(())
}

fn bind_let_scope<'a>(
    scopes: &mut Vec<HashMap<&'a str, TermId>>,
    results: &mut Vec<TermId>,
    names: Vec<&'a str>,
) {
    let values = results.split_off(results.len() - names.len());
    let mut scope = HashMap::new();
    for (name, value) in names.into_iter().zip(values) {
        scope.insert(name, value);
    }
    scopes.push(scope);
}

// --- datatype `match` desugaring (parse-time) --------------------------------
//
// SMT-LIB 2.6 `(match e ((pat result) ...))` is desugared at parse time to the
// datatype primitives the IR already has — `is-C` testers (`Op::DtTest`), field
// selectors (`Op::DtSelect`), and `ite` — so no IR or solver change is needed.
//
//   (match e ((C1 x y) r1) ((C2) r2) (z r3))
//     ⇒  (ite (is-C1 e) r1[x:=(selC1_0 e), y:=(selC1_1 e)]
//           (ite (is-C2 e) r2
//             r3[z := e]))
//
// Pattern variables bind by substitution into the case result via the same
// scope stack `let` uses, so nested matches/lets and shadowing work. The LAST
// case is always the unconditional `else` (SMT-LIB requires the match to be
// exhaustive); a non-exhaustive match (no trailing default and not all
// constructors covered) is rejected.

/// Queues `(match e (case ...))`: evaluate the scrutinee `e`, then the
/// [`Frame::MatchScrutinee`] plan that sets up the desugaring once `e`'s term
/// (and sort) is known.
fn queue_match_scrutinee<'a>(
    items: &'a [SExpr],
    frames: &mut Vec<Frame<'a>>,
) -> Result<(), SmtError> {
    if items.len() != 3 {
        return Err(SmtError::Syntax(
            "match expects `(match e (case ...))`".to_owned(),
        ));
    }
    let cases = items[2]
        .list()
        .filter(|c| !c.is_empty())
        .ok_or_else(|| SmtError::Syntax("match expects a non-empty case list".to_owned()))?;
    frames.push(Frame::MatchScrutinee { cases });
    frames.push(Frame::Eval(&items[1]));
    Ok(())
}

/// One planned `match` case: the `is-C` guard (`None` for the unconditional,
/// final/else case) and the pattern-variable scope to evaluate its body under.
struct MatchCasePlan<'a> {
    tester: Option<TermId>,
    scope: HashMap<&'a str, TermId>,
    body: &'a SExpr,
}

/// Sets up the `match` desugaring once the scrutinee term `scrutinee` is known:
/// resolves its datatype, plans every case (tester + pattern-variable scope),
/// checks exhaustiveness, and queues each case body's evaluation (under its
/// scope) followed by a [`Frame::CombineMatch`] fold.
///
/// # Errors
///
/// [`SmtError::Syntax`]/[`SmtError::Unsupported`] for a non-datatype scrutinee,
/// an unknown constructor, a wrong constructor field-arity, a default that is not
/// last, or a non-exhaustive match.
fn queue_match<'a>(
    arena: &mut TermArena,
    scrutinee: TermId,
    cases: &'a [SExpr],
    frames: &mut Vec<Frame<'a>>,
) -> Result<(), SmtError> {
    let dt = match arena.sort_of(scrutinee) {
        Sort::Datatype(dt) => dt,
        other => {
            return Err(SmtError::Syntax(format!(
                "match scrutinee must be a datatype value, got {other:?}"
            )));
        }
    };
    let plans = plan_match_cases(arena, scrutinee, dt, cases)?;
    let testers: Vec<Option<TermId>> = plans.iter().map(|p| p.tester).collect();
    frames.push(Frame::CombineMatch { testers });
    // Push each case's [PushScope, Eval(body), PopScope] block in reverse case
    // order so the results land case0, case1, … on the stack for CombineMatch.
    for plan in plans.into_iter().rev() {
        frames.push(Frame::PopScope);
        frames.push(Frame::Eval(plan.body));
        frames.push(Frame::PushScope(plan.scope));
    }
    Ok(())
}

/// Plans each `match` case over datatype `dt`: builds the `is-C` tester and the
/// pattern-variable → selector-term bindings, and validates the case set.
fn plan_match_cases<'a>(
    arena: &mut TermArena,
    scrutinee: TermId,
    dt: axeyum_ir::DatatypeId,
    cases: &'a [SExpr],
) -> Result<Vec<MatchCasePlan<'a>>, SmtError> {
    let mut plans: Vec<MatchCasePlan<'a>> = Vec::with_capacity(cases.len());
    let mut covered: Vec<axeyum_ir::ConstructorId> = Vec::new();
    let mut has_default = false;
    for (idx, case) in cases.iter().enumerate() {
        let parts = case
            .list()
            .filter(|p| p.len() == 2)
            .ok_or_else(|| SmtError::Syntax("match case `(pattern result)`".to_owned()))?;
        let pattern = &parts[0];
        let body = &parts[1];
        if has_default {
            return Err(SmtError::Syntax(
                "match: a default (variable/wildcard) pattern must be the last case".to_owned(),
            ));
        }
        let is_last = idx + 1 == cases.len();
        match plan_one_case(arena, scrutinee, dt, pattern)? {
            CasePattern::Default { scope } => {
                has_default = true;
                plans.push(MatchCasePlan {
                    tester: None,
                    scope,
                    body,
                });
            }
            CasePattern::Constructor { ctor, scope } => {
                if covered.contains(&ctor) {
                    return Err(SmtError::Syntax(format!(
                        "match: duplicate case for constructor `{}`",
                        arena.constructor_name(ctor)
                    )));
                }
                covered.push(ctor);
                // The final case is the unconditional `else` of the right-nested
                // `ite`; for an exhaustive match its `is-C` guard is redundant.
                let tester = if is_last {
                    None
                } else {
                    Some(arena.dt_test(ctor, scrutinee)?)
                };
                plans.push(MatchCasePlan {
                    tester,
                    scope,
                    body,
                });
            }
        }
    }
    // Exhaustiveness: either a trailing default, or every constructor covered.
    if !has_default && covered.len() != arena.datatype_constructors(dt).len() {
        return Err(SmtError::Syntax(format!(
            "non-exhaustive match on `{}`: add the missing constructor cases or a default",
            arena.datatype_name(dt)
        )));
    }
    Ok(plans)
}

/// A single resolved `match` pattern.
enum CasePattern<'a> {
    /// A constructor pattern `(C x …)` or nullary `C`: matched by `is-C`, with
    /// each field variable bound to its selector applied to the scrutinee.
    Constructor {
        ctor: axeyum_ir::ConstructorId,
        scope: HashMap<&'a str, TermId>,
    },
    /// A variable `x` or wildcard `_` default: binds the whole scrutinee to `x`
    /// (`_` binds nothing) and always matches.
    Default { scope: HashMap<&'a str, TermId> },
}

/// Resolves one `match` pattern against datatype `dt`, building its binding scope.
fn plan_one_case<'a>(
    arena: &mut TermArena,
    scrutinee: TermId,
    dt: axeyum_ir::DatatypeId,
    pattern: &'a SExpr,
) -> Result<CasePattern<'a>, SmtError> {
    match pattern {
        // Bare symbol: a nullary constructor of `dt`, or a variable/wildcard.
        SExpr::Atom(name) => {
            if name == "_" {
                return Ok(CasePattern::Default {
                    scope: HashMap::new(),
                });
            }
            match arena.find_constructor(name) {
                Some(ctor) if arena.constructor_datatype(ctor) == dt => {
                    if !arena.constructor_fields(ctor).is_empty() {
                        return Err(SmtError::Syntax(format!(
                            "match: constructor `{name}` takes fields; use `({name} x …)`"
                        )));
                    }
                    Ok(CasePattern::Constructor {
                        ctor,
                        scope: HashMap::new(),
                    })
                }
                // A constructor of a *different* datatype is a name clash, not a
                // valid variable binder here; reject it.
                Some(_) => Err(SmtError::Syntax(format!(
                    "match: `{name}` is a constructor of another datatype, not a valid pattern \
                     for `{}`",
                    arena.datatype_name(dt)
                ))),
                // Not a constructor: a variable pattern binding the whole scrutinee.
                None => {
                    let mut scope = HashMap::new();
                    scope.insert(name.as_str(), scrutinee);
                    Ok(CasePattern::Default { scope })
                }
            }
        }
        // Constructor pattern `(C x1 … xk)`: bind each field variable to its
        // selector applied to the scrutinee.
        SExpr::List(parts) => {
            let cname = parts
                .first()
                .and_then(SExpr::atom)
                .ok_or_else(|| SmtError::Syntax("match constructor pattern head".to_owned()))?;
            let ctor = arena
                .find_constructor(cname)
                .filter(|&c| arena.constructor_datatype(c) == dt)
                .ok_or_else(|| {
                    SmtError::Unsupported(format!(
                        "match: unknown constructor `{cname}` for `{}`",
                        arena.datatype_name(dt)
                    ))
                })?;
            let field_count = arena.constructor_fields(ctor).len();
            let vars = &parts[1..];
            if vars.len() != field_count {
                return Err(SmtError::Syntax(format!(
                    "match: constructor `{cname}` binds {field_count} field(s), pattern has {}",
                    vars.len()
                )));
            }
            let mut scope = HashMap::new();
            for (i, var) in vars.iter().enumerate() {
                let vname = var
                    .atom()
                    .ok_or_else(|| SmtError::Syntax("match pattern variable".to_owned()))?;
                let sel =
                    arena.dt_select(ctor, u32::try_from(i).expect("field fits u32"), scrutinee)?;
                if vname != "_" && scope.insert(vname, sel).is_some() {
                    return Err(SmtError::Syntax(format!(
                        "match: duplicate pattern variable `{vname}`"
                    )));
                }
            }
            Ok(CasePattern::Constructor { ctor, scope })
        }
    }
}

/// Folds the `match` case results (top `testers.len()` results, in case order)
/// into the right-nested `ite`: each guarded case `Some(t)` becomes
/// `(ite t result <rest>)`, and the final case (`None`) is the innermost else.
fn combine_match(
    arena: &mut TermArena,
    results: &mut Vec<TermId>,
    testers: &[Option<TermId>],
) -> Result<(), SmtError> {
    let n = testers.len();
    let case_results = results.split_off(results.len() - n);
    // Fold from the last case inward. The last case is the unconditional else.
    let mut acc = *case_results
        .last()
        .ok_or_else(|| SmtError::Syntax("match has no cases".to_owned()))?;
    for i in (0..n - 1).rev() {
        let tester = testers[i].ok_or_else(|| {
            SmtError::Syntax(
                "match: only the final case may be an unconditional default".to_owned(),
            )
        })?;
        acc = arena.ite(tester, case_results[i], acc)?;
    }
    results.push(acc);
    Ok(())
}

// --- bounded string front-end (ADR-0029, first slice) ------------------------
//
// A `String` of maximum length `m` bytes is represented as one bit-vector
// packing a length in the low `len_width(m)` bits and `m` content bytes above it
// (byte `i` at bits `[len_width(m) + 8i, +8)`). The packed width is therefore
// `string_total(m) = len_width(m) + 8m`, and `m` is recoverable from that width
// alone (`string_max_len_of`) — strings are **self-describing by width**, so no
// side table is needed. String variables carry a canonical well-formedness
// constraint (length ≤ max; padding bytes zero), so two equal strings share
// exactly one bit pattern and `=` / `distinct` over strings are decided as plain
// bit-vector equality / inequality through the existing BV path.
//
// Variable `str.++` (concat over non-constant operands, ADR-0029 slice 2)
// produces a result in a **wider** packed sort — `max_len(x) + max_len(y)` bytes,
// exactly like the API `BoundedString::concat` — so the join never silently
// overflows the operand bound. The result string is again self-describing, so
// `str.len` / `=` / `str.at` / `str.contains` / prefix / suffix all decide over
// it. When the summed bound exceeds `STRING_BOUND_CAP` the concat is a clean
// `Unsupported` (Unknown to the consumer) — never a wrong verdict.

/// Default maximum bounded string length in bytes for a declared symbol or literal.
/// A directly compared symbol/literal pair may use [`STRING_LITERAL_MAX_LEN`].
const STRING_MAX_LEN: u32 = 12;
/// Maximum adaptive bound for a literal and a directly-compared declared symbol.
/// Keeping this separate from [`STRING_MAX_LEN`] avoids widening every symbolic
/// string and its CNF because one path names a 13-byte protocol token.
const STRING_LITERAL_MAX_LEN: u32 = 13;
/// Hard cap on any packed string's `max_len`. Concatenation can temporarily double
/// the largest adaptively-bounded declaration without truncating either operand.
pub(crate) const STRING_BOUND_CAP: u32 = 26;

/// Bits holding a length in `0..=m` for a string of maximum length `m`.
pub(crate) const fn len_width(m: u32) -> u32 {
    // bits to hold the value `m` (and every smaller length); matches
    // `BoundedString::len_width` so the two encodings agree on widths.
    32 - m.leading_zeros()
}

/// Total packed width of a string of maximum length `m`: length bits plus `m`
/// content bytes.
pub(crate) const fn string_total(m: u32) -> u32 {
    len_width(m) + m * 8
}

/// Total packed width for the default `STRING_MAX_LEN` layout.
const STRING_TOTAL: u32 = string_total(STRING_MAX_LEN);

/// Recovers a packed string's maximum length `m` from its bit-vector width `w`
/// (the inverse of [`string_total`]). Returns `None` if `w` is not the width of
/// any `m ∈ 1..=STRING_BOUND_CAP` — i.e. the term is a genuine `BitVec`, not a
/// packed string — so a real `(_ BitVec w)` is never mistaken for a string.
fn string_max_len_of(w: u32) -> Option<u32> {
    (1..=STRING_BOUND_CAP).find(|&m| string_total(m) == w)
}

/// The maximum length of the packed string term `v`, from its sort width.
///
/// # Errors
///
/// [`SmtError::Unsupported`] if `v` is not a packed-string-shaped bit-vector
/// (so a non-string operand to a `str.*` op declines rather than misbehaves).
fn string_max_len(arena: &TermArena, v: TermId) -> Result<u32, SmtError> {
    match arena.sort_of(v) {
        Sort::BitVec(w) => string_max_len_of(w).ok_or_else(|| {
            SmtError::Unsupported(format!(
                "string operator applied to a non-string `BitVec({w})` (ADR-0029)"
            ))
        }),
        s => Err(SmtError::Unsupported(format!(
            "string operator applied to a non-string operand of sort {s:?} (ADR-0029)"
        ))),
    }
}

/// Parse-time builder for the **unbounded length abstraction** (P2.7 A.2).
///
/// Threaded through the parse as `&LenAbs` (interior-mutable, mirroring
/// [`SeqInfo`]'s `nth_apps`): the string/sequence operator hooks record, per
/// hooked term, its abstraction twin — a shared *unbounded* integer length
/// expression for string-valued terms, `fresh_bool ∧ implied_length_fact` for
/// string atoms, and a free integer for content bridges (`str.to_int`, …). The
/// map is exported on [`Script::len_abstraction_map`]; rewriting an assertion
/// through it (root-first) yields a **relaxation of the real (unbounded) string
/// semantics**, so an `unsat` of the rewritten active stack (plus the facts)
/// confirms a bounded `unsat` bound-independent.
///
/// Soundness of each entry (the relaxation argument — every real model of the
/// unbounded theory extends to a model of the abstraction):
///
/// - a string atom `A` maps to `B ∧ fact` with `B` fresh and `fact` implied by
///   `A` in the unbounded theory: extend the model by `B := value(A)` (if `A`
///   holds, `fact` holds, so `B ∧ fact = A = true`; if not, `B ∧ fact = A =
///   false`) — faithful under any Boolean structure, negation included;
/// - a string-valued term's length expression is its true length under the
///   homomorphism (`len(x ++ y) = len(x) + len(y)`, `len(lit) = |lit|`,
///   `len(seq.unit e) = 1`) or an otherwise-fresh `len ≥ 0` variable;
/// - a content bridge (`str.to_int`/`to_code`/`indexof`/`seq.nth`) maps to a
///   wholly-free integer (assign it the term's real value);
/// - the exported facts (`len ≥ 0`, literal lengths) are universally true of
///   real lengths.
#[derive(Default)]
struct LenAbs {
    /// Whether this script is small enough to admit `PyEx`'s correlated
    /// split/replace/rejoin terms into the packed encoding. Larger generated
    /// pipelines retain the source-level fallback instead of building a huge DAG.
    admit_split_replace_rejoin: bool,
    /// String/sequence-valued term → its abstraction-side `Int` length
    /// expression.
    len_of: std::cell::RefCell<HashMap<TermId, TermId>>,
    /// Original term (string atom or `Int` bridge) → replacement, in
    /// first-recorded order (deterministic export).
    repl: std::cell::RefCell<Vec<(TermId, TermId)>>,
    /// String-valued term → its `str.to_code` code-point twin `Int`
    /// ([`LenAbs::note_code_bridge`]); consulted by the single-char code↔
    /// equality link ([`LenAbs::note_code_eq_link`]).
    code_of: std::cell::RefCell<HashMap<TermId, TermId>>,
    /// Globally-true side facts (`len(v) ≥ 0`, …).
    facts: std::cell::RefCell<Vec<TermId>>,
    /// **Encoding-bound** facts (`len(v) ≤ max_len`) — true of the *bounded
    /// encoding only*, never of the real theory. Used exclusively by the
    /// solver's bound-bite detector (a length system unsatisfiable *with* these
    /// but not *without* proves the encoding bound bit, so a bounded `unsat`
    /// must downgrade to `unknown`); never part of the sound abstraction.
    bounds: std::cell::RefCell<Vec<TermId>>,
    /// Per-term **bounded-encoding guards** needed to make a lossy lowering
    /// injective. At present these are the signed-range guards for symbolic
    /// `(Seq Int)` elements before `int2bv(SEQ_INT_WIDTH, e)`. The parser
    /// conjoins the newly-recorded guards with the assertion (or assumption)
    /// whose term created them, preserving incremental scope.
    encoding_guards: std::cell::RefCell<Vec<TermId>>,
    /// Fresh-symbol counter (deterministic `!lenabs.N` names).
    fresh: std::cell::Cell<u32>,
    /// A **coarsely-abstracted** string atom is present (`str.<`/`str.<=` —
    /// no length implication exists — or `str.in_re`, whose match-length
    /// interval cannot see union gaps): for these, the length abstraction may
    /// miss a bound bite (a real model may exist only past the bound while
    /// bound-fitting lengths satisfy every recorded fact), so an *unconfirmed*
    /// bounded `unsat` must downgrade rather than pass through.
    coarse: std::cell::Cell<bool>,
    /// Any genuine string/sequence *operator* was hooked. (Declared
    /// `String`/`(Seq E)` symbols set [`Script::uses_bounded_strings`]
    /// directly; the `=`-hook deliberately does **not** set this, so a
    /// string-*shaped* user bit-vector width never activates the gate.)
    used: std::cell::Cell<bool>,
}

impl LenAbs {
    fn mark_used(&self) {
        self.used.set(true);
    }

    /// Checkpoint the assertion-local encoding guards. A term parser may call
    /// [`LenAbs::note_encoding_guard`] several times; the command parser uses
    /// this index to attach exactly those guards to the command being parsed.
    fn encoding_guard_checkpoint(&self) -> usize {
        self.encoding_guards.borrow().len()
    }

    /// Encoding guards recorded since `checkpoint`, in deterministic term
    /// order. The global log is retained because later commands need their own
    /// independent checkpoints; callers only clone their command-local suffix.
    fn encoding_guards_since(&self, checkpoint: usize) -> Vec<TermId> {
        let guards = self.encoding_guards.borrow();
        let mut unique = Vec::new();
        for &guard in &guards[checkpoint..] {
            if !unique.contains(&guard) {
                unique.push(guard);
            }
        }
        unique
    }

    /// Record a restriction required only by the bounded representation.
    ///
    /// The guard is conjoined with the bounded query by [`parse_command`], but
    /// is rewritten to `true` in the unbounded abstraction and separately fed
    /// to the bound-bite detector. Marking the abstraction coarse prevents the
    /// weaker bridge-only fallback from certifying an UNSAT that the unbounded
    /// abstraction could not prove. Thus:
    ///
    /// - a bounded SAT model satisfies the guard, so the lossy lowering is
    ///   injective and the model lifts to the real theory;
    /// - a bounded UNSAT that needs the guard is downgraded to `unknown` unless
    ///   the guard-free abstraction independently refutes the source formula.
    fn note_encoding_guard(&self, arena: &mut TermArena, guard: TermId) {
        self.mark_used();
        self.encoding_guards.borrow_mut().push(guard);
        let mut bounds = self.bounds.borrow_mut();
        if !bounds.contains(&guard) {
            bounds.push(guard);
        }
        drop(bounds);
        let truth = arena.bool_const(true);
        self.note_repl(guard, truth);
        self.coarse.set(true);
    }

    /// Declares a fresh abstraction symbol of `sort`; `nonneg` adds the
    /// universally-true `0 ≤ v` length fact.
    fn fresh_var(
        &self,
        arena: &mut TermArena,
        sort: Sort,
        nonneg: bool,
    ) -> Result<TermId, SmtError> {
        let n = self.fresh.get();
        self.fresh.set(n + 1);
        let sym = arena.declare_internal(&format!("!lenabs.{n}"), sort)?;
        let v = arena.var(sym);
        if nonneg {
            let zero = arena.int_const(0);
            let fact = arena.int_le(zero, v)?;
            self.facts.borrow_mut().push(fact);
        }
        Ok(v)
    }

    /// The abstraction-side length expression of a **packed string** term:
    /// a recorded expression (concat sums, literals), the decoded exact length
    /// of a constant, or a fresh `≥ 0` length variable (with its encoding
    /// bound `≤ max_len` recorded on the bite-detector side).
    fn len_expr_string(&self, arena: &mut TermArena, t: TermId) -> Result<TermId, SmtError> {
        if let Some(&e) = self.len_of.borrow().get(&t) {
            return Ok(e);
        }
        let e = if let Some(len) = packed_string_len(arena, t) {
            arena.int_const(i128::from(len))
        } else {
            let v = self.fresh_var(arena, Sort::Int, true)?;
            if let Ok(m) = string_max_len(arena, t) {
                let cap = arena.int_const(i128::from(m));
                let bound = arena.int_le(v, cap)?;
                self.bounds.borrow_mut().push(bound);
            }
            v
        };
        self.len_of.borrow_mut().insert(t, e);
        Ok(e)
    }

    /// The abstraction-side length expression of a **packed sequence** term.
    /// (No constant decoding in this slice — an unrecorded term gets a fresh
    /// `≥ 0` variable, which is always sound.)
    fn len_expr_seq(&self, arena: &mut TermArena, t: TermId) -> Result<TermId, SmtError> {
        if let Some(&e) = self.len_of.borrow().get(&t) {
            return Ok(e);
        }
        let e = self.fresh_var(arena, Sort::Int, true)?;
        self.len_of.borrow_mut().insert(t, e);
        Ok(e)
    }

    /// Records a string/sequence-valued result's length expression (skipped if
    /// the hash-consed term was already recorded).
    fn note_len(&self, t: TermId, expr: TermId) {
        self.len_of.borrow_mut().entry(t).or_insert(expr);
    }

    /// Records `original → replacement` for the exported abstraction map.
    fn note_repl(&self, original: TermId, replacement: TermId) {
        let mut repl = self.repl.borrow_mut();
        if !repl.iter().any(|&(o, _)| o == original) {
            repl.push((original, replacement));
        }
    }

    /// Hooks a string atom with **no** derivable length fact: `atom →
    /// fresh_bool`. Every string atom must enter the map — an atom left
    /// verbatim would keep its *bounded* encoding inside the "unbounded"
    /// abstraction, breaking the relaxation (a real model with over-bound
    /// strings could fail the kept atom's packed lowering, letting the confirm
    /// step wrongly bless a bound-induced `unsat`).
    fn note_atom_free(&self, arena: &mut TermArena, atom: TermId) -> Result<(), SmtError> {
        // A constant-folded atom is exact (no bound sensitivity, nothing to
        // relax) — keep it verbatim and do not mark the script coarse.
        if matches!(arena.node(atom), TermNode::BoolConst(_)) {
            return Ok(());
        }
        self.coarse.set(true);
        let b = self.fresh_var(arena, Sort::Bool, false)?;
        self.note_repl(atom, b);
        Ok(())
    }

    /// Hooks a string atom that is **exactly equivalent** to `predicate` in the
    /// unbounded theory (not merely *implied* by it): `atom → predicate`, with
    /// **no** fresh Boolean. Used for equality against the empty string, where
    /// `s = "" ⟺ len(s) = 0` — the empty string is the *unique* length-zero
    /// string, so the length predicate captures the atom's full content. This
    /// lets step 1 refute e.g. `len(s) = 0 ∧ s ≠ ""` that the weaker
    /// `fresh_bool ∧ (len = 0)` relaxation leaves satisfiable (pick the Boolean
    /// false). Sound because the replacement has the *same truth value* as the
    /// atom in every real model, so it is faithful under any Boolean structure.
    fn note_atom_exact(&self, arena: &TermArena, atom: TermId, predicate: TermId) {
        if matches!(arena.node(atom), TermNode::BoolConst(_)) {
            return;
        }
        self.note_repl(atom, predicate);
    }

    /// Hooks a string atom: `atom → fresh_bool ∧ fact`. Returns the fresh
    /// Boolean `b` (`None` for a constant-folded atom kept verbatim), so a
    /// caller can add further facts that reference the abstraction-side truth
    /// value of the atom (e.g. the [`LenAbs::note_code_eq_link`] single-char
    /// code↔equality bridge).
    fn note_atom_fact(
        &self,
        arena: &mut TermArena,
        atom: TermId,
        fact: TermId,
    ) -> Result<Option<TermId>, SmtError> {
        // A constant-folded atom is exact — keep it verbatim (replacing the
        // interned `true`/`false` would rewrite every other use of the
        // constant too).
        if matches!(arena.node(atom), TermNode::BoolConst(_)) {
            return Ok(None);
        }
        let b = self.fresh_var(arena, Sort::Bool, false)?;
        let repl = arena.and(b, fact)?;
        self.note_repl(atom, repl);
        Ok(Some(b))
    }

    /// Hooks a content bridge (`str.to_int`, `str.indexof`, `seq.nth`, …): the
    /// `Int`-valued term maps to a wholly-free integer.
    fn note_bridge_free(&self, arena: &mut TermArena, t: TermId) -> Result<(), SmtError> {
        // A bridge that folded to an integer literal is already exact. Replacing
        // that shared literal by a fresh integer would also rewrite unrelated uses
        // of the constant and can erase a source-independent contradiction such as
        // `indexof(s, "", 0) = -1` (the left side is exactly zero).
        if matches!(arena.node(t), TermNode::IntConst(_)) {
            return Ok(());
        }
        self.mark_used();
        let v = self.fresh_var(arena, Sort::Int, false)?;
        self.note_repl(t, v);
        Ok(())
    }

    /// Hooks the **code-point bridge** `str.to_code s` (result term `r`): a
    /// fresh `Int` `c` standing for the code point, tied to the abstraction-side
    /// length `len(s)` by the *universally-true* (byte-model) fact
    ///
    /// ```text
    /// (len(s) = 1 ∧ 0 ≤ c ≤ 0x2FFFF) ∨ (len(s) ≠ 1 ∧ c = -1)
    /// ```
    ///
    /// This is `str.to_code`'s SMT-LIB definition (`ite(|s| = 1, codepoint(s[0]),
    /// -1)`) *minus* the specific code point, which stays free — so it is a sound
    /// **relaxation**: assign `c := value(str.to_code s)` and `len(s) := |s|` and
    /// the disjunction holds in every real model. The upper cap is the SMT-LIB
    /// maximum code point `0x2FFFF`, **not** the byte model's `255`: over-
    /// approximating the alphabet keeps the abstraction a relaxation of the *real*
    /// (Unicode) theory, so it can never refute a formula satisfiable only by a
    /// code point above the byte range (which would DISAGREE with Z3/cvc5).
    /// Unlike [`note_bridge_free`] (a wholly-free
    /// integer), this pins the code point's domain and its coupling to the
    /// length, which lets the unbounded abstraction refute the code-range /
    /// code-arithmetic conflicts (`str-code-unsat*`) without the bounded
    /// integer bit-blast. Records `s → c` in [`LenAbs::code_of`] so string
    /// (dis)equalities over `s` can add the single-char code↔equality link.
    fn note_code_bridge(
        &self,
        arena: &mut TermArena,
        s: TermId,
        r: TermId,
    ) -> Result<(), SmtError> {
        self.mark_used();
        // Idempotent per operand: `str.to_code s` may appear many times (all
        // hooked to the same code twin `c`). Minting a fresh twin per occurrence
        // would leave the arithmetic uses (mapped through `r → c₀`) and the
        // equality-link uses (`code_of[s] = cₙ`) referencing *different*
        // variables, breaking the coupling. Reuse the first twin.
        if let Some(&c) = self.code_of.borrow().get(&s) {
            self.note_repl(r, c);
            return Ok(());
        }
        let ls = self.len_expr_string(arena, s)?;
        // `c` may be `-1`, so it is *not* declared non-negative.
        let c = self.fresh_var(arena, Sort::Int, false)?;
        let one = arena.int_const(1);
        let zero = arena.int_const(0);
        // SMT-LIB maximum code point (`0x2FFFF`), not the byte model's 255 — see
        // the doc comment: over-approximating the alphabet keeps the abstraction
        // a sound relaxation of the real Unicode theory.
        let cap = arena.int_const(0x2_FFFF);
        let neg_one = arena.int_const(-1);
        let is_one = arena.eq(ls, one)?;
        let ge0 = arena.int_le(zero, c)?;
        let le255 = arena.int_le(c, cap)?;
        let in_range = arena.and(ge0, le255)?;
        let single = arena.and(is_one, in_range)?;
        let not_one = arena.not(is_one)?;
        let is_neg = arena.eq(c, neg_one)?;
        let other = arena.and(not_one, is_neg)?;
        let fact = arena.or(single, other)?;
        self.facts.borrow_mut().push(fact);
        self.note_repl(r, c);
        self.code_of.borrow_mut().insert(s, c);
        Ok(())
    }

    /// The abstraction-side **code-point expression** of a string operand `t`,
    /// if one exists: the recorded code twin `c` of a `str.to_code`-hooked
    /// variable, or the literal code point of a single-character string
    /// constant. `None` for any other operand.
    fn code_expr(&self, arena: &mut TermArena, t: TermId) -> Option<TermId> {
        if let Some(&c) = self.code_of.borrow().get(&t) {
            return Some(c);
        }
        single_char_code(arena, t).map(|code| arena.int_const(i128::from(code)))
    }

    /// Adds the single-character **code↔equality link** for a string equality
    /// atom `p = q` whose abstraction-side truth value is `b`: when both
    /// operands carry a code-point expression (`c_p`, `c_q`) the *universally-
    /// true* (byte-model) fact
    ///
    /// ```text
    /// (len(p) = 1 ∧ len(q) = 1 ∧ c_p = c_q) → b
    /// ```
    ///
    /// is recorded. Sound as a relaxation: in a real model a single-character
    /// string is exactly its code point, so equal single-character code points
    /// force the strings equal (`b = value(p = q) = true`). This lets the
    /// abstraction see that distinct single-character strings need distinct
    /// codes (`str-code-unsat`, `str-code-unsat-3`) — the piece a wholly-free
    /// bridge and a fresh-Boolean equality would drop. No-op unless both
    /// operands have a code expression.
    fn note_code_eq_link(
        &self,
        arena: &mut TermArena,
        b: TermId,
        p: TermId,
        lp: TermId,
        q: TermId,
        lq: TermId,
    ) -> Result<(), SmtError> {
        let (Some(cp), Some(cq)) = (self.code_expr(arena, p), self.code_expr(arena, q)) else {
            return Ok(());
        };
        let one = arena.int_const(1);
        let p_single = arena.eq(lp, one)?;
        let q_single = arena.eq(lq, one)?;
        let codes_eq = arena.eq(cp, cq)?;
        let ante = arena.and(p_single, q_single)?;
        let ante = arena.and(ante, codes_eq)?;
        let link = arena.implies(ante, b)?;
        self.facts.borrow_mut().push(link);
        Ok(())
    }

    /// Exports `(map, facts, bounds, coarse, used)` for the [`Script`] fields.
    fn export(self) -> LenAbsExport {
        (
            self.repl.into_inner(),
            self.facts.into_inner(),
            self.bounds.into_inner(),
            self.coarse.get(),
            self.used.get(),
        )
    }
}

/// The [`LenAbs::export`] payload: `(map, facts, bounds, coarse, used)` for
/// the corresponding [`Script`] fields.
type LenAbsExport = (Vec<(TermId, TermId)>, Vec<TermId>, Vec<TermId>, bool, bool);

/// Whether `t` is a bit-vector *constant* (narrow or wide) — a ground string
/// operand, whose atoms are exact at every bound (literals are within the
/// bound by construction, so no encoding artifact can flip them).
fn packed_const(arena: &TermArena, t: TermId) -> bool {
    matches!(
        arena.node(t),
        TermNode::BvConst { .. } | TermNode::WideBvConst(_)
    )
}

/// Whether `t`'s sort is a packed-string-shaped bit-vector width.
fn string_shaped(arena: &TermArena, t: TermId) -> bool {
    matches!(arena.sort_of(t), Sort::BitVec(w) if string_max_len_of(w).is_some())
}

/// The exact length of a **constant** packed string, decoded from its low
/// length-field bits; `None` for non-constants, wide constants, or a value
/// whose decoded length exceeds its own bound (not a valid packed string).
fn packed_string_len(arena: &TermArena, t: TermId) -> Option<u32> {
    let TermNode::BvConst { width, value } = arena.node(t) else {
        return None;
    };
    let m = string_max_len_of(*width)?;
    let len = u32::try_from(value & ((1u128 << len_width(m)) - 1)).ok()?;
    (len <= m).then_some(len)
}

/// The code point (single content byte, `0..=255`) of a **single-character**
/// packed string constant; `None` unless `t` is a length-1 constant string.
/// This is exactly `str.to_code t` for a literal in the byte model, used to
/// give a single-char string literal a code expression for the code↔equality
/// link ([`LenAbs::note_code_eq_link`]).
fn single_char_code(arena: &TermArena, t: TermId) -> Option<u8> {
    if packed_string_len(arena, t) != Some(1) {
        return None;
    }
    let TermNode::BvConst { width, value } = arena.node(t) else {
        return None;
    };
    let m = string_max_len_of(*width)?;
    let byte = (value >> len_width(m)) & 0xFF;
    u8::try_from(byte).ok()
}

/// Packs a string literal's bytes into the canonical bit-vector representation
/// (length low, content above, padding zero). Errors if it exceeds the bound.
/// The SMT-LIB maximum string code point (`\u{2FFFF}`). A larger escape is
/// ill-formed; the literal is declined rather than silently truncated.
const SMTLIB_MAX_CODE_POINT: u32 = 0x2_FFFF;

/// Decodes the inner text of an SMT-LIB string literal — the characters between
/// the surrounding quotes, with the doubled-quote escape `""` **already**
/// collapsed to a single `"` — into its sequence of Unicode code points, expanding
/// the two SMT-LIB escape forms `\u{h…}` (1–5 hex digits, braces) and `\uhhhh`
/// (exactly 4 hex digits). Every other backslash is a **literal** `\` — SMT-LIB
/// gives `\` no special meaning outside those two escapes, matching Z3/cvc5.
///
/// Both the byte-model bounded encoder ([`string_literal_bytes`]) and the
/// code-point word/skeleton route ([`word_literal`]) decode through this one
/// function, so a literal like `"\u{62}"` denotes the single character `b`
/// **identically** on every route (the P0 hole was that neither string-literal
/// route expanded escapes, so `"\u{62}"` was six raw bytes `\ u { 6 2 }` — a wrong
/// verdict against the regex side, which does expand them).
///
/// Returns `None` if an escape names a code point above [`SMTLIB_MAX_CODE_POINT`],
/// so the caller declines the literal instead of emitting a truncated character.
pub(crate) fn decode_string_code_points(inner: &str) -> Option<Vec<u32>> {
    let chars: Vec<char> = inner.chars().collect();
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        // A `\u{h…}` / `\uhhhh` escape, or a literal backslash if neither matches.
        if chars[i] == '\\' && chars.get(i + 1) == Some(&'u') {
            let after = i + 2;
            if chars.get(after) == Some(&'{') {
                if let Some(close) = chars[after + 1..].iter().position(|&c| c == '}') {
                    let hex: String = chars[after + 1..after + 1 + close].iter().collect();
                    if (1..=5).contains(&hex.len())
                        && let Ok(v) = u32::from_str_radix(&hex, 16)
                    {
                        if v > SMTLIB_MAX_CODE_POINT {
                            return None;
                        }
                        out.push(v);
                        i = after + 1 + close + 1;
                        continue;
                    }
                }
            } else if after + 4 <= chars.len() {
                let hex: String = chars[after..after + 4].iter().collect();
                if let Ok(v) = u32::from_str_radix(&hex, 16) {
                    if v > SMTLIB_MAX_CODE_POINT {
                        return None;
                    }
                    out.push(v);
                    i = after + 4;
                    continue;
                }
            }
            // Not a well-formed `\u` escape: a literal backslash.
            out.push(u32::from('\\'));
            i += 1;
        } else {
            out.push(chars[i] as u32);
            i += 1;
        }
    }
    Some(out)
}

/// The byte-model bytes of an SMT-LIB string literal's inner text (see
/// [`decode_string_code_points`]): one byte per decoded code point. A code point
/// above `0xFF` has no byte-model representation, so the literal is declined
/// ([`SmtError::Unsupported`]) — the word / membership routes then decide it,
/// never a wrong verdict from a truncated character.
fn string_literal_bytes(inner: &str) -> Result<Vec<u8>, SmtError> {
    let code_points = decode_string_code_points(inner).ok_or_else(|| {
        SmtError::Unsupported("string literal escape names a code point above U+2FFFF".to_owned())
    })?;
    code_points
        .iter()
        .map(|&cp| {
            u8::try_from(cp).map_err(|_| {
                SmtError::Unsupported(format!(
                    "string literal code point U+{cp:04X} exceeds the bounded byte model (ADR-0029)"
                ))
            })
        })
        .collect()
}

fn pack_string_literal(arena: &mut TermArena, bytes: &[u8]) -> Result<TermId, SmtError> {
    if bytes.len() > STRING_LITERAL_MAX_LEN as usize {
        return Err(SmtError::Unsupported(format!(
            "string literal longer than the bounded length {STRING_LITERAL_MAX_LEN} (ADR-0029)"
        )));
    }
    let max_len =
        STRING_MAX_LEN.max(u32::try_from(bytes.len()).expect("literal length is bounded"));
    let mut content: u128 = 0;
    for (i, &b) in bytes.iter().enumerate() {
        content |= u128::from(b) << (8 * i);
    }
    let packed = u128::from(u32::try_from(bytes.len()).expect("literal length is bounded"))
        | (content << len_width(max_len));
    arena
        .bv_const(string_total(max_len), packed)
        .map_err(SmtError::Ir)
}

/// The length field (a `BitVec(len_width(m))`) of a packed string of max length
/// `m`.
fn string_len_field(arena: &mut TermArena, v: TermId, m: u32) -> Result<TermId, SmtError> {
    arena.extract(len_width(m) - 1, 0, v).map_err(SmtError::Ir)
}

/// Content byte `i` (a `BitVec(8)`) of a packed string of max length `m`.
fn string_byte_m(arena: &mut TermArena, v: TermId, i: u32, m: u32) -> Result<TermId, SmtError> {
    let lo = len_width(m) + i * 8;
    arena.extract(lo + 7, lo, v).map_err(SmtError::Ir)
}

/// Re-packs a packed string `v` (max length `m`) into the layout of a string of
/// max length `to` (`to ≥ m`): the length is zero-extended to the wider
/// `len_width(to)`, and each content byte is moved to its position in the wider
/// layout. A plain `zero_ext` would **not** work, because the content bytes start
/// at bit `len_width(m)`, which differs from `len_width(to)` when the length
/// widths differ. Under well-formedness the result denotes the same string, so
/// two strings widened to a common `to` compare byte-for-byte.
fn string_widen(arena: &mut TermArena, v: TermId, m: u32, to: u32) -> Result<TermId, SmtError> {
    debug_assert!(to >= m, "string_widen only widens");
    if to == m {
        return Ok(v);
    }
    let len = string_len_field(arena, v, m)?;
    let rlen = arena.zero_ext(len_width(to) - len_width(m), len)?;
    // Assemble content bytes high-to-low for the wider layout (byte `to-1` … 0).
    let zero8 = arena.bv_const(8, 0)?;
    let mut content: Option<TermId> = None;
    for i in (0..to).rev() {
        let byte = if i < m {
            string_byte_m(arena, v, i, m)?
        } else {
            zero8
        };
        content = Some(match content {
            None => byte,
            Some(acc) => arena.concat(acc, byte)?,
        });
    }
    let content = content.expect("to ≥ 1");
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// Widens `x` and `y` to a shared max length `max(m_x, m_y)`, returning the
/// re-packed terms and that common length. The comparison/relation builders run
/// over the shared layout so they decide across mixed-width operands (e.g. a
/// variable concat result against a literal).
fn string_align(
    arena: &mut TermArena,
    x: TermId,
    y: TermId,
) -> Result<(TermId, TermId, u32), SmtError> {
    let mx = string_max_len(arena, x)?;
    let my = string_max_len(arena, y)?;
    let m = mx.max(my);
    let xw = string_widen(arena, x, mx, m)?;
    let yw = string_widen(arena, y, my, m)?;
    Ok((xw, yw, m))
}

/// `str.prefixof x y` — `x` is a prefix of `y`: `len(x) ≤ len(y)` and the first
/// `len(x)` bytes match. A pure bit-vector/Boolean formula over the packed
/// strings, so it decides both directions (no Int / theory-combination gap).
fn string_prefixof(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    // Exact identities first. Besides avoiding a quadratic byte comparison, these
    // keep generated rewrite lemmas independent of the artificial packed bound.
    if x == y || string_const_bytes(arena, x).is_some_and(|bytes| bytes.is_empty()) {
        return Ok(arena.bool_const(true));
    }
    if string_const_bytes(arena, y).is_some_and(|bytes| bytes.is_empty()) {
        return string_aware_eq(arena, x, y)?
            .map_or_else(|| arena.eq(x, y).map_err(SmtError::Ir), Ok);
    }
    let (x, y, m) = string_align(arena, x, y)?;
    let xlen = string_len_field(arena, x, m)?;
    let ylen = string_len_field(arena, y, m)?;
    let mut acc = arena.bv_ule(xlen, ylen)?;
    for i in 0..m {
        let xb = string_byte_m(arena, x, i, m)?;
        let yb = string_byte_m(arena, y, i, m)?;
        let beq = arena.eq(xb, yb)?;
        let idx = arena.bv_const(len_width(m), u128::from(i))?;
        let active = arena.bv_ult(idx, xlen)?; // i < len(x)
        let nactive = arena.not(active)?;
        let ok = arena.or(nactive, beq)?; // i ≥ len(x) ∨ bytes equal
        acc = arena.and(acc, ok)?;
    }
    Ok(acc)
}

/// `str.contains x y` — `y` occurs in `x` as a contiguous substring. A pure
/// bit-vector/Boolean formula: the disjunction over each start offset `d` of
/// "`y` fits at `d` (`d + len(y) ≤ len(x)`) and matches there". Bounded
/// (`O(MAX_LEN²)`), decides both directions.
fn string_contains(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    // Every word contains itself and the empty word. Conversely, the empty word
    // contains only the empty word. These are exact over unbounded strings.
    if x == y || string_const_bytes(arena, y).is_some_and(|bytes| bytes.is_empty()) {
        return Ok(arena.bool_const(true));
    }
    if string_const_bytes(arena, x).is_some_and(|bytes| bytes.is_empty()) {
        return string_aware_eq(arena, x, y)?
            .map_or_else(|| arena.eq(x, y).map_err(SmtError::Ir), Ok);
    }
    let (x, y, m) = string_align(arena, x, y)?;
    let xlen = string_len_field(arena, x, m)?;
    let ylen = string_len_field(arena, y, m)?;
    // Widen lengths by one bit so `d + len(y)` cannot overflow the length width.
    let xlen_w = arena.zero_ext(1, xlen)?;
    let ylen_w = arena.zero_ext(1, ylen)?;
    let wlen = len_width(m) + 1;
    let mut any = arena.bool_const(false);
    for d in 0..m {
        let dconst = arena.bv_const(wlen, u128::from(d))?;
        let sum = arena.bv_add(dconst, ylen_w)?;
        let fits = arena.bv_ule(sum, xlen_w)?; // d + len(y) ≤ len(x)
        let mut matched = fits;
        for j in 0..m {
            if d + j >= m {
                break; // x has no byte at d+j; under `fits` this forces j ≥ len(y)
            }
            let xb = string_byte_m(arena, x, d + j, m)?;
            let yb = string_byte_m(arena, y, j, m)?;
            let beq = arena.eq(xb, yb)?;
            let jconst = arena.bv_const(len_width(m), u128::from(j))?;
            let jactive = arena.bv_ult(jconst, ylen)?; // j < len(y)
            let njactive = arena.not(jactive)?;
            let ok = arena.or(njactive, beq)?; // j ≥ len(y) ∨ bytes equal
            matched = arena.and(matched, ok)?;
        }
        any = arena.or(any, matched)?;
    }
    Ok(any)
}

/// `str.suffixof x y` — `x` is a suffix of `y`: aligned at offset
/// `o = len(y) − len(x)`, the bytes match. Disjunction over `o` (pure BV/Bool,
/// decides both directions).
fn string_suffixof(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    if x == y || string_const_bytes(arena, x).is_some_and(|bytes| bytes.is_empty()) {
        return Ok(arena.bool_const(true));
    }
    if string_const_bytes(arena, y).is_some_and(|bytes| bytes.is_empty()) {
        return string_aware_eq(arena, x, y)?
            .map_or_else(|| arena.eq(x, y).map_err(SmtError::Ir), Ok);
    }
    let (x, y, m) = string_align(arena, x, y)?;
    let xlen = string_len_field(arena, x, m)?;
    let ylen = string_len_field(arena, y, m)?;
    let xlen_w = arena.zero_ext(1, xlen)?;
    let ylen_w = arena.zero_ext(1, ylen)?;
    let wlen = len_width(m) + 1;
    let mut any = arena.bool_const(false);
    for o in 0..=m {
        let oconst = arena.bv_const(wlen, u128::from(o))?;
        let sum = arena.bv_add(oconst, xlen_w)?;
        let aligned = arena.eq(sum, ylen_w)?; // len(y) == o + len(x)
        let mut matched = aligned;
        for i in 0..m {
            if o + i >= m {
                break; // y has no byte at o+i; under `aligned` this forces i ≥ len(x)
            }
            let xb = string_byte_m(arena, x, i, m)?;
            let yb = string_byte_m(arena, y, o + i, m)?;
            let beq = arena.eq(xb, yb)?;
            let iconst = arena.bv_const(len_width(m), u128::from(i))?;
            let iactive = arena.bv_ult(iconst, xlen)?; // i < len(x)
            let niactive = arena.not(iactive)?;
            let ok = arena.or(niactive, beq)?;
            matched = arena.and(matched, ok)?;
        }
        any = arena.or(any, matched)?;
    }
    Ok(any)
}

/// `str.at s k` for a **constant** index `k`: the length-1 string holding byte
/// `s[k]` when `0 ≤ k < len(s)` (and within the bound), else the empty string.
/// The result is a max-length-1 packed string (the smallest sort), canonical, so
/// it composes with equality. Pure BV/Bool — decides both directions.
fn string_at_const(arena: &mut TermArena, s: TermId, k: i128) -> Result<TermId, SmtError> {
    if let Some(bytes) = string_const_bytes(arena, s) {
        let out = usize::try_from(k)
            .ok()
            .and_then(|index| bytes.get(index).copied())
            .map_or_else(Vec::new, |byte| vec![byte]);
        return pack_string_literal(arena, &out);
    }
    let m = string_max_len(arena, s)?;
    // Declared strings use STRING_MAX_LEN. A non-constant packed string with an
    // exact maximum length of one is therefore a result of a length-≤1 operator
    // (`str.at`, `str.from_code`, ...), so index >=1 is genuinely out of range,
    // not merely beyond an artificial declaration bound.
    if m == 1 && k >= 1 {
        return pack_string_literal(arena, &[]);
    }
    // A negative index is out of range for EVERY string (SMT-LIB), regardless of
    // length — so folding to the empty string is sound and bound-independent.
    if k < 0 {
        return arena.bv_const(string_total(1), 0).map_err(SmtError::Ir);
    }
    // `k ≥ m` is beyond the *packed* length, but a SYMBOLIC `s` could really be
    // longer than `m`, so folding to a hard `""` is UNSOUND — it manufactured
    // wrong-unsats (e.g. `(= (str.at s 100) "x")` is sat: `s` of length 101 with
    // 'x' at 100, but the bounded fold makes it `(= "" "x")` = unsat; task #76).
    // Route through the Int-index mux instead, so the result carries the length
    // channel: the bounded path reports a sound `unknown` (mirroring `str.substr`
    // past the cap), and the bounded-completeness route (#75) still upgrades the
    // genuinely length-capped cases to `unsat`.
    if k >= i128::from(m) {
        let ki = arena.int_const(k);
        return string_at_int(arena, s, ki);
    }
    let kk = u32::try_from(k).expect("0 ≤ k < m");
    let slen = string_len_field(arena, s, m)?;
    let kconst = arena.bv_const(len_width(m), u128::from(kk))?;
    let active = arena.bv_ult(kconst, slen)?; // k < len(s)
    let byte_k = string_byte_m(arena, s, kk, m)?;
    let zero8 = arena.bv_const(8, 0)?;
    // Result is a max-length-1 string: length width is `len_width(1) = 1`.
    let one_len = arena.bv_const(len_width(1), 1)?;
    let zero_len = arena.bv_const(len_width(1), 0)?;
    let rlen = arena.ite(active, one_len, zero_len)?;
    let rbyte = arena.ite(active, byte_k, zero8)?;
    // Pack: packed = byte0(rbyte) ++ length.
    arena.concat(rbyte, rlen).map_err(SmtError::Ir)
}

/// `len(s)` as an `Int` (the length field lifted out of the packed BV via
/// `bv2nat`). Used by the Int-indexed string ops (`str.at`/`str.substr` with a
/// non-constant index), which compare an `Int` index against the length.
fn string_len_int(arena: &mut TermArena, s: TermId, m: u32) -> Result<TermId, SmtError> {
    let len = string_len_field(arena, s, m)?;
    arena.bv2nat(len).map_err(SmtError::Ir)
}

/// Selects content byte at an **`Int`** index `i` of a packed string `s` (max
/// length `m`): returns `(byte, in_range)` where `in_range` holds exactly when
/// `0 ≤ i < len(s)` and `byte` is `s[i]` there (else `0`). The selection is an
/// `Int`-equality mux over the `m` representable positions, so a negative or
/// out-of-bound `i` (including values ≥ `m`) matches no position and yields
/// `(0, false)` — matching the SMT-LIB total-function semantics exactly.
fn string_byte_at_int(
    arena: &mut TermArena,
    s: TermId,
    i: TermId,
    m: u32,
) -> Result<(TermId, TermId), SmtError> {
    let len_i = string_len_int(arena, s, m)?;
    let zero8 = arena.bv_const(8, 0)?;
    let mut byte = zero8;
    let mut in_range = arena.bool_const(false);
    // Walk positions high-to-low so the ITE cascade ends with position 0 outermost.
    for k in (0..m).rev() {
        let kconst = arena.int_const(i128::from(k));
        let i_is_k = arena.eq(i, kconst)?; // i == k (Int)
        let k_in_len = arena.int_lt(kconst, len_i)?; // k < len(s)
        let hit = arena.and(i_is_k, k_in_len)?;
        let byte_k = string_byte_m(arena, s, k, m)?;
        byte = arena.ite(hit, byte_k, byte)?;
        in_range = arena.ite(i_is_k, k_in_len, in_range)?;
    }
    Ok((byte, in_range))
}

/// `str.at s i` for a **non-constant** `Int` index `i`: the length-1 string
/// `s[i]` when `0 ≤ i < len(s)`, else the empty string (SMT-LIB total function).
/// Result is a max-length-1 packed string (smallest sort), so it composes with
/// equality. Pure mux over the ≤`m` positions — decides both directions.
fn string_at_int(arena: &mut TermArena, s: TermId, i: TermId) -> Result<TermId, SmtError> {
    let m = string_max_len(arena, s)?;
    let (byte, in_range) = string_byte_at_int(arena, s, i, m)?;
    let zero8 = arena.bv_const(8, 0)?;
    let one_len = arena.bv_const(len_width(1), 1)?;
    let zero_len = arena.bv_const(len_width(1), 0)?;
    let rlen = arena.ite(in_range, one_len, zero_len)?;
    let rbyte = arena.ite(in_range, byte, zero8)?;
    arena.concat(rbyte, rlen).map_err(SmtError::Ir)
}

/// Resizes a packed-string length field after a caller has proved the numeric
/// value fits in the destination width.
fn resize_string_len(
    arena: &mut TermArena,
    len: TermId,
    from_max: u32,
    to_max: u32,
) -> Result<TermId, SmtError> {
    let from = len_width(from_max);
    let to = len_width(to_max);
    match from.cmp(&to) {
        std::cmp::Ordering::Less => arena.zero_ext(to - from, len).map_err(SmtError::Ir),
        std::cmp::Ordering::Equal => Ok(len),
        std::cmp::Ordering::Greater => arena.extract(to - 1, 0, len).map_err(SmtError::Ir),
    }
}

/// Exact packed-BV path for `str.substr(s, 0, count)` with positive constant
/// `count`. The generic substring builder selects every source byte through an
/// Int-equality mux; a constant prefix instead copies each byte directly and
/// computes `min(len(s), count)` in the length field.
fn string_prefix_const(arena: &mut TermArena, s: TermId, count: u32) -> Result<TermId, SmtError> {
    debug_assert!(count > 0);
    let m = string_max_len(arena, s)?;
    debug_assert!(count < m, "only a genuinely narrower prefix is specialized");
    let slen = string_len_field(arena, s, m)?;
    let count_bv = arena.bv_const(len_width(m), u128::from(count))?;
    let shorter = arena.bv_ule(slen, count_bv)?;
    let clipped = arena.ite(shorter, slen, count_bv)?;
    let rlen = resize_string_len(arena, clipped, m, count)?;
    let mut content: Option<TermId> = None;
    for index in (0..count).rev() {
        let byte = string_byte_m(arena, s, index, m)?;
        content = Some(match content {
            None => byte,
            Some(previous) => arena.concat(previous, byte)?,
        });
    }
    arena
        .concat(content.expect("positive prefix bound"), rlen)
        .map_err(SmtError::Ir)
}

/// Exact packed-BV path for `str.substr(s, dropped, len(s)-dropped)` when the
/// constant offset is inside the packed bound. This is the generated "tail"
/// idiom used throughout `PyEx`: copy bytes `dropped..m` and compute
/// `max(len(s)-dropped, 0)` directly in BV, without an Int-index search.
fn string_suffix_const(
    arena: &mut TermArena,
    s: TermId,
    dropped: u32,
) -> Result<Option<TermId>, SmtError> {
    let m = string_max_len(arena, s)?;
    if dropped == 0 {
        return Ok(Some(s));
    }
    // Do not turn an offset beyond the artificial packed bound into a hard
    // empty word. The generic path retains the length channel needed to decline
    // rather than manufacture an unbounded-theory UNSAT.
    if dropped >= m {
        return Ok(None);
    }
    let result_max = m - dropped;
    let slen = string_len_field(arena, s, m)?;
    let dropped_bv = arena.bv_const(len_width(m), u128::from(dropped))?;
    let has_suffix = arena.bv_ult(dropped_bv, slen)?;
    let remaining = arena.bv_sub(slen, dropped_bv)?;
    let zero = arena.bv_const(len_width(m), 0)?;
    let clipped = arena.ite(has_suffix, remaining, zero)?;
    let rlen = resize_string_len(arena, clipped, m, result_max)?;
    let mut content: Option<TermId> = None;
    for index in (0..result_max).rev() {
        let byte = string_byte_m(arena, s, dropped + index, m)?;
        content = Some(match content {
            None => byte,
            Some(previous) => arena.concat(previous, byte)?,
        });
    }
    Ok(Some(
        arena.concat(content.expect("positive suffix bound"), rlen)?,
    ))
}

/// `str.substr s off n` (SMT-LIB total function): the substring of `s` starting
/// at position `off` of length at most `n`. Non-empty only when `0 ≤ off < |s|`
/// and `n > 0`; the result is `s[off .. min(off+n, |s|)]`. Any out-of-range
/// `off` (negative or `≥ |s|`) or non-positive `n` yields the empty string. The
/// result is a packed string of the **same** max length `m` as `s` (a substring
/// is never longer than the source). `off` and `n` are arbitrary `Int`s; output
/// byte `p` is `s[off + p]` selected by the same Int-equality mux, gated by
/// `p < n`, and the result length is the count of valid output positions.
fn string_substr(
    arena: &mut TermArena,
    s: TermId,
    off: TermId,
    n: TermId,
) -> Result<TermId, SmtError> {
    let off_const = ground_int_term(arena, off);
    let n_const = ground_int_term(arena, n);
    // Total-function corners and exact ground folds. Performing them before the
    // bounded mux is both cheaper and bound-independent.
    if off_const.is_some_and(|value| value < 0) || n_const.is_some_and(|value| value <= 0) {
        return pack_string_literal(arena, &[]);
    }
    if let Some(bytes) = string_const_bytes(arena, s) {
        if let (Some(off), Some(n)) = (off_const, n_const) {
            let start = usize::try_from(off).unwrap_or(bytes.len());
            // A positive `i128` too large for `usize` means "take through the
            // end", not zero bytes.
            let take = usize::try_from(n).unwrap_or(usize::MAX);
            let end = start.saturating_add(take).min(bytes.len());
            let out = bytes.get(start..end).unwrap_or(&[]);
            return pack_string_literal(arena, out);
        }
        // For a one-character literal, `(str.substr s i i)` is always empty:
        // i<0 is invalid, i=0 requests zero bytes, and i>=1 starts past the end.
        if bytes.len() <= 1 && off == n {
            return pack_string_literal(arena, &[]);
        }
        if bytes.is_empty()
            || off_const
                .is_some_and(|off| usize::try_from(off).map_or(true, |index| index >= bytes.len()))
        {
            return pack_string_literal(arena, &[]);
        }
    }
    // A one-byte slice is precisely `str.at`, including negative/out-of-range
    // indices and the empty-result cases.
    if n_const == Some(1) {
        return match off_const {
            Some(index) => string_at_const(arena, s, index),
            None => string_at_int(arena, s, off),
        };
    }
    let m = string_max_len(arena, s)?;
    // Taking from zero through the exact length is the original word.
    if off_const == Some(0) && n == string_len_int(arena, s, m)? {
        return Ok(s);
    }
    let len_i = string_len_int(arena, s, m)?;
    let zero_i = arena.int_const(0);
    // `off` is a valid start: 0 ≤ off < len(s). Out of that range → "" entirely.
    let off_nonneg = arena.int_ge(off, zero_i)?;
    let off_in = arena.int_lt(off, len_i)?;
    let start_ok = arena.and(off_nonneg, off_in)?;
    let zero8 = arena.bv_const(8, 0)?;
    // Output byte `p` present iff start_ok ∧ p < n ∧ (off+p) < len(s).
    let present = |arena: &mut TermArena, p: u32, src_in: TermId| -> Result<TermId, SmtError> {
        let pconst = arena.int_const(i128::from(p));
        let p_lt_n = arena.int_lt(pconst, n)?;
        let present0 = arena.and(start_ok, p_lt_n)?;
        arena.and(present0, src_in).map_err(SmtError::Ir)
    };
    // Length count (low→high) and content assembly (high→low).
    let mut count_i = arena.int_const(0);
    for p in 0..m {
        let pconst = arena.int_const(i128::from(p));
        let src = arena.int_add(off, pconst)?;
        let (_byte, src_in) = string_byte_at_int(arena, s, src, m)?;
        let pres = present(arena, p, src_in)?;
        let one_i = arena.int_const(1);
        let inc = arena.ite(pres, one_i, zero_i)?;
        count_i = arena.int_add(count_i, inc)?;
    }
    let mut content: Option<TermId> = None;
    for p in (0..m).rev() {
        let pconst = arena.int_const(i128::from(p));
        let src = arena.int_add(off, pconst)?;
        let (byte, src_in) = string_byte_at_int(arena, s, src, m)?;
        let pres = present(arena, p, src_in)?;
        let out_byte = arena.ite(pres, byte, zero8)?;
        content = Some(match content {
            None => out_byte,
            Some(acc) => arena.concat(acc, out_byte)?,
        });
    }
    let content = content.expect("m ≥ 1");
    // Result length: the byte count, as an `Int`, packed back into the BV field.
    let rlen = arena.int2bv(len_width(m), count_i)?;
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// Evaluates a ground integer term built from constants and the arithmetic
/// constructors emitted for SMT-LIB `+`, `-`, and `*`. Generated corpora often
/// spell tiny constants as nested arithmetic (for example `(- (+ 1 1) 1)`), and
/// recognizing those values preserves the same exact constant-index string path.
fn ground_int_term(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        TermNode::App { op, args } => match (op, args.as_ref()) {
            (Op::IntNeg, [arg]) => ground_int_term(arena, *arg)?.checked_neg(),
            (Op::IntAdd, [left, right]) => {
                ground_int_term(arena, *left)?.checked_add(ground_int_term(arena, *right)?)
            }
            (Op::IntSub, [left, right]) => {
                ground_int_term(arena, *left)?.checked_sub(ground_int_term(arena, *right)?)
            }
            (Op::IntMul, [left, right]) => {
                ground_int_term(arena, *left)?.checked_mul(ground_int_term(arena, *right)?)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Inverts an integer-valued Boolean indicator compared with a constant.
///
/// Generated symbolic-execution corpora routinely encode a Boolean `c` as
/// `(ite c 1 0)` and immediately compare it with `0` or `1`. When both branches
/// and the comparison target are integer constants, the equality is exactly one
/// of `true`, `false`, `c`, or `not c`; recovering that Boolean before string
/// gating exposes the original predicate without any bounded-theory assumption.
fn int_ite_const_equality(
    arena: &mut TermArena,
    candidate: TermId,
    target: TermId,
) -> Result<Option<TermId>, SmtError> {
    let target_value = match arena.node(target) {
        TermNode::IntConst(value) => *value,
        _ => return Ok(None),
    };
    let (condition, then_term, else_term) = match arena.node(candidate) {
        TermNode::App { op: Op::Ite, args } => match args.as_ref() {
            [condition, then_term, else_term] => (*condition, *then_term, *else_term),
            _ => return Ok(None),
        },
        _ => return Ok(None),
    };
    let then_value = match arena.node(then_term) {
        TermNode::IntConst(value) => *value,
        _ => return Ok(None),
    };
    let else_value = match arena.node(else_term) {
        TermNode::IntConst(value) => *value,
        _ => return Ok(None),
    };
    let then_matches = then_value == target_value;
    let else_matches = else_value == target_value;
    Ok(Some(match (then_matches, else_matches) {
        (true, true) => arena.bool_const(true),
        (false, false) => arena.bool_const(false),
        (true, false) => condition,
        (false, true) => arena.not(condition)?,
    }))
}

/// `str.update s i t` (SMT-LIB total function): the string equal to `s` except that
/// the `len(t)` bytes starting at position `i` are overwritten by `t` — but ONLY when
/// `0 ≤ i < len(s)` (otherwise the result is `s` unchanged), and the overwrite is
/// clipped to `[i, min(len(s), i + len(t)))`. The result length is **always** `len(s)`
/// (an update never grows or shrinks the string), so the result is packed in the
/// **same** max length `m` as `s` — no cap risk. Output byte `p` is `t[p − i]` when it
/// is inside the (active, clipped) window and `s[p]` otherwise. Every byte read goes
/// through the in-range mux [`string_byte_at_int`], which yields `0` past the source
/// length, so out-of-length output positions are canonically zero. `i` is an arbitrary
/// `Int`; a negative or `≥ len(s)` index leaves `s` unchanged, matching cvc5/SMT-LIB.
fn string_update(
    arena: &mut TermArena,
    s: TermId,
    idx: TermId,
    t: TermId,
) -> Result<TermId, SmtError> {
    let m = string_max_len(arena, s)?;
    let mt = string_max_len(arena, t)?;
    let len_s = string_len_int(arena, s, m)?;
    let len_t = string_len_int(arena, t, mt)?;
    let zero_i = arena.int_const(0);
    // The update applies only for a start index inside `s` (`0 ≤ i < len(s)`); any
    // other index leaves `s` unchanged.
    let idx_nonneg = arena.int_ge(idx, zero_i)?;
    let idx_in = arena.int_lt(idx, len_s)?;
    let active = arena.and(idx_nonneg, idx_in)?;
    let mut content: Option<TermId> = None;
    for p in (0..m).rev() {
        let pconst = arena.int_const(i128::from(p));
        // `s[p]` (0 past `len(s)`) and `t[p − i]` (0 outside `[0, len(t))`).
        let (s_byte, _) = string_byte_at_int(arena, s, pconst, m)?;
        let t_idx = arena.int_sub(pconst, idx)?;
        let (t_byte, _) = string_byte_at_int(arena, t, t_idx, mt)?;
        // in_window = active ∧ (i ≤ p) ∧ (p < i + len(t)) ∧ (p < len(s)).
        let p_ge_idx = arena.int_ge(pconst, idx)?;
        let end = arena.int_add(idx, len_t)?;
        let p_lt_end = arena.int_lt(pconst, end)?;
        let p_lt_lens = arena.int_lt(pconst, len_s)?;
        let w = arena.and(active, p_ge_idx)?;
        let w = arena.and(w, p_lt_end)?;
        let in_window = arena.and(w, p_lt_lens)?;
        let out_byte = arena.ite(in_window, t_byte, s_byte)?;
        content = Some(match content {
            None => out_byte,
            Some(acc) => arena.concat(acc, out_byte)?,
        });
    }
    let content = content.expect("m ≥ 1");
    // Result length is exactly `len(s)`, packed back into the length field.
    let rlen = arena.int2bv(len_width(m), len_s)?;
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// `(str.replace s a b)` — replace the **first leftmost** occurrence of `a` in
/// `s` with `b` (SMT-LIB total function). Corner cases verbatim: if `a` does not
/// occur in `s`, the result is `s` unchanged; if `a` is the **empty** string, the
/// first match is at position 0, so the result is `b ++ s` (`b` prepended). The
/// result length is `len(s) − len(a) + len(b)` when found (it can grow or shrink),
/// else `len(s)`.
///
/// Encoding (bounded match + byte-wise splice over the packed layout, no concat
/// blowup): the first-match position `P` and a `found` flag are a mux over the
/// candidate starts `p ∈ 0..=m_s`. `match(p)` holds when `p + len(a) ≤ len(s)` and
/// `s[p+j] = a[j]` for every `j < len(a)`; `first(p) = match(p) ∧ ¬match(q)` for
/// all `q < p`. The result byte at output position `o` is selected by Int
/// comparisons against the symbolic boundaries `P` and `P + len(b)`: `s[o]` for
/// `o < P`, `b[o − P]` for `P ≤ o < P + len(b)`, and the tail `s[o − len(b) +
/// len(a)]` for `o ≥ P + len(b)` — and plain `s[o]` when `¬found`. This is sound
/// for **arbitrary** (literal or symbolic) `a`/`b`, because `len(a)`/`len(b)` are
/// kept as `Int`s and every byte read goes through the in-range mux
/// ([`string_byte_at_int`]).
///
/// The result is packed in a max-length-`rm` layout where `rm = m_s + m_b` (the
/// largest the splice can produce — the prepend case `len(a)=0` keeps all of `s`
/// and adds all of `b`). When `rm > STRING_BOUND_CAP` the op is **declined**
/// (`Unsupported` → `unknown`), never truncated to a wrong string.
#[allow(clippy::too_many_lines)]
fn string_replace(
    arena: &mut TermArena,
    s: TermId,
    a: TermId,
    b: TermId,
) -> Result<TermId, SmtError> {
    // Exact algebraic identities. These are especially important before the
    // result-bound calculation: a normalized no-op must not be rejected merely
    // because the unreduced splice could have had a wider packed layout.
    if s == a {
        return Ok(b);
    }
    if a == b {
        return Ok(s);
    }
    if string_const_bytes(arena, a).is_some_and(|bytes| bytes.is_empty()) {
        return string_concat(arena, &[b, s]);
    }
    // A constant non-empty needle absent from a constant subject makes the
    // replacement a no-op regardless of the (possibly symbolic) replacement.
    // Recognize that before result-width accounting: the exact result is `s`,
    // so a wide symbolic `b` cannot make this harmless case exceed the cap.
    if let (Some(sb), Some(ab)) = (string_const_bytes(arena, s), string_const_bytes(arena, a))
        && !ab.is_empty()
        && !sb.windows(ab.len()).any(|window| window == ab)
    {
        return Ok(s);
    }
    // Fully-ground first-occurrence replacement. Keep the existing symbolic
    // encoding as a fallback when the exact result exceeds the literal cap.
    if let (Some(sb), Some(ab), Some(bb)) = (
        string_const_bytes(arena, s),
        string_const_bytes(arena, a),
        string_const_bytes(arena, b),
    ) {
        let hit = sb.windows(ab.len()).position(|window| window == ab);
        if let Some(pos) = hit {
            let mut out = Vec::with_capacity(sb.len() - ab.len() + bb.len());
            out.extend_from_slice(&sb[..pos]);
            out.extend_from_slice(&bb);
            out.extend_from_slice(&sb[pos + ab.len()..]);
            if out.len() <= STRING_MAX_LEN as usize {
                return pack_string_literal(arena, &out);
            }
        } else {
            return Ok(s);
        }
    }
    let ms = string_max_len(arena, s)?;
    let ma = string_max_len(arena, a)?;
    let mb = string_max_len(arena, b)?;
    // Result max length: when found, `len(s) − len(a) + len(b) ≤ m_s − len(a)_min
    // + m_b`; when **not** found the result is `s` (≤ `m_s`). So `rm = max(m_s,
    // m_s − len(a)_min + m_b)`. A **literal** `a` pins `len(a)_min` to its exact
    // length, tightening the bound; a symbolic `a` can be empty (the prepend
    // case), so `len(a)_min = 0`.
    let a_lit_len =
        string_const_bytes(arena, a).map_or(0, |bytes| u32::try_from(bytes.len()).unwrap_or(0));
    let rm = ms.max(ms.saturating_sub(a_lit_len) + mb);
    if rm > STRING_BOUND_CAP {
        return Err(SmtError::Unsupported(format!(
            "str.replace result of bounded max length {rm} exceeds the cap {STRING_BOUND_CAP} \
             (ADR-0029)"
        )));
    }
    let len_s = string_len_int(arena, s, ms)?;
    let len_a = string_len_int(arena, a, ma)?;
    let len_b = string_len_int(arena, b, mb)?;
    let zero8 = arena.bv_const(8, 0)?;

    // `match(p)` for a candidate start position `p` (an `Int` constant): the
    // substring `a` fits (`p + len(a) ≤ len(s)`) and aligns byte-for-byte. We walk
    // `p` over `0..=m_s` (an empty `a` can match at `p = len(s)`, but the first
    // match for an empty `a` is `p = 0`, so the cascade below picks it).
    let match_at = |arena: &mut TermArena, p: u32| -> Result<TermId, SmtError> {
        let pconst = arena.int_const(i128::from(p));
        let p_plus_la = arena.int_add(pconst, len_a)?;
        let mut fits = arena.int_le(p_plus_la, len_s)?; // p + len(a) ≤ len(s)
        for j in 0..ma {
            let jconst = arena.int_const(i128::from(j));
            let j_lt_la = arena.int_lt(jconst, len_a)?; // j < len(a)
            // s[p+j] and a[j] (both via the in-range Int mux / direct slot).
            let src = arena.int_add(pconst, jconst)?;
            let (sbyte, _sin) = string_byte_at_int(arena, s, src, ms)?;
            let abyte = string_byte_m(arena, a, j, ma)?;
            let beq = arena.eq(sbyte, abyte)?;
            let nj = arena.not(j_lt_la)?;
            let ok = arena.or(nj, beq)?; // j ≥ len(a) ∨ s[p+j] = a[j]
            fits = arena.and(fits, ok)?;
        }
        Ok(fits)
    };

    // First-match position `P` (an `Int`) and `found`: `first(p) = match(p) ∧
    // ¬match(q)` for all `q < p`. Walk low→high; the first `match` wins.
    let mut found = arena.bool_const(false);
    let mut pos_i = arena.int_const(0); // P; meaningful only when `found`.
    let mut none_before = arena.bool_const(true); // ¬match(q) for every q seen so far.
    for p in 0..=ms {
        let mp = match_at(arena, p)?;
        let first_p = arena.and(none_before, mp)?; // this is the leftmost match
        let pconst = arena.int_const(i128::from(p));
        pos_i = arena.ite(first_p, pconst, pos_i)?;
        found = arena.or(found, first_p)?;
        let nmp = arena.not(mp)?;
        none_before = arena.and(none_before, nmp)?;
    }

    // Result length: `len(s) − len(a) + len(b)` when found, else `len(s)`.
    let found_len0 = arena.int_sub(len_s, len_a)?;
    let found_len = arena.int_add(found_len0, len_b)?;
    let result_len = arena.ite(found, found_len, len_s)?;

    // Result content, byte-by-byte (high→low), over `rm` output positions.
    let mut content: Option<TermId> = None;
    for o in (0..rm).rev() {
        let oconst = arena.int_const(i128::from(o));
        // not-found branch: plain `s[o]`.
        let (s_o, _s_o_in) = string_byte_at_int(arena, s, oconst, ms)?;
        // found branch boundaries: P and P + len(b).
        let o_lt_p = arena.int_lt(oconst, pos_i)?; // o < P  → s[o]
        let p_plus_lb = arena.int_add(pos_i, len_b)?;
        let o_lt_p_lb = arena.int_lt(oconst, p_plus_lb)?; // o < P+len(b)
        // b[o − P]  (valid only in the middle band; the mux gates by len(b)).
        let o_minus_p = arena.int_sub(oconst, pos_i)?;
        let (b_byte, _b_in) = string_byte_at_int(arena, b, o_minus_p, mb)?;
        // tail s[o − len(b) + len(a)]  (for o ≥ P+len(b)).
        let tail_idx0 = arena.int_sub(oconst, len_b)?;
        let tail_idx = arena.int_add(tail_idx0, len_a)?;
        let (tail_byte, _t_in) = string_byte_at_int(arena, s, tail_idx, ms)?;
        // middle band (P ≤ o < P+len(b)) → b[o−P]; else tail.
        let mid_or_tail = arena.ite(o_lt_p_lb, b_byte, tail_byte)?;
        // o < P → s[o]; else (middle or tail).
        let found_byte = arena.ite(o_lt_p, s_o, mid_or_tail)?;
        // gate the whole output byte by `o < result_len` (else canonical 0 pad).
        let o_lt_len = arena.int_lt(oconst, result_len)?;
        let chosen = arena.ite(found, found_byte, s_o)?;
        let out_byte = arena.ite(o_lt_len, chosen, zero8)?;
        content = Some(match content {
            None => out_byte,
            Some(acc) => arena.concat(acc, out_byte)?,
        });
    }
    let content = content.expect("rm ≥ 1");
    let rlen = arena.int2bv(len_width(rm), result_len)?;
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// `(str.indexof s t i)` — the position of the **first** occurrence of `t` in
/// `s` at or after offset `i`, or `-1` if there is none (SMT-LIB total function;
/// result is an `Int`). Corner cases verbatim: `i < 0` → `-1`; `i > len(s)` →
/// `-1`; `t = ""` → `i` when `0 ≤ i ≤ len(s)` (the empty pattern matches at every
/// position, so the first one at-or-after `i` is `i` itself); `t` not occurring
/// at-or-after `i` → `-1`. The 2-argument form `(str.indexof s t)` is offset `0`.
///
/// Encoding: reuses the first-match cascade of [`string_replace`] — `match(p)`
/// holds when `p + len(t) ≤ len(s)` and `s[p+j] = t[j]` for every `j < len(t)` —
/// but restricted to **eligible** candidates `p ≥ i`. The leftmost eligible match
/// position `P` (an `Int`) and a `found` flag are a mux over `p ∈ 0..=m_s`;
/// the result is `P` when `found ∧ i ≥ 0`, else `-1`. This is a **pure position
/// search** (no length-changing rebuild), so there is no result-length cap to
/// exceed — but the operands must still pack (over-bound `s`/`t` decline at pack
/// time). Sound for literal **or** symbolic `s`/`t`/`i` (every byte read goes
/// through the in-range `Int` mux [`string_byte_at_int`]).
fn string_indexof(
    arena: &mut TermArena,
    s: TermId,
    t: TermId,
    i: TermId,
) -> Result<TermId, SmtError> {
    if let Some(offset) = ground_int_term(arena, i) {
        if offset < 0 {
            return Ok(arena.int_const(-1));
        }
        if offset == 0
            && (s == t || string_const_bytes(arena, t).is_some_and(|bytes| bytes.is_empty()))
        {
            return Ok(arena.int_const(0));
        }
    }
    // A non-empty constant needle absent from a constant subject is never found,
    // independent of the start index (including symbolic or out-of-range starts).
    if let (Some(sb), Some(tb)) = (string_const_bytes(arena, s), string_const_bytes(arena, t))
        && !tb.is_empty()
        && !sb.windows(tb.len()).any(|window| window == tb)
    {
        return Ok(arena.int_const(-1));
    }
    let ms = string_max_len(arena, s)?;
    let mt = string_max_len(arena, t)?;
    let len_s = string_len_int(arena, s, ms)?;
    let len_t = string_len_int(arena, t, mt)?;

    // `match(p)`: `t` fits at `p` (`p + len(t) ≤ len(s)`) and aligns byte-for-byte.
    // (Identical to `string_replace`'s `match_at`, over `t` here.)
    let match_at = |arena: &mut TermArena, p: u32| -> Result<TermId, SmtError> {
        let pconst = arena.int_const(i128::from(p));
        let p_plus_lt = arena.int_add(pconst, len_t)?;
        let mut fits = arena.int_le(p_plus_lt, len_s)?; // p + len(t) ≤ len(s)
        for j in 0..mt {
            let jconst = arena.int_const(i128::from(j));
            let j_lt_lt = arena.int_lt(jconst, len_t)?; // j < len(t)
            let src = arena.int_add(pconst, jconst)?;
            let (sbyte, _sin) = string_byte_at_int(arena, s, src, ms)?;
            let tbyte = string_byte_m(arena, t, j, mt)?;
            let beq = arena.eq(sbyte, tbyte)?;
            let nj = arena.not(j_lt_lt)?;
            let ok = arena.or(nj, beq)?; // j ≥ len(t) ∨ s[p+j] = t[j]
            fits = arena.and(fits, ok)?;
        }
        Ok(fits)
    };

    // Leftmost **eligible** (`p ≥ i`) match: walk low→high, the first eligible
    // match wins. `none_before` only tracks eligible matches already seen.
    let mut found = arena.bool_const(false);
    let mut pos_i = arena.int_const(0); // P; meaningful only when `found`.
    let mut none_before = arena.bool_const(true);
    for p in 0..=ms {
        let pconst = arena.int_const(i128::from(p));
        let p_ge_i = arena.int_le(i, pconst)?; // i ≤ p  ⇔  p ≥ i
        let mp = match_at(arena, p)?;
        let eligible = arena.and(p_ge_i, mp)?;
        let first_p = arena.and(none_before, eligible)?;
        pos_i = arena.ite(first_p, pconst, pos_i)?;
        found = arena.or(found, first_p)?;
        let neli = arena.not(eligible)?;
        none_before = arena.and(none_before, neli)?;
    }

    // `i < 0` ⇒ `-1` regardless of any match (`p ≥ i` is vacuous for negative `i`,
    // so it is gated here, not in the cascade). `i > len(s)` already yields no
    // eligible match (no `p ≤ m_s` is both `≥ i` and `≤ len(s)`), so it falls to
    // the `-1` branch via `¬found`.
    let zero = arena.int_const(0);
    let i_ge_0 = arena.int_le(zero, i)?;
    let valid = arena.and(found, i_ge_0)?;
    let neg_one = arena.int_const(-1);
    arena.ite(valid, pos_i, neg_one).map_err(SmtError::Ir)
}

/// `(str.replace_all s a b)` — replace **all** non-overlapping, left-to-right
/// occurrences of `a` in `s` with `b` (SMT-LIB total function). Corner cases
/// verbatim: `a = ""` → `s` **unchanged** (the empty-pattern `replace_all` is the
/// identity — this differs from single `str.replace`, where an empty `a` prepends
/// `b`; **verified against Z3/cvc5**); `a` not occurring → `s`; matches are
/// consumed left-to-right and the scan resumes **after** each inserted `b` (it
/// does **not** rescan inside `b`, so `(str.replace_all "aa" "a" "aa") = "aaaa"`,
/// not a divergent rewrite).
///
/// Encoding: this slice wires the **fully-ground** case exactly (all of `s`, `a`,
/// `b` are packed constants) by folding the non-overlapping replacement in Rust
/// and packing the literal result. The unbounded-round splice over a *symbolic*
/// `s`/`b` (or a symbolic `a`, whose length — hence the round count — is unknown)
/// is **declined** cleanly (`Unsupported` → `unknown`), never a wrong/truncated
/// string: a sound symbolic `replace_all` needs a moving-cursor splice whose round
/// count is bounded only when `len(a)` is concrete and whose growing result must
/// stay under `STRING_BOUND_CAP` — left as a tightly-scoped follow-up. An
/// over-bound ground result (more than `STRING_MAX_LEN` bytes) declines at pack
/// time rather than truncate.
fn string_replace_all(
    arena: &mut TermArena,
    s: TermId,
    a: TermId,
    b: TermId,
) -> Result<TermId, SmtError> {
    let (Some(sb), Some(ab), Some(bb)) = (
        string_const_bytes(arena, s),
        string_const_bytes(arena, a),
        string_const_bytes(arena, b),
    ) else {
        return Err(SmtError::Unsupported(
            "str.replace_all over a non-constant operand is outside the wired sound subset \
             (a symbolic moving-cursor splice is bounded only for a concrete len(a); ADR-0029)"
                .to_owned(),
        ));
    };
    // `a = ""` is the identity (empty-pattern replace_all leaves `s` unchanged).
    if ab.is_empty() {
        return pack_string_literal(arena, &sb);
    }
    // Non-overlapping, left-to-right: at each match consume `a` and emit `b`, then
    // resume scanning **after** the emitted `b`'s source span (never inside `b`).
    let mut out: Vec<u8> = Vec::new();
    let mut k = 0usize;
    while k < sb.len() {
        if k + ab.len() <= sb.len() && sb[k..k + ab.len()] == ab[..] {
            out.extend_from_slice(&bb);
            k += ab.len();
        } else {
            out.push(sb[k]);
            k += 1;
        }
    }
    pack_string_literal(arena, &out)
}

/// `(str.replace_re s R t)` — replace the **leftmost, shortest** substring of `s`
/// matching the regex `R` with `t` (SMT-LIB `UnicodeStrings`). Spec semantics
/// verbatim: `⟦str.replace_re⟧(w, L, t) = u₁ t u₂` where `u₁, w₁` are the
/// **shortest** words with `w = u₁ w₁ u₂` and `w₁ ∈ L` — so `u₁` shortest selects
/// the **leftmost** start, and `w₁` shortest selects the **shortest** match at
/// that start (which is `ε` when `ε ∈ L`, giving the prepend `t ++ w`). If no
/// substring of `w` is in `L`, the result is `w` unchanged.
///
/// This slice wires the **ground** case (a constant `s`): the literal bytes are
/// scanned for the leftmost-shortest match by concrete NFA simulation over each
/// substring, the splice is folded in Rust, and the literal result is packed —
/// so it rides the pure-BV path and decides both directions. `t` may be any
/// packed string (constant or symbolic) — only `s` must be constant here. A
/// **symbolic** `s` declines cleanly (`Unsupported` → `unknown`), never a
/// truncated/wrong string: the leftmost-shortest splice over an unknown string is
/// a scoped follow-up. The regex `R` is compiled (and may decline on its own —
/// over-cap DFA, unsupported construct). An over-bound ground result declines at
/// pack time.
fn string_replace_re(
    arena: &mut TermArena,
    s: TermId,
    re: &SExpr,
    t: TermId,
) -> Result<TermId, SmtError> {
    let Some(sb) = string_const_bytes(arena, s) else {
        return Err(SmtError::Unsupported(
            "str.replace_re over a non-constant string is outside the wired sound subset \
             (the leftmost-shortest splice over a symbolic string is a scoped follow-up; ADR-0029)"
                .to_owned(),
        ));
    };
    let Some(tb) = string_const_bytes(arena, t) else {
        return Err(SmtError::Unsupported(
            "str.replace_re with a non-constant replacement `t` is outside the wired ground \
             subset (ADR-0029)"
                .to_owned(),
        ));
    };
    let rx = crate::regex::compile_regex(re)?;
    // Leftmost-shortest match: smallest start `i`, and at that `i` the smallest
    // `j ≥ i` with `R` accepting `s[i..j]` (allowing the empty match `j = i`).
    let mut spliced: Option<Vec<u8>> = None;
    'outer: for i in 0..=sb.len() {
        for j in i..=sb.len() {
            if rx.matches(&sb[i..j]) {
                let mut out = Vec::with_capacity(i + tb.len() + (sb.len() - j));
                out.extend_from_slice(&sb[..i]);
                out.extend_from_slice(&tb);
                out.extend_from_slice(&sb[j..]);
                spliced = Some(out);
                break 'outer;
            }
        }
    }
    // No substring matched → `s` unchanged.
    let out = spliced.unwrap_or(sb);
    pack_string_literal(arena, &out)
}

/// `(str.replace_re_all s R t)` — replace **all** non-overlapping, left-to-right
/// **leftmost-shortest non-empty** matches of the regex `R` with `t` (SMT-LIB
/// `UnicodeStrings`). Spec semantics verbatim: each replaced `w₁` is the
/// **shortest** word at the leftmost remaining start with `w₁ ∈ L` **and**
/// `w₁ ≠ ε` (empty matches are *not* replaced — `replace_re_all` never inserts on
/// an `ε ∈ L`, so it terminates), and the scan resumes **after** each consumed
/// match. If no non-empty substring is in `L`, the result is `s` unchanged.
///
/// Wired for the **ground** case (constant `s`); a symbolic `s` declines cleanly
/// (`Unsupported` → `unknown`). `t` may be symbolic only via the constant path —
/// here it must also be constant to fold. An over-bound ground result declines at
/// pack time.
fn string_replace_re_all(
    arena: &mut TermArena,
    s: TermId,
    re: &SExpr,
    t: TermId,
) -> Result<TermId, SmtError> {
    let Some(sb) = string_const_bytes(arena, s) else {
        return Err(SmtError::Unsupported(
            "str.replace_re_all over a non-constant string is outside the wired sound subset \
             (a moving-cursor regex splice over a symbolic string is a scoped follow-up; \
             ADR-0029)"
                .to_owned(),
        ));
    };
    let Some(tb) = string_const_bytes(arena, t) else {
        return Err(SmtError::Unsupported(
            "str.replace_re_all with a non-constant replacement `t` is outside the wired ground \
             subset (ADR-0029)"
                .to_owned(),
        ));
    };
    let rx = crate::regex::compile_regex(re)?;
    let mut out: Vec<u8> = Vec::new();
    let mut k = 0usize;
    while k < sb.len() {
        // Leftmost-shortest **non-empty** match at-or-after `k`: scan starts
        // `i = k.., j > i` shortest. (`replace_re_all` never matches `ε`, so the
        // cursor always advances and the loop terminates.)
        let mut hit: Option<(usize, usize)> = None;
        'find: for lo in k..sb.len() {
            for hi in (lo + 1)..=sb.len() {
                if rx.matches(&sb[lo..hi]) {
                    hit = Some((lo, hi));
                    break 'find;
                }
            }
        }
        match hit {
            Some((lo, hi)) => {
                out.extend_from_slice(&sb[k..lo]); // unmatched prefix kept verbatim
                out.extend_from_slice(&tb); // the replacement
                k = hi; // resume after the consumed match
            }
            None => break, // no further match: keep the tail below
        }
    }
    out.extend_from_slice(&sb[k..]);
    pack_string_literal(arena, &out)
}

/// `str.to_code s`: the code point of the single character of `s` when
/// `|s| = 1`, else `-1` (SMT-LIB total function). In the byte model a character
/// is one byte, so the code is `bv2nat(s[0])` (`0..=255`); any other length
/// yields `-1`. Decides both directions (composes with `Int` arithmetic).
fn string_to_code(arena: &mut TermArena, s: TermId) -> Result<TermId, SmtError> {
    let m = string_max_len(arena, s)?;
    let len_i = string_len_int(arena, s, m)?;
    let one_i = arena.int_const(1);
    let is_one = arena.eq(len_i, one_i)?;
    let byte0 = string_byte_m(arena, s, 0, m)?;
    let code = arena.bv2nat(byte0)?; // 0..=255
    let neg_one = arena.int_const(-1);
    arena.ite(is_one, code, neg_one).map_err(SmtError::Ir)
}

/// `str.from_code i`: the length-1 string whose single character has code point
/// `i` when `i` is a valid Unicode code point (`0 ≤ i ≤ 0x2FFFF`), else the empty
/// string (SMT-LIB `UnicodeStrings` total function).
///
/// **Soundness.** axeyum's string model is an 8-bit *byte* alphabet — a character
/// is one byte — so [`string_to_code`] round-trips the full range `0..=255` via
/// `bv2nat(s[0])`. `str.from_code` must be the exact partial inverse over that
/// same range; anything else self-contradicts the theorem
/// `str.to_code (str.from_code i) = i`. We split on the argument:
///
/// * **`0 ≤ i ≤ 255`** — representable: the length-1 string of byte `i`. Exact,
///   and round-trips with `str.to_code` (`to_code (from_code i) = i`).
/// * **`i < 0` or `i > 0x2FFFF`** — not a valid code point: the empty string,
///   exactly as SMT-LIB specifies. Byte-model-agnostic and sound.
/// * **`256 ≤ i ≤ 0x2FFFF`** — a *valid, non-empty* code point the 8-bit byte
///   alphabet cannot faithfully encode. Folding it to `""` is the wrong-sat this
///   function shipped (P0: `(= (str.from_code 200) "")` was `sat`; Z3 `unsat`),
///   and every byte-level surrogate is likewise unsound — `i mod 256` fabricates
///   a wrong-sat on `(= (from_code i) c)` and a wrong-unsat on
///   `(= (to_code (from_code i)) i)`. So we **decline** (`Unsupported` → the query
///   is reported `Unknown`), never a wrong verdict.
///
/// A **symbolic** `i` could be assigned by the solver anywhere, including the
/// unrepresentable `256..=0x2FFFF` window where no byte-model encoding is sound
/// (an empty/`mod 256`/fresh-byte result each admits a wrong-sat or a wrong-unsat
/// on `to_code ∘ from_code`). Since the argument is not provably `≤ 255` at parse
/// time, a non-constant argument declines wholesale — conservative (loses some
/// symbolic completeness) but never wrong. Constant arguments — the common case,
/// including the P0 — fold exactly.
fn string_from_code(arena: &mut TermArena, i: TermId) -> Result<TermId, SmtError> {
    /// SMT-LIB `UnicodeStrings` maximum code point.
    const MAX_CODE_POINT: i128 = 0x2FFFF;
    // `constant_int_value` folds literals *and* constant arithmetic (e.g. the
    // SMT-LIB negative literal `(- 1)` → `-1`), so every ground code point takes
    // the exact path below rather than declining as "symbolic".
    if let Some(v) = constant_int_value(arena, i) {
        return if (0..=255).contains(&v) {
            // Representable: the length-1 byte string, packed exactly as a literal
            // so it compares against string constants and round-trips `str.to_code`.
            let byte = u8::try_from(v).expect("0..=255 fits u8");
            pack_string_literal(arena, &[byte])
        } else if !(0..=MAX_CODE_POINT).contains(&v) {
            // Invalid code point → the empty string (SMT-LIB total function).
            pack_string_literal(arena, &[])
        } else {
            // 256..=0x2FFFF: a valid, non-empty character outside the byte
            // alphabet. Decline rather than commit any wrong (byte) string.
            Err(SmtError::Unsupported(format!(
                "str.from_code of the constant {v}: a valid code point in \
                 256..=0x2FFFF is a non-empty character the 8-bit byte model \
                 cannot represent — declining to Unknown rather than folding to a \
                 wrong string (ADR-0029; P0, task #46)"
            )))
        };
    }
    // Symbolic argument: the solver could assign `i` into the unrepresentable
    // 256..=0x2FFFF window, where no byte-model encoding is sound. Decline.
    Err(SmtError::Unsupported(
        "str.from_code over a symbolic code point is outside the sound byte-model \
         subset: an argument in 256..=0x2FFFF is a valid non-empty character the \
         8-bit alphabet cannot represent, and no byte encoding decides that window \
         soundly, so a non-constant argument is declined (ADR-0029; task #46)"
            .to_owned(),
    ))
}

/// Maximum number of decimal digits a `str.from_int` result string carries (the
/// max length of the packed string `str.from_int` builds). Sized so it holds the
/// full decimal expansion of **every** integer the bounded int bit-blast can
/// model — `DEFAULT_INT_WIDTH = 32` bits, so the largest representable value is
/// `2^31 − 1 = 2_147_483_647 < 10^10`, i.e. ≤ 10 digits. Building the result in a
/// 10-byte packed sort therefore makes [`string_from_int`] *faithful for every
/// `i` the solver can assign*: any `i ≥ 10^10` is already outside the int-blast
/// range (replay returns `Unknown`), so the bounded encoding never claims a wrong
/// string. Kept ≤ `STRING_BOUND_CAP` so the packed width is representable.
const FROM_INT_MAX_DIGITS: u32 = 10;

/// `str.to_int s` (SMT-LIB `UnicodeStrings` total function): the decimal value of
/// `s` when `s` is a **non-empty** string of ASCII digits `'0'..='9'`, else `-1`.
/// Leading zeros are valid (`"007" → 7`, `"0001" → 1`); the empty string and any
/// string containing a non-digit character yield `-1`. Encoded as a bounded
/// Horner fold over the ≤`m` content bytes guarded by a digit-validity check;
/// the result is an `Int`, so it composes with integer arithmetic.
///
/// Position 0 is the most-significant digit, so the fold
/// `acc ← acc·10 + digit(s[p])` over the *present* positions (`p < len(s)`)
/// builds the value left-to-right; positions `p ≥ len(s)` contribute nothing
/// (`acc·1 + 0`). The maximum value is `10^m − 1`. At the current
/// `STRING_MAX_LEN = 12`, values above the default signed width are deliberately
/// incomplete: an over-wide Horner value overflows the int blast and original-
/// query replay returns `Unknown`, never a wrong verdict.
fn string_to_int(arena: &mut TermArena, s: TermId) -> Result<TermId, SmtError> {
    let m = string_max_len(arena, s)?;
    let len_field = string_len_field(arena, s, m)?;
    let ascii_zero = arena.bv_const(8, u128::from(b'0'))?;
    let ascii_nine = arena.bv_const(8, u128::from(b'9'))?;
    let ten = arena.int_const(10);
    let mut acc = arena.int_const(0);
    // `all_digits`: every *present* byte (`p < len(s)`) is an ASCII digit.
    let mut all_digits = arena.bool_const(true);
    for p in 0..m {
        let byte = string_byte_m(arena, s, p, m)?;
        // Present iff p < len(s).
        let pconst = arena.bv_const(len_width(m), u128::from(p))?;
        let present = arena.bv_ult(pconst, len_field)?;
        // Digit-ness: '0' ≤ byte ≤ '9'.
        let ge0 = arena.bv_uge(byte, ascii_zero)?;
        let le9 = arena.bv_ule(byte, ascii_nine)?;
        let is_digit = arena.and(ge0, le9)?;
        // A present byte must be a digit; an absent byte is unconstrained here.
        let npresent = arena.not(present)?;
        let ok = arena.or(npresent, is_digit)?;
        all_digits = arena.and(all_digits, ok)?;
        // Digit value (only meaningful when present ∧ digit): byte − '0', as Int.
        let digit_bv = arena.bv_sub(byte, ascii_zero)?;
        let digit_int = arena.bv2nat(digit_bv)?; // 0..=255 (0..=9 under is_digit)
        // Contribute only when present: acc ← present ? acc·10 + digit : acc.
        let shifted = arena.int_mul(acc, ten)?;
        let added = arena.int_add(shifted, digit_int)?;
        acc = arena.ite(present, added, acc)?;
    }
    // Non-empty: len(s) ≥ 1.
    let zero_len = arena.bv_const(len_width(m), 0)?;
    let is_empty = arena.eq(len_field, zero_len)?;
    let nonempty = arena.not(is_empty)?;
    let valid = arena.and(nonempty, all_digits)?;
    let neg_one = arena.int_const(-1);
    arena.ite(valid, acc, neg_one).map_err(SmtError::Ir)
}

/// `str.from_int i` (SMT-LIB `UnicodeStrings` total function): the canonical
/// decimal string of `i` when `i ≥ 0` (no leading zeros, `0 → "0"`), and `""`
/// when `i < 0`. The result is a packed string of max length
/// [`FROM_INT_MAX_DIGITS`] = 10, which holds the full decimal expansion of every
/// integer the bounded int bit-blast can assign (`< 2^31 < 10^10`), so the
/// encoding is **faithful for every model the solver can produce** — see
/// [`FROM_INT_MAX_DIGITS`] for the soundness argument.
///
/// Construction: for `i < 0` the string is empty. For `0 ≤ i` we mux over the
/// digit-count `nd ∈ 1..=10`: under the guard `10^{nd−1} ≤ i < 10^{nd}` (with the
/// `nd = 1` lower bound relaxed to `i ≥ 0`) the result is the `nd`-byte
/// left-aligned string whose byte `p` (0 = most significant) is the ASCII digit
/// `(i / 10^{nd−1−p}) mod 10`. An `i ≥ 10^{10}` selects no `nd` and yields `""`,
/// but such an `i` is outside the int-blast range, so this case never appears in
/// a replaying model.
fn string_from_int(arena: &mut TermArena, i: TermId) -> Result<TermId, SmtError> {
    let m = FROM_INT_MAX_DIGITS;
    let lw = len_width(m);
    let zero_i = arena.int_const(0);
    let nonneg = arena.int_ge(i, zero_i)?;
    let ten = arena.int_const(10);
    // Powers of ten 10^0..=10^m as Int constants (10^m guards the top digit-count).
    let mut pow10: Vec<TermId> = Vec::with_capacity((m + 1) as usize);
    let mut acc: i128 = 1;
    for _ in 0..=m {
        pow10.push(arena.int_const(acc));
        acc = acc.saturating_mul(10);
    }
    // `i / 10^k mod 10` as an Int (the k-th least-significant decimal digit).
    let digit_k = |arena: &mut TermArena, i: TermId, k: u32| -> Result<TermId, SmtError> {
        let div = arena.int_div(i, pow10[k as usize])?;
        let dmod = arena.int_mod(div, ten)?;
        Ok(dmod)
    };
    // Result bytes, high-to-low position; default (no nd selected, or i < 0) "".
    let zero8 = arena.bv_const(8, 0)?;
    let ascii_zero_int = arena.int_const(i128::from(b'0'));
    // For each digit-count nd, build its guard and its byte layout, then mux.
    // byte[p] (0 = most significant) and len = nd, all defaulting to the empty
    // string and overwritten by the matching nd.
    let mut bytes: Vec<TermId> = vec![zero8; m as usize];
    let zero_len = arena.bv_const(lw, 0)?;
    let mut rlen = zero_len;
    for nd in 1..=m {
        // Guard: i < 10^nd  ∧  (nd == 1 ? true : i ≥ 10^{nd-1}).
        let lt_hi = arena.int_lt(i, pow10[nd as usize])?;
        let guard = if nd == 1 {
            arena.and(nonneg, lt_hi)?
        } else {
            let ge_lo = arena.int_ge(i, pow10[(nd - 1) as usize])?;
            let g0 = arena.and(nonneg, ge_lo)?;
            arena.and(g0, lt_hi)?
        };
        // Under this nd, byte position p (0 = MSB) is digit (nd-1-p); set len = nd.
        let nd_len = arena.bv_const(lw, u128::from(nd))?;
        rlen = arena.ite(guard, nd_len, rlen)?;
        for p in 0..nd {
            let k = nd - 1 - p; // least-significant index of the digit at position p
            let dval = digit_k(arena, i, k)?; // 0..=9 Int
            let byte_int = arena.int_add(dval, ascii_zero_int)?; // ASCII digit
            let byte_bv = arena.int2bv(8, byte_int)?;
            let slot = p as usize;
            bytes[slot] = arena.ite(guard, byte_bv, bytes[slot])?;
        }
    }
    // Assemble the packed string: content bytes high-to-low, then the length field.
    let mut content: Option<TermId> = None;
    for p in (0..m as usize).rev() {
        content = Some(match content {
            None => bytes[p],
            Some(c) => arena.concat(c, bytes[p])?,
        });
    }
    let content = content.expect("m ≥ 1");
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// `str.from_int i` for a **constant** `i`: folds to the exact decimal-string
/// literal, packed into the same [`FROM_INT_MAX_DIGITS`]-byte sort the symbolic
/// [`string_from_int`] builds (so a constant and a symbolic `from_int` compare).
/// `i < 0 → ""`; otherwise the canonical decimal (no leading zeros, `0 → "0"`).
/// **Declines** (`Unsupported`) when the decimal expansion needs more than
/// `FROM_INT_MAX_DIGITS` bytes — a value the bounded string sort cannot hold, so
/// it is reported as Unknown rather than truncated to a wrong string.
fn string_from_int_const(arena: &mut TermArena, v: i128) -> Result<TermId, SmtError> {
    let m = FROM_INT_MAX_DIGITS;
    let bytes: Vec<u8> = if v < 0 {
        Vec::new()
    } else {
        v.to_string().into_bytes()
    };
    if bytes.len() > m as usize {
        return Err(SmtError::Unsupported(format!(
            "str.from_int of the constant {v} needs {} decimal digits, exceeding the \
             bounded string length {m} (ADR-0029); widen the bound to decide this query",
            bytes.len()
        )));
    }
    // Pack into the m-byte layout (length low, content above, padding zero).
    let mut content: u128 = 0;
    for (idx, &b) in bytes.iter().enumerate() {
        content |= u128::from(b) << (8 * idx);
    }
    let packed =
        u128::from(u32::try_from(bytes.len()).expect("len ≤ m")) | (content << len_width(m));
    arena
        .bv_const(string_total(m), packed)
        .map_err(SmtError::Ir)
}

/// `str.< x y` — strict lexicographic order over the packed bytes. `x < y` iff
/// at the first position where they differ `x` has the smaller byte, or `x` is a
/// proper prefix of `y`. Encoded as a bounded cascade over the ≤`m` positions:
/// `x < y` holds at the first index `i` with `x[i] < y[i]` provided every earlier
/// byte was equal, OR all `min(|x|,|y|)` shared bytes are equal and `|x| < |y|`.
/// Pure BV/Bool — decides both directions. Matches SMT-LIB's code-point order on
/// the ASCII byte model.
fn string_lt(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    let (x, y, m) = string_align(arena, x, y)?;
    let xlen = string_len_field(arena, x, m)?;
    let ylen = string_len_field(arena, y, m)?;
    // `eq_prefix` (Bool): bytes 0..i are all "shared and equal". Built inline.
    let mut eq_prefix = arena.bool_const(true);
    let mut less = arena.bool_const(false);
    for i in 0..m {
        let iconst = arena.bv_const(len_width(m), u128::from(i))?;
        let i_in_x = arena.bv_ult(iconst, xlen)?; // i < len(x)
        let i_in_y = arena.bv_ult(iconst, ylen)?; // i < len(y)
        let xb = string_byte_m(arena, x, i, m)?;
        let yb = string_byte_m(arena, y, i, m)?;
        // Strict-less is decided at the first shared, still-equal-prefix position:
        //   (a) y has byte i but x ended here: x is a proper prefix of y → less.
        //   (b) both have byte i and x[i] < y[i].
        let x_ended = arena.not(i_in_x)?;
        let prefix_case = arena.and(x_ended, i_in_y)?; // x ran out, y did not
        let byte_lt = arena.bv_ult(xb, yb)?; // x[i] < y[i] (both present here)
        let both = arena.and(i_in_x, i_in_y)?;
        let byte_lt_here = arena.and(both, byte_lt)?;
        let decide_here = arena.or(prefix_case, byte_lt_here)?;
        let decide = arena.and(eq_prefix, decide_here)?;
        less = arena.or(less, decide)?;
        // Extend the equal-prefix flag: byte i is shared (both present) and equal.
        let beq = arena.eq(xb, yb)?;
        let shared_eq = arena.and(both, beq)?;
        eq_prefix = arena.and(eq_prefix, shared_eq)?;
    }
    Ok(less)
}

/// `str.<= x y` — `x < y ∨ x = y` (non-strict lexicographic order). Reuses
/// [`string_lt`] and [`string_equal`].
fn string_le(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    let lt = string_lt(arena, x, y)?;
    let eq = string_equal(arena, x, y)?;
    arena.or(lt, eq).map_err(SmtError::Ir)
}

/// The bytes and total length of a **constant** packed string argument, or
/// `None` if `arg` is not a string constant (so a mixed const/variable `str.++`
/// folds the constant runs and concatenates the variable spans symbolically).
fn string_const_bytes(arena: &TermArena, arg: TermId) -> Option<Vec<u8>> {
    let (width, value) = match arena.node(arg) {
        TermNode::BvConst { width, value } => (*width, *value),
        _ => return None,
    };
    let m = string_max_len_of(width)?;
    let lwm = len_width(m);
    let len = usize::try_from(value & ((1u128 << lwm) - 1)).ok()?;
    if len > m as usize {
        return None; // not well-formed as a string of this max length
    }
    let content = value >> lwm;
    let mut bytes = Vec::with_capacity(len);
    for i in 0..len {
        bytes.push(u8::try_from((content >> (8 * i)) & 0xff).expect("byte fits u8"));
    }
    Some(bytes)
}

/// `str.++` of two **packed-string** operands (constant or variable). Produces a
/// result in the wider sort `max_len(x) + max_len(y)` (capped at
/// `STRING_BOUND_CAP`), exactly like the API `BoundedString::concat`: the
/// result length is `len(x) + len(y)`, and the result content is
/// `content(x) | (content(y) << (len(x)·8))` with `x`'s padding masked off. So
/// the join never overflows the operand bound, and the result is a self-describing
/// packed string that the other `str.*` ops decide over. Over-`STRING_BOUND_CAP`
/// is a clean `Unsupported`.
#[allow(clippy::similar_names)] // len_x_r/len_y_r/len_x_c mirror the layout
fn string_concat_pair(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    let mx = string_max_len(arena, x)?;
    let my = string_max_len(arena, y)?;
    let rm = mx + my;
    if rm > STRING_BOUND_CAP {
        return Err(SmtError::Unsupported(format!(
            "str.++ result of bounded max length {rm} exceeds the cap {STRING_BOUND_CAP} \
             (ADR-0029); the query needs a larger string bound"
        )));
    }
    let rcw = rm * 8; // result content width
    let rlw = len_width(rm); // result length width

    let xlen = string_len_field(arena, x, mx)?;
    let ylen = string_len_field(arena, y, my)?;
    // result length = len_x + len_y, widened to the result's length width.
    let len_x_r = arena.zero_ext(rlw - len_width(mx), xlen)?;
    let len_y_r = arena.zero_ext(rlw - len_width(my), ylen)?;
    let rlen = arena.bv_add(len_x_r, len_y_r)?;

    // x content, repacked into the result's byte layout (low `mx` bytes).
    let mut xcontent: Option<TermId> = None;
    let zero8 = arena.bv_const(8, 0)?;
    for i in (0..rm).rev() {
        let byte = if i < mx {
            string_byte_m(arena, x, i, mx)?
        } else {
            zero8
        };
        xcontent = Some(match xcontent {
            None => byte,
            Some(acc) => arena.concat(acc, byte)?,
        });
    }
    let x_content_r = xcontent.expect("rm ≥ 1");

    // y content, repacked into the result's byte layout (low `my` bytes).
    let mut ycontent: Option<TermId> = None;
    for i in (0..rm).rev() {
        let byte = if i < my {
            string_byte_m(arena, y, i, my)?
        } else {
            zero8
        };
        ycontent = Some(match ycontent {
            None => byte,
            Some(acc) => arena.concat(acc, byte)?,
        });
    }
    let y_content_r = ycontent.expect("rm ≥ 1");

    // shift (in bits) for y = len_x * 8, in the result content width.
    let len_x_c = arena.zero_ext(rcw - len_width(mx), xlen)?;
    let three = arena.bv_const(rcw, 3)?; // *8
    let shift = arena.bv_shl(len_x_c, three)?;

    // mask x's content to its low len_x*8 bits (drop padding bytes).
    let one = arena.bv_const(rcw, 1)?;
    let pow = arena.bv_shl(one, shift)?; // 2^(len_x*8)
    let mask = arena.bv_sub(pow, one)?; // low len_x*8 ones
    let x_masked = arena.bv_and(x_content_r, mask)?;

    // place y after x.
    let y_shifted = arena.bv_shl(y_content_r, shift)?;
    let rcontent = arena.bv_or(x_masked, y_shifted)?;

    arena.concat(rcontent, rlen).map_err(SmtError::Ir)
}

/// `str.++` over `args`: left-fold [`string_concat_pair`]. A run of leading
/// constant operands is folded into one literal first (keeping the tight literal
/// width), then variable operands extend it pairwise. Zero operands is the empty
/// string; one operand is itself.
fn string_concat(arena: &mut TermArena, args: &[TermId]) -> Result<TermId, SmtError> {
    // Empty words are the two-sided identity. Remove them before width accounting
    // so `x ++ ""` stays exactly `x` instead of acquiring an artificial wider
    // packed sort (and so nested generated rewrites canonicalize structurally).
    let args: Vec<TermId> = args
        .iter()
        .copied()
        .filter(|&arg| !string_len_is_zero(arena, arg))
        .collect();
    if args.is_empty() {
        return pack_string_literal(arena, &[]);
    }
    if args.len() == 1 {
        return Ok(args[0]);
    }
    // Fold a leading constant prefix into a single literal (so `(str.++ "a" "b" v)`
    // does not pay for two concat layers before reaching the variable `v`).
    let mut idx = 0;
    let mut const_bytes: Vec<u8> = Vec::new();
    while idx < args.len() {
        if let Some(bytes) = string_const_bytes(arena, args[idx]) {
            const_bytes.extend_from_slice(&bytes);
            idx += 1;
        } else {
            break;
        }
    }
    let mut acc = if idx > 0 {
        // All-constant fast path keeps the exact-length literal (no width growth).
        if idx == args.len() {
            return pack_string_literal(arena, &const_bytes);
        }
        pack_string_literal(arena, &const_bytes)?
    } else {
        let first = args[0];
        // Validate it really is a packed string before folding.
        string_max_len(arena, first)?;
        idx = 1;
        first
    };
    for &arg in &args[idx..] {
        acc = string_concat_pair(arena, acc, arg)?;
    }
    Ok(acc)
}

/// Concatenates packed strings into a caller-proved result bound.
///
/// Unlike [`string_concat`], this does not sum the operands' independent static
/// maxima. The caller must have proved that the actual concatenated length is at
/// most `result_max`; active bytes are then copied and shifted exactly as in the
/// ordinary concatenation encoding. This is used only for syntactically exact
/// splice identities whose correlated substring lengths establish that bound.
fn string_concat_with_proved_bound(
    arena: &mut TermArena,
    args: &[TermId],
    result_max: u32,
) -> Result<TermId, SmtError> {
    let result_len_width = len_width(result_max);
    let result_content_width = result_max * 8;
    let mut result_len = arena.bv_const(result_len_width, 0)?;
    let mut result_content = arena.bv_const(result_content_width, 0)?;
    let shift_scale = arena.bv_const(result_content_width, 3)?;
    let zero_byte = arena.bv_const(8, 0)?;

    for &arg in args {
        let arg_max = string_max_len(arena, arg)?;
        let arg_len_width = len_width(arg_max);
        let arg_len = string_len_field(arena, arg, arg_max)?;
        let widened_len = match arg_len_width.cmp(&result_len_width) {
            std::cmp::Ordering::Less => {
                arena.zero_ext(result_len_width - arg_len_width, arg_len)?
            }
            std::cmp::Ordering::Equal => arg_len,
            std::cmp::Ordering::Greater => arena.extract(result_len_width - 1, 0, arg_len)?,
        };

        let mut packed_content: Option<TermId> = None;
        for index in (0..result_max).rev() {
            let byte = if index < arg_max {
                string_byte_m(arena, arg, index, arg_max)?
            } else {
                zero_byte
            };
            packed_content = Some(match packed_content {
                None => byte,
                Some(previous) => arena.concat(previous, byte)?,
            });
        }
        let packed_content = packed_content.expect("result_max is positive");
        let shift_len = arena.zero_ext(result_content_width - result_len_width, result_len)?;
        let shift = arena.bv_shl(shift_len, shift_scale)?;
        let shifted = arena.bv_shl(packed_content, shift)?;
        result_content = arena.bv_or(result_content, shifted)?;
        result_len = arena.bv_add(result_len, widened_len)?;
    }

    arena
        .concat(result_content, result_len)
        .map_err(SmtError::Ir)
}

/// Recognizes an exact fixed-position splice whose correlated substring lengths
/// keep the result within the base string's bound:
///
/// `substr(s, 0, i) ++ literal ++ substr(s, i+|literal|, len(s)-(i+|literal|))`.
///
/// For `L = len(s)`, the result length is
/// `min(L,i) + |literal| + max(L-i-|literal|,0)`, hence at most the base bound
/// whenever `i + |literal|` is within it. This includes the short-string cases;
/// it is not the simpler `str.update` identity, which would differ there.
fn fixed_splice_concat_bound(arena: &TermArena, items: &[SExpr], args: &[TermId]) -> Option<u32> {
    let split = fixed_splice_split(items)?;
    let result_max = string_max_len(arena, args[1]).ok()?;
    (split <= result_max).then_some(result_max)
}

/// Recognizes `PyEx`'s exact split/replace/rejoin spelling of a length-preserving
/// first-occurrence replacement:
///
/// `replace(substr(s,0,indexof(s,n,0)+1), n, r)
///    ++ substr(s,indexof(s,n,0)+1,len(s)-(indexof(s,n,0)+1))`.
///
/// For equal-length `n` and `r`, a found occurrence changes content but not
/// length. When `n` is absent, `indexof = -1`, the prefix is empty, and the
/// suffix is all of `s`. Thus the result always has exactly `len(s)` and fits in
/// the suffix/base bound even though independently summing the replace and
/// suffix maxima is much larger.
fn split_replace_rejoin_concat_bound(
    arena: &TermArena,
    items: &[SExpr],
    args: &[TermId],
) -> Option<u32> {
    split_replace_rejoin_base(items, &[])?;
    string_max_len(arena, args[1]).ok()
}

fn proved_concat_bound(
    arena: &TermArena,
    items: &[SExpr],
    args: &[TermId],
    admit_split_replace_rejoin: bool,
) -> Option<u32> {
    fixed_splice_concat_bound(arena, items, args).or_else(|| {
        admit_split_replace_rejoin
            .then(|| split_replace_rejoin_concat_bound(arena, items, args))
            .flatten()
    })
}

/// One exact generated fixed-position splice.
struct FixedSpliceParts<'a> {
    base: &'a SExpr,
    index: u32,
    replacement: Vec<u32>,
    split: u32,
}

/// Returns the split point of the exact fixed-splice shape recognized by both
/// the packed lowering and the UNSAT-only word abstraction.
fn fixed_splice_split(items: &[SExpr]) -> Option<u32> {
    Some(fixed_splice_parts(items)?.split)
}

/// Decomposes the fixed-splice shape into its base, replacement index/value, and
/// suffix split point.
fn fixed_splice_parts(items: &[SExpr]) -> Option<FixedSpliceParts<'_>> {
    let [head, left, right] = items else {
        return None;
    };
    if !matches!(head.atom(), Some("str.++" | "str.concat")) {
        return None;
    }
    let inner = left.list()?;
    let [inner_head, prefix_expr, replacement_expr] = inner else {
        return None;
    };
    if !matches!(inner_head.atom(), Some("str.++" | "str.concat")) {
        return None;
    }
    let prefix = prefix_expr.list()?;
    let suffix = right.list()?;
    if prefix.len() != 4
        || suffix.len() != 4
        || prefix[0].atom() != Some("str.substr")
        || suffix[0].atom() != Some("str.substr")
        || prefix[1] != suffix[1]
    {
        return None;
    }
    let prefix_start = parse_int_literal(strip_subtracted_zero(&prefix[2]))?;
    let prefix_len = u32::try_from(parse_int_literal(strip_subtracted_zero(&prefix[3]))?).ok()?;
    if prefix_start != 0 {
        return None;
    }
    let replacement = literal_pattern_cps(replacement_expr)?;
    if replacement
        .iter()
        .any(|&code_point| code_point > u32::from(u8::MAX))
    {
        return None;
    }
    let replacement_len = u32::try_from(replacement.len()).ok()?;
    let split = prefix_len.checked_add(replacement_len)?;
    let suffix_start = u32::try_from(parse_int_literal(strip_subtracted_zero(&suffix[2]))?).ok()?;
    if suffix_start != split || len_minus_constant(&suffix[3], &suffix[1])? != split {
        return None;
    }
    Some(FixedSpliceParts {
        base: &prefix[1],
        index: prefix_len,
        replacement,
        split,
    })
}

/// Guaranteed source-string consequences used by the UNSAT-only word skeleton.
#[derive(Default)]
struct SourceStringSemanticFacts {
    pinned_words: Vec<(SExpr, Vec<u32>)>,
    derived_equalities: Vec<(SExpr, SExpr)>,
    conflict: bool,
    eager_boolean_path_conflict: bool,
}

/// A bound-independent normal form for the small SMT-LIB rewrite language used
/// by the Noetzli string-rewrite corpus. Unknown terms stay structural; only
/// SMT-LIB total-function identities and fully-ground operations are folded.
/// Consequently equality of two normal forms proves equality in the unbounded
/// source theory and never depends on the packed-string implementation bound.
#[derive(Clone, Debug, PartialEq, Eq)]
enum ExactRewriteTerm {
    Bool(bool),
    Int(i128),
    String(Vec<u32>),
    IndexOfSelf(Box<ExactRewriteTerm>),
    Opaque(SExpr),
    App(String, Vec<ExactRewriteTerm>),
}

const EXACT_REWRITE_DEPTH_CAP: u32 = 64;

fn exact_rewrite_term(expression: &SExpr, depth: u32) -> ExactRewriteTerm {
    if depth > EXACT_REWRITE_DEPTH_CAP {
        return ExactRewriteTerm::Opaque(expression.clone());
    }
    if let Some(value) = literal_pattern_cps(expression) {
        return ExactRewriteTerm::String(value);
    }
    if let Some(atom) = expression.atom() {
        return match atom {
            "true" => ExactRewriteTerm::Bool(true),
            "false" => ExactRewriteTerm::Bool(false),
            _ => atom.parse::<i128>().map_or_else(
                |_| ExactRewriteTerm::Opaque(expression.clone()),
                ExactRewriteTerm::Int,
            ),
        };
    }
    let Some(items) = expression.list() else {
        return ExactRewriteTerm::Opaque(expression.clone());
    };
    let Some(head) = items.first().and_then(SExpr::atom) else {
        return ExactRewriteTerm::Opaque(expression.clone());
    };
    if let Some(rewritten) = exact_rewrite_prefixed_self_needle(items) {
        return rewritten;
    }
    if let Some(rewritten) = exact_rewrite_self_replacement_view(items, depth + 1) {
        return rewritten;
    }
    if let Some(rewritten) = exact_rewrite_head_totality_view(items, depth + 1) {
        return rewritten;
    }
    if let Some(rewritten) = exact_rewrite_one_code_point_replace_view(items, depth + 1) {
        return rewritten;
    }
    if let Some(rewritten) = exact_rewrite_one_code_point_deletion_view(items, depth + 1) {
        return rewritten;
    }
    let args: Vec<_> = items[1..]
        .iter()
        .map(|arg| exact_rewrite_term(arg, depth + 1))
        .collect();
    let rewritten = exact_rewrite_app(head, args);
    if head == "not"
        && let Some(value) = exact_boolean_constant(&rewritten)
    {
        return ExactRewriteTerm::Bool(value);
    }
    rewritten
}

/// Rewrites the exact one-code-point identities
/// `replace(c ++ x, x, "") = c` and `replace(c ++ x, x, c) = c ++ c`.
///
/// If the leftmost occurrence of nonempty `x` begins inside the one-code-point
/// prefix, `x` must be a nonempty power of `c`; replacing that occurrence has
/// the same result as replacing the explicit suffix occurrence. Empty `x` is
/// the SMT-LIB insertion-at-zero case and yields the same two results.
fn exact_rewrite_prefixed_self_needle(items: &[SExpr]) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::String;

    if items.first()?.atom() != Some("str.replace") || items.len() != 4 {
        return None;
    }
    let concat = items[1].list()?;
    if concat.len() != 3 || concat[0].atom() != Some("str.++") || concat[2] != items[2] {
        return None;
    }
    let prefix = literal_pattern_cps(&concat[1])?;
    if prefix.len() != 1 {
        return None;
    }
    let replacement = literal_pattern_cps(&items[3])?;
    if replacement.is_empty() {
        return Some(String(prefix));
    }
    if replacement == prefix {
        return Some(String(prefix.repeat(2)));
    }
    None
}

/// Preserves equality and word-boundary observations of replacing a factor by
/// the whole source. The raw shape is required because normalizing the inner
/// replacement first expands its empty-needle case into a decision tree.
fn exact_rewrite_self_replacement_view(items: &[SExpr], depth: u32) -> Option<ExactRewriteTerm> {
    let head = items.first()?.atom()?;
    if !matches!(head, "=" | "str.prefixof" | "str.suffixof" | "str.contains") || items.len() != 3 {
        return None;
    }
    for (replacement_index, other_index) in [(1, 2), (2, 1)] {
        let Some(replacement) = items[replacement_index].list() else {
            continue;
        };
        if replacement.len() != 4
            || replacement[0].atom() != Some("str.replace")
            || replacement[1] != replacement[3]
        {
            continue;
        }
        let subject = exact_rewrite_term(&replacement[1], depth);
        let needle = exact_rewrite_term(&replacement[2], depth);
        let other = exact_rewrite_term(&items[other_index], depth);
        if other != needle {
            continue;
        }
        let mut args = [
            exact_rewrite_term(&items[1], depth),
            exact_rewrite_term(&items[2], depth),
        ];
        args[replacement_index - 1] = subject;
        return Some(exact_rewrite_app(head, args.into()));
    }
    None
}

/// Canonicalizes head observations using unbounded SMT-LIB total-function
/// identities before inner terms can expand into unrelated decision trees.
fn exact_rewrite_head_totality_view(items: &[SExpr], depth: u32) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::Int;

    if items.first()?.atom() == Some("str.substr")
        && items.len() == 4
        && exact_rewrite_term(&items[2], depth) == Int(0)
        && let Some(at) = items[1].list()
        && at.len() == 3
        && at[0].atom() == Some("str.at")
    {
        let subject = exact_rewrite_term(&at[1], depth);
        let index = exact_rewrite_term(&at[2], depth);
        let length = exact_rewrite_term(&items[3], depth);
        return Some(exact_rewrite_app(
            "str.at",
            vec![
                exact_rewrite_app("str.substr", vec![subject, index, length]),
                Int(0),
            ],
        ));
    }
    if items.first()?.atom() == Some("str.replace")
        && items.len() == 4
        && literal_pattern_cps(&items[3]).is_some_and(|replacement| replacement.is_empty())
        && let Some(at) = items[2].list()
        && at.len() == 3
        && at[0].atom() == Some("str.at")
        && at[1] == items[1]
        && exact_rewrite_term(&at[2], depth) == Int(0)
    {
        let subject = exact_rewrite_term(&items[1], depth);
        return Some(exact_rewrite_app(
            "str.substr",
            vec![
                subject.clone(),
                Int(1),
                exact_rewrite_app("str.len", vec![subject]),
            ],
        ));
    }
    if items.first()?.atom() == Some("str.at")
        && items.len() == 3
        && exact_rewrite_term(&items[2], depth) == Int(0)
        && let Some(replace) = items[1].list()
        && replace.len() == 4
        && replace[0].atom() == Some("str.replace")
    {
        let subject = exact_rewrite_term(&replace[1], depth);
        let needle = exact_rewrite_term(&replace[2], depth);
        let replacement = exact_rewrite_term(&replace[3], depth);
        let exact_one_code_point = |term: &ExactRewriteTerm| {
            exact_string_min_len(term, 0) == Some(1) && exact_string_max_len(term, 0) == Some(1)
        };
        if exact_one_code_point(&needle) && exact_one_code_point(&replacement) {
            return Some(exact_rewrite_app(
                "str.replace",
                vec![
                    exact_rewrite_app("str.at", vec![subject, Int(0)]),
                    needle,
                    replacement,
                ],
            ));
        }
    }
    None
}

/// Canonicalizes exact views whose inner one-code-point replacement would
/// otherwise expand to a differently ordered `ite` tree before the outer view
/// can recognize it. Every case is an unbounded SMT-LIB total-function law.
fn exact_rewrite_singleton_prefix_replace_view(
    items: &[SExpr],
    depth: u32,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{Bool, String};

    if items.first()?.atom() != Some("str.prefixof") || items.len() != 3 {
        return None;
    }
    let probe = literal_pattern_cps(&items[1])?;
    let replace = items[2].list()?;
    let (Some(needle), Some(replacement)) = (
        replace.get(2).and_then(literal_pattern_cps),
        replace.get(3).and_then(literal_pattern_cps),
    ) else {
        return None;
    };
    if probe.len() != 1
        || replace.len() != 4
        || replace[0].atom() != Some("str.replace")
        || needle.len() != 1
        || replacement.len() != 1
        || needle == replacement
    {
        return None;
    }
    let source = exact_rewrite_term(&replace[1], depth);
    let probe = String(probe);
    let needle = String(needle);
    let replacement = String(replacement);
    if probe == needle {
        // The first needle code point, if any, is replaced; an earlier source
        // head therefore cannot be the needle either.
        return Some(Bool(false));
    }
    if probe == replacement {
        // The replacement code point heads the result exactly when it or the
        // replaced needle headed the source.
        return Some(exact_rewrite_app(
            "or",
            vec![
                exact_rewrite_app("str.prefixof", vec![needle, source.clone()]),
                exact_rewrite_app("str.prefixof", vec![replacement, source]),
            ],
        ));
    }
    Some(exact_rewrite_app("str.prefixof", vec![probe, source]))
}

fn exact_rewrite_one_code_point_replace_view(
    items: &[SExpr],
    depth: u32,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{Int, String};

    let exact_one_code_point = |term: &ExactRewriteTerm| {
        exact_string_min_len(term, 0) == Some(1) && exact_string_max_len(term, 0) == Some(1)
    };
    if let Some(rewritten) = exact_rewrite_singleton_prefix_replace_view(items, depth) {
        return Some(rewritten);
    }
    if items.first()?.atom() == Some("str.substr") && items.len() == 4 {
        let subject = exact_rewrite_term(&items[1], depth);
        let offset = exact_rewrite_term(&items[2], depth);
        let length = exact_rewrite_term(&items[3], depth);
        if let Some(replace) = items[1].list()
            && replace.len() == 4
            && replace[0].atom() == Some("str.replace")
        {
            let base = exact_rewrite_term(&replace[1], depth);
            let needle = exact_rewrite_term(&replace[2], depth);
            let replacement = exact_rewrite_term(&replace[3], depth);
            if exact_one_code_point(&base) && exact_one_code_point(&replacement) {
                // Replacing in a one-code-point base yields `replacement+base`
                // for an empty needle and at most one code point otherwise.
                if offset == Int(1) {
                    return Some(exact_rewrite_app(
                        "str.substr",
                        vec![base, exact_rewrite_app("str.len", vec![needle]), length],
                    ));
                }
                // At equal start/length, the only nonempty case is start one
                // after an empty needle, which selects the original base.
                if offset == length {
                    return Some(exact_rewrite_app(
                        "ite",
                        vec![
                            exact_rewrite_app(
                                "and",
                                vec![
                                    exact_rewrite_app("=", vec![offset, Int(1)]),
                                    exact_rewrite_app("=", vec![needle, String(Vec::new())]),
                                ],
                            ),
                            base,
                            String(Vec::new()),
                        ],
                    ));
                }
            }
        }
        if offset == Int(0)
            && let Some(indexof) = items[3].list()
            && indexof.len() == 4
            && indexof[0].atom() == Some("str.indexof")
        {
            let probe = exact_rewrite_term(&indexof[1], depth);
            let needle = exact_rewrite_term(&indexof[2], depth);
            let start = exact_rewrite_term(&indexof[3], depth);
            if exact_one_code_point(&subject) && exact_one_code_point(&probe) {
                // `indexof(one, needle, start)` supplies a positive substring
                // length exactly when `start=1` and `needle` is empty.
                return Some(exact_rewrite_app(
                    "ite",
                    vec![
                        exact_rewrite_app(
                            "and",
                            vec![
                                exact_rewrite_app("=", vec![start, Int(1)]),
                                exact_rewrite_app("=", vec![needle, String(Vec::new())]),
                            ],
                        ),
                        subject,
                        String(Vec::new()),
                    ],
                ));
            }
        }
    }
    if items.first()?.atom() == Some("str.replace")
        && items.len() == 4
        && literal_pattern_cps(&items[1]).is_some_and(|subject| subject.is_empty())
        && let Some(inner) = items[2].list()
        && inner.len() == 4
        && inner[0].atom() == Some("str.replace")
        && literal_pattern_cps(&inner[3]).is_some_and(|replacement| replacement.is_empty())
    {
        let source = exact_rewrite_term(&inner[1], depth);
        let needle = exact_rewrite_term(&inner[2], depth);
        let replacement = exact_rewrite_term(&items[3], depth);
        if exact_one_code_point(&needle) && exact_one_code_point(&replacement) {
            // Removing one code point makes `source` empty exactly when source
            // is empty or that code point. This is the same condition under
            // which it occurs as a needle in the one-code-point probe.
            return Some(exact_rewrite_app(
                "str.at",
                vec![
                    replacement,
                    exact_rewrite_app("str.indexof", vec![needle, source, Int(0)]),
                ],
            ));
        }
    }
    None
}

/// Canonicalizes boundary observations of deleting one exact code point. The
/// raw shape is required because rewriting the inner replacement first would
/// hide the correlation between its needle and the outer observation.
fn exact_rewrite_one_code_point_deletion_view(
    items: &[SExpr],
    depth: u32,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::String;

    let head = items.first()?.atom()?;
    if !matches!(head, "str.prefixof" | "str.suffixof") || items.len() != 3 {
        return None;
    }
    let boundary = exact_rewrite_term(&items[1], depth);
    let replace = items[2].list()?;
    if replace.len() != 4 || replace[0].atom() != Some("str.replace") {
        return None;
    }
    let subject = exact_rewrite_term(&replace[1], depth);
    let needle = exact_rewrite_term(&replace[2], depth);
    let replacement = exact_rewrite_term(&replace[3], depth);
    if head == "str.suffixof"
        && boundary == needle
        && exact_string_min_len(&needle, 0) == Some(1)
        && exact_string_max_len(&needle, 0) == Some(1)
        && exact_string_min_len(&replacement, 0) == Some(1)
        && exact_string_max_len(&replacement, 0) == Some(1)
        && exact_string_alphabets_disjoint(&needle, &replacement)
    {
        return Some(exact_rewrite_app(
            "str.suffixof",
            vec![
                boundary,
                exact_rewrite_app("str.replace", vec![subject, needle, String(Vec::new())]),
            ],
        ));
    }
    if !matches!(replacement, String(word) if word.is_empty()) {
        return None;
    }
    if head == "str.prefixof"
        && boundary == needle
        && exact_string_min_len(&needle, 0) == Some(1)
        && exact_string_max_len(&needle, 0) == Some(1)
    {
        return Some(exact_rewrite_app(
            "str.prefixof",
            vec![exact_rewrite_concat(&[needle.clone(), needle]), subject],
        ));
    }
    if boundary == needle
        && exact_string_min_len(&subject, 0) == Some(1)
        && exact_string_max_len(&subject, 0) == Some(1)
    {
        return Some(exact_rewrite_equality(&needle, &String(Vec::new())));
    }
    None
}

#[allow(clippy::too_many_lines)] // One explicit allow-list of exact SMT-LIB identities.
fn exact_rewrite_app(head: &str, args: Vec<ExactRewriteTerm>) -> ExactRewriteTerm {
    use ExactRewriteTerm::{App, Bool, IndexOfSelf, Int, String};

    match (head, args.as_slice()) {
        ("not", [Bool(value)]) => return Bool(!value),
        ("not", [App(inner, inner_args)])
            if inner == "not" && matches!(inner_args.as_slice(), [_]) =>
        {
            return inner_args[0].clone();
        }
        ("=", [left, right]) if left == right => return Bool(true),
        ("=", [Bool(left), Bool(right)]) => return Bool(left == right),
        ("=", [Int(left), Int(right)]) => return Bool(left == right),
        ("=", [String(left), String(right)]) => return Bool(left == right),
        ("=", [left, right])
            if exact_string_alphabets_disjoint(left, right)
                && (exact_string_min_len(left, 0).is_some_and(|length| length > 0)
                    || exact_string_min_len(right, 0).is_some_and(|length| length > 0)) =>
        {
            return Bool(false);
        }
        ("=", [left, right]) => return exact_rewrite_equality(left, right),
        ("ite", [Bool(true), then_term, _]) => return then_term.clone(),
        ("ite", [Bool(false), _, else_term]) => return else_term.clone(),
        ("ite", [_, then_term, else_term]) if then_term == else_term => return then_term.clone(),
        ("ite", [condition, Bool(true), Bool(false)]) => return condition.clone(),
        ("ite", [condition, Bool(false), Bool(true)]) => {
            return exact_rewrite_app("not", vec![condition.clone()]);
        }
        ("ite", [condition, App(inner, inner_args), else_term])
            if inner == "ite"
                && matches!(inner_args.as_slice(), [inner_condition, _, _]
                    if inner_condition == condition) =>
        {
            return exact_rewrite_app(
                "ite",
                vec![condition.clone(), inner_args[1].clone(), else_term.clone()],
            );
        }
        ("ite", [condition, then_term, App(inner, inner_args)])
            if inner == "ite"
                && matches!(inner_args.as_slice(), [inner_condition, _, _]
                    if inner_condition == condition) =>
        {
            return exact_rewrite_app(
                "ite",
                vec![condition.clone(), then_term.clone(), inner_args[2].clone()],
            );
        }
        ("-", [Int(value)]) => {
            if let Some(value) = value.checked_neg() {
                return Int(value);
            }
        }
        ("-", [left, right]) if left == right => return Int(0),
        ("-", [Int(left), Int(right)]) => {
            if let Some(value) = left.checked_sub(*right) {
                return Int(value);
            }
        }
        ("+", values) => return exact_rewrite_sum(values),
        ("-", [left, Int(0)]) => return left.clone(),
        ("*", values) if values.iter().all(|value| matches!(value, Int(_))) => {
            if let Some(value) = values
                .iter()
                .try_fold(1_i128, |product, value| match value {
                    Int(value) => product.checked_mul(*value),
                    _ => None,
                })
            {
                return Int(value);
            }
        }
        ("<", [Int(left), Int(right)]) => return Bool(left < right),
        ("<=", [Int(left), Int(right)]) => return Bool(left <= right),
        (">", [Int(left), Int(right)]) => return Bool(left > right),
        (">=", [Int(left), Int(right)]) => return Bool(left >= right),
        ("<", [left, right]) | (">", [right, left]) if left == right => return Bool(false),
        ("<=", [left, right]) | (">=", [right, left]) if left == right => return Bool(true),
        ("and", values) => return exact_rewrite_boolean_nary("and", values),
        ("or", values) => return exact_rewrite_boolean_nary("or", values),
        ("str.++" | "seq.++", values) => return exact_rewrite_concat(values),
        ("str.len" | "seq.len", [String(value)]) => {
            if let Ok(length) = i128::try_from(value.len()) {
                return Int(length);
            }
        }
        ("str.from_int", [Int(value)]) => return String(decimal_code_points(*value)),
        ("str.from_int", [IndexOfSelf(offset)]) => {
            // `indexof(x,x,i)` is zero exactly at `i = 0` and `-1`
            // otherwise. `from_int` therefore spells the same one-code-point
            // view as indexing the decimal word `"0"` at `i`.
            return exact_rewrite_app(
                "str.at",
                vec![String(vec![u32::from(b'0')]), *offset.clone()],
            );
        }
        ("str.to_int", [String(value)]) => {
            if let Some(integer) = to_int_of_code_points(value) {
                return Int(integer);
            }
        }
        ("str.substr", [String(value), Int(offset), Int(length)]) => {
            return String(substr_code_points(value, *offset, *length));
        }
        ("str.substr", [App(from_int, from_int_args), offset, length])
            if from_int == "str.from_int"
                && matches!(from_int_args.as_slice(), [value]
                    if value == offset && value == length) =>
        {
            // Negative values produce the empty word. Zero requests length
            // zero. Every positive integer has at most that many decimal
            // digits, so starting at the integer itself is out of range.
            return String(Vec::new());
        }
        ("str.substr", [_, _, _])
            if args.iter().any(exact_is_ite)
                && args.iter().map(exact_ite_count).sum::<u32>() <= 6 =>
        {
            return exact_distribute_app_ite(head, &args)
                .expect("a bounded ite argument must distribute");
        }
        // `if let` guards are unstable (>MSRV 1.88); use a boolean guard + recompute
        // so the arm still falls through to later arms when the rewrite is None.
        ("str.substr", [subject, offset, length])
            if exact_rewrite_concat_substr(subject, offset, length).is_some() =>
        {
            return exact_rewrite_concat_substr(subject, offset, length)
                .expect("guard just checked is_some");
        }
        ("str.substr", [_, Int(offset), _]) if *offset < 0 => return String(Vec::new()),
        ("str.substr", [_, _, Int(length)]) if *length <= 0 => return String(Vec::new()),
        ("str.substr", [String(value), Int(offset), _])
            if usize::try_from(*offset).map_or(true, |offset| offset >= value.len()) =>
        {
            return String(Vec::new());
        }
        ("str.substr", [String(value), _, _]) if value.is_empty() => {
            return String(Vec::new());
        }
        ("str.substr", [subject, App(indexof, index_args), length])
            if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1)
                && indexof == "str.indexof"
                && matches!(index_args.as_slice(), [_, _, index_offset]
                    if index_offset == length) =>
        {
            // A nonnegative `indexof` result is at least its start. At start
            // zero the requested length is zero; above zero the result starts
            // beyond a one-code-point word. Negative starts return `-1`.
            return String(Vec::new());
        }
        ("str.substr", [subject, App(indexof, index_args), _])
            if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1)
                && indexof == "str.indexof"
                && matches!(index_args.as_slice(), [_, _, Int(index_offset)]
                    if *index_offset >= 1) =>
        {
            return String(Vec::new());
        }
        ("str.substr", [String(value), offset, length]) if value.len() <= 1 && offset == length => {
            return String(Vec::new());
        }
        ("str.substr", [subject, App(indexof, index_args), offset])
            if indexof == "str.indexof"
                && matches!(index_args.as_slice(), [_, String(needle), index_offset]
                    if needle.is_empty() && index_offset == offset) =>
        {
            // `indexof(s,"",i)` is either `i` or `-1`. In the first case the
            // two views are identical; in the second one has a negative start
            // and the other a negative length, so both are empty.
            return exact_rewrite_app(
                "str.substr",
                vec![
                    subject.clone(),
                    offset.clone(),
                    App(indexof.clone(), index_args.clone()),
                ],
            );
        }
        ("str.substr", [subject, offset, App(indexof, index_args)])
            if indexof == "str.indexof"
                && matches!(index_args.as_slice(), [index_subject, String(needle), index_offset]
                    if index_subject == subject && needle.is_empty() && index_offset == offset) =>
        {
            return exact_rewrite_app(
                "str.substr",
                vec![subject.clone(), offset.clone(), offset.clone()],
            );
        }
        ("str.substr", [subject, offset, App(indexof, index_args)])
            if indexof == "str.indexof"
                && matches!(index_args.as_slice(), [index_subject, String(needle), Int(1)]
                    if index_subject == subject && needle.is_empty()) =>
        {
            // `indexof(subject,"",1)` is one exactly when `subject` is
            // nonempty and `-1` otherwise, so this is the one-code-point view
            // at `offset` in both cases.
            return exact_rewrite_app("str.at", vec![subject.clone(), offset.clone()]);
        }
        ("str.substr", [subject, offset, App(indexof, index_args)])
            if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1)
                && indexof == "str.indexof"
                && matches!(index_args.as_slice(), [_, String(needle), Int(1)]
                    if needle.is_empty()) =>
        {
            return exact_rewrite_app(
                "str.substr",
                vec![
                    subject.clone(),
                    offset.clone(),
                    exact_rewrite_app("str.len", vec![index_args[0].clone()]),
                ],
            );
        }
        ("str.substr", [subject, Int(1), App(indexof, index_args)])
            if indexof == "str.indexof"
                && matches!(index_args.as_slice(), [_, String(needle), Int(1)]
                    if needle.is_empty()) =>
        {
            return exact_rewrite_app(
                "str.at",
                vec![subject.clone(), App(indexof.clone(), index_args.clone())],
            );
        }
        ("str.substr", [subject, offset, length])
            if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1)
                && exact_affine_zero_forces_nonpositive(offset, length) =>
        {
            return String(Vec::new());
        }
        ("str.substr", [subject, offset, length])
            if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1)
                && exact_affine_zero_forces_positive(offset, length) =>
        {
            return exact_rewrite_app("str.at", vec![subject.clone(), offset.clone()]);
        }
        ("str.substr", [String(value), offset, length]) if value.len() == 1 => {
            let in_range = exact_rewrite_app(
                "and",
                vec![
                    exact_rewrite_app("=", vec![offset.clone(), Int(0)]),
                    exact_positive_substring_length_condition(length),
                ],
            );
            return exact_rewrite_app(
                "ite",
                vec![in_range, String(value.clone()), String(Vec::new())],
            );
        }
        ("str.substr", [App(inner, inner_args), Int(0), length])
            if inner == "str.substr"
                && matches!(inner_args.as_slice(), [_, _, inner_length] if inner_length == length) =>
        {
            return App(inner.clone(), inner_args.clone());
        }
        ("str.substr", [subject, Int(0), App(length, length_args)])
            if length == "str.len"
                && matches!(length_args.as_slice(), [length_subject] if length_subject == subject) =>
        {
            return subject.clone();
        }
        ("str.substr", [subject, offset, length])
            if exact_substr_is_empty(subject, offset, length) =>
        {
            return String(Vec::new());
        }
        ("str.substr", [subject, App(indexof, index_args), length])
            if indexof == "str.indexof"
                && matches!(index_args.as_slice(), [index_subject, String(needle), _offset]
                    if index_subject == subject && needle.is_empty()) =>
        {
            return exact_rewrite_app(
                "str.substr",
                vec![subject.clone(), index_args[2].clone(), length.clone()],
            );
        }
        ("str.substr", [subject, offset, Int(1)]) => {
            return App("str.at".to_owned(), vec![subject.clone(), offset.clone()]);
        }
        ("str.at", [String(value), Int(index)]) => {
            let result = usize::try_from(*index)
                .ok()
                .and_then(|index| value.get(index).copied())
                .map_or_else(Vec::new, |code_point| vec![code_point]);
            return String(result);
        }
        ("str.at", [subject, App(indexof, index_args)])
            if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1)
                && indexof == "str.indexof"
                && matches!(index_args.as_slice(), [_, _, Int(index_offset)]
                    if *index_offset >= 1) =>
        {
            return String(Vec::new());
        }
        ("str.at", [subject, App(indexof, index_args)])
            if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1)
                && indexof == "str.indexof"
                && matches!(index_args.as_slice(), [_, String(needle), _]
                    if needle.is_empty()) =>
        {
            return exact_rewrite_app("str.at", vec![subject.clone(), index_args[2].clone()]);
        }
        ("str.at", [_, _])
            if args.iter().any(exact_is_ite)
                && args.iter().map(exact_ite_count).sum::<u32>() <= 6 =>
        {
            return exact_distribute_app_ite(head, &args)
                .expect("a bounded ite argument must distribute");
        }
        // `if let` guard is unstable (>MSRV 1.88); boolean guard + recompute so the
        // arm still falls through to later arms when the rewrite is None.
        ("str.at", [subject, index]) if exact_rewrite_concat_at(subject, index).is_some() => {
            return exact_rewrite_concat_at(subject, index).expect("guard just checked is_some");
        }
        ("str.at", [String(value), _]) if value.is_empty() => return String(Vec::new()),
        ("str.at", [subject, IndexOfSelf(offset)])
            if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1) =>
        {
            return exact_rewrite_app("str.at", vec![subject.clone(), *offset.clone()]);
        }
        ("str.at", [subject, IndexOfSelf(offset)]) => {
            return exact_rewrite_app(
                "str.at",
                vec![
                    exact_rewrite_app("str.at", vec![subject.clone(), *offset.clone()]),
                    *offset.clone(),
                ],
            );
        }
        ("str.at", [App(from_int, from_int_args), index])
            if from_int == "str.from_int"
                && matches!(from_int_args.as_slice(), [value] if value == index) =>
        {
            // For a nonnegative integer `i`, its decimal representation has
            // at most `i` code points unless `i = 0`; negative inputs produce
            // the empty word. Thus only index zero can return a code point.
            return exact_rewrite_app("str.at", vec![String(vec![u32::from(b'0')]), index.clone()]);
        }
        ("str.at", [App(inner, inner_args), index])
            if inner == "str.at"
                && index != &Int(0)
                && matches!(inner_args.as_slice(), [_, inner_index] if inner_index == index) =>
        {
            return exact_rewrite_app(
                "str.at",
                vec![
                    exact_rewrite_app("str.at", vec![inner_args[0].clone(), Int(0)]),
                    index.clone(),
                ],
            );
        }
        ("str.at", [String(value), index]) if value.len() == 1 => {
            let in_range = exact_rewrite_app("=", vec![index.clone(), Int(0)]);
            return exact_rewrite_app(
                "ite",
                vec![in_range, String(value.clone()), String(Vec::new())],
            );
        }
        ("str.at", [App(inner, inner_args), Int(0)])
            if inner == "str.at" && inner_args.len() == 2 =>
        {
            return App(inner.clone(), inner_args.clone());
        }
        ("str.at", [self_replacement, Int(0)]) => {
            if let Some((subject, _)) = exact_self_replacement(self_replacement) {
                // Replacing a factor of `subject` by all of `subject` preserves
                // its first code point, including the empty-word case.
                return exact_rewrite_app("str.at", vec![subject.clone(), Int(0)]);
            }
        }
        ("str.at", [App(inner, _), Int(index)]) if inner == "str.at" && *index >= 1 => {
            return String(Vec::new());
        }
        ("str.at", [subject, index]) if exact_view_index_is_out_of_range(subject, index) => {
            return String(Vec::new());
        }
        ("str.at", [subject, App(indexof, index_args)])
            if indexof == "str.indexof"
                && matches!(index_args.as_slice(), [index_subject, String(needle), _]
                    if index_subject == subject && needle.is_empty()) =>
        {
            return exact_rewrite_app("str.at", vec![subject.clone(), index_args[2].clone()]);
        }
        ("str.indexof", [subject, needle]) => {
            if let Some(index) = exact_rewrite_indexof(subject, needle, Some(0)) {
                return Int(index);
            }
            if let String(subject) = subject
                && subject.len() <= 1
            {
                return exact_rewrite_small_subject_indexof(subject, needle, &Int(0));
            }
        }
        ("str.indexof", [subject, needle, offset]) => {
            if subject == needle {
                return match offset {
                    Int(0) => Int(0),
                    Int(_) => Int(-1),
                    offset => IndexOfSelf(Box::new(offset.clone())),
                };
            }
            let offset = match offset {
                Int(offset) => Some(*offset),
                _ => None,
            };
            if let Some(index) = exact_rewrite_indexof(subject, needle, offset) {
                return Int(index);
            }
            if let String(subject) = subject
                && subject.len() <= 1
            {
                return exact_rewrite_small_subject_indexof(subject, needle, &args[2]);
            }
        }
        ("str.replace", [subject, needle, replacement]) => {
            if let Some((expanded_needle, inner_subject)) = exact_self_replacement(needle)
                && inner_subject == subject
            {
                // `replace(x, replace(y, x, y), r) = replace(x, y, r)`.
                // If `y` occurs in `x`, then `x` cannot occur properly in `y`,
                // so the inner replacement is `y`. If `y` does not occur in
                // `x`, the inner result still contains `y` and therefore also
                // cannot occur in `x`. Both outer replacements take the same
                // first-occurrence branch, including the empty-word cases.
                return exact_rewrite_app(
                    "str.replace",
                    vec![
                        subject.clone(),
                        expanded_needle.clone(),
                        replacement.clone(),
                    ],
                );
            }
            if subject == needle {
                return replacement.clone();
            }
            if needle == replacement {
                return subject.clone();
            }
            if matches!(subject, String(value) if value.is_empty())
                && let App(concat, parts) = needle
                && matches!(concat.as_str(), "str.++" | "seq.++")
                && parts.contains(replacement)
            {
                // If the concatenated needle is empty, every component—and
                // therefore the selected replacement—is empty. Otherwise a
                // nonempty needle cannot occur in the empty subject. Both
                // branches return the empty word.
                return String(Vec::new());
            }
            if matches!(needle, String(value) if value.is_empty()) {
                return exact_rewrite_concat(&[replacement.clone(), subject.clone()]);
            }
            if exact_string_alphabets_disjoint(subject, needle)
                && (exact_string_min_len(needle, 0).is_some_and(|length| length > 0)
                    || matches!(replacement, String(value) if value.is_empty()))
            {
                return subject.clone();
            }
            if let (String(subject), String(needle)) = (subject, needle)
                && !needle.is_empty()
                && !subject
                    .windows(needle.len())
                    .any(|candidate| candidate == needle)
            {
                return String(subject.clone());
            }
            if let (String(subject), String(needle), String(replacement)) =
                (subject, needle, replacement)
            {
                return String(replace_first_code_points(subject, needle, replacement));
            }
            if let Some(rewritten) =
                exact_rewrite_concat_subject_replace(subject, needle, replacement)
            {
                return rewritten;
            }
            if let String(subject) = subject
                && subject.len() <= 1
            {
                return exact_rewrite_small_subject_replace(subject, needle, replacement);
            }
            if let Some(distributed) = exact_distribute_app_ite(head, &args) {
                return distributed;
            }
            // If the needle is at least as long as the subject, its only possible
            // occurrence is the whole subject. Preserve both branches explicitly.
            if exact_string_length_le(subject, needle, 0) {
                return exact_rewrite_app(
                    "ite",
                    vec![
                        exact_rewrite_equality(subject, needle),
                        replacement.clone(),
                        subject.clone(),
                    ],
                );
            }
        }
        ("str.prefixof", [left, right]) => {
            if left == right || matches!(left, String(value) if value.is_empty()) {
                return Bool(true);
            }
            if let (String(left), String(right)) = (left, right) {
                return Bool(right.starts_with(left));
            }
            if exact_prefix_view(left, right) {
                return Bool(true);
            }
            if exact_string_max_len(left, 0).is_some_and(|maximum| maximum <= 1)
                && let Some((subject, _)) = exact_self_replacement(right)
            {
                // The replacement result contains `subject` and introduces no
                // new code points, so its one-code-point boundary is unchanged.
                return exact_rewrite_app("str.prefixof", vec![left.clone(), subject.clone()]);
            }
            if let Some(rewritten) = exact_rewrite_concat_prefix(left, right) {
                return rewritten;
            }
            if exact_string_min_len(left, 0).is_some_and(|length| length > 0)
                && exact_string_alphabets_disjoint(left, right)
            {
                return Bool(false);
            }
            if exact_string_length_le(right, left, 0) {
                return exact_rewrite_equality(left, right);
            }
            if matches!(left, String(word) if word.len() == 1) {
                return exact_rewrite_equality(
                    &exact_rewrite_app("str.at", vec![right.clone(), Int(0)]),
                    left,
                );
            }
            if !exact_is_ite(left)
                && exact_string_max_len(right, 0).is_some_and(|maximum| maximum <= 1)
            {
                let empty = String(Vec::new());
                return exact_rewrite_app(
                    "or",
                    vec![
                        exact_rewrite_equality(left, &empty),
                        exact_rewrite_equality(left, right),
                    ],
                );
            }
            if let String(word) = right
                && let Some(rewritten) =
                    exact_rewrite_fixed_word_language(word, left, ExactFixedWordLanguage::Prefixes)
            {
                return rewritten;
            }
        }
        ("str.suffixof", [left, right]) => {
            if left == right || matches!(left, String(value) if value.is_empty()) {
                return Bool(true);
            }
            if let (String(left), String(right)) = (left, right) {
                return Bool(right.ends_with(left));
            }
            if exact_suffix_view(left, right) {
                return Bool(true);
            }
            if exact_string_max_len(left, 0).is_some_and(|maximum| maximum <= 1)
                && let Some((subject, _)) = exact_self_replacement(right)
            {
                return exact_rewrite_app("str.suffixof", vec![left.clone(), subject.clone()]);
            }
            if let Some(rewritten) = exact_rewrite_concat_suffix(left, right) {
                return rewritten;
            }
            if exact_string_min_len(left, 0).is_some_and(|length| length > 0)
                && exact_string_alphabets_disjoint(left, right)
            {
                return Bool(false);
            }
            if exact_string_length_le(right, left, 0) {
                return exact_rewrite_equality(left, right);
            }
            if exact_string_max_len(right, 0).is_some_and(|maximum| maximum <= 1) {
                return exact_rewrite_app("str.prefixof", vec![left.clone(), right.clone()]);
            }
            if let String(word) = right
                && let Some(rewritten) =
                    exact_rewrite_fixed_word_language(word, left, ExactFixedWordLanguage::Suffixes)
            {
                return rewritten;
            }
        }
        ("str.contains", [subject, needle]) => {
            if subject == needle || matches!(needle, String(value) if value.is_empty()) {
                return Bool(true);
            }
            if let (String(subject), String(needle)) = (subject, needle) {
                return Bool(
                    needle.is_empty()
                        || subject
                            .windows(needle.len())
                            .any(|candidate| candidate == needle),
                );
            }
            if let String(subject) = subject
                && subject
                    .iter()
                    .all(|code_point| !(u32::from(b'0')..=u32::from(b'9')).contains(code_point))
                && let Some(empty) = exact_from_int_empty_condition(needle)
            {
                // A nonempty decimal word cannot occur in a fixed word with
                // no decimal code points; the empty word occurs everywhere.
                return empty;
            }
            if exact_contained_view(subject, needle) {
                return Bool(true);
            }
            if let Some((base, replaced)) = exact_self_replacement(subject) {
                // `replace(base, replaced, base)` contains `base`, preserves
                // whether `replaced` occurs, and has exactly `base`'s alphabet.
                if needle == base {
                    return Bool(true);
                }
                if needle == replaced
                    || exact_string_max_len(needle, 0).is_some_and(|maximum| maximum <= 1)
                {
                    return exact_rewrite_app("str.contains", vec![base.clone(), needle.clone()]);
                }
            }
            if let Some(rewritten) = exact_rewrite_concat_contains(subject, needle) {
                return rewritten;
            }
            if exact_string_min_len(needle, 0).is_some_and(|length| length > 0)
                && exact_string_alphabets_disjoint(subject, needle)
            {
                return Bool(false);
            }
            if exact_string_length_le(subject, needle, 0) {
                return exact_rewrite_equality(subject, needle);
            }
            if exact_is_ite(needle) && exact_ite_count(needle) <= 6 {
                // Preserve the generic bounded ITE distribution before the
                // one-code-point fallback returns a finite prefix language.
                // Each branch can then use the ordinary containment rules.
                return exact_distribute_app_ite(head, &args)
                    .expect("a bounded ite needle must distribute");
            }
            if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1) {
                return exact_rewrite_app("str.prefixof", vec![needle.clone(), subject.clone()]);
            }
            if let String(word) = subject
                && let Some(rewritten) = exact_rewrite_fixed_word_language(
                    word,
                    needle,
                    ExactFixedWordLanguage::Substrings,
                )
            {
                return rewritten;
            }
        }
        _ => {}
    }
    if let Some(distributed) = exact_distribute_app_ite(head, &args) {
        return distributed;
    }
    App(head.to_owned(), args)
}

fn exact_rewrite_replace_emptiness(
    replacement: &ExactRewriteTerm,
    other: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    if !matches!(other, ExactRewriteTerm::String(value) if value.is_empty()) {
        return None;
    }
    if let Some((subject, _)) = exact_self_replacement(replacement) {
        // Replacing a factor of a word by the whole word preserves emptiness.
        // Keep this stronger identity canonical ahead of the general theorem.
        return Some(exact_rewrite_app(
            "=",
            vec![subject.clone(), ExactRewriteTerm::String(Vec::new())],
        ));
    }
    let ExactRewriteTerm::App(head, args) = replacement else {
        return None;
    };
    let [subject, needle, value] = args.as_slice() else {
        return None;
    };
    if head != "str.replace" {
        return None;
    }

    // Replacing the first occurrence yields the empty word exactly for an
    // empty source with either a nonempty needle or an empty replacement, or
    // for a source equal to the needle with an empty replacement.
    let empty = ExactRewriteTerm::String(Vec::new());
    let subject_empty = exact_rewrite_app("=", vec![subject.clone(), empty.clone()]);
    let needle_empty = exact_rewrite_app("=", vec![needle.clone(), empty.clone()]);
    let replacement_empty = exact_rewrite_app("=", vec![value.clone(), empty]);
    Some(exact_rewrite_app(
        "or",
        vec![
            exact_rewrite_app(
                "and",
                vec![
                    subject_empty,
                    exact_rewrite_app(
                        "or",
                        vec![
                            exact_rewrite_app("not", vec![needle_empty]),
                            replacement_empty.clone(),
                        ],
                    ),
                ],
            ),
            exact_rewrite_app(
                "and",
                vec![
                    exact_rewrite_app("=", vec![subject.clone(), needle.clone()]),
                    replacement_empty,
                ],
            ),
        ],
    ))
}

/// Canonical truth condition for a positive SMT-LIB substring length in the
/// exact string rewrite fragment.  The two specialized forms expose the
/// integer and string-totality complements used by one-code-point views:
/// `1 - n > 0` iff `n <= 0`, and `len(s) > 0` iff `s != ""`.
fn exact_positive_substring_length_condition(length: &ExactRewriteTerm) -> ExactRewriteTerm {
    use ExactRewriteTerm::{App, Int, String};

    if let App(head, args) = length {
        if head == "-"
            && let [Int(1), value] = args.as_slice()
        {
            return exact_rewrite_app(
                "not",
                vec![exact_rewrite_app(">", vec![value.clone(), Int(0)])],
            );
        }
        if head == "-"
            && let [Int(0), value] | [value] = args.as_slice()
        {
            return exact_rewrite_app("<", vec![value.clone(), Int(0)]);
        }
        if matches!(head.as_str(), "str.len" | "seq.len")
            && let [subject] = args.as_slice()
        {
            return exact_rewrite_app(
                "not",
                vec![exact_rewrite_equality(subject, &String(Vec::new()))],
            );
        }
    }
    exact_rewrite_app(">", vec![length.clone(), Int(0)])
}

/// Symbolic `str.from_int(i)` is empty exactly for negative `i`.
fn exact_from_int_empty_condition(term: &ExactRewriteTerm) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, Int};

    let App(head, args) = term else {
        return None;
    };
    let [value] = args.as_slice() else {
        return None;
    };
    (head == "str.from_int").then(|| exact_rewrite_app("<", vec![value.clone(), Int(0)]))
}

fn exact_rewrite_from_int_emptiness(
    from_int: &ExactRewriteTerm,
    other: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    if !matches!(other, ExactRewriteTerm::String(value) if value.is_empty()) {
        return None;
    }
    exact_from_int_empty_condition(from_int)
}

/// Exact emptiness of a prefix substring.  At offset zero the result is empty
/// exactly when the requested length is nonpositive or the source is empty.
fn exact_rewrite_prefix_substr_emptiness(
    substring: &ExactRewriteTerm,
    other: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, Int, String};

    if !matches!(other, String(value) if value.is_empty()) {
        return None;
    }
    let App(head, args) = substring else {
        return None;
    };
    let [subject, Int(0), length] = args.as_slice() else {
        return None;
    };
    if head != "str.substr" {
        return None;
    }
    Some(exact_rewrite_app(
        "or",
        vec![
            exact_rewrite_app(
                "not",
                vec![exact_positive_substring_length_condition(length)],
            ),
            exact_rewrite_equality(subject, &String(Vec::new())),
        ],
    ))
}

/// Exact condition under which first-occurrence replacement preserves its
/// source. For an empty needle this requires an empty inserted prefix. For a
/// nonempty needle, the source is unchanged exactly when the needle is absent
/// or the replacement is the needle itself.
fn exact_rewrite_replace_preserves_subject(
    replacement: &ExactRewriteTerm,
    other: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, String};

    let App(head, args) = replacement else {
        return None;
    };
    let [subject, needle, value] = args.as_slice() else {
        return None;
    };
    if head != "str.replace" || subject != other {
        return None;
    }
    let empty = String(Vec::new());
    let needle_empty = exact_rewrite_equality(needle, &empty);
    Some(exact_rewrite_app(
        "or",
        vec![
            exact_rewrite_app(
                "and",
                vec![needle_empty.clone(), exact_rewrite_equality(value, &empty)],
            ),
            exact_rewrite_app(
                "and",
                vec![
                    exact_rewrite_app("not", vec![needle_empty]),
                    exact_rewrite_app(
                        "or",
                        vec![
                            exact_rewrite_app(
                                "not",
                                vec![exact_rewrite_app(
                                    "str.contains",
                                    vec![subject.clone(), needle.clone()],
                                )],
                            ),
                            exact_rewrite_equality(needle, value),
                        ],
                    ),
                ],
            ),
        ],
    ))
}

/// Characterizes exactly when one first-occurrence replacement is a fixed
/// one-code-point word.  The result has only four nonempty-needle shapes:
/// the needle is absent from the one-code-point source, it consumes the whole
/// source, or it consumes everything before/after the surviving code point.
/// This is an inverse-image rule over the unbounded SMT-LIB string semantics;
/// it does not enumerate or bound the symbolic operands.
fn exact_rewrite_replace_singleton_equality(
    replacement: &ExactRewriteTerm,
    other: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, String};

    let String(target) = other else {
        return None;
    };
    if target.len() != 1 {
        return None;
    }
    let App(head, args) = replacement else {
        return None;
    };
    let [subject, needle, value] = args.as_slice() else {
        return None;
    };
    if head != "str.replace" {
        return None;
    }

    let empty = String(Vec::new());
    let target = String(target.clone());
    let needle_empty = exact_rewrite_app("=", vec![needle.clone(), empty.clone()]);
    let needle_nonempty = exact_rewrite_app("not", vec![needle_empty.clone()]);
    let value_empty = exact_rewrite_app("=", vec![value.clone(), empty.clone()]);
    let empty_needle_case = exact_rewrite_app(
        "and",
        vec![
            needle_empty,
            exact_rewrite_app(
                "=",
                vec![
                    exact_rewrite_concat(&[value.clone(), subject.clone()]),
                    target.clone(),
                ],
            ),
        ],
    );
    let nonempty_case = exact_rewrite_app(
        "or",
        vec![
            // The only nonempty substring of a one-code-point source is the
            // source itself.  A different nonempty needle is therefore absent.
            exact_rewrite_app(
                "and",
                vec![
                    exact_rewrite_app("=", vec![subject.clone(), target.clone()]),
                    exact_rewrite_app(
                        "not",
                        vec![exact_rewrite_app("=", vec![needle.clone(), target.clone()])],
                    ),
                ],
            ),
            // The first occurrence consumes the whole source.
            exact_rewrite_app(
                "and",
                vec![
                    exact_rewrite_app("=", vec![subject.clone(), needle.clone()]),
                    exact_rewrite_app("=", vec![value.clone(), target.clone()]),
                ],
            ),
            // The target code point survives after the replaced occurrence.
            exact_rewrite_app(
                "and",
                vec![
                    value_empty.clone(),
                    exact_rewrite_app(
                        "=",
                        vec![
                            subject.clone(),
                            exact_rewrite_concat(&[needle.clone(), target.clone()]),
                        ],
                    ),
                ],
            ),
            // Or it survives before the occurrence.  Excluding a prefix
            // occurrence makes this the actual leftmost occurrence; commuting
            // cases are already covered by the preceding suffix shape.
            exact_rewrite_app(
                "and",
                vec![
                    value_empty,
                    exact_rewrite_app(
                        "=",
                        vec![
                            subject.clone(),
                            exact_rewrite_concat(&[target.clone(), needle.clone()]),
                        ],
                    ),
                    exact_rewrite_app(
                        "not",
                        vec![exact_rewrite_app(
                            "str.prefixof",
                            vec![needle.clone(), subject.clone()],
                        )],
                    ),
                ],
            ),
        ],
    );
    Some(exact_rewrite_app(
        "or",
        vec![
            empty_needle_case,
            exact_rewrite_app("and", vec![needle_nonempty, nonempty_case]),
        ],
    ))
}

fn exact_rewrite_head_totality_equality(
    left: &ExactRewriteTerm,
    right: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    for (length, other) in [(left, right), (right, left)] {
        if other == &ExactRewriteTerm::Int(0)
            && let ExactRewriteTerm::App(head, args) = length
            && head == "str.len"
            && let [subject] = args.as_slice()
        {
            return Some(exact_rewrite_app(
                "=",
                vec![subject.clone(), ExactRewriteTerm::String(Vec::new())],
            ));
        }
    }
    for (at, other) in [(left, right), (right, left)] {
        if matches!(other, ExactRewriteTerm::String(value) if value.is_empty())
            && let ExactRewriteTerm::App(head, args) = at
            && head == "str.at"
            && let [subject, ExactRewriteTerm::Int(index)] = args.as_slice()
            && *index >= 0
        {
            // `at(s,k)` is empty exactly when the nonnegative prefix through
            // `k` already contains all of `s`.
            return Some(exact_rewrite_app(
                "=",
                vec![
                    subject.clone(),
                    exact_rewrite_app(
                        "str.substr",
                        vec![
                            subject.clone(),
                            ExactRewriteTerm::Int(0),
                            ExactRewriteTerm::Int(*index),
                        ],
                    ),
                ],
            ));
        }
    }
    None
}

fn exact_rewrite_special_equality(
    left: &ExactRewriteTerm,
    right: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    exact_rewrite_head_totality_equality(left, right)
        .or_else(|| exact_rewrite_from_int_emptiness(left, right))
        .or_else(|| exact_rewrite_from_int_emptiness(right, left))
        .or_else(|| exact_rewrite_prefix_substr_emptiness(left, right))
        .or_else(|| exact_rewrite_prefix_substr_emptiness(right, left))
        .or_else(|| exact_rewrite_replace_preserves_subject(left, right))
        .or_else(|| exact_rewrite_replace_preserves_subject(right, left))
        .or_else(|| exact_rewrite_replace_emptiness(left, right))
        .or_else(|| exact_rewrite_replace_emptiness(right, left))
        .or_else(|| exact_rewrite_replace_singleton_equality(left, right))
        .or_else(|| exact_rewrite_replace_singleton_equality(right, left))
}

fn exact_rewrite_equality(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> ExactRewriteTerm {
    if left == right {
        return ExactRewriteTerm::Bool(true);
    }
    if matches!(
        (left, right),
        (ExactRewriteTerm::Bool(_), ExactRewriteTerm::Bool(_))
            | (ExactRewriteTerm::Int(_), ExactRewriteTerm::Int(_))
            | (ExactRewriteTerm::String(_), ExactRewriteTerm::String(_))
    ) {
        return ExactRewriteTerm::Bool(false);
    }
    if let Some(rewritten) = exact_rewrite_special_equality(left, right) {
        return rewritten;
    }
    for (replacement, other) in [(left, right), (right, left)] {
        if let ExactRewriteTerm::String(target) = other
            && target.len() == 1
            && let ExactRewriteTerm::App(head, args) = replacement
            && head == "str.replace"
            && let [
                subject,
                ExactRewriteTerm::String(needle),
                ExactRewriteTerm::String(value),
            ] = args.as_slice()
            && needle.len() == 1
            && value.is_empty()
        {
            // Deleting one fixed code point yields `target` only from target
            // itself (when distinct), needle+target, or target+needle. When
            // needle==target only the doubled word remains.
            let mut sources = BTreeSet::new();
            if needle == target {
                sources.insert([needle.as_slice(), target.as_slice()].concat());
            } else {
                sources.insert(target.clone());
                sources.insert([needle.as_slice(), target.as_slice()].concat());
                sources.insert([target.as_slice(), needle.as_slice()].concat());
            }
            return exact_rewrite_app(
                "or",
                sources
                    .into_iter()
                    .map(|source| {
                        exact_rewrite_equality(subject, &ExactRewriteTerm::String(source))
                    })
                    .collect(),
            );
        }
    }
    if matches!(left, ExactRewriteTerm::String(_)) && !matches!(right, ExactRewriteTerm::String(_))
    {
        return exact_rewrite_equality(right, left);
    }
    if let Some(rewritten) = exact_rewrite_small_concat_equality(left, right)
        .or_else(|| exact_rewrite_small_concat_equality(right, left))
    {
        return rewritten;
    }
    if exact_symmetric_equalities_equal(left, right) {
        return ExactRewriteTerm::Bool(true);
    }
    if exact_boolean_nary_terms_equal(left, right) {
        return ExactRewriteTerm::Bool(true);
    }
    if exact_unary_concat_terms_equal(left, right) {
        return ExactRewriteTerm::Bool(true);
    }
    if exact_piecewise_terms_equal(left, right) {
        return ExactRewriteTerm::Bool(true);
    }
    for (self_replacement, other) in [(left, right), (right, left)] {
        if let Some((subject, needle)) = exact_self_replacement(self_replacement)
            && (matches!(other, ExactRewriteTerm::String(value) if value.is_empty())
                || (exact_string_min_len(needle, 0).is_some_and(|minimum| minimum > 0)
                    && exact_string_max_len(other, 0).is_some_and(|maximum| maximum <= 1)))
        {
            // Emptiness is preserved for every needle. With a nonempty needle,
            // equality to a word of length at most one is preserved as well.
            return exact_rewrite_equality(subject, other);
        }
    }
    if let Some(rewritten) = exact_rewrite_ite_equality(left, right) {
        return rewritten;
    }
    for (base, candidate) in [(left, right), (right, left)] {
        if let Some(residual) = exact_concat_residual(base, candidate) {
            return exact_rewrite_equality(&residual, &ExactRewriteTerm::String(Vec::new()));
        }
        if exact_self_view_is_strict(base, candidate) {
            return ExactRewriteTerm::App(
                "=".to_owned(),
                vec![base.clone(), ExactRewriteTerm::String(Vec::new())],
            );
        }
    }
    ExactRewriteTerm::App("=".to_owned(), vec![left.clone(), right.clone()])
}

fn exact_symmetric_equalities_equal(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
    let (
        ExactRewriteTerm::App(left_head, left_args),
        ExactRewriteTerm::App(right_head, right_args),
    ) = (left, right)
    else {
        return false;
    };
    left_head == "="
        && right_head == "="
        && matches!((left_args.as_slice(), right_args.as_slice()),
            ([left_a, left_b], [right_a, right_b])
                if left_a == right_b && left_b == right_a)
}

#[derive(Default)]
struct ExactAffineForm {
    constant: i128,
    terms: Vec<(ExactRewriteTerm, i128)>,
    used_arithmetic: bool,
}

impl ExactAffineForm {
    fn add_constant(&mut self, value: i128) -> bool {
        let Some(sum) = self.constant.checked_add(value) else {
            return false;
        };
        self.constant = sum;
        true
    }

    fn add_term(&mut self, term: &ExactRewriteTerm, coefficient: i128) -> bool {
        if coefficient == 0 {
            return true;
        }
        if let Some((_, prior)) = self.terms.iter_mut().find(|(prior, _)| prior == term) {
            let Some(sum) = prior.checked_add(coefficient) else {
                return false;
            };
            *prior = sum;
            self.terms.retain(|(_, coefficient)| *coefficient != 0);
        } else {
            self.terms.push((term.clone(), coefficient));
        }
        true
    }

    fn coefficient(&self, term: &ExactRewriteTerm) -> i128 {
        self.terms
            .iter()
            .find_map(|(candidate, coefficient)| (candidate == term).then_some(*coefficient))
            .unwrap_or(0)
    }
}

fn exact_collect_affine(
    term: &ExactRewriteTerm,
    scale: i128,
    form: &mut ExactAffineForm,
    depth: u32,
) -> bool {
    use ExactRewriteTerm::{App, Bool, Int, String};

    if depth > 32 {
        return false;
    }
    match term {
        Int(value) => {
            form.used_arithmetic = true;
            value
                .checked_mul(scale)
                .is_some_and(|value| form.add_constant(value))
        }
        Bool(_) | String(_) => false,
        App(head, args) if head == "+" => {
            form.used_arithmetic = true;
            args.iter()
                .all(|argument| exact_collect_affine(argument, scale, form, depth + 1))
        }
        App(head, args) if head == "-" => {
            form.used_arithmetic = true;
            match args.as_slice() {
                [value] => scale
                    .checked_neg()
                    .is_some_and(|scale| exact_collect_affine(value, scale, form, depth + 1)),
                [left, right] => {
                    exact_collect_affine(left, scale, form, depth + 1)
                        && scale.checked_neg().is_some_and(|scale| {
                            exact_collect_affine(right, scale, form, depth + 1)
                        })
                }
                _ => false,
            }
        }
        App(head, args) if head == "*" => {
            let scaled = match args.as_slice() {
                [Int(factor), value] | [value, Int(factor)] => {
                    scale.checked_mul(*factor).map(|scale| (value, scale))
                }
                _ => None,
            };
            if let Some((value, scale)) = scaled {
                form.used_arithmetic = true;
                exact_collect_affine(value, scale, form, depth + 1)
            } else {
                form.add_term(term, scale)
            }
        }
        _ => form.add_term(term, scale),
    }
}

fn exact_affine_difference(
    left: &ExactRewriteTerm,
    right: &ExactRewriteTerm,
) -> Option<ExactAffineForm> {
    let mut form = ExactAffineForm::default();
    if !exact_collect_affine(left, 1, &mut form, 0)
        || !exact_collect_affine(right, -1, &mut form, 0)
    {
        return None;
    }
    Some(form)
}

/// Checks whether two affine equality atoms differ only by multiplication by
/// a nonzero rational scalar. Checked arithmetic makes overflow a decline.
fn exact_affine_equalities_equal(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
    let (
        ExactRewriteTerm::App(left_head, left_args),
        ExactRewriteTerm::App(right_head, right_args),
    ) = (left, right)
    else {
        return false;
    };
    let ([left_a, left_b], [right_a, right_b]) = (left_args.as_slice(), right_args.as_slice())
    else {
        return false;
    };
    if left_head != "=" || right_head != "=" {
        return false;
    }
    let (Some(left), Some(right)) = (
        exact_affine_difference(left_a, left_b),
        exact_affine_difference(right_a, right_b),
    ) else {
        return false;
    };
    if !left.used_arithmetic || !right.used_arithmetic {
        return false;
    }
    let mut components = vec![(left.constant, right.constant)];
    for (term, coefficient) in &left.terms {
        components.push((*coefficient, right.coefficient(term)));
    }
    for (term, coefficient) in &right.terms {
        if left.coefficient(term) == 0 {
            components.push((0, *coefficient));
        }
    }
    let Some((left_scale, right_scale)) = components.iter().copied().find(|(left, _)| *left != 0)
    else {
        return components.iter().all(|(_, right)| *right == 0);
    };
    if right_scale == 0 {
        return false;
    }
    components.into_iter().all(|(left, right)| {
        left.checked_mul(right_scale)
            .zip(right.checked_mul(left_scale))
            .is_some_and(|(left, right)| left == right)
    })
}

fn exact_conditions_equal(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
    left == right
        || exact_boolean_nary_terms_equal(left, right)
        || exact_affine_equalities_equal(left, right)
        || exact_affine_orderings_equal(left, right)
}

/// Checks whether two affine order atoms have the same strictness and their
/// normalized differences differ only by a positive rational scalar.
fn exact_affine_orderings_equal(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
    let relation = |term: &ExactRewriteTerm| {
        let ExactRewriteTerm::App(head, args) = term else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        let (strict, left, right) = match head.as_str() {
            ">" => (true, left, right),
            "<" => (true, right, left),
            ">=" => (false, left, right),
            "<=" => (false, right, left),
            _ => return None,
        };
        exact_affine_difference(left, right).map(|form| (strict, form))
    };
    let (Some((left_strict, left)), Some((right_strict, right))) =
        (relation(left), relation(right))
    else {
        return false;
    };
    if left_strict != right_strict || !left.used_arithmetic || !right.used_arithmetic {
        return false;
    }
    let mut components = vec![(left.constant, right.constant)];
    for (term, coefficient) in &left.terms {
        components.push((*coefficient, right.coefficient(term)));
    }
    for (term, coefficient) in &right.terms {
        if left.coefficient(term) == 0 {
            components.push((0, *coefficient));
        }
    }
    let Some((left_scale, right_scale)) = components
        .iter()
        .copied()
        .find(|(left, right)| *left != 0 || *right != 0)
    else {
        return false;
    };
    if left_scale == 0 || right_scale == 0 || left_scale.is_positive() != right_scale.is_positive()
    {
        return false;
    }
    components.into_iter().all(|(left, right)| {
        left.checked_mul(right_scale)
            .zip(right.checked_mul(left_scale))
            .is_some_and(|(left, right)| left == right)
    })
}

fn exact_u128_gcd(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        (left, right) = (right, left % right);
    }
    left
}

/// Proves `length <= 0` whenever `offset = 0` for affine integer terms. This
/// is exactly the condition needed to prove a one-code-point substring empty.
fn exact_affine_zero_forces_nonpositive(
    offset: &ExactRewriteTerm,
    length: &ExactRewriteTerm,
) -> bool {
    let zero = ExactRewriteTerm::Int(0);
    let (Some(offset), Some(length)) = (
        exact_affine_difference(offset, &zero),
        exact_affine_difference(length, &zero),
    ) else {
        return false;
    };
    if !offset.used_arithmetic || !length.used_arithmetic {
        return false;
    }
    if offset.terms.is_empty() {
        return offset.constant != 0 || (length.terms.is_empty() && length.constant <= 0);
    }
    let coefficient_gcd = offset.terms.iter().fold(0_u128, |gcd, (_, coefficient)| {
        exact_u128_gcd(gcd, coefficient.unsigned_abs())
    });
    if coefficient_gcd != 0 && offset.constant.unsigned_abs() % coefficient_gcd != 0 {
        return true;
    }
    if length.terms.is_empty() {
        return length.constant <= 0;
    }
    let Some((offset_scale, length_scale)) =
        offset.terms.iter().find_map(|(term, offset_scale)| {
            let length_scale = length.coefficient(term);
            (length_scale != 0).then_some((*offset_scale, length_scale))
        })
    else {
        return false;
    };
    if length
        .terms
        .iter()
        .any(|(term, _)| offset.coefficient(term) == 0)
    {
        return false;
    }
    let proportional = offset.terms.iter().all(|(term, offset_coefficient)| {
        let length_coefficient = length.coefficient(term);
        length_coefficient
            .checked_mul(offset_scale)
            .zip(offset_coefficient.checked_mul(length_scale))
            .is_some_and(|(left, right)| left == right)
    });
    if !proportional {
        return false;
    }
    let Some(numerator) = length
        .constant
        .checked_mul(offset_scale)
        .zip(length_scale.checked_mul(offset.constant))
        .and_then(|(left, right)| left.checked_sub(right))
    else {
        return false;
    };
    if offset_scale > 0 {
        numerator <= 0
    } else {
        numerator >= 0
    }
}

/// Proves `length > 0` whenever `offset = 0` for affine integer terms. Over a
/// word of length at most one, that makes `substr(word, offset, length)` exactly
/// the same total-function view as `at(word, offset)`.
fn exact_affine_zero_forces_positive(offset: &ExactRewriteTerm, length: &ExactRewriteTerm) -> bool {
    let zero = ExactRewriteTerm::Int(0);
    let (Some(offset), Some(length)) = (
        exact_affine_difference(offset, &zero),
        exact_affine_difference(length, &zero),
    ) else {
        return false;
    };
    if !offset.used_arithmetic || !length.used_arithmetic {
        return false;
    }
    if offset.terms.is_empty() {
        return offset.constant != 0 || (length.terms.is_empty() && length.constant > 0);
    }
    let coefficient_gcd = offset.terms.iter().fold(0_u128, |gcd, (_, coefficient)| {
        exact_u128_gcd(gcd, coefficient.unsigned_abs())
    });
    if coefficient_gcd != 0 && offset.constant.unsigned_abs() % coefficient_gcd != 0 {
        return true;
    }
    if length.terms.is_empty() {
        return length.constant > 0;
    }
    let Some((offset_scale, length_scale)) =
        offset.terms.iter().find_map(|(term, offset_scale)| {
            let length_scale = length.coefficient(term);
            (length_scale != 0).then_some((*offset_scale, length_scale))
        })
    else {
        return false;
    };
    if length
        .terms
        .iter()
        .any(|(term, _)| offset.coefficient(term) == 0)
    {
        return false;
    }
    let proportional = offset.terms.iter().all(|(term, offset_coefficient)| {
        let length_coefficient = length.coefficient(term);
        length_coefficient
            .checked_mul(offset_scale)
            .zip(offset_coefficient.checked_mul(length_scale))
            .is_some_and(|(left, right)| left == right)
    });
    if !proportional {
        return false;
    }
    let Some(numerator) = length
        .constant
        .checked_mul(offset_scale)
        .zip(length_scale.checked_mul(offset.constant))
        .and_then(|(left, right)| left.checked_sub(right))
    else {
        return false;
    };
    if offset_scale > 0 {
        numerator > 0
    } else {
        numerator < 0
    }
}

fn exact_self_replacement(
    term: &ExactRewriteTerm,
) -> Option<(&ExactRewriteTerm, &ExactRewriteTerm)> {
    let ExactRewriteTerm::App(head, args) = term else {
        return None;
    };
    let [subject, needle, replacement] = args.as_slice() else {
        return None;
    };
    (head == "str.replace" && subject == replacement).then_some((subject, needle))
}

const EXACT_ITE_CASE_CAP: usize = 64;

struct ExactIteCase {
    assignments: Vec<(ExactRewriteTerm, bool)>,
    value: ExactRewriteTerm,
}

/// Equivalence facts for the equality atoms on one path through an exact
/// rewrite decision tree.  Small-subject string operations introduce tests
/// such as `x = ""`, `x = "A"`, and `x = y`; treating those tests as unrelated
/// leaves semantically impossible path pairs alive and prevents otherwise
/// identical decision trees from meeting.  This deliberately implements only
/// equality closure and explicit disequality -- no word-equation inference.
#[derive(Default)]
struct ExactEqualityFacts {
    terms: Vec<ExactRewriteTerm>,
    parents: Vec<usize>,
    disequalities: Vec<(usize, usize)>,
    conflict: bool,
}

impl ExactEqualityFacts {
    fn from_assignments(assignments: &[(ExactRewriteTerm, bool)]) -> Self {
        let mut facts = Self::default();
        for (condition, value) in assignments {
            facts.record(condition, *value);
        }
        facts.finish();
        facts
    }

    fn record(&mut self, condition: &ExactRewriteTerm, value: bool) {
        use ExactRewriteTerm::{App, Bool};

        match condition {
            Bool(actual) => self.conflict |= *actual != value,
            App(head, args) if head == "not" && args.len() == 1 => {
                self.record(&args[0], !value);
            }
            App(head, args) if head == "=" && args.len() == 2 => {
                let left = self.intern(args[0].clone());
                let right = self.intern(args[1].clone());
                if value {
                    self.union(left, right);
                } else {
                    self.disequalities.push((left, right));
                }
            }
            _ => {}
        }
    }

    fn intern(&mut self, term: ExactRewriteTerm) -> usize {
        if let Some(index) = self.terms.iter().position(|candidate| candidate == &term) {
            return index;
        }
        let index = self.terms.len();
        self.terms.push(term);
        self.parents.push(index);
        index
    }

    fn root(&self, mut index: usize) -> usize {
        while self.parents[index] != index {
            index = self.parents[index];
        }
        index
    }

    fn union(&mut self, left: usize, right: usize) {
        let left = self.root(left);
        let right = self.root(right);
        if left != right {
            self.parents[right] = left;
        }
    }

    fn finish(&mut self) {
        self.propagate_empty_concats();
        for (index, term) in self.terms.iter().enumerate() {
            if !exact_is_literal(term) {
                continue;
            }
            let root = self.root(index);
            if self.terms.iter().enumerate().any(|(other_index, other)| {
                other_index != index
                    && exact_is_literal(other)
                    && self.root(other_index) == root
                    && other != term
            }) {
                self.conflict = true;
                return;
            }
        }
        if self
            .disequalities
            .iter()
            .any(|(left, right)| self.root(*left) == self.root(*right))
        {
            self.conflict = true;
        }
    }

    /// Propagates the exact free-monoid identity
    /// `concat(parts) = ""` iff every part is empty.  The rule activates only
    /// in an equality class already connected to the fixed empty string, so it
    /// cannot infer content or collapse a merely unknown component.
    fn propagate_empty_concats(&mut self) {
        use ExactRewriteTerm::{App, String};

        let empty = self.intern(String(Vec::new()));
        let mut concats = Vec::new();
        for (term_index, term) in self.terms.clone().into_iter().enumerate() {
            let App(head, parts) = term else {
                continue;
            };
            if !matches!(head.as_str(), "str.++" | "seq.++") {
                continue;
            }
            let parts: Vec<usize> = parts.into_iter().map(|part| self.intern(part)).collect();
            concats.push((term_index, parts));
        }

        for _ in 0..self.terms.len() {
            let mut changed = false;
            for (concat, parts) in &concats {
                if self.root(*concat) == self.root(empty) {
                    for part in parts {
                        if self.root(*part) != self.root(empty) {
                            self.union(*part, empty);
                            changed = true;
                        }
                    }
                } else if parts
                    .iter()
                    .all(|part| self.root(*part) == self.root(empty))
                {
                    self.union(*concat, empty);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }

    fn index_of(&self, term: &ExactRewriteTerm) -> Option<usize> {
        self.terms.iter().position(|candidate| candidate == term)
    }

    fn equal(&self, left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
        left == right
            || self
                .index_of(left)
                .zip(self.index_of(right))
                .is_some_and(|(left, right)| self.root(left) == self.root(right))
    }

    fn distinct(&self, left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
        let explicitly_distinct =
            self.index_of(left)
                .zip(self.index_of(right))
                .is_some_and(|(left, right)| {
                    let left = self.root(left);
                    let right = self.root(right);
                    self.disequalities.iter().any(|(a, b)| {
                        let a = self.root(*a);
                        let b = self.root(*b);
                        (a == left && b == right) || (a == right && b == left)
                    })
                });
        explicitly_distinct || (exact_is_literal(left) && exact_is_literal(right) && left != right)
    }

    fn literal_for(&self, term: &ExactRewriteTerm) -> Option<ExactRewriteTerm> {
        let root = self.root(self.index_of(term)?);
        self.terms
            .iter()
            .enumerate()
            .find(|(index, candidate)| exact_is_literal(candidate) && self.root(*index) == root)
            .map(|(_, candidate)| candidate.clone())
    }

    fn condition_value(&self, condition: &ExactRewriteTerm) -> Option<bool> {
        use ExactRewriteTerm::{App, Bool};

        match condition {
            Bool(value) => Some(*value),
            App(head, args) if head == "not" && args.len() == 1 => {
                self.condition_value(&args[0]).map(|value| !value)
            }
            App(head, args) if head == "=" && args.len() == 2 => {
                if self.equal(&args[0], &args[1]) {
                    Some(true)
                } else if self.distinct(&args[0], &args[1]) {
                    Some(false)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Whether exact string equalities force a class containing a fixed word
    /// to be longer than that word.  Lower bounds flow only through
    /// concatenation and equality classes; an unknown string contributes zero.
    fn string_length_conflict(&self) -> bool {
        use ExactRewriteTerm::{App, String};

        fn lower_bound(
            facts: &ExactEqualityFacts,
            term: &ExactRewriteTerm,
            bounds: &[usize],
            depth: u32,
        ) -> usize {
            if depth > 32 {
                return 0;
            }
            match term {
                String(value) => value.len(),
                App(head, parts) if matches!(head.as_str(), "str.++" | "seq.++") => {
                    parts.iter().fold(0_usize, |sum, part| {
                        sum.saturating_add(lower_bound(facts, part, bounds, depth + 1))
                    })
                }
                App(head, args) if head == "ite" => {
                    let [_, then_term, else_term] = args.as_slice() else {
                        return 0;
                    };
                    lower_bound(facts, then_term, bounds, depth + 1).min(lower_bound(
                        facts,
                        else_term,
                        bounds,
                        depth + 1,
                    ))
                }
                _ => facts
                    .index_of(term)
                    .map_or(0, |index| bounds[facts.root(index)]),
            }
        }

        let mut bounds = vec![0_usize; self.terms.len()];
        for _ in 0..self.terms.len() {
            let mut changed = false;
            for (index, term) in self.terms.iter().enumerate() {
                let root = self.root(index);
                let candidate = lower_bound(self, term, &bounds, 0);
                if candidate > bounds[root] {
                    bounds[root] = candidate;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        self.terms.iter().enumerate().any(
            |(index, term)| matches!(term, String(value) if bounds[self.root(index)] > value.len()),
        )
    }
}

/// Compares two bounded `ite` decision trees without requiring their branch
/// conditions to appear in the same order. Conditions are treated as
/// independent Boolean atoms, so checking every syntactically compatible pair
/// of leaves is conservative: logical relationships between distinct atoms can
/// only make this decline an identity, never prove a false one.
fn exact_piecewise_terms_equal(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
    if !exact_is_ite(left) && !exact_is_ite(right) {
        return false;
    }
    let mut left_cases = Vec::new();
    let mut right_cases = Vec::new();
    if !exact_collect_ite_cases(left, &mut Vec::new(), &mut left_cases)
        || !exact_collect_ite_cases(right, &mut Vec::new(), &mut right_cases)
    {
        return false;
    }
    let mut compared = false;
    for left_case in &left_cases {
        for right_case in &right_cases {
            if !exact_ite_assignments_compatible(&left_case.assignments, &right_case.assignments) {
                continue;
            }
            compared = true;
            let mut assignments = left_case.assignments.clone();
            for assignment in &right_case.assignments {
                if !assignments
                    .iter()
                    .any(|(condition, _)| exact_conditions_equal(condition, &assignment.0))
                {
                    assignments.push(assignment.clone());
                }
            }
            let left_value = exact_rewrite_under_assignments(&left_case.value, &assignments, 0);
            let right_value = exact_rewrite_under_assignments(&right_case.value, &assignments, 0);
            if exact_rewrite_equality(&left_value, &right_value) != ExactRewriteTerm::Bool(true) {
                return false;
            }
        }
    }
    compared
}

const EXACT_BOOLEAN_ATOM_CAP: usize = 10;

/// Proves a small normalized Boolean term constant by exhaustively checking
/// its primitive atoms. Equality-inconsistent assignments are unreachable and
/// discarded; every other assignment must reduce to the same Boolean. Treating
/// non-equality predicates as independent atoms is conservative.
fn exact_boolean_constant(term: &ExactRewriteTerm) -> Option<bool> {
    let mut atoms = Vec::new();
    if !exact_collect_boolean_atoms(term, &mut atoms) || atoms.len() > EXACT_BOOLEAN_ATOM_CAP {
        return None;
    }
    let mut result = None;
    for mask in 0_u64..(1_u64 << atoms.len()) {
        let assignments = atoms
            .iter()
            .enumerate()
            .map(|(index, atom)| (atom.clone(), mask & (1_u64 << index) != 0))
            .collect::<Vec<_>>();
        if ExactEqualityFacts::from_assignments(&assignments).conflict {
            continue;
        }
        let ExactRewriteTerm::Bool(value) = exact_rewrite_under_assignments(term, &assignments, 0)
        else {
            return None;
        };
        if result.is_some_and(|prior| prior != value) {
            return None;
        }
        result = Some(value);
    }
    result
}

fn exact_collect_boolean_atoms(term: &ExactRewriteTerm, atoms: &mut Vec<ExactRewriteTerm>) -> bool {
    use ExactRewriteTerm::{App, Bool};

    match term {
        Bool(_) => true,
        App(head, args) if head == "not" && args.len() == 1 => {
            exact_collect_boolean_atoms(&args[0], atoms)
        }
        App(head, args) if matches!(head.as_str(), "and" | "or") => args
            .iter()
            .all(|argument| exact_collect_boolean_atoms(argument, atoms)),
        App(head, args)
            if head == "=" && args.len() == 2 && args.iter().all(exact_term_is_boolean) =>
        {
            args.iter()
                .all(|argument| exact_collect_boolean_atoms(argument, atoms))
        }
        App(head, args) if head == "ite" && args.len() == 3 => args
            .iter()
            .all(|argument| exact_collect_boolean_atoms(argument, atoms)),
        atom => {
            if !atoms
                .iter()
                .any(|candidate| exact_conditions_equal(candidate, atom))
            {
                atoms.push(atom.clone());
            }
            atoms.len() <= EXACT_BOOLEAN_ATOM_CAP
        }
    }
}

fn exact_term_is_boolean(term: &ExactRewriteTerm) -> bool {
    use ExactRewriteTerm::{App, Bool};

    match term {
        Bool(_) => true,
        App(head, args) if head == "ite" && args.len() == 3 => {
            exact_term_is_boolean(&args[1]) && exact_term_is_boolean(&args[2])
        }
        App(head, _) => matches!(
            head.as_str(),
            "not"
                | "and"
                | "or"
                | "="
                | "<"
                | "<="
                | ">"
                | ">="
                | "str.prefixof"
                | "str.suffixof"
                | "str.contains"
                | "str.in_re"
        ),
        _ => false,
    }
}

fn exact_rewrite_under_assignments(
    term: &ExactRewriteTerm,
    assignments: &[(ExactRewriteTerm, bool)],
    depth: u32,
) -> ExactRewriteTerm {
    let facts = ExactEqualityFacts::from_assignments(assignments);
    if facts.conflict {
        return term.clone();
    }
    exact_rewrite_under_assignment_facts(term, assignments, &facts, depth)
}

fn exact_rewrite_under_assignment_facts(
    term: &ExactRewriteTerm,
    assignments: &[(ExactRewriteTerm, bool)],
    facts: &ExactEqualityFacts,
    depth: u32,
) -> ExactRewriteTerm {
    use ExactRewriteTerm::{App, Bool, IndexOfSelf};

    if depth > EXACT_REWRITE_DEPTH_CAP {
        return term.clone();
    }
    let semantic = exact_rewrite_under_equality_facts(term, facts, depth);
    if semantic != *term {
        return exact_rewrite_under_assignment_facts(&semantic, assignments, facts, depth + 1);
    }
    if let Some((_, value)) = assignments
        .iter()
        .find(|(condition, _)| exact_conditions_equal(condition, term))
    {
        return Bool(*value);
    }
    if let Some(value) = facts.condition_value(term) {
        return Bool(value);
    }
    if let Some(literal) = facts.literal_for(term) {
        return literal;
    }
    for (condition, value) in assignments {
        if !value {
            continue;
        }
        let App(head, sides) = condition else {
            continue;
        };
        let [left, right] = sides.as_slice() else {
            continue;
        };
        if head == "=" {
            if term == left && exact_is_literal(right) {
                return right.clone();
            }
            if term == right && exact_is_literal(left) {
                return left.clone();
            }
        }
    }
    match term {
        App(head, args) => {
            let args: Vec<_> = args
                .iter()
                .map(|arg| exact_rewrite_under_assignment_facts(arg, assignments, facts, depth + 1))
                .collect();
            if head == "str.replace"
                && let [subject, needle, _] = args.as_slice()
                && exact_string_min_len(needle, 0).is_some_and(|length| length > 0)
                && exact_assignment_value(
                    &App(
                        "str.contains".to_owned(),
                        vec![subject.clone(), needle.clone()],
                    ),
                    assignments,
                )
                .or_else(|| {
                    facts.condition_value(&App(
                        "str.contains".to_owned(),
                        vec![subject.clone(), needle.clone()],
                    ))
                }) == Some(false)
            {
                return subject.clone();
            }
            exact_rewrite_app(head, args)
        }
        IndexOfSelf(argument) => IndexOfSelf(Box::new(exact_rewrite_under_assignment_facts(
            argument,
            assignments,
            facts,
            depth + 1,
        ))),
        _ => term.clone(),
    }
}

/// Re-evaluates compound exact terms after path equalities pin any of their
/// operands.  This runs before treating a remaining predicate as an independent
/// Boolean atom: an assignment such as `x = "BA"` must make
/// `at(x, 0) = "A"` false rather than allowing an impossible path that assigns
/// both atoms true.  Unsupported terms remain structural.
fn exact_rewrite_under_equality_facts(
    term: &ExactRewriteTerm,
    facts: &ExactEqualityFacts,
    depth: u32,
) -> ExactRewriteTerm {
    use ExactRewriteTerm::{App, IndexOfSelf};

    if depth > EXACT_REWRITE_DEPTH_CAP {
        return term.clone();
    }
    if let Some(literal) = facts.literal_for(term) {
        return literal;
    }
    match term {
        App(head, args) => exact_rewrite_app(
            head,
            args.iter()
                .map(|argument| exact_rewrite_under_equality_facts(argument, facts, depth + 1))
                .collect(),
        ),
        IndexOfSelf(argument) => IndexOfSelf(Box::new(exact_rewrite_under_equality_facts(
            argument,
            facts,
            depth + 1,
        ))),
        _ => term.clone(),
    }
}

fn exact_assignment_value(
    condition: &ExactRewriteTerm,
    assignments: &[(ExactRewriteTerm, bool)],
) -> Option<bool> {
    assignments.iter().find_map(|(candidate, value)| {
        exact_conditions_equal(candidate, condition).then_some(*value)
    })
}

fn exact_is_literal(term: &ExactRewriteTerm) -> bool {
    matches!(
        term,
        ExactRewriteTerm::Bool(_) | ExactRewriteTerm::Int(_) | ExactRewriteTerm::String(_)
    )
}

fn exact_is_ite(term: &ExactRewriteTerm) -> bool {
    matches!(term, ExactRewriteTerm::App(head, args) if head == "ite" && args.len() == 3)
}

fn exact_collect_ite_cases(
    term: &ExactRewriteTerm,
    assignments: &mut Vec<(ExactRewriteTerm, bool)>,
    cases: &mut Vec<ExactIteCase>,
) -> bool {
    use ExactRewriteTerm::App;

    if let App(head, args) = term
        && head == "ite"
        && let [condition, then_term, else_term] = args.as_slice()
    {
        for (value, branch) in [(true, then_term), (false, else_term)] {
            if let Some((_, prior)) = assignments
                .iter()
                .find(|(candidate, _)| exact_conditions_equal(candidate, condition))
            {
                if *prior == value && !exact_collect_ite_cases(branch, assignments, cases) {
                    return false;
                }
                continue;
            }
            assignments.push((condition.clone(), value));
            if !exact_collect_ite_cases(branch, assignments, cases) {
                return false;
            }
            assignments.pop();
        }
        return true;
    }
    if cases.len() >= EXACT_ITE_CASE_CAP {
        return false;
    }
    cases.push(ExactIteCase {
        assignments: assignments.clone(),
        value: term.clone(),
    });
    true
}

fn exact_ite_assignments_compatible(
    left: &[(ExactRewriteTerm, bool)],
    right: &[(ExactRewriteTerm, bool)],
) -> bool {
    let directly_compatible = left.iter().all(|(condition, value)| {
        right
            .iter()
            .find(|(candidate, _)| exact_conditions_equal(candidate, condition))
            .is_none_or(|(_, other)| value == other)
    });
    if !directly_compatible {
        return false;
    }
    let assignments = left.iter().chain(right).cloned().collect::<Vec<_>>();
    !ExactEqualityFacts::from_assignments(&assignments).conflict
}

fn exact_rewrite_ite_equality(
    left: &ExactRewriteTerm,
    right: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::App;

    if let App(head, left_args) = left
        && head == "ite"
        && let [condition, left_then, left_else] = left_args.as_slice()
    {
        if let App(right_head, right_args) = right
            && right_head == "ite"
            && let [right_condition, right_then, right_else] = right_args.as_slice()
            && exact_conditions_equal(right_condition, condition)
        {
            return Some(exact_rewrite_app(
                "ite",
                vec![
                    condition.clone(),
                    exact_rewrite_equality(left_then, right_then),
                    exact_rewrite_equality(left_else, right_else),
                ],
            ));
        }
        return Some(exact_rewrite_app(
            "ite",
            vec![
                condition.clone(),
                exact_rewrite_equality(left_then, right),
                exact_rewrite_equality(left_else, right),
            ],
        ));
    }
    if let App(head, right_args) = right
        && head == "ite"
        && let [condition, right_then, right_else] = right_args.as_slice()
    {
        return Some(exact_rewrite_app(
            "ite",
            vec![
                condition.clone(),
                exact_rewrite_equality(left, right_then),
                exact_rewrite_equality(left, right_else),
            ],
        ));
    }
    None
}

fn exact_rewrite_small_subject_replace(
    subject: &[u32],
    needle: &ExactRewriteTerm,
    replacement: &ExactRewriteTerm,
) -> ExactRewriteTerm {
    use ExactRewriteTerm::String;

    let subject = String(subject.to_vec());
    let empty = String(Vec::new());
    let empty_needle = exact_rewrite_equality(needle, &empty);
    if matches!(&subject, String(value) if value.is_empty()) {
        return exact_rewrite_app("ite", vec![empty_needle, replacement.clone(), empty]);
    }
    let equal_needle = exact_rewrite_equality(needle, &subject);
    let nonempty_case = exact_rewrite_app(
        "ite",
        vec![equal_needle, replacement.clone(), subject.clone()],
    );
    exact_rewrite_app(
        "ite",
        vec![
            empty_needle,
            exact_rewrite_concat(&[replacement.clone(), subject]),
            nonempty_case,
        ],
    )
}

fn exact_rewrite_small_subject_indexof(
    subject: &[u32],
    needle: &ExactRewriteTerm,
    offset: &ExactRewriteTerm,
) -> ExactRewriteTerm {
    use ExactRewriteTerm::{Int, String};

    let empty = String(Vec::new());
    let at_zero = exact_rewrite_app("=", vec![offset.clone(), Int(0)]);
    let empty_needle = exact_rewrite_app("=", vec![needle.clone(), empty.clone()]);
    if subject.is_empty() {
        return exact_rewrite_app(
            "ite",
            vec![
                at_zero,
                exact_rewrite_app("ite", vec![empty_needle, Int(0), Int(-1)]),
                Int(-1),
            ],
        );
    }
    let subject = String(subject.to_vec());
    let matching_needle = exact_rewrite_app("=", vec![needle.clone(), subject]);
    let zero_result = exact_rewrite_app(
        "ite",
        vec![
            empty_needle.clone(),
            Int(0),
            exact_rewrite_app("ite", vec![matching_needle, Int(0), Int(-1)]),
        ],
    );
    let one_result = exact_rewrite_app("ite", vec![empty_needle, Int(1), Int(-1)]);
    exact_rewrite_app(
        "ite",
        vec![
            at_zero,
            zero_result,
            exact_rewrite_app(
                "ite",
                vec![
                    exact_rewrite_app("=", vec![offset.clone(), Int(1)]),
                    one_result,
                    Int(-1),
                ],
            ),
        ],
    )
}

fn exact_rewrite_concat_subject_replace(
    subject: &ExactRewriteTerm,
    needle: &ExactRewriteTerm,
    replacement: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, String};

    let App(head, parts) = subject else {
        return None;
    };
    if !matches!(head.as_str(), "str.++" | "seq.++") || parts.len() < 2 {
        return None;
    }
    let prefix = &parts[0];
    let suffix = exact_rewrite_concat(&parts[1..]);
    if prefix == needle {
        return Some(exact_rewrite_concat(&[replacement.clone(), suffix]));
    }
    if !matches!(needle, String(value) if value.len() == 1) {
        return None;
    }
    let condition = exact_rewrite_app("str.contains", vec![prefix.clone(), needle.clone()]);
    let replace_prefix = exact_rewrite_app(
        "str.replace",
        vec![prefix.clone(), needle.clone(), replacement.clone()],
    );
    let replace_suffix = exact_rewrite_app(
        "str.replace",
        vec![suffix.clone(), needle.clone(), replacement.clone()],
    );
    Some(exact_rewrite_app(
        "ite",
        vec![
            condition,
            exact_rewrite_concat(&[replace_prefix, suffix]),
            exact_rewrite_concat(&[prefix.clone(), replace_suffix]),
        ],
    ))
}

fn exact_ite_count(term: &ExactRewriteTerm) -> u32 {
    match term {
        ExactRewriteTerm::App(head, args) => {
            args.iter().fold(u32::from(head == "ite"), |sum, arg| {
                sum.saturating_add(exact_ite_count(arg))
            })
        }
        ExactRewriteTerm::IndexOfSelf(argument) => exact_ite_count(argument),
        _ => 0,
    }
}

fn exact_distribute_app_ite(head: &str, args: &[ExactRewriteTerm]) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::App;

    if head == "ite" || args.iter().map(exact_ite_count).sum::<u32>() > 6 {
        return None;
    }
    let (index, condition, then_term, else_term) =
        args.iter().enumerate().find_map(|(index, argument)| {
            let App(head, ite_args) = argument else {
                return None;
            };
            let [condition, then_term, else_term] = ite_args.as_slice() else {
                return None;
            };
            (head == "ite").then_some((index, condition, then_term, else_term))
        })?;
    let mut then_args = args.to_vec();
    then_args[index] = then_term.clone();
    let mut else_args = args.to_vec();
    else_args[index] = else_term.clone();
    Some(exact_rewrite_app(
        "ite",
        vec![
            condition.clone(),
            exact_rewrite_app(head, then_args),
            exact_rewrite_app(head, else_args),
        ],
    ))
}

/// For a word of length at most one, equality with a concatenation is a finite
/// choice: exactly one component supplies that word and every other component
/// is empty. This is an unbounded source-string theorem, independent of the
/// packed representation's configured maximum length.
fn exact_rewrite_small_concat_equality(
    concat: &ExactRewriteTerm,
    small: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, String};

    if exact_string_max_len(small, 0)? > 1 {
        return None;
    }
    let App(head, parts) = concat else {
        return None;
    };
    if !matches!(head.as_str(), "str.++" | "seq.++") || parts.len() > 6 {
        return None;
    }
    let empty = String(Vec::new());
    let choices = parts
        .iter()
        .enumerate()
        .map(|(selected, _)| {
            let conditions = parts
                .iter()
                .enumerate()
                .map(|(index, candidate)| {
                    exact_rewrite_app(
                        "=",
                        vec![
                            candidate.clone(),
                            if index == selected {
                                small.clone()
                            } else {
                                empty.clone()
                            },
                        ],
                    )
                })
                .collect::<Vec<_>>();
            exact_rewrite_app("and", conditions)
        })
        .collect::<Vec<_>>();
    Some(exact_rewrite_app("or", choices))
}

#[derive(Clone, Copy)]
enum ExactFixedWordLanguage {
    Prefixes,
    Suffixes,
    Substrings,
}

/// Expands membership in the finite prefix, suffix, or substring language of a
/// fixed small word. These are complete source-theory languages, independent
/// of the packed-string bound; the cap controls only normal-form size.
fn exact_rewrite_fixed_word_language(
    word: &[u32],
    candidate: &ExactRewriteTerm,
    language: ExactFixedWordLanguage,
) -> Option<ExactRewriteTerm> {
    if word.len() > 4 {
        return None;
    }
    let words = match language {
        ExactFixedWordLanguage::Prefixes => (0..=word.len())
            .map(|end| word[..end].to_vec())
            .collect::<BTreeSet<_>>(),
        ExactFixedWordLanguage::Suffixes => (0..=word.len())
            .map(|start| word[start..].to_vec())
            .collect::<BTreeSet<_>>(),
        ExactFixedWordLanguage::Substrings => (0..=word.len())
            .flat_map(|start| (start..=word.len()).map(move |end| word[start..end].to_vec()))
            .collect::<BTreeSet<_>>(),
    };
    Some(exact_rewrite_app(
        "or",
        words
            .into_iter()
            .map(|word| {
                exact_rewrite_app("=", vec![candidate.clone(), ExactRewriteTerm::String(word)])
            })
            .collect(),
    ))
}

/// Routes a fixed index through a concatenation when the leading component has
/// an exact source-theory length. Index zero also commutes with repeated copies
/// of the same possibly-empty component.
fn exact_rewrite_concat_at(
    subject: &ExactRewriteTerm,
    index: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, Int};

    let App(head, parts) = subject else {
        return None;
    };
    if !matches!(head.as_str(), "str.++" | "seq.++") || parts.len() < 2 || parts.len() > 6 {
        return None;
    }
    let first = &parts[0];
    let Int(index) = index else {
        return None;
    };
    if *index == 0 && parts.iter().all(|part| part == first) {
        return Some(exact_rewrite_app("str.at", vec![first.clone(), Int(0)]));
    }
    let minimum = exact_string_min_len(first, 0)?;
    let maximum = exact_string_max_len(first, 0)?;
    if minimum != maximum || *index < 0 {
        return None;
    }
    let length = i128::try_from(minimum).ok()?;
    if *index < length {
        return Some(exact_rewrite_app(
            "str.at",
            vec![first.clone(), Int(*index)],
        ));
    }
    Some(exact_rewrite_app(
        "str.at",
        vec![
            exact_rewrite_concat(&parts[1..]),
            Int(index.checked_sub(length)?),
        ],
    ))
}

/// Moves a substring start across one exact leading code point. The symbolic
/// case is sound when the length is nonpositive at start zero: negative starts
/// are empty, zero is empty by the premise, and positive starts are in the
/// suffix with the index shifted by one.
fn exact_rewrite_concat_substr(
    subject: &ExactRewriteTerm,
    offset: &ExactRewriteTerm,
    length: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, Int};

    let App(head, parts) = subject else {
        return None;
    };
    if !matches!(head.as_str(), "str.++" | "seq.++") || parts.len() < 2 || parts.len() > 6 {
        return None;
    }
    if exact_string_min_len(&parts[0], 0)? != 1 || exact_string_max_len(&parts[0], 0)? != 1 {
        return None;
    }
    let shifted = match offset {
        Int(offset) if *offset >= 1 => Int(offset.checked_sub(1)?),
        Int(_) => return None,
        offset if exact_affine_zero_forces_nonpositive(offset, length) => {
            exact_rewrite_app("-", vec![offset.clone(), Int(1)])
        }
        _ => return None,
    };
    Some(exact_rewrite_app(
        "str.substr",
        vec![exact_rewrite_concat(&parts[1..]), shifted, length.clone()],
    ))
}

/// A prefix of length at most one depends only on the first nonempty concat
/// component. The recursive call strictly shortens the flattened concat.
fn exact_rewrite_concat_prefix(
    prefix: &ExactRewriteTerm,
    word: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, String};

    if exact_string_max_len(prefix, 0)? > 1 {
        return None;
    }
    let App(head, parts) = word else {
        return None;
    };
    if !matches!(head.as_str(), "str.++" | "seq.++") || parts.len() < 2 || parts.len() > 6 {
        return None;
    }
    let first = &parts[0];
    let rest = exact_rewrite_concat(&parts[1..]);
    let first_empty = exact_rewrite_app("=", vec![first.clone(), String(Vec::new())]);
    Some(exact_rewrite_app(
        "ite",
        vec![
            first_empty,
            exact_rewrite_app("str.prefixof", vec![prefix.clone(), rest]),
            exact_rewrite_app("str.prefixof", vec![prefix.clone(), first.clone()]),
        ],
    ))
}

/// A suffix of length at most one depends only on the last nonempty concat
/// component. The recursive call strictly shortens the flattened concat.
fn exact_rewrite_concat_suffix(
    suffix: &ExactRewriteTerm,
    word: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::{App, String};

    if exact_string_max_len(suffix, 0)? > 1 {
        return None;
    }
    let App(head, parts) = word else {
        return None;
    };
    if !matches!(head.as_str(), "str.++" | "seq.++") || parts.len() < 2 || parts.len() > 6 {
        return None;
    }
    let last = parts.last()?;
    let rest = exact_rewrite_concat(&parts[..parts.len() - 1]);
    let last_empty = exact_rewrite_app("=", vec![last.clone(), String(Vec::new())]);
    Some(exact_rewrite_app(
        "ite",
        vec![
            last_empty,
            exact_rewrite_app("str.suffixof", vec![suffix.clone(), rest]),
            exact_rewrite_app("str.suffixof", vec![suffix.clone(), last.clone()]),
        ],
    ))
}

/// A needle of length at most one cannot cross a concatenation boundary, so it
/// occurs in the whole word exactly when it occurs in at least one component.
fn exact_rewrite_concat_contains(
    subject: &ExactRewriteTerm,
    needle: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    use ExactRewriteTerm::App;

    if exact_string_max_len(needle, 0)? > 1 {
        return None;
    }
    let App(head, parts) = subject else {
        return None;
    };
    if !matches!(head.as_str(), "str.++" | "seq.++") || parts.len() > 6 {
        return None;
    }
    Some(exact_rewrite_app(
        "or",
        parts
            .iter()
            .map(|part| exact_rewrite_app("str.contains", vec![part.clone(), needle.clone()]))
            .collect(),
    ))
}

/// Boolean conjunction and disjunction are commutative after the n-ary
/// normalizer has flattened and deduplicated operands. Compare them as
/// multisets so differently ordered concat decompositions meet.
fn exact_boolean_nary_terms_equal(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
    let (
        ExactRewriteTerm::App(left_head, left_args),
        ExactRewriteTerm::App(right_head, right_args),
    ) = (left, right)
    else {
        return false;
    };
    if left_head != right_head
        || !matches!(left_head.as_str(), "and" | "or")
        || left_args.len() != right_args.len()
    {
        return false;
    }
    let mut matched = vec![false; right_args.len()];
    left_args.iter().all(|left_arg| {
        right_args
            .iter()
            .enumerate()
            .find(|(index, right_arg)| {
                !matched[*index]
                    && (left_arg == *right_arg
                        || exact_boolean_nary_terms_equal(left_arg, right_arg))
            })
            .is_some_and(|(index, _)| {
                matched[index] = true;
                true
            })
    })
}

/// Concatenation is commutative for words over one shared code point. Requiring
/// the same component multiset proves equal total length without trying to
/// infer symbolic lengths; the shared unary alphabet then proves equal content.
fn exact_unary_concat_terms_equal(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
    let (
        ExactRewriteTerm::App(left_head, left_parts),
        ExactRewriteTerm::App(right_head, right_parts),
    ) = (left, right)
    else {
        return false;
    };
    if !matches!(left_head.as_str(), "str.++" | "seq.++")
        || !matches!(right_head.as_str(), "str.++" | "seq.++")
        || left_parts.len() != right_parts.len()
    {
        return false;
    }

    let Some(alphabet) =
        left_parts
            .iter()
            .chain(right_parts)
            .try_fold(BTreeSet::new(), |mut alphabet, part| {
                alphabet.extend(exact_string_alphabet(part, 0)?);
                Some(alphabet)
            })
    else {
        return false;
    };
    if alphabet.len() > 1 {
        return false;
    }

    let mut matched = vec![false; right_parts.len()];
    left_parts.iter().all(|left_part| {
        right_parts
            .iter()
            .enumerate()
            .find(|(index, right_part)| !matched[*index] && left_part == *right_part)
            .is_some_and(|(index, _)| {
                matched[index] = true;
                true
            })
    })
}

fn exact_concat_residual(
    base: &ExactRewriteTerm,
    candidate: &ExactRewriteTerm,
) -> Option<ExactRewriteTerm> {
    let ExactRewriteTerm::App(head, parts) = candidate else {
        return None;
    };
    if !matches!(head.as_str(), "str.++" | "seq.++") || parts.len() != 2 {
        return None;
    }
    if &parts[0] == base {
        Some(parts[1].clone())
    } else if &parts[1] == base {
        Some(parts[0].clone())
    } else {
        None
    }
}

fn exact_self_view_is_strict(base: &ExactRewriteTerm, candidate: &ExactRewriteTerm) -> bool {
    use ExactRewriteTerm::{App, Int};

    let App(head, args) = candidate else {
        return false;
    };
    match (head.as_str(), args.as_slice()) {
        ("str.at", [source, Int(index)]) => source == base && *index >= 1,
        ("str.substr", [source, Int(offset), _]) => source == base && *offset >= 1,
        ("str.substr", [source, offset, length]) => source == base && offset == length,
        _ => false,
    }
}

/// Proves `len(shorter) <= len(longer)` from source-theory structure alone.
/// Every recursive case is an SMT-LIB length theorem; no declared packed bound
/// or inferred benchmark-specific limit enters this relation.
fn exact_string_length_le(
    shorter: &ExactRewriteTerm,
    longer: &ExactRewriteTerm,
    depth: u32,
) -> bool {
    use ExactRewriteTerm::{App, String};

    if depth > 32 || shorter == longer {
        return shorter == longer;
    }
    if matches!(shorter, String(value) if value.is_empty()) {
        return true;
    }
    if let (String(shorter), String(longer)) = (shorter, longer) {
        return shorter.len() <= longer.len();
    }
    if let (Some(maximum), Some(minimum)) = (
        exact_string_max_len(shorter, depth + 1),
        exact_string_min_len(longer, depth + 1),
    ) && maximum <= minimum
    {
        return true;
    }
    match shorter {
        App(head, args)
            if matches!(head.as_str(), "str.at" | "str.substr") && args.first() == Some(longer) =>
        {
            return true;
        }
        App(head, args) if head == "str.replace" => {
            if let [subject, needle, replacement] = args.as_slice()
                && subject == longer
                && exact_string_length_le(replacement, needle, depth + 1)
            {
                return true;
            }
        }
        _ => {}
    }
    match longer {
        App(head, parts)
            if matches!(head.as_str(), "str.++" | "seq.++")
                && parts.iter().any(|part| part == shorter) =>
        {
            return true;
        }
        App(head, args) if head == "str.replace" => {
            if let [subject, needle, replacement] = args.as_slice()
                && subject == shorter
                // Replacing inside `subject` by all of `subject` cannot shorten it.
                && (replacement == subject
                    || exact_string_length_le(needle, replacement, depth + 1))
            {
                return true;
            }
        }
        _ => {}
    }
    false
}

fn exact_string_min_len(term: &ExactRewriteTerm, depth: u32) -> Option<usize> {
    use ExactRewriteTerm::{App, String};

    if depth > 32 {
        return None;
    }
    match term {
        String(value) => Some(value.len()),
        App(head, parts) if matches!(head.as_str(), "str.++" | "seq.++") => {
            parts.iter().try_fold(0_usize, |sum, part| {
                sum.checked_add(exact_string_min_len(part, depth + 1)?)
            })
        }
        App(head, args) if head == "ite" => {
            let [_, then_term, else_term] = args.as_slice() else {
                return None;
            };
            Some(
                exact_string_min_len(then_term, depth + 1)?
                    .min(exact_string_min_len(else_term, depth + 1)?),
            )
        }
        _ => None,
    }
}

fn exact_string_max_len(term: &ExactRewriteTerm, depth: u32) -> Option<usize> {
    use ExactRewriteTerm::{App, String};

    if depth > 32 {
        return None;
    }
    match term {
        String(value) => Some(value.len()),
        App(head, _) if head == "str.at" => Some(1),
        App(head, args) if head == "str.substr" => exact_string_max_len(args.first()?, depth + 1),
        App(head, parts) if matches!(head.as_str(), "str.++" | "seq.++") => {
            parts.iter().try_fold(0_usize, |sum, part| {
                sum.checked_add(exact_string_max_len(part, depth + 1)?)
            })
        }
        App(head, args) if head == "ite" => {
            let [_, then_term, else_term] = args.as_slice() else {
                return None;
            };
            Some(
                exact_string_max_len(then_term, depth + 1)?
                    .max(exact_string_max_len(else_term, depth + 1)?),
            )
        }
        App(head, args) if head == "str.replace" => {
            let [subject, needle, replacement] = args.as_slice() else {
                return None;
            };
            let subject_max = exact_string_max_len(subject, depth + 1)?;
            let needle_min = exact_string_min_len(needle, depth + 1)?;
            let replacement_max = exact_string_max_len(replacement, depth + 1)?;
            Some(
                subject_max.max(
                    subject_max
                        .saturating_sub(needle_min)
                        .checked_add(replacement_max)?,
                ),
            )
        }
        _ => None,
    }
}

fn exact_int_lower_bound(term: &ExactRewriteTerm, depth: u32) -> Option<i128> {
    use ExactRewriteTerm::{App, IndexOfSelf, Int};

    if depth > 32 {
        return None;
    }
    match term {
        Int(value) => Some(*value),
        IndexOfSelf(_) => Some(-1),
        App(head, _) if head == "str.indexof" => Some(-1),
        App(head, args) if matches!(head.as_str(), "str.len" | "seq.len") => {
            i128::try_from(exact_string_min_len(args.first()?, depth + 1)?).ok()
        }
        App(head, values) if head == "+" => values.iter().try_fold(0_i128, |sum, value| {
            sum.checked_add(exact_int_lower_bound(value, depth + 1)?)
        }),
        App(head, args) if head == "-" => match args.as_slice() {
            [value] => exact_int_upper_bound(value, depth + 1)?.checked_neg(),
            [left, right] => exact_int_lower_bound(left, depth + 1)?
                .checked_sub(exact_int_upper_bound(right, depth + 1)?),
            _ => None,
        },
        _ => None,
    }
}

fn exact_int_upper_bound(term: &ExactRewriteTerm, depth: u32) -> Option<i128> {
    use ExactRewriteTerm::{App, IndexOfSelf, Int};

    if depth > 32 {
        return None;
    }
    match term {
        Int(value) => Some(*value),
        IndexOfSelf(_) => Some(0),
        App(head, args) if matches!(head.as_str(), "str.len" | "seq.len") => {
            i128::try_from(exact_string_max_len(args.first()?, depth + 1)?).ok()
        }
        App(head, args) if head == "str.indexof" => {
            let [subject, _, offset] = args.as_slice() else {
                return None;
            };
            let maximum = exact_string_max_len(subject, depth + 1)?;
            if maximum == 0 || (maximum <= 1 && offset == &Int(0)) {
                Some(0)
            } else {
                i128::try_from(maximum).ok()
            }
        }
        App(head, values) if head == "+" => values.iter().try_fold(0_i128, |sum, value| {
            sum.checked_add(exact_int_upper_bound(value, depth + 1)?)
        }),
        App(head, args) if head == "-" => match args.as_slice() {
            [value] => exact_int_lower_bound(value, depth + 1)?.checked_neg(),
            [left, right] => exact_int_upper_bound(left, depth + 1)?
                .checked_sub(exact_int_lower_bound(right, depth + 1)?),
            _ => None,
        },
        _ => None,
    }
}

fn exact_is_length_of(term: &ExactRewriteTerm, subject: &ExactRewriteTerm) -> bool {
    matches!(
        term,
        ExactRewriteTerm::App(head, args)
            if matches!(head.as_str(), "str.len" | "seq.len")
                && matches!(args.as_slice(), [length_subject] if length_subject == subject)
    )
}

fn exact_negates(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
    matches!(
        right,
        ExactRewriteTerm::App(head, args)
            if head == "-" && matches!(args.as_slice(), [ExactRewriteTerm::Int(0), value]
                if value == left)
    )
}

fn exact_substr_is_empty(
    subject: &ExactRewriteTerm,
    offset: &ExactRewriteTerm,
    length: &ExactRewriteTerm,
) -> bool {
    use ExactRewriteTerm::{App, IndexOfSelf};

    if exact_int_upper_bound(length, 0).is_some_and(|upper| upper <= 0)
        || exact_is_length_of(offset, subject)
        || exact_negates(offset, length)
        || exact_negates(length, offset)
        || matches!((offset, length), (IndexOfSelf(argument), value) if argument.as_ref() == value)
    {
        return true;
    }
    if let (Some(maximum), Some(lower)) = (
        exact_string_max_len(subject, 0),
        exact_int_lower_bound(offset, 0),
    ) && i128::try_from(maximum).is_ok_and(|maximum| lower >= maximum)
    {
        return true;
    }
    if exact_string_max_len(subject, 0).is_some_and(|maximum| maximum <= 1) && offset == length {
        return true;
    }
    matches!(
        subject,
        App(head, args)
            if head == "str.substr"
                && matches!(args.as_slice(), [_, _, inner_length] if inner_length == offset)
    )
}

fn exact_view_index_is_out_of_range(subject: &ExactRewriteTerm, index: &ExactRewriteTerm) -> bool {
    use ExactRewriteTerm::App;

    if exact_int_upper_bound(index, 0).is_some_and(|upper| upper < 0)
        || exact_is_length_of(index, subject)
    {
        return true;
    }
    if let (Some(maximum), Some(lower)) = (
        exact_string_max_len(subject, 0),
        exact_int_lower_bound(index, 0),
    ) && i128::try_from(maximum).is_ok_and(|maximum| lower >= maximum)
    {
        return true;
    }
    matches!(
        subject,
        App(head, args)
            if head == "str.substr"
                && matches!(args.as_slice(), [_, _, inner_length] if inner_length == index)
    )
}

/// Returns a conservative finite set containing every code point a term can
/// produce. `None` means unknown; a returned set may be an over-approximation.
/// Disjoint returned sets therefore prove that two nonempty strings differ and
/// that a nonempty needle cannot occur in its subject.
fn exact_string_alphabet(term: &ExactRewriteTerm, depth: u32) -> Option<BTreeSet<u32>> {
    use ExactRewriteTerm::{App, String};

    if depth > 32 {
        return None;
    }
    match term {
        String(value) => Some(value.iter().copied().collect()),
        App(head, _) if head == "str.from_int" => Some((b'0'..=b'9').map(u32::from).collect()),
        App(head, args) if matches!(head.as_str(), "str.at" | "str.substr") => {
            exact_string_alphabet(args.first()?, depth + 1)
        }
        App(head, parts) if matches!(head.as_str(), "str.++" | "seq.++") => {
            parts
                .iter()
                .try_fold(BTreeSet::new(), |mut alphabet, part| {
                    alphabet.extend(exact_string_alphabet(part, depth + 1)?);
                    Some(alphabet)
                })
        }
        App(head, args) if head == "ite" => {
            let [_, then_term, else_term] = args.as_slice() else {
                return None;
            };
            let mut alphabet = exact_string_alphabet(then_term, depth + 1)?;
            alphabet.extend(exact_string_alphabet(else_term, depth + 1)?);
            Some(alphabet)
        }
        App(head, args) if head == "str.replace" => {
            let [subject, _, replacement] = args.as_slice() else {
                return None;
            };
            let mut alphabet = exact_string_alphabet(subject, depth + 1)?;
            alphabet.extend(exact_string_alphabet(replacement, depth + 1)?);
            Some(alphabet)
        }
        _ => None,
    }
}

fn exact_string_alphabets_disjoint(left: &ExactRewriteTerm, right: &ExactRewriteTerm) -> bool {
    let (Some(left), Some(right)) = (
        exact_string_alphabet(left, 0),
        exact_string_alphabet(right, 0),
    ) else {
        return false;
    };
    left.is_disjoint(&right)
}

fn exact_prefix_view(prefix: &ExactRewriteTerm, word: &ExactRewriteTerm) -> bool {
    use ExactRewriteTerm::{App, Int};

    if let App(head, parts) = word
        && matches!(head.as_str(), "str.++" | "seq.++")
        && parts.first() == Some(prefix)
    {
        return true;
    }
    matches!(
        prefix,
        App(head, args)
            if head == "str.substr"
                && matches!(args.as_slice(), [source, Int(0), _] if source == word)
    ) || matches!(
        prefix,
        App(head, args)
            if head == "str.at"
                && matches!(args.as_slice(), [source, Int(0)] if source == word)
    )
}

fn exact_suffix_view(suffix: &ExactRewriteTerm, word: &ExactRewriteTerm) -> bool {
    use ExactRewriteTerm::{App, Int};

    if let App(head, parts) = word
        && matches!(head.as_str(), "str.++" | "seq.++")
        && parts.last() == Some(suffix)
    {
        return true;
    }
    let App(head, args) = suffix else {
        return false;
    };
    if head == "str.substr"
        && let [source, offset, App(subtract, difference)] = args.as_slice()
        && source == word
        && subtract == "-"
        && matches!(difference.as_slice(), [App(length, length_args), tail_offset]
            if length == "str.len"
                && matches!(length_args.as_slice(), [length_source] if length_source == source)
                && tail_offset == offset)
    {
        return true;
    }
    head == "str.at"
        && matches!(args.as_slice(), [source, App(subtract, difference)]
            if source == word
                && subtract == "-"
                && matches!(difference.as_slice(), [App(length, length_args), Int(1)]
                    if length == "str.len"
                        && matches!(length_args.as_slice(), [length_source]
                            if length_source == source)))
}

fn exact_contained_view(subject: &ExactRewriteTerm, needle: &ExactRewriteTerm) -> bool {
    use ExactRewriteTerm::App;

    if let App(head, args) = needle
        && matches!(head.as_str(), "str.at" | "str.substr")
        && args.first() == Some(subject)
    {
        return true;
    }
    matches!(
        subject,
        App(head, parts)
            if matches!(head.as_str(), "str.++" | "seq.++")
                && parts.iter().any(|part| part == needle)
    )
}

/// Flattens associative Boolean connectives, removes their identity element,
/// and deduplicates repeated operands. These are exact Boolean-algebra laws;
/// retaining first-occurrence order keeps the normal form deterministic without
/// requiring an ordering over opaque source expressions.
fn exact_rewrite_boolean_nary(head: &str, values: &[ExactRewriteTerm]) -> ExactRewriteTerm {
    use ExactRewriteTerm::{App, Bool};

    let (absorbing, identity) = match head {
        "and" => (false, true),
        "or" => (true, false),
        _ => return App(head.to_owned(), values.to_vec()),
    };
    let mut terms = Vec::new();
    let mut pending: Vec<_> = values.iter().rev().cloned().collect();
    while let Some(value) = pending.pop() {
        match value {
            Bool(value) if value == absorbing => return Bool(absorbing),
            Bool(value) if value == identity => {}
            App(inner, nested) if inner == head => pending.extend(nested.into_iter().rev()),
            value if !terms.contains(&value) => terms.push(value),
            _ => {}
        }
    }
    if head == "and" {
        let assignments = terms
            .iter()
            .cloned()
            .map(|condition| (condition, true))
            .collect::<Vec<_>>();
        let facts = ExactEqualityFacts::from_assignments(&assignments);
        if facts.conflict {
            return Bool(false);
        }
        if terms.len() <= EXACT_BOOLEAN_ATOM_CAP {
            let mut semantic_terms = Vec::new();
            for (index, term) in terms.iter().enumerate() {
                // Rewrite one conjunct only from the *other* conjuncts.  Using
                // the conjunct itself as an assumption would erase every
                // condition as trivially true and is not equivalent.
                let other_assignments = terms
                    .iter()
                    .enumerate()
                    .filter(|(other, _)| *other != index)
                    .map(|(_, condition)| (condition.clone(), true))
                    .collect::<Vec<_>>();
                let other_facts = ExactEqualityFacts::from_assignments(&other_assignments);
                if other_facts.conflict {
                    return Bool(false);
                }
                match exact_rewrite_under_equality_facts(term, &other_facts, 0) {
                    Bool(false) => return Bool(false),
                    Bool(true) => {}
                    rewritten if !semantic_terms.contains(&rewritten) => {
                        semantic_terms.push(rewritten);
                    }
                    _ => {}
                }
            }
            if semantic_terms != terms {
                return exact_rewrite_boolean_nary(head, &semantic_terms);
            }
        }
    }
    match terms.as_slice() {
        [] => Bool(identity),
        [single] => single.clone(),
        _ => App(head.to_owned(), terms),
    }
}

fn exact_rewrite_sum(values: &[ExactRewriteTerm]) -> ExactRewriteTerm {
    use ExactRewriteTerm::{App, Int};

    let mut terms = Vec::new();
    let mut constant = 0_i128;
    for value in values {
        match value {
            Int(value) => {
                let Some(sum) = constant.checked_add(*value) else {
                    return App("+".to_owned(), values.to_vec());
                };
                constant = sum;
            }
            App(head, nested) if head == "+" => terms.extend(nested.iter().cloned()),
            value => terms.push(value.clone()),
        }
    }
    if constant != 0 || terms.is_empty() {
        terms.push(Int(constant));
    }
    match terms.as_slice() {
        [single] => single.clone(),
        _ => App("+".to_owned(), terms),
    }
}

fn exact_rewrite_concat(values: &[ExactRewriteTerm]) -> ExactRewriteTerm {
    use ExactRewriteTerm::{App, String};

    let mut out = Vec::new();
    for value in values {
        match value {
            String(value) if value.is_empty() => {}
            App(head, nested) if matches!(head.as_str(), "str.++" | "seq.++") => {
                out.extend(nested.iter().cloned());
            }
            value => out.push(value.clone()),
        }
    }
    let mut merged = Vec::new();
    for value in out {
        match (merged.last_mut(), value) {
            (Some(String(left)), String(right)) => left.extend(right),
            (_, value) => merged.push(value),
        }
    }
    match merged.as_slice() {
        [] => String(Vec::new()),
        [single] => single.clone(),
        _ => App("str.++".to_owned(), merged),
    }
}

fn exact_rewrite_indexof(
    subject: &ExactRewriteTerm,
    needle: &ExactRewriteTerm,
    offset: Option<i128>,
) -> Option<i128> {
    use ExactRewriteTerm::String;

    if offset.is_some_and(|offset| offset < 0) {
        return Some(-1);
    }
    if offset == Some(0) && subject == needle {
        return Some(0);
    }
    let (String(subject), String(needle)) = (subject, needle) else {
        return (offset == Some(0) && matches!(needle, String(value) if value.is_empty()))
            .then_some(0);
    };
    if !needle.is_empty()
        && !subject
            .windows(needle.len())
            .any(|candidate| candidate == needle)
    {
        return Some(-1);
    }
    let offset = offset?;
    let Ok(offset) = usize::try_from(offset) else {
        return Some(-1);
    };
    if offset > subject.len() {
        return Some(-1);
    }
    if needle.is_empty() {
        return i128::try_from(offset).ok();
    }
    subject[offset..]
        .windows(needle.len())
        .position(|candidate| candidate == needle)
        .and_then(|position| i128::try_from(offset + position).ok())
        .or(Some(-1))
}

fn replace_first_code_points(subject: &[u32], needle: &[u32], replacement: &[u32]) -> Vec<u32> {
    if needle.is_empty() {
        let mut result = replacement.to_vec();
        result.extend_from_slice(subject);
        return result;
    }
    let Some(position) = subject
        .windows(needle.len())
        .position(|candidate| candidate == needle)
    else {
        return subject.to_vec();
    };
    let mut result = Vec::with_capacity(subject.len() - needle.len() + replacement.len());
    result.extend_from_slice(&subject[..position]);
    result.extend_from_slice(replacement);
    result.extend_from_slice(&subject[position + needle.len()..]);
    result
}

fn exact_rewrite_contradiction(conjuncts: &[&SExpr]) -> bool {
    let terms: Vec<_> = conjuncts
        .iter()
        .map(|conjunct| exact_rewrite_term(conjunct, 0))
        .collect();
    terms
        .iter()
        .any(|term| term == &ExactRewriteTerm::Bool(false))
        || exact_boolean_alias_contradiction(&terms)
}

/// Propagates exact top-level Boolean aliases before checking their induced
/// equality facts.
///
/// Symbolic-execution generators commonly spell one path condition as
/// `T = condition; assert T`.  Looking at either conjunct alone misses direct
/// contradictions such as two aliases requiring `s = ""` and `s != ""`.
/// This pass follows Boolean-valued symbol definitions, selected top-level
/// `ite` branches, strict-order disequalities, and exact string emptiness/concat
/// length consequences; every queued assignment is therefore forced by the
/// asserted conjunction.  The final equality check remains deliberately
/// limited to congruence classes, explicit disequalities, and nonnegative
/// string-length lower bounds.
#[allow(clippy::too_many_lines)] // One auditable, fail-closed path-propagation pass.
fn exact_boolean_alias_contradiction(terms: &[ExactRewriteTerm]) -> bool {
    use ExactRewriteTerm::{App, Bool, Opaque};

    let mut aliases = Vec::new();
    let mut length_aliases = Vec::new();
    for term in terms {
        let App(head, args) = term else {
            continue;
        };
        let [left, right] = args.as_slice() else {
            continue;
        };
        if head != "=" {
            continue;
        }
        for (symbol, condition) in [(left, right), (right, left)] {
            if matches!(symbol, Opaque(expression) if expression.atom().is_some()) {
                if exact_term_is_boolean(condition) {
                    aliases.push((symbol.clone(), condition.clone()));
                }
                if matches!(condition, App(head, args)
                    if matches!(head.as_str(), "str.len" | "seq.len") && args.len() == 1)
                {
                    length_aliases.push((symbol.clone(), condition.clone()));
                }
            }
        }
    }
    if aliases.is_empty() {
        return false;
    }
    let guarded_branches: Vec<_> = terms
        .iter()
        .filter_map(|term| match term {
            App(head, args) if head == "ite" => {
                let [guard, then_term, else_term] = args.as_slice() else {
                    return None;
                };
                Some((guard.clone(), then_term.clone(), else_term.clone()))
            }
            _ => None,
        })
        .collect();

    let mut assignments: Vec<(ExactRewriteTerm, bool)> = Vec::new();
    let mut pending: Vec<_> = terms.iter().cloned().map(|term| (term, true)).collect();
    while let Some((condition, required)) = pending.pop() {
        if let Some((_, prior)) = assignments
            .iter()
            .find(|(candidate, _)| exact_conditions_equal(candidate, &condition))
        {
            if *prior != required {
                return true;
            }
            continue;
        }
        assignments.push((condition.clone(), required));

        match &condition {
            Bool(actual) if *actual != required => return true,
            App(head, args) if head == "not" && args.len() == 1 => {
                pending.push((args[0].clone(), !required));
            }
            App(head, args) if head == "and" && required => {
                pending.extend(args.iter().cloned().map(|argument| (argument, true)));
            }
            App(head, args) if head == "or" && !required => {
                pending.extend(args.iter().cloned().map(|argument| (argument, false)));
            }
            _ => {}
        }
        if !required {
            pending.push((exact_rewrite_app("not", vec![condition.clone()]), true));
            if let App(head, args) = &condition
                && head == "="
                && let [left, right] = args.as_slice()
            {
                pending.push((
                    exact_rewrite_app(
                        "not",
                        vec![exact_rewrite_app("=", vec![right.clone(), left.clone()])],
                    ),
                    true,
                ));
            }
        }
        if let Some(disequality) = exact_order_disequality(&condition, required) {
            pending.push((disequality, false));
        }
        if let Some(consequence) =
            exact_length_emptiness_consequence(&condition, required, &length_aliases)
        {
            match consequence {
                ExactLengthEmptiness::Conflict => pending.push((Bool(false), true)),
                ExactLengthEmptiness::Requires { subject, empty } => pending.push((
                    exact_rewrite_app("=", vec![subject, ExactRewriteTerm::String(Vec::new())]),
                    empty,
                )),
            }
        }
        for (guard, then_term, else_term) in &guarded_branches {
            if exact_conditions_equal(&condition, guard) {
                pending.push((
                    if required {
                        then_term.clone()
                    } else {
                        else_term.clone()
                    },
                    true,
                ));
            }
        }

        for (symbol, definition) in &aliases {
            if exact_conditions_equal(&condition, symbol) {
                pending.push((definition.clone(), required));
            } else if exact_conditions_equal(&condition, definition) {
                pending.push((symbol.clone(), required));
            }
        }
    }

    let facts = ExactEqualityFacts::from_assignments(&assignments);
    facts.conflict
        || exact_order_assignments_conflict(&assignments, &facts)
        || exact_fixed_segment_overlap_conflict(&facts)
        || facts.string_length_conflict()
}

struct ExactFixedSegment {
    source: usize,
    position: usize,
    value: Vec<u32>,
}

/// Finds conflicting fixed words anchored at exact offsets in two equal concat
/// decompositions of the same source.  If one segment starts `k` code points
/// after another and lies wholly inside it, their overlapping code points must
/// agree.  All source, position, and prefix-length links come from equality
/// classes; an unproved offset or partial overlap is a decline.
#[allow(clippy::too_many_lines)] // One auditable fail-closed overlap proof.
fn exact_fixed_segment_overlap_conflict(facts: &ExactEqualityFacts) -> bool {
    use ExactRewriteTerm::{App, String};

    fn append_segment(out: &mut Vec<ExactRewriteTerm>, segment: ExactRewriteTerm) {
        match (out.last_mut(), segment) {
            (_, String(value)) if value.is_empty() => {}
            (Some(String(left)), String(right)) => left.extend(right),
            (_, segment) => out.push(segment),
        }
    }

    fn expand(
        facts: &ExactEqualityFacts,
        term: &ExactRewriteTerm,
        visited: &mut BTreeSet<usize>,
        depth: u32,
    ) -> Vec<ExactRewriteTerm> {
        if depth > 32 {
            return vec![term.clone()];
        }
        if let Some(String(value)) = facts.literal_for(term) {
            return (!value.is_empty())
                .then_some(String(value))
                .into_iter()
                .collect();
        }
        let Some(index) = facts.index_of(term) else {
            return vec![term.clone()];
        };
        let root = facts.root(index);
        if !visited.insert(root) {
            return vec![term.clone()];
        }
        let concat = facts
            .terms
            .iter()
            .enumerate()
            .find(|(candidate, candidate_term)| {
                facts.root(*candidate) == root
                    && matches!(candidate_term, App(head, _)
                        if matches!(head.as_str(), "str.++" | "seq.++"))
            })
            .map(|(_, term)| term);
        let Some(App(_, parts)) = concat else {
            visited.remove(&root);
            return vec![term.clone()];
        };
        let mut out = Vec::new();
        for part in parts {
            for segment in expand(facts, part, visited, depth + 1) {
                append_segment(&mut out, segment);
            }
        }
        visited.remove(&root);
        out
    }

    fn position_delta(facts: &ExactEqualityFacts, later: usize, earlier: usize) -> Option<i128> {
        for (later_index, later_term) in facts.terms.iter().enumerate() {
            if facts.root(later_index) != later {
                continue;
            }
            for (earlier_index, earlier_term) in facts.terms.iter().enumerate() {
                if facts.root(earlier_index) != earlier {
                    continue;
                }
                let Some(difference) = exact_affine_difference(later_term, earlier_term) else {
                    continue;
                };
                if difference.terms.is_empty() {
                    return Some(difference.constant);
                }
            }
        }
        None
    }

    let mut segments = Vec::new();
    for (index, term) in facts.terms.iter().enumerate() {
        let App(head, parts) = term else {
            continue;
        };
        if !matches!(head.as_str(), "str.++" | "seq.++") {
            continue;
        }
        let mut expanded = Vec::new();
        let mut visited = BTreeSet::new();
        for part in parts {
            for segment in expand(facts, part, &mut visited, 0) {
                append_segment(&mut expanded, segment);
            }
        }
        for (segment_index, segment) in expanded.iter().enumerate() {
            let String(value) = segment else {
                continue;
            };
            if value.is_empty() {
                continue;
            }
            let prefix = exact_rewrite_concat(&expanded[..segment_index]);
            let prefix_length = exact_rewrite_app("str.len", vec![prefix]);
            let Some(position) = facts.index_of(&prefix_length) else {
                continue;
            };
            segments.push(ExactFixedSegment {
                source: facts.root(index),
                position: facts.root(position),
                value: value.clone(),
            });
        }
    }

    segments.iter().enumerate().any(|(index, earlier)| {
        segments[index + 1..].iter().any(|later| {
            if earlier.source != later.source {
                return false;
            }
            for (earlier, later) in [(earlier, later), (later, earlier)] {
                let Some(offset) = position_delta(facts, later.position, earlier.position)
                    .and_then(|offset| usize::try_from(offset).ok())
                else {
                    continue;
                };
                let Some(end) = offset.checked_add(later.value.len()) else {
                    continue;
                };
                if end <= earlier.value.len()
                    && &earlier.value[offset..end] != later.value.as_slice()
                {
                    return true;
                }
            }
            false
        })
    })
}

/// Whether two required linear-order atoms form an opposite cycle with at
/// least one strict edge.  Over a total arithmetic order, `a <= b` and
/// `b <= a` may meet at equality, while any strict edge makes the pair
/// contradictory.  Equality endpoints are compared through exact classes only.
fn exact_order_assignments_conflict(
    assignments: &[(ExactRewriteTerm, bool)],
    facts: &ExactEqualityFacts,
) -> bool {
    fn constraint(
        condition: &ExactRewriteTerm,
        required: bool,
    ) -> Option<(&ExactRewriteTerm, &ExactRewriteTerm, bool)> {
        let ExactRewriteTerm::App(relation, args) = condition else {
            return None;
        };
        let [left, right] = args.as_slice() else {
            return None;
        };
        match (relation.as_str(), required) {
            ("<", true) | (">=", false) => Some((left, right, true)),
            ("<", false) | (">=", true) => Some((right, left, false)),
            ("<=", true) | (">", false) => Some((left, right, false)),
            ("<=", false) | (">", true) => Some((right, left, true)),
            _ => None,
        }
    }

    let constraints: Vec<_> = assignments
        .iter()
        .filter_map(|(condition, required)| constraint(condition, *required))
        .collect();
    constraints.iter().enumerate().any(|(index, first)| {
        (first.2 && facts.equal(first.0, first.1))
            || constraints[index + 1..].iter().any(|second| {
                (first.2 || second.2)
                    && facts.equal(first.0, second.1)
                    && facts.equal(first.1, second.0)
            })
    })
}

/// A strict order known true, or a non-strict order known false, forces its
/// operands to differ.  No converse or integrality-specific inference is used.
fn exact_order_disequality(
    condition: &ExactRewriteTerm,
    required: bool,
) -> Option<ExactRewriteTerm> {
    let ExactRewriteTerm::App(relation, args) = condition else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    ((required && matches!(relation.as_str(), "<" | ">"))
        || (!required && matches!(relation.as_str(), "<=" | ">=")))
    .then(|| exact_rewrite_app("=", vec![left.clone(), right.clone()]))
}

enum ExactLengthEmptiness {
    Conflict,
    Requires {
        subject: ExactRewriteTerm,
        empty: bool,
    },
}

/// Extracts only those integral string-length comparisons that force
/// emptiness or nonemptiness.  String length is a nonnegative integer, so the
/// boundary between the two cases is exact at zero/one; wider bounds are used
/// only when one polarity still forces the same side of that boundary.
fn exact_length_emptiness_consequence(
    condition: &ExactRewriteTerm,
    required: bool,
    aliases: &[(ExactRewriteTerm, ExactRewriteTerm)],
) -> Option<ExactLengthEmptiness> {
    use ExactLengthEmptiness::{Conflict, Requires};
    use ExactRewriteTerm::{App, Int};

    let App(relation, args) = condition else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    let direct_length_subject = |term: &ExactRewriteTerm| match term {
        App(head, args) if matches!(head.as_str(), "str.len" | "seq.len") => {
            let [subject] = args.as_slice() else {
                return None;
            };
            Some(subject.clone())
        }
        _ => None,
    };
    let length_subject = |term: &ExactRewriteTerm| {
        direct_length_subject(term).or_else(|| {
            aliases.iter().find_map(|(symbol, length)| {
                exact_conditions_equal(term, symbol)
                    .then(|| direct_length_subject(length))
                    .flatten()
            })
        })
    };
    let (relation, subject, bound) =
        if let (Some(subject), Int(bound)) = (length_subject(left), right) {
            (relation.as_str(), subject, *bound)
        } else if let (Int(bound), Some(subject)) = (left, length_subject(right)) {
            let relation = match relation.as_str() {
                "<" => ">",
                "<=" => ">=",
                ">" => "<",
                ">=" => "<=",
                "=" => "=",
                _ => return None,
            };
            (relation, subject, *bound)
        } else {
            return None;
        };

    let empty = match relation {
        "=" if required => {
            if bound < 0 {
                return Some(Conflict);
            }
            bound == 0
        }
        "=" if bound == 0 => false,
        "<" if required => {
            if bound <= 0 {
                return Some(Conflict);
            }
            if bound != 1 {
                return None;
            }
            true
        }
        "<" if bound >= 1 => false,
        "<=" if required => {
            if bound < 0 {
                return Some(Conflict);
            }
            if bound != 0 {
                return None;
            }
            true
        }
        "<=" if bound >= 0 => false,
        ">" if required && bound >= 0 => false,
        ">" if !required => {
            if bound < 0 {
                return Some(Conflict);
            }
            if bound != 0 {
                return None;
            }
            true
        }
        ">=" if required && bound >= 1 => false,
        ">=" if !required => {
            if bound <= 0 {
                return Some(Conflict);
            }
            if bound != 1 {
                return None;
            }
            true
        }
        _ => return None,
    };
    Some(Requires { subject, empty })
}

// This path is intentionally population-gated. The exact condition comparison
// is useful on dense symbolic-execution paths, but charging every small string
// query for it can consume a meaningful fraction of a sub-second solve budget.
// The measured PyEx family starts at 131 flattened guaranteed conjuncts; 64
// leaves ample headroom while excluding the 26-conjunct retained control that
// exposed the overhead regression.
const BOOLEAN_PATH_MIN_CONJUNCTS: usize = 64;

/// Whether unconditional path literals require one exact Boolean condition both
/// true and false.
///
/// Symbolic-execution corpora commonly re-encode a predicate `p` as
/// `(= (ite p 1 0) 0)` and wrap that indicator in varying numbers of `not`s.
/// [`guaranteed_boolean_condition`] recovers the original condition and required
/// polarity. A structural match is deliberately strict: no algebraic equivalence
/// or implication is assumed, so a positive/negative collision is a direct
/// propositional contradiction for every theory interpretation.
#[cold]
#[inline(never)]
fn guaranteed_boolean_literal_conflict(conjuncts: &[&SExpr]) -> bool {
    let mut required_true = BTreeSet::new();
    let mut required_false = BTreeSet::new();
    let mut empty_views = Vec::new();
    let mut nonempty_views = Vec::new();
    let mut contains_literals: Vec<(&SExpr, Vec<u32>, bool)> = Vec::new();
    let mut at_most_one_views = Vec::new();
    let mut boundary_literals: Vec<(&SExpr, bool, Vec<u32>, bool)> = Vec::new();
    for conjunct in conjuncts {
        let (condition, required) = guaranteed_boolean_condition(conjunct);
        let (same, opposite) = if required {
            (&mut required_true, &required_false)
        } else {
            (&mut required_false, &required_true)
        };
        if opposite.contains(condition) {
            return true;
        }
        same.insert(condition);

        if let Some((view, condition_means_empty)) = exact_empty_condition(condition) {
            if required == condition_means_empty {
                if contains_literals
                    .iter()
                    .any(|(seen_view, _, seen_required)| *seen_view == view && *seen_required)
                {
                    return true;
                }
                empty_views.push(view);
                if let Some(base) = exact_one_code_point_bound(view) {
                    at_most_one_views.push(base);
                }
            } else {
                nonempty_views.push(view);
            }
        }

        if let Some((view, literal, condition_means_contains)) =
            exact_contains_literal_condition(condition)
        {
            let required_contains = required == condition_means_contains;
            if required_contains && empty_views.contains(&view) {
                return true;
            }
            if contains_literals
                .iter()
                .any(|(seen_view, seen_literal, seen_required)| {
                    *seen_view == view
                        && *seen_literal == literal
                        && *seen_required != required_contains
                })
            {
                return true;
            }
            contains_literals.push((view, literal, required_contains));
        }

        if let Some((view, literal, condition_means_at_equality)) =
            exact_at_literal_equality(condition)
            && required == condition_means_at_equality
        {
            // `str.at(W, i) = C` for one code point proves both that W is
            // nonempty and that W contains C, at every integer i.
            if empty_views.contains(&view)
                || contains_literals
                    .iter()
                    .any(|(seen_view, seen_literal, seen_required)| {
                        *seen_view == view && *seen_literal == literal && !*seen_required
                    })
            {
                return true;
            }
            contains_literals.push((view, literal, true));
        }

        if let Some((view, first, literal, condition_means_at_equality)) =
            exact_boundary_at_literal_equality(condition)
        {
            boundary_literals.push((
                view,
                first,
                literal,
                required == condition_means_at_equality,
            ));
        }
    }

    exact_boundary_literal_conflict(boundary_literals, &nonempty_views, &at_most_one_views)
}

fn exact_boundary_literal_conflict<'a>(
    mut boundary_literals: Vec<(&'a SExpr, bool, Vec<u32>, bool)>,
    nonempty_views: &[&'a SExpr],
    at_most_one_views: &[&'a SExpr],
) -> bool {
    let original_boundary_literals = boundary_literals.clone();
    for (view, first, literal, equal) in original_boundary_literals {
        if !first || (!equal && !nonempty_views.contains(&view)) {
            continue;
        }
        let mut current = view;
        while let Some(base) = exact_zero_prefix_base(current) {
            boundary_literals.push((base, true, literal.clone(), equal));
            current = base;
        }
    }

    for (index, (left_view, left_first, left_literal, left_equal)) in
        boundary_literals.iter().enumerate()
    {
        for (right_view, right_first, right_literal, right_equal) in &boundary_literals[index + 1..]
        {
            if left_view != right_view
                || (left_first != right_first && !at_most_one_views.contains(left_view))
            {
                continue;
            }
            if (*left_equal && *right_equal && left_literal != right_literal)
                || (left_literal == right_literal && left_equal != right_equal)
            {
                return true;
            }
        }
    }
    false
}

/// The base `W` when `view` is `substr(W, 0, len(W) - 1)`. This view is empty
/// exactly when `W` has length at most one, including SMT-LIB's total negative-
/// length case for the empty word.
fn exact_one_code_point_bound(view: &SExpr) -> Option<&SExpr> {
    let [head, subject, offset, length] = view.list()? else {
        return None;
    };
    if !matches!(head.atom(), Some("str.substr" | "seq.extract"))
        || parse_int_literal(offset) != Some(0)
        || len_minus_constant(strip_subtracted_zero(length), subject) != Some(1)
    {
        return None;
    }
    Some(subject)
}

/// The base of any zero-offset substring. If the substring is known nonempty,
/// its first code point is exactly the base's first code point.
fn exact_zero_prefix_base(view: &SExpr) -> Option<&SExpr> {
    let [head, subject, offset, _length] = view.list()? else {
        return None;
    };
    (matches!(head.atom(), Some("str.substr" | "seq.extract"))
        && parse_int_literal(offset) == Some(0))
    .then_some(subject)
}

/// The exact empty-string condition encoded by `len(W) = 0`, allowing an
/// arbitrary number of structural negations around the equality.
fn exact_empty_condition(mut condition: &SExpr) -> Option<(&SExpr, bool)> {
    let mut negated = false;
    while let Some([head, inner]) = condition.list()
        && head.atom() == Some("not")
    {
        negated = !negated;
        condition = inner;
    }
    empty_string_view(condition).map(|view| (view, !negated))
}

/// Canonicalizes exact `contains`/`indexof` path predicates to
/// `(view, nonempty literal, condition means contains)`.
///
/// At offset zero SMT-LIB totality gives
/// `indexof(W, C, 0) = -1` iff `not contains(W, C)` for every nonempty literal
/// `C`. Accepting only the same structural `W`, the same decoded literal, and
/// equality with `-1` keeps this cross-spelling comparison exact and fail closed.
fn exact_contains_literal_condition(mut condition: &SExpr) -> Option<(&SExpr, Vec<u32>, bool)> {
    let mut negated = false;
    while let Some([head, inner]) = condition.list()
        && head.atom() == Some("not")
    {
        negated = !negated;
        condition = inner;
    }

    if let Some([head, view, literal]) = condition.list()
        && head.atom() == Some("str.contains")
    {
        let literal = literal_pattern_cps(literal)?;
        if literal.is_empty() {
            return None;
        }
        return Some((view, literal, !negated));
    }

    let [head, left, right] = condition.list()? else {
        return None;
    };
    if head.atom() != Some("=") {
        return None;
    }
    let indexof = if parse_int_literal(right) == Some(-1) {
        left
    } else if parse_int_literal(left) == Some(-1) {
        right
    } else {
        return None;
    };
    let [head, view, literal, offset] = indexof.list()? else {
        return None;
    };
    if head.atom() != Some("str.indexof") || parse_int_literal(offset) != Some(0) {
        return None;
    }
    let literal = literal_pattern_cps(literal)?;
    if literal.is_empty() {
        return None;
    }
    Some((view, literal, negated))
}

/// Canonicalizes `str.at(W, i) = C` for a one-code-point literal C, returning
/// whether the surrounding condition means the equality or its negation.
fn exact_at_literal_equality(mut condition: &SExpr) -> Option<(&SExpr, Vec<u32>, bool)> {
    let mut negated = false;
    while let Some([head, inner]) = condition.list()
        && head.atom() == Some("not")
    {
        negated = !negated;
        condition = inner;
    }
    let [head, left, right] = condition.list()? else {
        return None;
    };
    if head.atom() != Some("=") {
        return None;
    }
    for (candidate, literal) in [(left, right), (right, left)] {
        let Some([head, view, _index]) = candidate.list() else {
            continue;
        };
        if head.atom() != Some("str.at") {
            continue;
        }
        let literal = literal_pattern_cps(literal)?;
        if literal.len() == 1 {
            return Some((view, literal, !negated));
        }
    }
    None
}

/// Canonicalizes a one-code-point equality at either boundary of one word:
/// `str.at(W, 0) = C` or `str.at(W, len(W)-1) = C`.
fn exact_boundary_at_literal_equality(
    mut condition: &SExpr,
) -> Option<(&SExpr, bool, Vec<u32>, bool)> {
    let mut negated = false;
    while let Some([head, inner]) = condition.list()
        && head.atom() == Some("not")
    {
        negated = !negated;
        condition = inner;
    }
    let [head, left, right] = condition.list()? else {
        return None;
    };
    if head.atom() != Some("=") {
        return None;
    }
    for (candidate, literal) in [(left, right), (right, left)] {
        let Some([head, view, index]) = candidate.list() else {
            continue;
        };
        if head.atom() != Some("str.at") {
            continue;
        }
        let first = if parse_int_literal(index) == Some(0) {
            true
        } else if len_minus_constant(index, view) == Some(1) {
            false
        } else {
            continue;
        };
        let literal = literal_pattern_cps(literal)?;
        if literal.len() == 1 {
            return Some((view, first, literal, !negated));
        }
    }
    None
}

/// Computes exact constant propagation and the distinct-index splice theorem over
/// guaranteed top-level equality paths. Every fact is a consequence of the whole
/// asserted conjunction, so adding it to the word relaxation preserves UNSAT.
#[allow(clippy::too_many_lines)] // One auditable, fail-closed semantic analysis pass.
fn source_string_semantic_facts(exprs: &[SExpr]) -> SourceStringSemanticFacts {
    // These facts describe the conjunction of every assertion in the script. They
    // cannot be applied to one scoped query or across a macro expansion whose
    // source-level equality path is not represented here.
    let mut check_sats = 0_u32;
    let mut saw_check_sat = false;
    for expression in exprs {
        let head = expression
            .list()
            .and_then(|items| items.first())
            .and_then(SExpr::atom);
        if head == Some("check-sat") {
            check_sats = check_sats.saturating_add(1);
            saw_check_sat = true;
        }
        // The single-result front door solves the assertion stack *at* check-sat;
        // a later assertion is not part of that query. Decline the whole source
        // fact rather than smuggling a post-query contradiction into the verdict.
        if saw_check_sat && head == Some("assert") {
            return SourceStringSemanticFacts::default();
        }
        if let Some(
            "push" | "pop" | "check-sat-assuming" | "reset-assertions" | "define-fun"
            | "define-fun-rec" | "define-funs-rec" | "define-sort",
        ) = head
        {
            return SourceStringSemanticFacts::default();
        }
    }
    if check_sats > 1 {
        return SourceStringSemanticFacts::default();
    }

    let conjuncts = guaranteed_top_level_conjuncts(exprs);
    let eager_boolean_path_conflict = conjuncts.len() >= BOOLEAN_PATH_MIN_CONJUNCTS
        && guaranteed_boolean_literal_conflict(&conjuncts);
    let exact_rewrite_conflict =
        eager_boolean_path_conflict || exact_rewrite_contradiction(&conjuncts);
    let equalities: Vec<(&SExpr, &SExpr)> = conjuncts
        .iter()
        .filter_map(|conjunct| positive_word_equality(conjunct))
        .collect();
    let disequalities: Vec<(&SExpr, &SExpr)> = conjuncts
        .iter()
        .filter_map(|conjunct| negative_word_equality(conjunct))
        .collect();
    if equalities.is_empty() && disequalities.is_empty() {
        return SourceStringSemanticFacts {
            conflict: exact_rewrite_conflict,
            eager_boolean_path_conflict,
            ..SourceStringSemanticFacts::default()
        };
    }

    let mut nodes: Vec<SExpr> = Vec::new();
    let mut edges = Vec::new();
    for (left, right) in equalities {
        let left = intern_sexpr(&mut nodes, left);
        let right = intern_sexpr(&mut nodes, right);
        edges.push((left, right));
    }
    let disequalities: Vec<(usize, usize)> = disequalities
        .into_iter()
        .map(|(left, right)| {
            let left = intern_sexpr(&mut nodes, left);
            let right = intern_sexpr(&mut nodes, right);
            (left, right)
        })
        .collect();
    let mut parent: Vec<usize> = (0..nodes.len()).collect();
    for (left, right) in edges {
        union_classes(&mut parent, left, right);
    }
    for i in 0..parent.len() {
        parent[i] = find_class(&parent, i);
    }

    let mut class_values: Vec<Option<Vec<u32>>> = vec![None; nodes.len()];
    let mut conflict = exact_rewrite_conflict;
    for (i, node) in nodes.iter().enumerate() {
        if let Some(value) = literal_pattern_cps(node) {
            set_class_value(&mut class_values, parent[i], value, &mut conflict);
        }
    }

    // A class pin may make a fixed splice in another class concrete; iterate to a
    // stable point. The node count is a deterministic upper bound on propagation
    // rounds because each useful round pins at least one previously-unpinned class.
    for _ in 0..nodes.len() {
        let mut changed = false;
        for (i, node) in nodes.iter().enumerate() {
            let was_unpinned = class_values[parent[i]].is_none();
            if let Some(value) = eval_pinned_word_semantics(node, &nodes, &parent, &class_values, 0)
            {
                set_class_value(&mut class_values, parent[i], value, &mut conflict);
                changed |= was_unpinned;
            }
        }
        if !changed {
            break;
        }
    }

    // A guaranteed disequality is contradictory when positive equalities already
    // merged its operands or when exact constant/splice propagation gives both
    // operands the same value.
    for &(left, right) in &disequalities {
        if parent[left] == parent[right] {
            conflict = true;
            continue;
        }
        let left_value = eval_pinned_word(&nodes[left], &nodes, &parent, &class_values, 0);
        let right_value = eval_pinned_word(&nodes[right], &nodes, &parent, &class_values, 0);
        if left_value.is_some() && left_value == right_value {
            conflict = true;
        }
    }

    // Evaluate content predicates whose operands are exact after equality-class
    // propagation. This catches generated paths such as `view = "http"` together
    // with a required `contains(view, "A")`, including a compound `view` that the
    // general Boolean word skeleton deliberately declines. Only a fully concrete
    // predicate can set the UNSAT flag; every partial case remains untouched.
    for conjunct in &conjuncts {
        let (condition, required) = guaranteed_boolean_condition(conjunct);
        if eval_pinned_word_predicate(condition, &nodes, &parent, &class_values)
            .is_some_and(|actual| actual != required)
        {
            conflict = true;
        }
    }

    let pinned_words = nodes
        .iter()
        .enumerate()
        .filter_map(|(i, node)| {
            class_values[parent[i]]
                .as_ref()
                .map(|value| (node.clone(), value.clone()))
        })
        .collect();

    let lower_bounds: Vec<(&SExpr, u32)> = conjuncts
        .iter()
        .filter_map(|conjunct| guaranteed_string_length_lower_bound(conjunct))
        .collect();
    let mut derived_equalities = Vec::new();
    for i in 0..nodes.len() {
        let Some(left) = nodes[i].list().and_then(fixed_splice_parts) else {
            continue;
        };
        if left.replacement.len() != 1 {
            continue;
        }
        for j in i + 1..nodes.len() {
            if parent[i] != parent[j] {
                continue;
            }
            let Some(right) = nodes[j].list().and_then(fixed_splice_parts) else {
                continue;
            };
            if right.replacement.len() != 1 || left.base != right.base || left.index == right.index
            {
                continue;
            }
            let required = left.index.min(right.index).saturating_add(1);
            if lower_bounds
                .iter()
                .any(|(base, bound)| *base == left.base && *bound >= required)
            {
                let derived = (left.base.clone(), nodes[i].clone());
                if !derived_equalities.contains(&derived) {
                    derived_equalities.push(derived);
                }
            }
        }
    }

    SourceStringSemanticFacts {
        pinned_words,
        derived_equalities,
        conflict,
        eager_boolean_path_conflict,
    }
}

/// Every conjunct guaranteed by all top-level assertions, flattening only `and`.
fn guaranteed_top_level_conjuncts(exprs: &[SExpr]) -> Vec<&SExpr> {
    let mut out = Vec::new();
    let mut stack = Vec::new();
    for expression in exprs {
        let Some(items) = expression.list() else {
            continue;
        };
        if let [head, body] = items
            && head.atom() == Some("assert")
        {
            stack.push(body);
        }
    }
    while let Some(expression) = stack.pop() {
        if let Some(items) = expression.list()
            && items.first().and_then(SExpr::atom) == Some("and")
        {
            stack.extend(items[1..].iter());
        } else {
            out.push(expression);
        }
    }
    out
}

/// Whether guaranteed top-level path conditions require the same string-valued
/// expression to be both empty and to contain a non-empty literal.
///
/// `PyEx` encodes Boolean conditions as `(= (ite C 1 0) 0)` and wraps them in
/// varying numbers of `not`s. [`guaranteed_boolean_condition`] recovers the exact
/// required truth value of `C`; no inference is made through disjunctions or
/// implications. Syntactic identity of the string view is deliberate and
/// fail-closed: `len(W) = 0 ∧ contains(W, C)` is contradictory for every SMT-LIB
/// string expression `W` when literal `C` is non-empty.
fn guaranteed_empty_contains_conflict(exprs: &[SExpr]) -> bool {
    let mut empty_views = Vec::new();
    let mut nonempty_contains_views = Vec::new();
    for conjunct in guaranteed_top_level_conjuncts(exprs) {
        let (condition, required) = guaranteed_boolean_condition(conjunct);
        if !required {
            continue;
        }
        if let Some(view) = empty_string_view(condition) {
            empty_views.push(view);
        }
        if let Some(view) = nonempty_literal_contains_view(condition) {
            nonempty_contains_views.push(view);
        }
    }
    empty_views
        .iter()
        .any(|empty| nonempty_contains_views.contains(empty))
}

/// The underlying condition and truth value required by one asserted conjunct.
fn guaranteed_boolean_condition(mut expression: &SExpr) -> (&SExpr, bool) {
    let mut negated = false;
    while let Some([head, inner]) = expression.list()
        && head.atom() == Some("not")
    {
        negated = !negated;
        expression = inner;
    }
    if let Some(condition) = pyex_indicator_condition(expression) {
        // The indicator is `not condition`; an outer odd negation therefore
        // requires `condition`, while an even count requires its complement.
        (condition, negated)
    } else {
        (expression, !negated)
    }
}

/// `W` from the exact condition `(= (str.len W) 0)` (either orientation).
fn empty_string_view(condition: &SExpr) -> Option<&SExpr> {
    let [equal, left, right] = condition.list()? else {
        return None;
    };
    if equal.atom() != Some("=") {
        return None;
    }
    for (candidate, zero) in [(left, right), (right, left)] {
        let Some([len, view]) = candidate.list() else {
            continue;
        };
        if matches!(len.atom(), Some("str.len" | "seq.len")) && parse_int_literal(zero) == Some(0) {
            return Some(view);
        }
    }
    None
}

/// `W` from the exact condition `(str.contains W C)` for a non-empty literal `C`.
fn nonempty_literal_contains_view(condition: &SExpr) -> Option<&SExpr> {
    let [contains, view, literal] = condition.list()? else {
        return None;
    };
    (contains.atom() == Some("str.contains")
        && literal_pattern_cps(literal).is_some_and(|value| !value.is_empty()))
    .then_some(view)
}

/// A string equality known true either directly or through an odd-negated
/// `PyEx` indicator `(= (ite (= X Y) 1 0) 0)`.
fn positive_word_equality(expression: &SExpr) -> Option<(&SExpr, &SExpr)> {
    let mut expression = expression;
    let mut negated = false;
    while let Some([head, inner]) = expression.list()
        && head.atom() == Some("not")
    {
        negated = !negated;
        expression = inner;
    }
    if let Some(equality) = pyex_word_indicator_equality(expression) {
        return negated.then_some(equality);
    }
    let [head, left, right] = expression.list()? else {
        return None;
    };
    (head.atom() == Some("=") && !negated).then_some((left, right))
}

/// A string disequality known true either through direct negation or through an
/// even-negated `PyEx` indicator `(= (ite (= X Y) 1 0) 0)`.
fn negative_word_equality(expression: &SExpr) -> Option<(&SExpr, &SExpr)> {
    let mut expression = expression;
    let mut negated = false;
    while let Some([head, inner]) = expression.list()
        && head.atom() == Some("not")
    {
        negated = !negated;
        expression = inner;
    }
    if let Some(equality) = pyex_word_indicator_equality(expression) {
        return (!negated).then_some(equality);
    }
    let [head, left, right] = expression.list()? else {
        return None;
    };
    (head.atom() == Some("=") && negated).then_some((left, right))
}

/// The underlying word equality in a generated `PyEx` Boolean indicator. The
/// indicator itself is true exactly when this equality is false.
fn pyex_word_indicator_equality(expression: &SExpr) -> Option<(&SExpr, &SExpr)> {
    let condition = pyex_indicator_condition(expression)?;
    let [condition_head, left, right] = condition.list()? else {
        return None;
    };
    (condition_head.atom() == Some("=")).then_some((left, right))
}

/// `C` from the exact generated Boolean indicator `(= (ite C 1 0) 0)`.
fn pyex_indicator_condition(expression: &SExpr) -> Option<&SExpr> {
    let [equal, ite, zero] = expression.list()? else {
        return None;
    };
    if equal.atom() != Some("=") || parse_int_literal(zero) != Some(0) {
        return None;
    }
    let [ite_head, condition, one, branch_zero] = ite.list()? else {
        return None;
    };
    (ite_head.atom() == Some("ite")
        && parse_int_literal(one) == Some(1)
        && parse_int_literal(branch_zero) == Some(0))
    .then_some(condition)
}

/// A guaranteed `len(base) >= k` generated guard.
fn guaranteed_string_length_lower_bound(expression: &SExpr) -> Option<(&SExpr, u32)> {
    let [ge, difference, zero] = expression.list()? else {
        return None;
    };
    if ge.atom() != Some(">=") || parse_int_literal(strip_subtracted_zero(zero)) != Some(0) {
        return None;
    }
    let [minus, length, bound] = difference.list()? else {
        return None;
    };
    if minus.atom() != Some("-") {
        return None;
    }
    let [len, base] = length.list()? else {
        return None;
    };
    if len.atom() != Some("str.len") {
        return None;
    }
    let bound = u32::try_from(parse_int_literal(strip_subtracted_zero(bound))?).ok()?;
    Some((base, bound))
}

fn intern_sexpr(nodes: &mut Vec<SExpr>, expression: &SExpr) -> usize {
    if let Some(index) = nodes.iter().position(|candidate| candidate == expression) {
        index
    } else {
        nodes.push(expression.clone());
        nodes.len() - 1
    }
}

fn find_class(parent: &[usize], mut index: usize) -> usize {
    while parent[index] != index {
        index = parent[index];
    }
    index
}

fn union_classes(parent: &mut [usize], left: usize, right: usize) {
    let left = find_class(parent, left);
    let right = find_class(parent, right);
    if left != right {
        parent[right] = left;
    }
}

fn set_class_value(
    values: &mut [Option<Vec<u32>>],
    class: usize,
    value: Vec<u32>,
    conflict: &mut bool,
) {
    match &values[class] {
        Some(existing) if existing != &value => *conflict = true,
        Some(_) => {}
        None => values[class] = Some(value),
    }
}

/// Evaluates an exact string expression once its referenced equality classes
/// have constant pins. Unsupported or symbolic operands decline.
fn eval_pinned_word(
    expression: &SExpr,
    nodes: &[SExpr],
    parent: &[usize],
    values: &[Option<Vec<u32>>],
    depth: u32,
) -> Option<Vec<u32>> {
    if depth > 32 {
        return None;
    }
    if let Some(literal) = literal_pattern_cps(expression) {
        return Some(literal);
    }
    if let Some(index) = nodes.iter().position(|candidate| candidate == expression)
        && let Some(value) = &values[parent[index]]
    {
        return Some(value.clone());
    }
    eval_pinned_word_semantics(expression, nodes, parent, values, depth)
}

/// Evaluates an expression from its operands even when its own equality class is
/// pinned. Comparing this value with that class pin detects contradictions such
/// as `s = "abc"` together with `str.at(s, 1) = "c"`.
fn eval_pinned_word_semantics(
    expression: &SExpr,
    nodes: &[SExpr],
    parent: &[usize],
    values: &[Option<Vec<u32>>],
    depth: u32,
) -> Option<Vec<u32>> {
    if depth > 32 {
        return None;
    }
    if let Some(literal) = literal_pattern_cps(expression) {
        return Some(literal);
    }
    let items = expression.list()?;
    match items.first()?.atom()? {
        "str.++" | "str.concat" => {
            let mut result = Vec::new();
            for item in &items[1..] {
                result.extend(eval_pinned_word(item, nodes, parent, values, depth + 1)?);
            }
            Some(result)
        }
        "str.at" if items.len() == 3 => {
            let subject = eval_pinned_word(&items[1], nodes, parent, values, depth + 1)?;
            let index = eval_pinned_int(&items[2], nodes, parent, values, depth + 1)?;
            Some(substr_code_points(&subject, index, 1))
        }
        "str.substr" if items.len() == 4 => {
            let subject = eval_pinned_word(&items[1], nodes, parent, values, depth + 1)?;
            let offset = eval_pinned_int(&items[2], nodes, parent, values, depth + 1)?;
            let length = eval_pinned_int(&items[3], nodes, parent, values, depth + 1)?;
            Some(substr_code_points(&subject, offset, length))
        }
        "str.replace" if items.len() == 4 => {
            let subject = eval_pinned_word(&items[1], nodes, parent, values, depth + 1)?;
            let needle = eval_pinned_word(&items[2], nodes, parent, values, depth + 1)?;
            let replacement = eval_pinned_word(&items[3], nodes, parent, values, depth + 1)?;
            Some(replace_first_code_points(&subject, &needle, &replacement))
        }
        _ => None,
    }
}

/// Evaluates the exact integer fragment used by pinned string views.  Checked
/// arithmetic and all-or-nothing operand evaluation make overflow or a symbolic
/// value a decline.  This lets equality pins flow through `str.len`-based splice
/// indices without imposing any bound on the source string.
fn eval_pinned_int(
    expression: &SExpr,
    nodes: &[SExpr],
    parent: &[usize],
    values: &[Option<Vec<u32>>],
    depth: u32,
) -> Option<i128> {
    if depth > 32 {
        return None;
    }
    if let Some(value) = parse_int_literal(expression) {
        return Some(value);
    }
    let items = expression.list()?;
    match items.first()?.atom()? {
        "str.len" | "seq.len" if items.len() == 2 => {
            i128::try_from(eval_pinned_word(&items[1], nodes, parent, values, depth + 1)?.len())
                .ok()
        }
        "+" if items.len() >= 2 => items[1..].iter().try_fold(0_i128, |sum, item| {
            sum.checked_add(eval_pinned_int(item, nodes, parent, values, depth + 1)?)
        }),
        "-" if items.len() == 2 => {
            eval_pinned_int(&items[1], nodes, parent, values, depth + 1)?.checked_neg()
        }
        "-" if items.len() >= 3 => {
            let first = eval_pinned_int(&items[1], nodes, parent, values, depth + 1)?;
            items[2..].iter().try_fold(first, |difference, item| {
                difference.checked_sub(eval_pinned_int(item, nodes, parent, values, depth + 1)?)
            })
        }
        "*" if items.len() >= 2 => items[1..].iter().try_fold(1_i128, |product, item| {
            product.checked_mul(eval_pinned_int(item, nodes, parent, values, depth + 1)?)
        }),
        _ => None,
    }
}

/// Exact value of a string predicate after equality-class pins.
fn eval_pinned_word_predicate(
    expression: &SExpr,
    nodes: &[SExpr],
    parent: &[usize],
    values: &[Option<Vec<u32>>],
) -> Option<bool> {
    let [head, left, right] = expression.list()? else {
        return None;
    };
    let left = eval_pinned_word(left, nodes, parent, values, 0)?;
    let right = eval_pinned_word(right, nodes, parent, values, 0)?;
    match head.atom()? {
        "str.contains" => Some(
            right.is_empty()
                || left
                    .windows(right.len())
                    .any(|candidate| candidate == right),
        ),
        "str.prefixof" => Some(right.starts_with(&left)),
        "str.suffixof" => Some(right.ends_with(&left)),
        _ => None,
    }
}

/// Evaluates an arbitrary fixed-splice chain from the exact expression pins
/// retained by [`MembershipCollector`].
fn eval_guaranteed_pinned_word(
    expression: &SExpr,
    pins: &[(SExpr, Vec<u32>)],
    depth: u32,
) -> Option<Vec<u32>> {
    if depth > 32 {
        return None;
    }
    if let Some(value) = pins
        .iter()
        .find_map(|(candidate, value)| (candidate == expression).then_some(value))
    {
        return Some(value.clone());
    }
    if let Some(literal) = literal_pattern_cps(expression) {
        return Some(literal);
    }
    let splice = fixed_splice_parts(expression.list()?)?;
    let base = eval_guaranteed_pinned_word(splice.base, pins, depth + 1)?;
    let mut result = substr_code_points(&base, 0, i128::from(splice.index));
    result.extend_from_slice(&splice.replacement);
    result.extend(substr_code_points(
        &base,
        i128::from(splice.split),
        i128::try_from(base.len()).ok()? - i128::from(splice.split),
    ));
    Some(result)
}

/// The canonical well-formedness constraint for a packed string `v` of max length
/// `m`: its length is `≤ m`, and every content byte at or above the length is
/// zero.
fn string_wellformed_m(arena: &mut TermArena, v: TermId, m: u32) -> Result<TermId, SmtError> {
    let lwm = len_width(m);
    let len = arena.extract(lwm - 1, 0, v)?;
    let max = arena.bv_const(lwm, u128::from(m))?;
    let mut wf = arena.bv_ule(len, max)?;
    let zero8 = arena.bv_const(8, 0)?;
    for i in 0..m {
        let lo = lwm + i * 8;
        let byte = arena.extract(lo + 7, lo, v)?;
        let byte_zero = arena.eq(byte, zero8)?;
        let idx = arena.bv_const(lwm, u128::from(i))?;
        let active = arena.bv_ult(idx, len)?;
        let ok = arena.or(active, byte_zero)?;
        wf = arena.and(wf, ok)?;
    }
    Ok(wf)
}

/// Semantic string equality (equal length, equal bytes below the length, padding
/// ignored), aligning operands of differing widths first. Used by `=`/`distinct`
/// only when two packed-string operands have **different** widths — equal-width
/// operands keep plain bit-vector equality (sound by the canonical
/// well-formedness, and unchanged from slice 1).
fn string_equal(arena: &mut TermArena, x: TermId, y: TermId) -> Result<TermId, SmtError> {
    let (x, y, m) = string_align(arena, x, y)?;
    let xlen = string_len_field(arena, x, m)?;
    let ylen = string_len_field(arena, y, m)?;
    let mut acc = arena.eq(xlen, ylen)?;
    for i in 0..m {
        let idx = arena.bv_const(len_width(m), u128::from(i))?;
        let active = arena.bv_ult(idx, xlen)?; // i < len(x) == len(y)
        let bx = string_byte_m(arena, x, i, m)?;
        let by = string_byte_m(arena, y, i, m)?;
        let beq = arena.eq(bx, by)?;
        let nactive = arena.not(active)?;
        let implied = arena.or(nactive, beq)?;
        acc = arena.and(acc, implied)?;
    }
    Ok(acc)
}

/// `=`/`distinct` over a pair: plain bit-vector equality when the operands share
/// a sort, but semantic [`string_equal`] when both are packed strings of
/// **different** widths (e.g. a variable `str.++` result vs a literal). Returns
/// `None` (deferring to the caller's plain `arena.eq`) when the operands are not
/// both same-shaped or both string-shaped — so non-string equality is untouched.
fn string_aware_eq(
    arena: &mut TermArena,
    a: TermId,
    b: TermId,
) -> Result<Option<TermId>, SmtError> {
    let (Sort::BitVec(wa), Sort::BitVec(wb)) = (arena.sort_of(a), arena.sort_of(b)) else {
        return Ok(None);
    };
    if wa == wb {
        return Ok(None); // same sort — plain eq (slice-1 behavior, unchanged)
    }
    if string_max_len_of(wa).is_some() && string_max_len_of(wb).is_some() {
        return Ok(Some(string_equal(arena, a, b)?));
    }
    Ok(None) // genuinely differing BV widths: let `arena.eq` raise its sort error
}

/// Whether `t` is (statically) the **empty** packed string — a length-zero
/// constant. The empty string is the unique string of length 0, so an equality
/// against it is length-determined (`s = "" ⟺ len(s) = 0`).
fn string_len_is_zero(arena: &TermArena, t: TermId) -> bool {
    packed_string_len(arena, t) == Some(0)
}

/// Records the length abstraction fact for a **string** equality atom `atom`
/// over operands `p`, `q`. `p = q` implies `len(p) = len(q)` (the general,
/// relaxation fact via `fresh_bool ∧ fact`); when one operand is the empty
/// string the atom is *exactly* `len(other) = 0` (the empty string is the
/// unique length-0 string — recorded with [`LenAbs::note_atom_exact`], no fresh
/// Boolean, so step 1 can refute `s = "" ∧ len(s) = 0`-style conflicts).
fn string_eq_len_hook(
    arena: &mut TermArena,
    lenabs: &LenAbs,
    atom: TermId,
    p: TermId,
    q: TermId,
) -> Result<(), SmtError> {
    let lp = lenabs.len_expr_string(arena, p)?;
    let lq = lenabs.len_expr_string(arena, q)?;
    if string_len_is_zero(arena, p) {
        let zero = arena.int_const(0);
        let pred = arena.eq(lq, zero)?;
        lenabs.note_atom_exact(arena, atom, pred);
        Ok(())
    } else if string_len_is_zero(arena, q) {
        let zero = arena.int_const(0);
        let pred = arena.eq(lp, zero)?;
        lenabs.note_atom_exact(arena, atom, pred);
        Ok(())
    } else {
        let fact = arena.eq(lp, lq)?;
        if let Some(b) = lenabs.note_atom_fact(arena, atom, fact)? {
            lenabs.note_code_eq_link(arena, b, p, lp, q, lq)?;
        }
        Ok(())
    }
}

fn parse_atom(
    arena: &mut TermArena,
    a: &str,
    aliases: &HashMap<String, TermId>,
    named: &HashMap<String, TermId>,
    scopes: &[HashMap<&str, TermId>],
) -> Result<TermId, SmtError> {
    for scope in scopes.iter().rev() {
        if let Some(&t) = scope.get(a) {
            return Ok(t);
        }
    }
    match a {
        "true" => return Ok(arena.bool_const(true)),
        "false" => return Ok(arena.bool_const(false)),
        _ => {}
    }
    if let Some(hex) = a.strip_prefix("#x") {
        let value = u128::from_str_radix(hex, 16)
            .map_err(|_| SmtError::Syntax(format!("bad hex literal `{a}`")))?;
        return Ok(arena.bv_const(
            4 * u32::try_from(hex.len())
                .map_err(|_| SmtError::Syntax("literal too wide".to_owned()))?,
            value,
        )?);
    }
    if let Some(bin) = a.strip_prefix("#b") {
        let value = u128::from_str_radix(bin, 2)
            .map_err(|_| SmtError::Syntax(format!("bad binary literal `{a}`")))?;
        return Ok(arena.bv_const(
            u32::try_from(bin.len())
                .map_err(|_| SmtError::Syntax("literal too wide".to_owned()))?,
            value,
        )?);
    }
    // A finite-field literal `#fKmM` (value `K` mod prime `M`, QF_FF): a canonical
    // residue `BitVec(ff_width(M))` constant. Self-describing (the modulus is in
    // the token), so it needs no registry. A non-`#f…m…` token falls through.
    if let Some(res) = parse_ff_literal(arena, a) {
        return res;
    }
    // SMT-LIB string literal `"..."` (the lexer keeps the surrounding quotes;
    // a doubled `""` escapes one quote). Pack into the canonical bit-vector.
    if a.len() >= 2 && a.starts_with('"') && a.ends_with('"') {
        let inner = a[1..a.len() - 1].replace("\"\"", "\"");
        // Expand `\u{…}` / `\uhhhh` escapes to code points, then to byte-model bytes
        // (declining a > 0xFF code point) — never the six raw bytes of an unexpanded
        // escape (the P0 wrong-verdict hole).
        return pack_string_literal(arena, &string_literal_bytes(&inner)?);
    }
    if let Some(&t) = aliases.get(a) {
        return Ok(t);
    }
    if let Some(sym) = arena.find_symbol(a) {
        return Ok(arena.var(sym));
    }
    // A `:named` alias bound earlier by `(! t :named a)`. Consulted *after*
    // declared symbols so a real declaration is never shadowed by a `:named`.
    if let Some(&t) = named.get(a) {
        return Ok(t);
    }
    // A bare numeral is a non-negative integer literal (negatives are `(- n)`).
    if a.bytes().all(|b| b.is_ascii_digit()) {
        let value = a
            .parse::<i128>()
            .map_err(|_| SmtError::Syntax(format!("integer literal `{a}` out of range")))?;
        return Ok(arena.int_const(value));
    }
    // A decimal literal `d.ddd` is a non-negative real (ADR-0015).
    if let Some(rational) = parse_decimal(a) {
        return Ok(arena.real_const(rational));
    }
    // A nullary datatype constructor (e.g. an enum value `red`) used as a term.
    if let Some(ctor) = arena.find_constructor(a) {
        if arena.constructor_fields(ctor).is_empty() {
            return Ok(arena.construct(ctor, &[])?);
        }
        return Err(SmtError::Syntax(format!(
            "constructor `{a}` needs arguments"
        )));
    }
    // A literal `RoundingMode` keyword used as a *term* (not as the leading mode
    // of an `fp.*` op, which is consumed syntactically in `queue_list_eval` and
    // never reaches here): resolve to its `BitVec(ROUNDING_MODE_BITS)` token. This
    // is what lets a `(define-fun rne () RoundingMode roundNearestTiesToEven)`
    // alias body fold to the constant, and lets a literal mode flow as an operand
    // to a symbolic-mode `ite` selection.
    if let Some(mode) = parse_rounding_mode(&SExpr::Atom(a.to_owned())) {
        let code = arena.bv_const(ROUNDING_MODE_BITS, rounding_mode_value(mode))?;
        return Ok(arena.rounding_mode_from_bits(code)?);
    }
    // Nullary string/regex constants outside the wired bounded subset
    // (`re.none`/`re.all`/`re.allchar`, …) are declined cleanly (ADR-0029) so a
    // benchmark using them returns `Unsupported`, never a wrong verdict.
    if a.starts_with("re.") || a.starts_with("str.") {
        return Err(SmtError::Unsupported(format!(
            "string/regex constant `{a}` is outside the wired bounded subset (ADR-0029)"
        )));
    }
    Err(SmtError::Unsupported(format!("unknown identifier `{a}`")))
}

/// The IEEE format of a floating-point operand: read directly from a
/// `Sort::Float` (ADR-0026), or inferred from a bit-vector width as a fallback
/// (`16→F16`, `32→F32`, `64→F64`) for terms not yet float-typed.
fn fp_format(arena: &TermArena, t: TermId) -> Result<FloatFormat, SmtError> {
    match arena.sort_of(t) {
        Sort::Float { exp, sig } => Ok(FloatFormat {
            exp_bits: exp,
            sig_bits: sig,
        }),
        Sort::BitVec(16) => Ok(FloatFormat::F16),
        Sort::BitVec(32) => Ok(FloatFormat::F32),
        Sort::BitVec(64) => Ok(FloatFormat::F64),
        s => Err(SmtError::Unsupported(format!(
            "floating-point op on unsupported width/sort {s:?}"
        ))),
    }
}

/// Stamps the floating-point sort of `fmt` onto a bit-vector result `t` produced
/// by an FP formula builder, so downstream conversions can tell it is a float
/// (ADR-0026). If `t` is already that float sort this is a no-op.
fn as_float(arena: &mut TermArena, fmt: FloatFormat, t: TermId) -> Result<TermId, SmtError> {
    if arena.sort_of(t)
        == (Sort::Float {
            exp: fmt.exp_bits,
            sig: fmt.sig_bits,
        })
    {
        return Ok(t);
    }
    Ok(arena.fp_from_bits(t, fmt.exp_bits, fmt.sig_bits)?)
}

/// Reinterprets a `Float`-typed term to its `BitVec(exp + sig)` bits (identity on
/// bits) so the FP formula builders — which operate on bit-vectors and freely mix
/// operands with bit-vector constants — never see a `Float` operand. A non-float
/// term is returned unchanged.
fn to_bits(arena: &mut TermArena, t: TermId) -> Result<TermId, SmtError> {
    // A float built by `fp_from_bits` wraps a bit-vector directly: peel the
    // reinterpret to recover that exact term (preserving any `BvConst`, so the
    // constant-folding conversions still see a literal).
    if let TermNode::App { op, args } = arena.node(t)
        && let axeyum_ir::Op::FpFromBits { .. } = op
    {
        return Ok(args[0]);
    }
    match arena.sort_of(t) {
        Sort::Float { exp, sig } => Ok(arena.extract(exp + sig - 1, 0, t)?),
        _ => Ok(t),
    }
}

/// Whether `name` is a floating-point op whose first argument is a rounding mode.
fn is_fp_rounded_op(name: &str) -> bool {
    matches!(
        name,
        "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.fma" | "fp.sqrt" | "fp.roundToIntegral"
    )
}

/// Bit-width modeling the `RoundingMode` sort as a `BitVec`. Three bits give 8
/// patterns; only the low 5 (`0..=4`) name an SMT-LIB rounding mode (see
/// [`rounding_mode_value`] / [`ALL_ROUNDING_MODES`]). A declared `RoundingMode`
/// symbol is additionally constrained `≤ 4`, so the sort has exactly 5
/// inhabitants.
const ROUNDING_MODE_BITS: u32 = 3;

/// The 5 SMT-LIB rounding modes paired with their canonical `BitVec(3)` token, in
/// ascending value order. This is the single source of truth for both the literal
/// keyword → value map ([`rounding_mode_value`]) and the symbolic 5-way `ite`
/// ([`apply_fp_rounded_symbolic`] / [`apply_fp_rounded_indexed_symbolic`]).
const ALL_ROUNDING_MODES: [(RoundingMode, u128); 5] = [
    (RoundingMode::NearestEven, 0),
    (RoundingMode::NearestAway, 1),
    (RoundingMode::TowardPositive, 2),
    (RoundingMode::TowardNegative, 3),
    (RoundingMode::TowardZero, 4),
];

/// The `BitVec(ROUNDING_MODE_BITS)` token for a concrete rounding mode (the
/// inverse of the value column of [`ALL_ROUNDING_MODES`]).
fn rounding_mode_value(mode: RoundingMode) -> u128 {
    ALL_ROUNDING_MODES
        .iter()
        .find_map(|&(m, v)| (m == mode).then_some(v))
        .expect("every RoundingMode appears in ALL_ROUNDING_MODES")
}

/// Parses an SMT-LIB `RoundingMode` value (short or long form). Returns `None`
/// for anything that isn't a recognized mode symbol.
fn parse_rounding_mode(expr: &SExpr) -> Option<RoundingMode> {
    match expr.atom()? {
        "RNE" | "roundNearestTiesToEven" => Some(RoundingMode::NearestEven),
        "RNA" | "roundNearestTiesToAway" => Some(RoundingMode::NearestAway),
        "RTZ" | "roundTowardZero" => Some(RoundingMode::TowardZero),
        "RTP" | "roundTowardPositive" => Some(RoundingMode::TowardPositive),
        "RTN" | "roundTowardNegative" => Some(RoundingMode::TowardNegative),
        _ => None,
    }
}

/// Whether `name` is an indexed FP conversion op taking a leading rounding mode.
fn is_fp_indexed_conversion(name: &str) -> bool {
    matches!(name, "to_fp" | "to_fp_unsigned" | "fp.to_sbv" | "fp.to_ubv")
}

/// Applies an *indexed* rounding-mode FP conversion (`mode` already parsed). With
/// the first-class `Sort::Float` (ADR-0026) every overload is sort-disambiguated:
/// `(_ to_fp eb sb)` from a **real** constant (dyadic only — sound), from a
/// **float** (FP→FP reformat), or from a **bit-vector** (signed-BV→FP);
/// `(_ to_fp_unsigned eb sb)` from an unsigned bit-vector; and `(_ fp.to_sbv/
/// to_ubv m)` from a floating-point value.
#[allow(clippy::too_many_lines)]
fn apply_fp_rounded_indexed(
    arena: &mut TermArena,
    items: &[SExpr],
    mode: RoundingMode,
    args: &[TermId],
) -> Result<TermId, SmtError> {
    let head = items[0].list().expect("indexed head");
    let name = head.get(1).and_then(SExpr::atom).unwrap_or("");
    let index = |i: usize| -> Result<u32, SmtError> {
        head.get(i)
            .and_then(SExpr::atom)
            .and_then(|s| s.parse::<u32>().ok())
            .ok_or_else(|| SmtError::Syntax(format!("`{name}` index {i}")))
    };
    if args.len() != 1 {
        return Err(SmtError::Syntax(format!(
            "`{name}` expects 1 operand, got {}",
            args.len()
        )));
    }
    let x = args[0];
    let term = match name {
        "to_fp" => {
            let (eb, sb) = (index(2)?, index(3)?);
            let dst = FloatFormat {
                exp_bits: eb,
                sig_bits: sb,
            };
            match arena.sort_of(x) {
                Sort::Real => {
                    // Real → FP: round a rational constant exactly by integer
                    // arithmetic (including non-dyadic values such as 1/3).
                    let TermNode::RealConst(r) = *arena.node(x) else {
                        return Err(SmtError::Unsupported(
                            "(_ to_fp …) from a non-constant real".to_owned(),
                        ));
                    };
                    let bv = axeyum_fp::from_real(arena, dst, mode, r)?.ok_or_else(|| {
                        SmtError::Unsupported(format!(
                            "(_ to_fp {eb} {sb}) exact rational {}/{} exceeds the current integer rounder",
                            r.numerator(),
                            r.denominator()
                        ))
                    })?;
                    as_float(arena, dst, bv)?
                }
                Sort::Float { .. } => {
                    // FP → FP reformat: now sort-disambiguated from a signed-BV
                    // source (ADR-0026); the validated symbolic `to_fp` builder
                    // runs on the unwrapped bits.
                    let src = fp_format(arena, x)?;
                    let xb = to_bits(arena, x)?;
                    let r = axeyum_fp::to_fp(arena, src, dst, mode, xb)?;
                    as_float(arena, dst, r)?
                }
                Sort::BitVec(_) => {
                    // Signed bit-vector → FP (symbolic circuit via pack_value;
                    // None only if the working width exceeds MAX_BV_WIDTH).
                    let r = axeyum_fp::sbv_to_fp(arena, dst, x, mode)?.ok_or_else(|| {
                        SmtError::Unsupported(
                            "(_ to_fp …) from a signed bit-vector: integer width too large \
                             for the conversion circuit"
                                .to_owned(),
                        )
                    })?;
                    as_float(arena, dst, r)?
                }
                s => {
                    return Err(SmtError::Syntax(format!(
                        "(_ to_fp …) operand must be Real, Float, or BitVec, got {s:?}"
                    )));
                }
            }
        }
        "to_fp_unsigned" => {
            let fmt = FloatFormat {
                exp_bits: index(2)?,
                sig_bits: index(3)?,
            };
            let r = axeyum_fp::ubv_to_fp(arena, fmt, x, mode)?.ok_or_else(|| {
                SmtError::Unsupported(
                    "(_ to_fp_unsigned …): integer width too large for the conversion circuit"
                        .to_owned(),
                )
            })?;
            as_float(arena, fmt, r)?
        }
        "fp.to_ubv" => {
            let width = index(2)?;
            let fmt = fp_format(arena, x)?;
            let xb = to_bits(arena, x)?;
            // Constant + well-defined folds to a clean value; otherwise build the
            // symbolic circuit, routing NaN/∞/out-of-range to a fresh value
            // (SMT-LIB underspecification; ADR-0026).
            if let Some(c) = axeyum_fp::to_ubv(arena, fmt, mode, xb, width)? {
                c
            } else {
                let fresh = unspecified_conversion_value(arena, "to_ubv", x, width, mode)?;
                axeyum_fp::to_ubv_sym(arena, fmt, mode, xb, width, fresh)?
            }
        }
        "fp.to_sbv" => {
            let width = index(2)?;
            let fmt = fp_format(arena, x)?;
            let xb = to_bits(arena, x)?;
            if let Some(c) = axeyum_fp::to_sbv(arena, fmt, mode, xb, width)? {
                c
            } else {
                let fresh = unspecified_conversion_value(arena, "to_sbv", x, width, mode)?;
                axeyum_fp::to_sbv_sym(arena, fmt, mode, xb, width, fresh)?
            }
        }
        other => {
            return Err(SmtError::Unsupported(format!(
                "indexed rounding-mode FP op `{other}`"
            )));
        }
    };
    Ok(term)
}

/// Applies a rounding-mode FP op (`mode` already parsed from the first argument);
/// `args` are the evaluated operands. The format is recovered from operand width.
fn apply_fp_rounded(
    arena: &mut TermArena,
    items: &[SExpr],
    mode: RoundingMode,
    args: &[TermId],
) -> Result<TermId, SmtError> {
    let head = items[0].atom().unwrap_or("");
    let need = |n: usize| -> Result<(), SmtError> {
        if args.len() == n {
            Ok(())
        } else {
            Err(SmtError::Syntax(format!(
                "{head} expects {n} operand(s), got {}",
                args.len()
            )))
        }
    };
    // Format from the (float-typed) operand; builders run on the unwrapped bits.
    let fmt = fp_format(arena, args[0])?;
    let b = args
        .iter()
        .map(|&a| to_bits(arena, a))
        .collect::<Result<Vec<_>, _>>()?;
    let term = match head {
        "fp.add" => {
            need(2)?;
            axeyum_fp::add(arena, fmt, b[0], b[1], mode)?
        }
        "fp.sub" => {
            need(2)?;
            axeyum_fp::sub(arena, fmt, b[0], b[1], mode)?
        }
        "fp.mul" => {
            need(2)?;
            axeyum_fp::mul(arena, fmt, b[0], b[1], mode)?
        }
        "fp.div" => {
            need(2)?;
            axeyum_fp::div(arena, fmt, b[0], b[1], mode)?
        }
        "fp.sqrt" => {
            need(1)?;
            axeyum_fp::sqrt(arena, fmt, b[0], mode)?
        }
        "fp.fma" => {
            need(3)?;
            axeyum_fp::fma(arena, fmt, b[0], b[1], b[2], mode)?
        }
        "fp.roundToIntegral" => {
            need(1)?;
            axeyum_fp::round_to_integral_sym(arena, fmt, mode, b[0])?
        }
        other => {
            return Err(SmtError::Unsupported(format!(
                "rounding-mode FP op `{other}`"
            )));
        }
    };
    // Every rounding-mode op here is FP-valued; stamp the float sort (ADR-0026).
    as_float(arena, fmt, term)
}

/// Applies a rounding-mode FP op whose mode is a **symbolic** `RoundingMode` term
/// `rm` (a `BitVec(ROUNDING_MODE_BITS)`): builds the 5-way `ite` selecting among
/// [`apply_fp_rounded`] evaluated once per concrete mode.
///
/// `ite(rm = 0, …RNE, ite(rm = 1, …RNA, ite(rm = 2, …RTP, ite(rm = 3, …RTN,
/// …RTZ))))` — the innermost else is the last mode (RTZ), so any `rm` value
/// outside `0..=4` would resolve to RTZ; the declared-symbol `≤ 4` constraint
/// (see [`declare_rounding_mode_symbol`]) makes those patterns unreachable, so the
/// modeled sort has exactly its 5 inhabitants and each picks its exact mode's
/// result. Per-mode results are byte-identical to the literal-mode fast path.
fn apply_fp_rounded_symbolic(
    arena: &mut TermArena,
    items: &[SExpr],
    rm: TermId,
    operands: &[TermId],
) -> Result<TermId, SmtError> {
    rounding_mode_select(arena, rm, |arena, mode| {
        apply_fp_rounded(arena, items, mode, operands)
    })
}

/// Like [`apply_fp_rounded_symbolic`] but for an *indexed* head
/// (`((_ to_fp eb sb) rm x)`, `((_ fp.to_sbv m) rm x)`, …) with a symbolic mode.
fn apply_fp_rounded_indexed_symbolic(
    arena: &mut TermArena,
    items: &[SExpr],
    rm: TermId,
    operands: &[TermId],
) -> Result<TermId, SmtError> {
    rounding_mode_select(arena, rm, |arena, mode| {
        apply_fp_rounded_indexed(arena, items, mode, operands)
    })
}

/// Builds the right-nested 5-way `ite` over [`ALL_ROUNDING_MODES`] that selects
/// `build(mode)` for the mode named by the symbolic `BitVec(ROUNDING_MODE_BITS)`
/// term `rm`. The last mode is the innermost (unconditional) else; the
/// declared-symbol `≤ 4` constraint keeps the unused patterns out of any model, so
/// the selection is exact (see [`apply_fp_rounded_symbolic`]).
fn rounding_mode_select(
    arena: &mut TermArena,
    rm: TermId,
    mut build: impl FnMut(&mut TermArena, RoundingMode) -> Result<TermId, SmtError>,
) -> Result<TermId, SmtError> {
    // `rm` must be the modeled `BitVec(ROUNDING_MODE_BITS)`; reject anything else
    // (a wrong-width term can never be a sound rounding mode).
    if arena.sort_of(rm) != Sort::RoundingMode {
        return Err(SmtError::Syntax(format!(
            "symbolic rounding mode must have sort RoundingMode, \
             got {:?}",
            arena.sort_of(rm)
        )));
    }
    // Fold from the last (innermost else) mode outward.
    let mut iter = ALL_ROUNDING_MODES.iter().rev();
    let (last_mode, _) = *iter.next().expect("ALL_ROUNDING_MODES is non-empty");
    let mut acc = build(arena, last_mode)?;
    for &(mode, value) in iter {
        let code = arena.bv_const(ROUNDING_MODE_BITS, value)?;
        let token = arena.rounding_mode_from_bits(code)?;
        let is_mode = arena.eq(rm, token)?;
        let then = build(arena, mode)?;
        acc = arena.ite(is_mode, then, acc)?;
    }
    Ok(acc)
}

fn parse_indexed_constant(arena: &mut TermArena, items: &[SExpr]) -> Result<TermId, SmtError> {
    if items.len() == 3
        && let Some(name) = items[1].atom()
        && let Some(num) = name.strip_prefix("bv")
        && let (Ok(value), Some(Ok(width))) =
            (num.parse::<u128>(), items[2].atom().map(str::parse::<u32>))
    {
        return Ok(arena.bv_const(width, value)?);
    }
    // FP special constants `(_ <name> eb sb)` → the matching bit pattern in a
    // BitVec(eb+sb) (FP values are bit-vectors; ADR-0023).
    if items.len() == 4
        && let Some(name) = items[1].atom()
        && let (Some(Ok(eb)), Some(Ok(sb))) = (
            items[2].atom().map(str::parse::<u32>),
            items[3].atom().map(str::parse::<u32>),
        )
    {
        if eb <= 1 || sb <= 1 {
            return Err(SmtError::Syntax(format!(
                "FloatingPoint parameters must both be greater than 1, got ({eb}, {sb})"
            )));
        }
        let total = eb
            .checked_add(sb)
            .ok_or_else(|| SmtError::Syntax("FloatingPoint width overflow".to_owned()))?;
        if total > MAX_BV_WIDTH {
            return Err(SmtError::Syntax(format!(
                "FloatingPoint width {total} exceeds implementation cap {MAX_BV_WIDTH}"
            )));
        }
        if matches!(name, "+zero" | "-zero" | "+oo" | "-oo" | "NaN") {
            let mut bits = vec![false; total as usize];
            if matches!(name, "-zero" | "-oo") {
                bits[(total - 1) as usize] = true;
            }
            if matches!(name, "+oo" | "-oo" | "NaN") {
                for bit in sb - 1..sb - 1 + eb {
                    bits[bit as usize] = true;
                }
            }
            if name == "NaN" {
                bits[(sb - 2) as usize] = true;
            }
            let wide = WideUint::from_lsb_bits(&bits);
            let bv = if total <= 128 {
                arena.bv_const(total, wide.to_u128())?
            } else {
                arena.wide_bv_const(wide)
            };
            return Ok(arena.fp_from_bits(bv, eb, sb)?); // float-typed (ADR-0026)
        }
    }
    Err(SmtError::Unsupported(format!("indexed term {items:?}")))
}

// --- bounded finite Sequences front-end (`(Seq E)`, ADR-0029 generalization) --
//
// A `(Seq E)` over a **fixed-width** element sort `E` is the same packed
// bit-vector structure a bounded `String` uses, generalized from a byte
// (`elem_width = 8`) to an arbitrary element width `ew`. A sequence of maximum
// length `m` is one `BitVec(seq_total(ew, m))` packing a length in the low
// `len_width(m)` bits and `m` content elements above it (element `i` at bits
// `[len_width(m) + i·ew, +ew)`). Declared sequence symbols carry the same
// canonical well-formedness constraint strings do (length ≤ `m`; padding
// elements zero), so two equal sequences share exactly one bit pattern and
// `=` / `distinct` decide as plain bit-vector (in)equality.
//
// # Element sorts and their widths (the sound, fixed-width subset)
//
// `elem_width(E)` is `w` for `(_ BitVec w)`, `1` for `Bool`, and
// [`SEQ_INT_WIDTH`] for `Int` (the bounded-int element width, two's-complement).
// Every other element sort — `Real`, an uninterpreted/parametric sort, `String`,
// or a nested `(Seq …)` — has no sound fixed-width packing here and makes the
// sequence sort a clean [`SmtError::Unsupported`] (Unknown to the consumer),
// never a wrong verdict. The byte width `8` is **reserved for `String`**: a
// `(Seq (_ BitVec 8))` is declined so a packed sequence width can never be
// mistaken for (or collide with) a packed `String` on the shared `=` path.
//
// # The modeled operator subset (slice 1) and what is declined
//
// `seq.empty`/`seq.unit`/`seq.++`/`seq.len`/`seq.extract`, `=`/`distinct`, and
// `seq.prefixof`/`seq.suffixof`/`seq.contains` are all denotation-preserving
// over the packed layout (they only move, compare, or count whole elements —
// never read a tail element's value), exactly mirroring their `str.*`
// counterparts with the element width swapped in for `8`.
//
// `seq.nth` / `seq.at` are wired (slice 2). SMT-LIB sequences leave
// `(seq.nth s i)` **unconstrained** for `i` out of `[0, len(s))` (the
// out-of-bounds value is an arbitrary fixed element, *not* zero). A zero-padded
// layout would force `(seq.nth s i) = 0` for `i ≥ len(s)`, flipping a `sat` to a
// wrong `unsat`; instead the out-of-bounds case is a **fresh, free** value of the
// element sort, keyed per syntactic `(s, i)` so identical applications share it
// ([`seq_nth`]), with an eager Ackermann congruence pass
// ([`SeqInfo::drain_nth_congruence`]) closing semantically-equal operands —
// `seq.nth` stays a function even where its value is unspecified. `seq.at` is the
// **total** unit-sub-sequence (empty out-of-bounds), mirroring `str.at`.
//
// `seq.update` / `seq.rev` are wired (slice 3). Both are **total** functions over
// the packed layout with no unconstrained-out-of-bounds subtlety: `(seq.update s
// i t)` overlays `t`'s elements onto `s` at `[i, i+len(t))` (truncated to fit;
// out-of-bounds `i` is a no-op), keeping `len(s)` ([`seq_update`]); `(seq.rev s)`
// reverses the first `len(s)` elements ([`seq_rev`]) — a permutation. Both copy
// the length field verbatim and preserve the canonical padding.
// `seq.replace`/`seq.replace_all`/`seq.indexof` remain declined (slice 4).

/// Bounded-int element width for `(Seq Int)`: an `Int` element is modeled as a
/// two's-complement `BitVec(SEQ_INT_WIDTH)`. The slice-1 sequence operators only
/// move/compare/count whole elements (never do element arithmetic across the
/// width boundary), so equality/disequality over `Int` elements is exact for
/// every value representable in this width. An `Int` element **literal** outside
/// the signed range is declined; a symbolic element adds a scoped signed-range
/// guard to the bounded query and the guard is removed by the unbounded-UNSAT
/// abstraction. Thus a returned SAT model is injective at the element boundary,
/// while an UNSAT that depends on the finite range becomes `unknown`. `16` keeps
/// the packed `(Seq Int)` sort within the [`SEQ_TOTAL_BITS_CAP`] ceiling at a
/// useful element bound while still covering the small integers these benchmarks
/// name.
pub(crate) const SEQ_INT_WIDTH: u32 = 16;

/// Hard ceiling on any packed sequence's total bit width. The ground evaluator
/// (and the `seq.unit` / `seq.empty` constant packers) represent a bit-vector
/// value as a `u128`, so a packed sequence sort must fit in 128 bits — element
/// widths/lengths that would exceed this decline cleanly (Unknown), never wrap.
const SEQ_TOTAL_BITS_CAP: u32 = 128;

/// Soft cap on a packed sequence's `max_len` (in elements), for tractability —
/// the analogue of `STRING_MAX_LEN`. The realized bound is the smaller of this
/// and whatever [`SEQ_TOTAL_BITS_CAP`] allows for the element width.
const SEQ_LEN_SOFT_CAP: u32 = 8;

/// Total packed width of a sequence of max length `m` over element width `ew`:
/// the length field plus `m` content elements.
const fn seq_total(ew: u32, m: u32) -> u32 {
    len_width(m) + m * ew
}

/// The bounded maximum sequence length (in elements) for element width `ew`: the
/// largest `m ≤ SEQ_LEN_SOFT_CAP` whose packed sort `seq_total(ew, m)` fits the
/// [`SEQ_TOTAL_BITS_CAP`] ceiling. `None` if even a length-1 sequence over `ew`
/// would exceed the ceiling (so a too-wide element declines, never wraps).
fn seq_max_len_for(ew: u32) -> Option<u32> {
    (1..=SEQ_LEN_SOFT_CAP)
        .rev()
        .find(|&m| seq_total(ew, m) <= SEQ_TOTAL_BITS_CAP)
}

/// The [`SeqElemSort`] of a fixed-width element sort, or `None` for an element
/// sort with no sound fixed-width packing (Real, uninterpreted, String, nested
/// Seq) or the reserved string byte width `8`.
fn seq_elem_sort(sort: &SExpr) -> Option<SeqElemSort> {
    match sort {
        SExpr::Atom(a) if a == "Bool" => Some(SeqElemSort::Bool),
        SExpr::Atom(a) if a == "Int" => Some(SeqElemSort::Int),
        SExpr::List(items)
            if items.len() == 3
                && items[0].atom() == Some("_")
                && items[1].atom() == Some("BitVec") =>
        {
            // `(_ BitVec w)`, with `8` reserved for `String` (see the module note).
            items[2]
                .atom()
                .and_then(|w| w.parse::<u32>().ok())
                .filter(|&w| w >= 1 && w != 8)
                .map(SeqElemSort::BitVec)
        }
        _ => None,
    }
}

/// `elem_width(E)` for a fixed-width element sort, or `None` for an element sort
/// with no sound fixed-width packing (Real, uninterpreted, String, nested Seq) or
/// the reserved string byte width `8`.
fn seq_elem_width(sort: &SExpr) -> Option<u32> {
    seq_elem_sort(sort).map(SeqElemSort::width)
}

/// The SMT-LIB element sort of a `(Seq E)`, as far as the bounded packing
/// distinguishes it. Two sorts can share an element **width** yet differ in their
/// SMT-LIB result sort (`Bool` and `(_ BitVec 1)` both pack to a 1-bit element;
/// `Int` and `(_ BitVec 16)` both to 16 bits), so `seq.nth` — whose result is the
/// element sort, not the packed bits — must track the sort, not just the width.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum SeqElemSort {
    /// `Bool` element (`ew = 1`); `seq.nth` returns a `Bool` (`elem = #b1`).
    Bool,
    /// `Int` element (`ew = SEQ_INT_WIDTH`, two's-complement); `seq.nth` returns
    /// an `Int` (the signed value of the packed element).
    Int,
    /// `(_ BitVec w)` element; `seq.nth` returns the `BitVec(w)` element verbatim.
    BitVec(u32),
}

impl SeqElemSort {
    /// The packed element width of this element sort.
    fn width(self) -> u32 {
        match self {
            SeqElemSort::Bool => 1,
            SeqElemSort::Int => SEQ_INT_WIDTH,
            SeqElemSort::BitVec(w) => w,
        }
    }
}

/// A registered `seq.nth` application, retained for the eager Ackermann
/// congruence pass: two `seq.nth` applications with provably-equal sequence and
/// index operands must return the same out-of-bounds value (`seq.nth` is a
/// function even where SMT-LIB leaves its value unconstrained).
#[derive(Debug, Clone, Copy)]
pub(crate) struct NthApp {
    /// The sequence operand `s`.
    seq: TermId,
    /// The `Int` index operand `i`.
    idx: TermId,
    /// The fresh, unconstrained out-of-bounds value `oob(s, i)` (a `BitVec(ew)`
    /// declared symbol). Keyed by `(s.index, i.index)` so two **syntactically**
    /// identical applications already share it; the congruence pass closes the
    /// **semantic** case (distinct term ids that denote equal `s`, `i`).
    oob: TermId,
}

/// The packed width → element-sort registry, built as `(Seq E)` sorts are
/// parsed. Lets the `seq.*` operators (dispatched after term construction, where
/// only the operand's `BitVec` width is visible) recover the element width/sort of
/// a packed sequence operand. A genuine `BitVec` whose width is not registered is
/// **not** a sequence, so a non-sequence operand to a `seq.*` op declines cleanly.
#[derive(Debug, Default)]
pub(crate) struct SeqInfo {
    /// `packed_width → elem_width`. Built injectively: a width is inserted only
    /// for one element width; a would-be second, different element width at the
    /// same total width makes the *declaration* decline (see [`seq_register`]).
    width_to_ew: HashMap<u32, u32>,
    /// `packed_width → element sort`, for the registered (declared) sequence
    /// sorts. A `seq.nth` over a packed operand recovers its element sort here so
    /// the result has the right SMT-LIB sort (`Bool`/`Int`/`BitVec`). A collision
    /// (two element sorts at one packed width) makes the *declaration* decline.
    width_to_sort: HashMap<u32, SeqElemSort>,
    /// Registered `seq.nth` applications, for the eager congruence pass
    /// ([`SeqInfo::drain_nth_congruence`]). Interior-mutable so the read-only
    /// `&SeqInfo` threaded through the parse can still record applications; the
    /// width maps stay immutable.
    nth_apps: std::cell::RefCell<Vec<NthApp>>,
}

impl SeqInfo {
    /// The element width of a packed sequence operand of bit width `w`. Recognizes
    /// both a **declared** sequence width (registered directly) and a **derived**
    /// width produced by `seq.unit`/`seq.++`/`seq.extract` (a different max length
    /// over a registered element width): `w` is a sequence of element width `ew`
    /// iff `w = seq_total(ew, m)` for some `m ≤ SEQ_LEN_SOFT_CAP` and some
    /// registered element width `ew`. The element-width set is small (the distinct
    /// `(Seq E)` element types in the script), so this is a tiny linear scan.
    fn elem_width_of(&self, w: u32) -> Option<u32> {
        if let Some(&ew) = self.width_to_ew.get(&w) {
            return Some(ew);
        }
        // Derived width: match against each registered element width's length grid.
        let mut ews: Vec<u32> = self.width_to_ew.values().copied().collect();
        ews.sort_unstable();
        ews.dedup();
        ews.into_iter()
            .find(|&ew| (1..=SEQ_LEN_SOFT_CAP).any(|m| seq_total(ew, m) == w))
    }

    /// Whether any sequence sort has been registered (fast path: a script with no
    /// sequences threads an empty table and never hits the `seq.*` dispatch).
    fn is_empty(&self) -> bool {
        self.width_to_ew.is_empty()
    }

    /// The single element width shared by every registered sequence sort, if the
    /// script uses exactly one. `seq.unit`/`seq.empty` (whose element type is not
    /// recoverable from the element/ascription alone in the post-parse dispatch)
    /// use this; a script mixing two element widths makes them decline, which is
    /// sound (never a wrong verdict).
    fn sole_elem_width(&self) -> Option<u32> {
        let mut it = self.width_to_ew.values().copied();
        let first = it.next()?;
        it.all(|w| w == first).then_some(first)
    }

    /// The element **sort** of a packed sequence operand of bit width `w` — both
    /// the **declared** sequence widths (registered directly) and a **derived**
    /// width produced by `seq.unit`/`seq.++`/`seq.extract`. The derived case
    /// resolves to the registered element sort whose grid `seq_total(ew, m)` hits
    /// `w` (the element sort is recovered from the matching `ew`). `None` when `w`
    /// is not a sequence width or the script declares no element sort of that `ew`.
    fn elem_sort_of(&self, w: u32) -> Option<SeqElemSort> {
        if let Some(&s) = self.width_to_sort.get(&w) {
            return Some(s);
        }
        let ew = self.elem_width_of(w)?;
        // Pick the declared element sort with this width (Bool vs BitVec(1), Int
        // vs BitVec(16) are distinguished by which was actually declared). A
        // script can declare only one sort per width (the scan rejects a
        // collision), so this is unambiguous.
        self.width_to_sort
            .values()
            .copied()
            .find(|s| s.width() == ew)
    }

    /// Records a `seq.nth` application for the eager congruence pass.
    fn register_nth(&self, seq: TermId, idx: TermId, oob: TermId) {
        self.nth_apps.borrow_mut().push(NthApp { seq, idx, oob });
    }

    /// Drains the pending `seq.nth` Ackermann congruence constraints
    /// (`(s = s') ∧ (i = i') ⇒ oob(s,i) = oob(s',i')` over every distinct pair of
    /// registered applications) and clears the registry. Returns the conjunction
    /// of those implications (or `None` if there is nothing to constrain). The
    /// constraints only pin the **fresh** out-of-bounds symbols to agree on
    /// equal operands, so appending them to the assertion set is monotone and
    /// sound — it can never turn a genuine `sat` into `unsat`.
    fn drain_nth_congruence(&self, arena: &mut TermArena) -> Result<Option<TermId>, SmtError> {
        let apps = std::mem::take(&mut *self.nth_apps.borrow_mut());
        let mut acc: Option<TermId> = None;
        for (a, b) in apps
            .iter()
            .enumerate()
            .flat_map(|(k, a)| apps[k + 1..].iter().map(move |b| (a, b)))
        {
            // Same fresh symbol already ⇒ syntactically identical ⇒ nothing to add.
            if a.oob == b.oob {
                continue;
            }
            let seq_eq = arena.eq(a.seq, b.seq)?;
            let idx_eq = arena.eq(a.idx, b.idx)?;
            let operands_eq = arena.and(seq_eq, idx_eq)?;
            let val_eq = arena.eq(a.oob, b.oob)?;
            let imp = arena.implies(operands_eq, val_eq)?;
            acc = Some(match acc {
                None => imp,
                Some(conj) => arena.and(conj, imp)?,
            });
        }
        Ok(acc)
    }
}

/// Whether `e` mentions the `Seq` sort head or any `seq.*` operator anywhere
/// (the fast-path guard: a script with no sequences skips [`build_seq_info`] and
/// threads an empty table).
fn mentions_seq(e: &SExpr) -> bool {
    match e {
        SExpr::Atom(a) => a.starts_with("seq."),
        SExpr::List(items) => {
            items.first().and_then(SExpr::atom) == Some("Seq") || items.iter().any(mentions_seq)
        }
    }
}

/// Builds the packed-width → element-width registry for a script by scanning every
/// `(Seq E)` sort s-expr (declaration, function signature, `(as seq.empty (Seq
/// E))` ascription, …) once, up front. The width→ew map is then immutable for the
/// whole parse, so the
/// `seq.*` operator dispatch (which only sees a packed operand's bit width) can
/// recover its element width without threading mutable state through `parse_sort`.
///
/// # Errors
///
/// [`SmtError::Unsupported`] for a `(Seq E)` whose element sort `E` is not a
/// soundly-packable fixed-width sort (see [`seq_elem_width`]), or on a width
/// collision (two element widths packing to the same total width).
fn build_seq_info(exprs: &[SExpr]) -> Result<SeqInfo, SmtError> {
    let mut info = SeqInfo::default();
    if !exprs.iter().any(mentions_seq) {
        return Ok(info);
    }
    for e in exprs {
        scan_seq_sorts(e, &mut info)?;
    }
    Ok(info)
}

/// Recursively registers every `(Seq E)` sort s-expr in `e`.
fn scan_seq_sorts(e: &SExpr, info: &mut SeqInfo) -> Result<(), SmtError> {
    let SExpr::List(items) = e else { return Ok(()) };
    if items.len() == 2 && items[0].atom() == Some("Seq") {
        let es = seq_elem_sort(&items[1]).ok_or_else(|| {
            SmtError::Unsupported(format!(
                "`(Seq {:?})` has no sound fixed-width element packing (only Bool, Int, and \
                 `(_ BitVec w)` with w ≠ 8 are modeled; ADR-0029)",
                items[1]
            ))
        })?;
        let ew = es.width();
        // A nested element `(Seq …)` is itself a sort node, scanned below; but a
        // non-fixed-width element already declined above, so registration here is
        // for the fixed-width leaf cases only.
        let m = seq_max_len_for(ew).ok_or_else(|| {
            SmtError::Unsupported(format!(
                "sequence element width {ew} exceeds the packed-sort bit ceiling (ADR-0029)"
            ))
        })?;
        let w = seq_total(ew, m);
        match info.width_to_ew.insert(w, ew) {
            Some(prev) if prev != ew => {
                return Err(SmtError::Unsupported(format!(
                    "two sequence element widths ({prev} and {ew}) pack to the same width {w}; \
                     the script mixes element types this bounded encoding cannot separate"
                )));
            }
            _ => {}
        }
        // Track the element sort too (Bool vs BitVec(1), Int vs BitVec(16) share a
        // width but differ as `seq.nth` result sorts). A second, *different* sort
        // at the same packed width makes the declaration decline — that script
        // mixes element types this bounded encoding cannot separate on `seq.nth`.
        match info.width_to_sort.insert(w, es) {
            Some(prev) if prev != es => {
                return Err(SmtError::Unsupported(format!(
                    "two sequence element sorts ({prev:?} and {es:?}) pack to the same width {w}; \
                     the script mixes element types this bounded encoding cannot separate"
                )));
            }
            _ => {}
        }
    }
    for child in items {
        scan_seq_sorts(child, info)?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Finite fields (QF_FF) — a prime field `GF(p)` modeled as modular bit-vector
// arithmetic.
//
// `(_ FiniteField p)` is modeled as `BitVec(w)` with `w = ceil(log2(p))` (the
// fewest bits that index the `p` field elements `0..p`). A field element is the
// bit-vector holding its canonical residue `0 ≤ v < p`; declared field symbols
// carry a `bvult v p` well-formedness constraint (asserted at declaration), so
// the modeled domain is *exactly* `{0, …, p-1}` = `GF(p)`. Every field op is
// recomputed to a canonical residue `< p`:
//
//   * `ff.add x y …`  → `(x + y + …) mod p`   (n-ary; conditional subtract)
//   * `ff.neg x`      → `(p − x) mod p`        (`ite(x = 0, 0, p − x)`)
//   * `ff.mul x y …`  → `(x · y · …) mod p`    (n-ary; `bvurem` after a `2w` mul)
//   * `ff.bitsum x …` → `Σ 2^i · x_i mod p`    (cvc5 extension; positional sum)
//   * `=` / `distinct` over field elements → plain BV `=` (residues are
//     canonical `< p`, so equality is exact).
//
// Soundness: well-formedness (`< p`) makes the BV domain exactly `GF(p)`, and
// each op's result is reduced to a canonical residue `< p`, so the encoding is
// denotation-preserving — `bv = bv` iff the field elements are equal, and the
// modular arithmetic matches `GF(p)` verbatim. Fully bit-blasted, so SAT and
// UNSAT are both complete for any prime that fits the width cap.
//
// Bound: only primes whose modeling width fits `MAX_FF_PRIME_BITS` are decided;
// a larger (e.g. crypto-sized 254–381-bit) prime, a modulus that overflows
// `u128`, or a non-prime "field" (invalid SMT-LIB) makes the whole script a
// clean `Unsupported` (→ `unknown`), never a wrong/heavy result.
// ---------------------------------------------------------------------------

/// The maximum field-modulus bit-width axeyum bit-blasts for `QF_FF`. A modulus
/// of `b` bits is modeled as a `BitVec(b)`, and `ff.mul` forms a `2b`-bit product
/// before the `bvurem` reduction, so the heaviest bit-blasted operation is on
/// `2·MAX_FF_PRIME_BITS` bits. `16` decides every small test prime (2, 3, 5, 7,
/// 11, 13, 17 — all ≤ 5 bits) while declining crypto-sized primes whose
/// bit-blasting would blow up. (A modulus this small is also cheap to verify
/// prime by trial division.)
const MAX_FF_PRIME_BITS: u32 = 16;

/// The bit-width modeling a finite field `GF(p)`: the fewest bits that index the
/// `p` residues `0..p`, i.e. `ceil(log2(p))`. For `p ≤ 2` a single bit suffices.
fn ff_width(p: u128) -> u32 {
    if p <= 2 {
        1
    } else {
        // ceil(log2(p)) = bits needed to represent the largest residue `p-1`.
        (p - 1).ilog2() + 1
    }
}

/// Whether `p` is prime — a finite field's modulus must be prime (SMT-LIB
/// `FiniteField` requires a prime power; only prime fields are modeled). `p` is
/// already known to fit [`MAX_FF_PRIME_BITS`] (≤ 2^16), so trial division to
/// `sqrt(p) ≤ 256` is trivial.
fn is_ff_prime(p: u128) -> bool {
    if p < 2 {
        return false;
    }
    if p.is_multiple_of(2) {
        return p == 2;
    }
    let mut d: u128 = 3;
    while d * d <= p {
        if p.is_multiple_of(d) {
            return false;
        }
        d += 2;
    }
    true
}

/// Per-script finite-field registry: the modeled bit-width → prime modulus, and
/// the `define-sort` alias names that resolve to a finite field. Built once,
/// up front (mirroring [`build_seq_info`]); immutable for the parse, so the
/// `ff.*` operator dispatch can recover an operand's prime from its bit width.
#[derive(Default)]
pub(crate) struct FfInfo {
    /// `modeled_width → prime`. The width `ff_width(p)` is injective across the
    /// primes a *single* script declares unless two distinct primes share a
    /// bit-length (e.g. 11 and 13 both need 4 bits); such a collision makes the
    /// whole script decline (so an `ff.*` op can never recover the *wrong* prime
    /// from a width).
    width_to_prime: HashMap<u32, u128>,
    /// `define-sort` alias name → prime, so `(as ffK F)` over a sort alias `F`
    /// (e.g. `(define-sort F () (_ FiniteField 17))`) recovers its prime.
    alias_to_prime: HashMap<String, u128>,
}

impl FfInfo {
    /// Whether the script declares no finite-field sort (the fast path: a
    /// non-`QF_FF` script threads an empty registry and never hits FF dispatch).
    fn is_empty(&self) -> bool {
        self.width_to_prime.is_empty()
    }

    /// The prime modulus of a finite-field operand of bit width `w`, or `None` if
    /// `w` is not a registered finite-field width (so a stray `ff.*` over a plain
    /// bit-vector declines rather than misbehaves).
    fn prime_of_width(&self, w: u32) -> Option<u128> {
        self.width_to_prime.get(&w).copied()
    }
}

/// Whether `e` mentions a `FiniteField` sort head or any `ff.*`/`#f…` token
/// anywhere (the fast-path guard: a script with no finite fields skips
/// [`build_ff_info`]).
fn mentions_ff(e: &SExpr) -> bool {
    match e {
        SExpr::Atom(a) => a.starts_with("ff.") || a.starts_with("#f"),
        SExpr::List(items) => {
            items.get(1).and_then(SExpr::atom) == Some("FiniteField")
                || items.iter().any(mentions_ff)
        }
    }
}

/// Parses the modulus of a `(_ FiniteField p)` sort s-expr. Returns the prime as
/// a `u128`, declining (with the relevant `Unsupported` reason) when the modulus
/// overflows `u128`, exceeds the bit-width cap, or is not prime.
fn parse_ff_modulus(items: &[SExpr]) -> Result<u128, SmtError> {
    let raw = items[2]
        .atom()
        .ok_or_else(|| SmtError::Syntax("FiniteField modulus must be a numeral".to_owned()))?;
    let p = raw.parse::<u128>().map_err(|_| {
        SmtError::Unsupported(format!(
            "finite field modulus `{raw}` exceeds the modeled range (a crypto-sized prime; \
             bit-blasting is declined)"
        ))
    })?;
    if ff_width(p) > MAX_FF_PRIME_BITS {
        return Err(SmtError::Unsupported(format!(
            "finite field modulus {p} needs {} bits (> the {MAX_FF_PRIME_BITS}-bit cap); \
             bit-blasting a field this large is declined",
            ff_width(p)
        )));
    }
    if !is_ff_prime(p) {
        return Err(SmtError::Unsupported(format!(
            "finite field modulus {p} is not prime; only prime fields `GF(p)` are modeled"
        )));
    }
    Ok(p)
}

/// Whether an atom is a finite-field literal identifier `ffK` (`ff` followed by an
/// optional `-` and decimal digits, e.g. `ff0`, `ff16`, `ff-1`) — the term form
/// used inside `(as ffK Sort)`.
fn is_ff_literal_name(a: Option<&str>) -> bool {
    let Some(rest) = a.and_then(|a| a.strip_prefix("ff")) else {
        return false;
    };
    let digits = rest.strip_prefix('-').unwrap_or(rest);
    !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit())
}

/// Whether a sort s-expr is `(_ FiniteField p)` (a list of 3 with that head).
fn is_ff_sort_sexpr(e: &SExpr) -> bool {
    e.list().is_some_and(is_ff_sort_items)
}

/// Whether a list's items are `[_, FiniteField, p]` — the `(_ FiniteField p)` shape.
fn is_ff_sort_items(items: &[SExpr]) -> bool {
    items.len() == 3 && items[0].atom() == Some("_") && items[1].atom() == Some("FiniteField")
}

/// Builds the finite-field registry for a script by scanning every
/// `(_ FiniteField p)` sort s-expr — directly and through `define-sort` aliases —
/// once, up front (mirroring [`build_seq_info`]). The registry is then immutable
/// for the parse, so the `ff.*` dispatch can recover an operand's prime from its
/// modeled bit width.
///
/// # Errors
///
/// [`SmtError::Unsupported`] for a modulus that overflows `u128`, exceeds
/// [`MAX_FF_PRIME_BITS`], is non-prime, or a width collision (two distinct primes
/// of the same modeled bit-width — the dispatch could not tell them apart, so the
/// whole script declines, soundly).
fn build_ff_info(exprs: &[SExpr]) -> Result<FfInfo, SmtError> {
    let mut info = FfInfo::default();
    if !exprs.iter().any(mentions_ff) {
        return Ok(info);
    }
    for e in exprs {
        scan_ff_sorts(e, &mut info)?;
    }
    Ok(info)
}

/// Recursively registers every `(_ FiniteField p)` sort s-expr in `e`, and binds
/// `define-sort` aliases (`(define-sort F () (_ FiniteField p))`) to their prime.
/// Also registers the modulus of any `#fKmM` field literal, so a script whose
/// fields appear only through literals (no declared field symbol) still resolves
/// the `ff.*` dispatch.
fn scan_ff_sorts(e: &SExpr, info: &mut FfInfo) -> Result<(), SmtError> {
    let SExpr::Atom(a) = e else {
        let SExpr::List(items) = e else {
            return Ok(());
        };
        return scan_ff_sorts_list(items, info);
    };
    // A `#fKmM` literal carries its prime modulus `M`; register it (validating
    // bit-cap and primality) so the dispatch can recover the field by width.
    if let Some(body) = a.strip_prefix("#f")
        && let Some((_, m_str)) = body.split_once('m')
        && let Ok(m) = m_str.parse::<u128>()
    {
        if ff_width(m) > MAX_FF_PRIME_BITS {
            return Err(SmtError::Unsupported(format!(
                "finite-field literal `{a}` modulus needs > {MAX_FF_PRIME_BITS} bits; declined"
            )));
        }
        if !is_ff_prime(m) {
            return Err(SmtError::Unsupported(format!(
                "finite-field literal `{a}` modulus {m} is not prime"
            )));
        }
        register_ff_prime(info, m)?;
    }
    Ok(())
}

/// Registers finite-field sorts/aliases in a list s-expr (the recursive case of
/// [`scan_ff_sorts`]).
fn scan_ff_sorts_list(items: &[SExpr], info: &mut FfInfo) -> Result<(), SmtError> {
    if is_ff_sort_items(items) {
        let p = parse_ff_modulus(items)?;
        register_ff_prime(info, p)?;
        return Ok(());
    }
    // `(define-sort name () (_ FiniteField p))` — record name → prime so a later
    // `(as ffK name)` (and `(_ FiniteField p)` resolution) can recover the prime.
    if items.len() == 4
        && items[0].atom() == Some("define-sort")
        && items
            .get(2)
            .and_then(SExpr::list)
            .is_some_and(<[SExpr]>::is_empty)
        && is_ff_sort_sexpr(&items[3])
        && let Some(name) = items[1].atom()
    {
        let p = parse_ff_modulus(items[3].list().expect("checked is_ff_sort_sexpr"))?;
        register_ff_prime(info, p)?;
        info.alias_to_prime.insert(name.to_owned(), p);
    }
    for child in items {
        scan_ff_sorts(child, info)?;
    }
    Ok(())
}

/// Registers a finite-field prime by its modeled bit-width, declining on a width
/// collision (two distinct primes of the same bit-length).
fn register_ff_prime(info: &mut FfInfo, p: u128) -> Result<(), SmtError> {
    let w = ff_width(p);
    match info.width_to_prime.insert(w, p) {
        Some(prev) if prev != p => Err(SmtError::Unsupported(format!(
            "two finite-field moduli ({prev} and {p}) share the {w}-bit modeling width; \
             this script mixes fields the bit-width dispatch cannot separate"
        ))),
        _ => Ok(()),
    }
}

/// The prime modulus of a finite-field operand term `v`, recovered from its
/// modeled bit width.
///
/// # Errors
///
/// [`SmtError::Unsupported`] if `v` is not a registered finite-field operand (so a
/// stray `ff.*` over a plain bit-vector declines rather than misbehaves).
fn ff_prime_of(arena: &TermArena, ff: &FfInfo, v: TermId) -> Result<u128, SmtError> {
    match arena.sort_of(v) {
        Sort::BitVec(w) => ff.prime_of_width(w).ok_or_else(|| {
            SmtError::Unsupported(format!(
                "finite-field operator applied to a non-field `BitVec({w})`"
            ))
        }),
        s => Err(SmtError::Unsupported(format!(
            "finite-field operator applied to a non-field operand of sort {s:?}"
        ))),
    }
}

/// `(x + y) mod p` for two well-formed (`< p`) field elements of width `w`: add
/// in width `w + 1` (the sum is `< 2p ≤ 2^{w+1}`), then one conditional subtract
/// of `p` (`ite(sum ≥ p, sum − p, sum)`), truncated back to `w`. The single
/// conditional subtract is exact because both operands are `< p`, so the sum is
/// `< 2p`, hence at most one `p` need be removed.
fn ff_add2(
    arena: &mut TermArena,
    p: u128,
    w: u32,
    x: TermId,
    y: TermId,
) -> Result<TermId, SmtError> {
    let zero = arena.bv_const(1, 0)?;
    let xe = arena.concat(zero, x)?; // zero-extend to w+1
    let ye = arena.concat(zero, y)?;
    let sum = arena.bv_add(xe, ye)?; // < 2p, fits w+1 bits
    let pw = arena.bv_const(w + 1, p)?;
    let ge = arena.bv_uge(sum, pw)?;
    let sub = arena.bv_sub(sum, pw)?;
    let reduced = arena.ite(ge, sub, sum)?;
    Ok(arena.extract(w - 1, 0, reduced)?) // canonical residue, width w
}

/// `(p − x) mod p` = the field negation of a well-formed (`< p`) element:
/// `ite(x = 0, 0, p − x)`. (`p − x` is computed in width `w`; for `x ≠ 0` it
/// equals `(−x) mod p` and is already `< p`.)
fn ff_neg(arena: &mut TermArena, p: u128, w: u32, x: TermId) -> Result<TermId, SmtError> {
    let zero = arena.bv_const(w, 0)?;
    let pw = arena.bv_const(w, p)?;
    let is_zero = arena.eq(x, zero)?;
    let sub = arena.bv_sub(pw, x)?;
    Ok(arena.ite(is_zero, zero, sub)?)
}

/// `(x · y) mod p` for two well-formed (`< p`) field elements of width `w`:
/// zero-extend both to `2w`, multiply (the product `< p^2 ≤ 2^{2w}` fits), then
/// `bvurem` by `p` (exact unsigned remainder), truncated back to `w`.
fn ff_mul2(
    arena: &mut TermArena,
    p: u128,
    w: u32,
    x: TermId,
    y: TermId,
) -> Result<TermId, SmtError> {
    let zero = arena.bv_const(w, 0)?;
    let xe = arena.concat(zero, x)?; // zero-extend to 2w
    let ye = arena.concat(zero, y)?;
    let prod = arena.bv_mul(xe, ye)?; // < p^2, fits 2w bits
    let p2w = arena.bv_const(2 * w, p)?;
    let rem = arena.bv_urem(prod, p2w)?; // exact mod p, < p
    Ok(arena.extract(w - 1, 0, rem)?) // canonical residue, width w
}

/// `ff.bitsum x0 x1 … x_{k-1}` = `Σ_i 2^i · x_i (mod p)` (cvc5 extension): a
/// positional weighted sum of the field operands. Each weight `2^i mod p` is a
/// constant, so the term is built as a fold of `ff.add`s of `(2^i · x_i) mod p`.
fn ff_bitsum(arena: &mut TermArena, p: u128, w: u32, args: &[TermId]) -> Result<TermId, SmtError> {
    let mut acc = arena.bv_const(w, 0)?;
    let mut weight: u128 = 1 % p;
    for &xi in args {
        // weight·xi mod p, then add into the accumulator (both mod p).
        let wt = arena.bv_const(w, weight)?;
        let term = ff_mul2(arena, p, w, wt, xi)?;
        acc = ff_add2(arena, p, w, acc, term)?;
        weight = (weight * 2) % p;
    }
    Ok(acc)
}

/// Parses a finite-field literal atom `#fKmM` (value `K` mod modulus `M`) into a
/// canonical residue `BitVec(ff_width(M))` constant. `K` may be negative
/// (`#f-1m5`); the residue is `K mod M` reduced into `0..M`. Returns `None` if
/// `a` is not an `#f…m…` literal so `parse_atom` falls through.
fn parse_ff_literal(arena: &mut TermArena, a: &str) -> Option<Result<TermId, SmtError>> {
    let body = a.strip_prefix("#f")?;
    let (k_str, m_str) = body.split_once('m')?;
    Some((|| {
        let m = m_str.parse::<u128>().map_err(|_| {
            SmtError::Unsupported(format!(
                "finite-field literal modulus in `{a}` exceeds the modeled range"
            ))
        })?;
        if ff_width(m) > MAX_FF_PRIME_BITS {
            return Err(SmtError::Unsupported(format!(
                "finite-field literal `{a}` modulus needs > {MAX_FF_PRIME_BITS} bits; declined"
            )));
        }
        if !is_ff_prime(m) {
            return Err(SmtError::Unsupported(format!(
                "finite-field literal `{a}` modulus {m} is not prime"
            )));
        }
        let residue = ff_residue(k_str, m, a)?;
        Ok(arena.bv_const(ff_width(m), residue)?)
    })())
}

/// `(as ffK Sort)` — a field literal whose value is `K` and whose modulus comes
/// from the sort ascription (`(_ FiniteField p)` directly, or a `define-sort`
/// alias resolved via [`FfInfo::alias_to_prime`]). `K` may be negative. Returns
/// the canonical residue `BitVec(ff_width(p))` constant.
fn parse_ff_as_literal(
    arena: &mut TermArena,
    ff: &FfInfo,
    k_atom: &str,
    sort: &SExpr,
) -> Result<TermId, SmtError> {
    let k_str = k_atom.strip_prefix("ff").ok_or_else(|| {
        SmtError::Syntax(format!("`(as {k_atom} …)` is not a finite-field literal"))
    })?;
    let p = ff_sort_prime(ff, sort)?;
    let residue = ff_residue(k_str, p, k_atom)?;
    Ok(arena.bv_const(ff_width(p), residue)?)
}

/// The prime modulus of a sort s-expr that must be a finite field — either
/// `(_ FiniteField p)` directly or a `define-sort` alias registered in `ff`.
fn ff_sort_prime(ff: &FfInfo, sort: &SExpr) -> Result<u128, SmtError> {
    if is_ff_sort_sexpr(sort) {
        return parse_ff_modulus(sort.list().expect("checked is_ff_sort_sexpr"));
    }
    if let Some(name) = sort.atom()
        && let Some(&p) = ff.alias_to_prime.get(name)
    {
        return Ok(p);
    }
    Err(SmtError::Unsupported(format!(
        "`(as ff… {sort:?})` ascription is not a recognized finite-field sort"
    )))
}

/// The residue `K mod M` (in `0..M`) of a (possibly negative) field literal value
/// string `k_str`. The literal value is parsed as an `i128`; values outside that
/// range decline.
fn ff_residue(k_str: &str, m: u128, lit: &str) -> Result<u128, SmtError> {
    let k = k_str.parse::<i128>().map_err(|_| {
        SmtError::Unsupported(format!(
            "finite-field literal value in `{lit}` exceeds the modeled range"
        ))
    })?;
    let mi = i128::try_from(m).map_err(|_| {
        SmtError::Unsupported(format!(
            "finite-field modulus in `{lit}` exceeds the modeled range"
        ))
    })?;
    // `k.rem_euclid(m)` is the non-negative residue in `0..m`.
    let r = k.rem_euclid(mi);
    Ok(u128::try_from(r).expect("rem_euclid result is in 0..m, non-negative"))
}

/// Dispatch for the finite-field operators `ff.add`, `ff.neg`, `ff.mul`, and
/// `ff.bitsum` (`QF_FF`). Returns `Some(term)` for an `ff.*` head, or `None` for any
/// other operator (so the normal `apply_op` dispatch continues untouched). The
/// operand prime is recovered from the first field argument's modeled width; every
/// result is reduced to a canonical residue `< p` so the modeling stays
/// denotation-preserving.
fn apply_ff_op(
    arena: &mut TermArena,
    ff: &FfInfo,
    op: &str,
    args: &[TermId],
) -> Result<Option<TermId>, SmtError> {
    let out = match op {
        "ff.add" | "ff.mul" | "ff.bitsum" => {
            if args.is_empty() {
                return Err(SmtError::Syntax(format!("`{op}` expects ≥ 1 argument")));
            }
            let p = ff_prime_of(arena, ff, args[0])?;
            let w = ff_width(p);
            match op {
                "ff.add" => {
                    let mut acc = args[0];
                    for &next in &args[1..] {
                        acc = ff_add2(arena, p, w, acc, next)?;
                    }
                    acc
                }
                "ff.mul" => {
                    let mut acc = args[0];
                    for &next in &args[1..] {
                        acc = ff_mul2(arena, p, w, acc, next)?;
                    }
                    acc
                }
                "ff.bitsum" => ff_bitsum(arena, p, w, args)?,
                _ => unreachable!("matched ff.add/ff.mul/ff.bitsum"),
            }
        }
        "ff.neg" => {
            if args.len() != 1 {
                return Err(SmtError::Syntax(format!(
                    "`ff.neg` expects 1 argument, got {}",
                    args.len()
                )));
            }
            let p = ff_prime_of(arena, ff, args[0])?;
            ff_neg(arena, p, ff_width(p), args[0])?
        }
        _ => return Ok(None),
    };
    Ok(Some(out))
}

/// Resolves a `(Seq E)` sort s-expr to its packed `BitVec` sort (max length
/// [`SEQ_MAX_LEN`]). Pure: the width→ew mapping was registered by the up-front
/// [`build_seq_info`] scan, so this only computes the resolved [`Sort`].
///
/// # Errors
///
/// [`SmtError::Unsupported`] for a `(Seq E)` whose element sort `E` is not a
/// soundly-packable fixed-width sort (see [`seq_elem_width`]).
fn seq_sort(items: &[SExpr]) -> Result<Sort, SmtError> {
    let ew = seq_elem_width(&items[1]).ok_or_else(|| {
        SmtError::Unsupported(format!(
            "`(Seq {:?})` has no sound fixed-width element packing (only Bool, Int, and \
             `(_ BitVec w)` with w ≠ 8 are modeled; ADR-0029)",
            items[1]
        ))
    })?;
    let m = seq_max_len_for(ew).ok_or_else(|| {
        SmtError::Unsupported(format!(
            "sequence element width {ew} exceeds the packed-sort bit ceiling (ADR-0029)"
        ))
    })?;
    Ok(Sort::BitVec(seq_total(ew, m)))
}

/// The element width of a packed sequence term `v`, from the registry.
///
/// # Errors
///
/// [`SmtError::Unsupported`] if `v` is not a registered packed-sequence operand
/// (so a non-sequence operand to a `seq.*` op declines rather than misbehaves).
fn seq_ew(arena: &TermArena, seq: &SeqInfo, v: TermId) -> Result<u32, SmtError> {
    match arena.sort_of(v) {
        Sort::BitVec(w) => seq.elem_width_of(w).ok_or_else(|| {
            SmtError::Unsupported(format!(
                "sequence operator applied to a non-sequence `BitVec({w})` (ADR-0029)"
            ))
        }),
        s => Err(SmtError::Unsupported(format!(
            "sequence operator applied to a non-sequence operand of sort {s:?} (ADR-0029)"
        ))),
    }
}

/// The max length `m` of a packed sequence term `v` of element width `ew`,
/// recovered from its bit width `seq_total(ew, m) = len_width(m) + m·ew`.
fn seq_max_len(arena: &TermArena, seq: &SeqInfo, v: TermId) -> Result<(u32, u32), SmtError> {
    let ew = seq_ew(arena, seq, v)?;
    let Sort::BitVec(w) = arena.sort_of(v) else {
        unreachable!("seq_ew accepted a BitVec");
    };
    let m = (1..=SEQ_LEN_SOFT_CAP)
        .find(|&m| seq_total(ew, m) == w)
        .ok_or_else(|| {
            SmtError::Unsupported(format!(
                "packed sequence width {w} is not seq_total(ew={ew}, m) for any m ≤ \
                 {SEQ_LEN_SOFT_CAP}"
            ))
        })?;
    Ok((ew, m))
}

/// The length field (a `BitVec(len_width(m))`) of a packed sequence of max
/// length `m`.
fn seq_len_field(arena: &mut TermArena, v: TermId, m: u32) -> Result<TermId, SmtError> {
    arena.extract(len_width(m) - 1, 0, v).map_err(SmtError::Ir)
}

/// Content element `i` (a `BitVec(ew)`) of a packed sequence of max length `m`.
fn seq_elem_m(
    arena: &mut TermArena,
    v: TermId,
    i: u32,
    m: u32,
    ew: u32,
) -> Result<TermId, SmtError> {
    let lo = len_width(m) + i * ew;
    arena.extract(lo + ew - 1, lo, v).map_err(SmtError::Ir)
}

/// The canonical well-formedness constraint for a packed sequence `v` of max
/// length `m` and element width `ew`: its length is `≤ m`, and every content
/// element at or above the length is zero (so equal sequences share one bit
/// pattern and `=`/`distinct` decide via plain BV (in)equality).
fn seq_wellformed(arena: &mut TermArena, v: TermId, m: u32, ew: u32) -> Result<TermId, SmtError> {
    let lwm = len_width(m);
    let len = arena.extract(lwm - 1, 0, v)?;
    let max = arena.bv_const(lwm, u128::from(m))?;
    let mut wf = arena.bv_ule(len, max)?;
    let zero = arena.bv_const(ew, 0)?;
    for i in 0..m {
        let elem = seq_elem_m(arena, v, i, m, ew)?;
        let elem_zero = arena.eq(elem, zero)?;
        let idx = arena.bv_const(lwm, u128::from(i))?;
        let active = arena.bv_ult(idx, len)?;
        let ok = arena.or(active, elem_zero)?;
        wf = arena.and(wf, ok)?;
    }
    Ok(wf)
}

/// Re-packs a packed sequence `v` (max length `m`, element width `ew`) into the
/// layout of a sequence of max length `to` (`to ≥ m`): the length is
/// zero-extended to `len_width(to)`, and each content element is moved to its
/// position in the wider layout. Mirrors `string_widen` with `ew` for `8`.
fn seq_widen(
    arena: &mut TermArena,
    v: TermId,
    m: u32,
    to: u32,
    ew: u32,
) -> Result<TermId, SmtError> {
    debug_assert!(to >= m, "seq_widen only widens");
    if to == m {
        return Ok(v);
    }
    let len = seq_len_field(arena, v, m)?;
    let rlen = arena.zero_ext(len_width(to) - len_width(m), len)?;
    let zero = arena.bv_const(ew, 0)?;
    let mut content: Option<TermId> = None;
    for i in (0..to).rev() {
        let elem = if i < m {
            seq_elem_m(arena, v, i, m, ew)?
        } else {
            zero
        };
        content = Some(match content {
            None => elem,
            Some(acc) => arena.concat(acc, elem)?,
        });
    }
    let content = content.expect("to ≥ 1");
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// Widens `x` and `y` to a shared max length `max(m_x, m_y)` (they must share an
/// element width), returning the re-packed terms, that common length, and `ew`.
fn seq_align(
    arena: &mut TermArena,
    seq: &SeqInfo,
    x: TermId,
    y: TermId,
) -> Result<(TermId, TermId, u32, u32), SmtError> {
    let (ewx, mx) = seq_max_len(arena, seq, x)?;
    let (ewy, my) = seq_max_len(arena, seq, y)?;
    if ewx != ewy {
        return Err(SmtError::Unsupported(format!(
            "sequence operands have differing element widths ({ewx} vs {ewy})"
        )));
    }
    let m = mx.max(my);
    let xw = seq_widen(arena, x, mx, m, ewx)?;
    let yw = seq_widen(arena, y, my, m, ewx)?;
    Ok((xw, yw, m, ewx))
}

/// `(as seq.empty (Seq E))` — the empty sequence (length 0, zero content) in the
/// max-length-[`SEQ_MAX_LEN`] layout for element width `ew`.
fn seq_empty(arena: &mut TermArena, ew: u32) -> Result<TermId, SmtError> {
    let m = seq_max_len_for(ew).ok_or_else(|| {
        SmtError::Unsupported(format!(
            "sequence element width {ew} exceeds the packed-sort bit ceiling (ADR-0029)"
        ))
    })?;
    arena.bv_const(seq_total(ew, m), 0).map_err(SmtError::Ir)
}

/// `(seq.unit e)` — the length-1 sequence holding element `e` (already a
/// `BitVec(ew)`), packed as `e ++ length(1)`.
fn seq_unit(arena: &mut TermArena, e: TermId) -> Result<TermId, SmtError> {
    let one_len = arena.bv_const(len_width(1), 1)?;
    arena.concat(e, one_len).map_err(SmtError::Ir)
}

/// `(seq.len s)` as an `Int` (the length field lifted out via `bv2nat`).
fn seq_len(arena: &mut TermArena, seq: &SeqInfo, s: TermId) -> Result<TermId, SmtError> {
    let (_ew, m) = seq_max_len(arena, seq, s)?;
    let len = seq_len_field(arena, s, m)?;
    arena.bv2nat(len).map_err(SmtError::Ir)
}

/// Semantic sequence equality (equal length, equal elements below the length,
/// padding ignored), aligning operands of differing widths first. Used by
/// `=`/`distinct` only when two packed-sequence operands have **different**
/// widths; equal-width operands keep plain bit-vector equality (sound by the
/// canonical well-formedness).
fn seq_equal(
    arena: &mut TermArena,
    seq: &SeqInfo,
    x: TermId,
    y: TermId,
) -> Result<TermId, SmtError> {
    let (x, y, m, ew) = seq_align(arena, seq, x, y)?;
    let xlen = seq_len_field(arena, x, m)?;
    let ylen = seq_len_field(arena, y, m)?;
    let mut acc = arena.eq(xlen, ylen)?;
    for i in 0..m {
        let idx = arena.bv_const(len_width(m), u128::from(i))?;
        let active = arena.bv_ult(idx, xlen)?;
        let ex = seq_elem_m(arena, x, i, m, ew)?;
        let ey = seq_elem_m(arena, y, i, m, ew)?;
        let eeq = arena.eq(ex, ey)?;
        let nactive = arena.not(active)?;
        let implied = arena.or(nactive, eeq)?;
        acc = arena.and(acc, implied)?;
    }
    Ok(acc)
}

/// `=`/`distinct` over a pair of packed-sequence operands of **different**
/// widths → [`seq_equal`]; otherwise `None` (the caller keeps plain `arena.eq`).
/// Equal-width sequence operands are sound under plain BV equality (canonical
/// well-formedness), so they too return `None`.
fn seq_aware_eq(
    arena: &mut TermArena,
    seq: &SeqInfo,
    a: TermId,
    b: TermId,
) -> Result<Option<TermId>, SmtError> {
    let (Sort::BitVec(wa), Sort::BitVec(wb)) = (arena.sort_of(a), arena.sort_of(b)) else {
        return Ok(None);
    };
    if wa == wb {
        return Ok(None); // same sort — plain eq is sound by well-formedness
    }
    if seq.elem_width_of(wa).is_some() && seq.elem_width_of(wb).is_some() {
        return Ok(Some(seq_equal(arena, seq, a, b)?));
    }
    Ok(None)
}

/// `(seq.++ a b)` of two packed-sequence operands of element width `ew`. Produces
/// a result in the wider sort `max_len(x) + max_len(y)` (capped at
/// [`SEQ_BOUND_CAP`]): result length `len(x) + len(y)`, result content
/// `content(x) | (content(y) << (len(x)·ew))` with `x`'s padding masked off.
/// Mirrors `string_concat_pair` with `ew` for `8`.
#[allow(clippy::similar_names)]
fn seq_concat_pair(
    arena: &mut TermArena,
    seq: &SeqInfo,
    x: TermId,
    y: TermId,
) -> Result<TermId, SmtError> {
    let (ewx, mx) = seq_max_len(arena, seq, x)?;
    let (ewy, my) = seq_max_len(arena, seq, y)?;
    if ewx != ewy {
        return Err(SmtError::Unsupported(format!(
            "seq.++ over differing element widths ({ewx} vs {ewy})"
        )));
    }
    let ew = ewx;
    let rm = mx + my;
    if rm > SEQ_LEN_SOFT_CAP || seq_total(ew, rm) > SEQ_TOTAL_BITS_CAP {
        return Err(SmtError::Unsupported(format!(
            "seq.++ result of bounded max length {rm} (over {ew}-bit elements) exceeds the \
             packed-sequence bound (ADR-0029)"
        )));
    }
    let rcw = rm * ew; // result content width
    let rlw = len_width(rm); // result length width

    let xlen = seq_len_field(arena, x, mx)?;
    let ylen = seq_len_field(arena, y, my)?;
    let len_x_r = arena.zero_ext(rlw - len_width(mx), xlen)?;
    let len_y_r = arena.zero_ext(rlw - len_width(my), ylen)?;
    let rlen = arena.bv_add(len_x_r, len_y_r)?;

    let zero = arena.bv_const(ew, 0)?;
    let mut xcontent: Option<TermId> = None;
    for i in (0..rm).rev() {
        let elem = if i < mx {
            seq_elem_m(arena, x, i, mx, ew)?
        } else {
            zero
        };
        xcontent = Some(match xcontent {
            None => elem,
            Some(acc) => arena.concat(acc, elem)?,
        });
    }
    let x_content_r = xcontent.expect("rm ≥ 1");

    let mut ycontent: Option<TermId> = None;
    for i in (0..rm).rev() {
        let elem = if i < my {
            seq_elem_m(arena, y, i, my, ew)?
        } else {
            zero
        };
        ycontent = Some(match ycontent {
            None => elem,
            Some(acc) => arena.concat(acc, elem)?,
        });
    }
    let y_content_r = ycontent.expect("rm ≥ 1");

    // shift (in bits) for y = len_x * ew, in the result content width.
    let len_x_c = arena.zero_ext(rcw - len_width(mx), xlen)?;
    let ew_log = arena.bv_const(rcw, u128::from(ew))?;
    let shift = arena.bv_mul(len_x_c, ew_log)?;

    let one = arena.bv_const(rcw, 1)?;
    let pow = arena.bv_shl(one, shift)?; // 2^(len_x*ew)
    let mask = arena.bv_sub(pow, one)?;
    let x_masked = arena.bv_and(x_content_r, mask)?;

    let y_shifted = arena.bv_shl(y_content_r, shift)?;
    let rcontent = arena.bv_or(x_masked, y_shifted)?;

    arena.concat(rcontent, rlen).map_err(SmtError::Ir)
}

/// `(seq.++ args…)` — left-fold [`seq_concat_pair`]. Zero operands is declined
/// (the empty sequence has no element width without an `(as seq.empty …)`
/// annotation, which is handled at parse time); one operand is itself.
fn seq_concat(arena: &mut TermArena, seq: &SeqInfo, args: &[TermId]) -> Result<TermId, SmtError> {
    if args.is_empty() {
        return Err(SmtError::Unsupported(
            "nullary seq.++ has no element width to model".to_owned(),
        ));
    }
    let mut acc = args[0];
    seq_max_len(arena, seq, acc)?; // validate it is a packed sequence
    for &arg in &args[1..] {
        acc = seq_concat_pair(arena, seq, acc, arg)?;
    }
    Ok(acc)
}

/// `(seq.extract s off n)` — the bounded sub-sequence of `s` starting at `Int`
/// offset `off` for up to `n` elements, the SMT-LIB total function: the empty
/// sequence unless `0 ≤ off < len(s)` and `n > 0`, else `s[off .. min(off+n,
/// len(s))]`. Mirrors `string_substr` over elements (`ew` for `8`). The result is
/// packed in the operand's own max-length layout, so it composes with `=`/len.
fn seq_extract(
    arena: &mut TermArena,
    seq: &SeqInfo,
    s: TermId,
    off: TermId,
    n: TermId,
) -> Result<TermId, SmtError> {
    let (ew, m) = seq_max_len(arena, seq, s)?;
    let len_field = seq_len_field(arena, s, m)?;
    let len_i = arena.bv2nat(len_field)?;
    let zero_i = arena.int_const(0);
    let off_nonneg = arena.int_ge(off, zero_i)?;
    let off_in = arena.int_lt(off, len_i)?;
    let start_ok = arena.and(off_nonneg, off_in)?;
    let zero = arena.bv_const(ew, 0)?;
    // Selects element at `Int` index `src` of `s`: `(elem, in_range)` with
    // `in_range` exactly when `0 ≤ src < len(s)` (else `(0, false)`).
    let select = |arena: &mut TermArena, src: TermId| -> Result<(TermId, TermId), SmtError> {
        let mut elem = arena.bv_const(ew, 0)?;
        let mut in_range = arena.bool_const(false);
        for j in 0..m {
            let jconst = arena.int_const(i128::from(j));
            let is_j = arena.eq(src, jconst)?;
            let jbv = arena.bv_const(len_width(m), u128::from(j))?;
            let j_active = arena.bv_ult(jbv, len_field)?;
            let hit = arena.and(is_j, j_active)?;
            let ej = seq_elem_m(arena, s, j, m, ew)?;
            elem = arena.ite(hit, ej, elem)?;
            in_range = arena.or(in_range, hit)?;
        }
        Ok((elem, in_range))
    };
    let present = |arena: &mut TermArena, p: u32, src_in: TermId| -> Result<TermId, SmtError> {
        let pconst = arena.int_const(i128::from(p));
        let p_lt_n = arena.int_lt(pconst, n)?;
        let present0 = arena.and(start_ok, p_lt_n)?;
        arena.and(present0, src_in).map_err(SmtError::Ir)
    };
    let mut count_i = arena.int_const(0);
    for p in 0..m {
        let pconst = arena.int_const(i128::from(p));
        let src = arena.int_add(off, pconst)?;
        let (_elem, src_in) = select(arena, src)?;
        let pres = present(arena, p, src_in)?;
        let one_i = arena.int_const(1);
        let inc = arena.ite(pres, one_i, zero_i)?;
        count_i = arena.int_add(count_i, inc)?;
    }
    let mut content: Option<TermId> = None;
    for p in (0..m).rev() {
        let pconst = arena.int_const(i128::from(p));
        let src = arena.int_add(off, pconst)?;
        let (elem, src_in) = select(arena, src)?;
        let pres = present(arena, p, src_in)?;
        let out_elem = arena.ite(pres, elem, zero)?;
        content = Some(match content {
            None => out_elem,
            Some(acc) => arena.concat(acc, out_elem)?,
        });
    }
    let content = content.expect("m ≥ 1");
    let rlen = arena.int2bv(len_width(m), count_i)?;
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// `(seq.prefixof x y)` — `x` is a prefix of `y`: `len(x) ≤ len(y)` and the first
/// `len(x)` elements match. Mirrors `string_prefixof` over elements.
fn seq_prefixof(
    arena: &mut TermArena,
    seq: &SeqInfo,
    x: TermId,
    y: TermId,
) -> Result<TermId, SmtError> {
    let (x, y, m, ew) = seq_align(arena, seq, x, y)?;
    let xlen = seq_len_field(arena, x, m)?;
    let ylen = seq_len_field(arena, y, m)?;
    let mut acc = arena.bv_ule(xlen, ylen)?;
    for i in 0..m {
        let xe = seq_elem_m(arena, x, i, m, ew)?;
        let ye = seq_elem_m(arena, y, i, m, ew)?;
        let eeq = arena.eq(xe, ye)?;
        let idx = arena.bv_const(len_width(m), u128::from(i))?;
        let active = arena.bv_ult(idx, xlen)?;
        let nactive = arena.not(active)?;
        let ok = arena.or(nactive, eeq)?;
        acc = arena.and(acc, ok)?;
    }
    Ok(acc)
}

/// `(seq.suffixof x y)` — `x` is a suffix of `y`. Mirrors `string_suffixof`.
fn seq_suffixof(
    arena: &mut TermArena,
    seq: &SeqInfo,
    x: TermId,
    y: TermId,
) -> Result<TermId, SmtError> {
    let (x, y, m, ew) = seq_align(arena, seq, x, y)?;
    let xlen = seq_len_field(arena, x, m)?;
    let ylen = seq_len_field(arena, y, m)?;
    let xlen_w = arena.zero_ext(1, xlen)?;
    let ylen_w = arena.zero_ext(1, ylen)?;
    let wlen = len_width(m) + 1;
    let mut any = arena.bool_const(false);
    for o in 0..=m {
        let oconst = arena.bv_const(wlen, u128::from(o))?;
        let sum = arena.bv_add(oconst, xlen_w)?;
        let aligned = arena.eq(sum, ylen_w)?;
        let mut matched = aligned;
        for i in 0..m {
            if o + i >= m {
                break;
            }
            let xe = seq_elem_m(arena, x, i, m, ew)?;
            let ye = seq_elem_m(arena, y, o + i, m, ew)?;
            let eeq = arena.eq(xe, ye)?;
            let iconst = arena.bv_const(len_width(m), u128::from(i))?;
            let iactive = arena.bv_ult(iconst, xlen)?;
            let niactive = arena.not(iactive)?;
            let ok = arena.or(niactive, eeq)?;
            matched = arena.and(matched, ok)?;
        }
        any = arena.or(any, matched)?;
    }
    Ok(any)
}

/// `(seq.contains x y)` — `y` occurs in `x` as a contiguous sub-sequence. Mirrors
/// `string_contains` over elements.
fn seq_contains(
    arena: &mut TermArena,
    seq: &SeqInfo,
    x: TermId,
    y: TermId,
) -> Result<TermId, SmtError> {
    let (x, y, m, ew) = seq_align(arena, seq, x, y)?;
    let xlen = seq_len_field(arena, x, m)?;
    let ylen = seq_len_field(arena, y, m)?;
    let xlen_w = arena.zero_ext(1, xlen)?;
    let ylen_w = arena.zero_ext(1, ylen)?;
    let wlen = len_width(m) + 1;
    let mut any = arena.bool_const(false);
    for d in 0..m {
        let dconst = arena.bv_const(wlen, u128::from(d))?;
        let sum = arena.bv_add(dconst, ylen_w)?;
        let fits = arena.bv_ule(sum, xlen_w)?;
        let mut matched = fits;
        for j in 0..m {
            if d + j >= m {
                break;
            }
            let xe = seq_elem_m(arena, x, d + j, m, ew)?;
            let ye = seq_elem_m(arena, y, j, m, ew)?;
            let eeq = arena.eq(xe, ye)?;
            let jconst = arena.bv_const(len_width(m), u128::from(j))?;
            let jactive = arena.bv_ult(jconst, ylen)?;
            let njactive = arena.not(jactive)?;
            let ok = arena.or(njactive, eeq)?;
            matched = arena.and(matched, ok)?;
        }
        any = arena.or(any, matched)?;
    }
    Ok(any)
}

/// Lifts a packed element `BitVec(ew)` back to its SMT-LIB element sort `es`: a
/// `Bool` element is `elem = #b1`, an `Int` element is its **signed** value
/// (`bv2nat(elem) − 2^ew · msb(elem)`, exact two's-complement), and a `BitVec`
/// element passes through. The inverse of [`seq_coerce_elem`] for the result of
/// `seq.nth`.
fn seq_lift_elem(arena: &mut TermArena, elem: TermId, es: SeqElemSort) -> Result<TermId, SmtError> {
    match es {
        SeqElemSort::Bool => {
            let one = arena.bv_const(1, 1)?;
            arena.eq(elem, one).map_err(SmtError::Ir)
        }
        SeqElemSort::Int => {
            let ew = SEQ_INT_WIDTH;
            let uns = arena.bv2nat(elem)?;
            // sign bit (the top bit) lifted to an `Int` 0/1, times 2^ew.
            let msb = arena.extract(ew - 1, ew - 1, elem)?;
            let msb_i = arena.bv2nat(msb)?;
            let pow = arena.int_const(1i128 << ew);
            let corr = arena.int_mul(msb_i, pow)?;
            arena.int_sub(uns, corr).map_err(SmtError::Ir)
        }
        SeqElemSort::BitVec(_) => Ok(elem),
    }
}

/// A fresh, unconstrained `BitVec(ew)` value standing for the **out-of-bounds**
/// result of `(seq.nth s i)`. SMT-LIB leaves the out-of-bounds value
/// unconstrained, so this is a free symbol; it is keyed deterministically by the
/// operand term ids `(s.index, i.index)` so two **syntactically** identical
/// applications already share one value (`seq.nth` is a function). Semantic
/// congruence over distinct-but-equal operands is closed by
/// [`SeqInfo::drain_nth_congruence`].
fn seq_nth_oob_value(
    arena: &mut TermArena,
    s: TermId,
    i: TermId,
    ew: u32,
) -> Result<TermId, SmtError> {
    let name = format!("!seq.nth.oob.{}.{}.{ew}", s.index(), i.index());
    // Internal namespace: reuse by name so the same OOB `seq.nth` shares one
    // unspecified value, but never alias a user `declare` of this name
    // (no-aliasing firewall — see `TermArena::declare_internal`).
    let sym = match arena.find_internal_symbol(&name) {
        Some(sym) => sym,
        None => arena.declare_internal(&name, Sort::BitVec(ew))?,
    };
    Ok(arena.var(sym))
}

/// `(seq.nth s i)` — the `i`-th element of `s`, the SMT-LIB **partial** function:
/// in-bounds (`0 ≤ i < len(s)`) it is the element; out-of-bounds it is
/// **unconstrained** (a fresh, free value, *not* a fixed default — zero-padding
/// here would force a wrong `unsat`). The result has the sequence's element sort.
///
/// In-bounds value is the existing position mux (an `Int`-equality select over the
/// `≤ m` content slots). The out-of-bounds value is a fresh per-`(s,i)` symbol
/// ([`seq_nth_oob_value`]); the application is registered so the eager congruence
/// pass pins equal-operand applications to agree. A **constant** index resolves
/// in/out-of-bounds against the literal directly; a symbolic index threads the
/// `ite(0 ≤ i < len(s), mux, oob)`.
fn seq_nth(arena: &mut TermArena, seq: &SeqInfo, s: TermId, i: TermId) -> Result<TermId, SmtError> {
    let (ew, m) = seq_max_len(arena, seq, s)?;
    let es = seq
        .elem_sort_of(match arena.sort_of(s) {
            Sort::BitVec(w) => w,
            _ => unreachable!("seq_max_len accepted a BitVec"),
        })
        .ok_or_else(|| {
            SmtError::Unsupported(
                "seq.nth over a sequence whose element sort is not registered (ADR-0029)"
                    .to_owned(),
            )
        })?;
    let len_field = seq_len_field(arena, s, m)?;
    // The position mux: the `i`-th content element, with an `in_bounds` flag that
    // is true exactly when `0 ≤ i < len(s)` — a slot `j` is hit only when the
    // `Int` index equals `j` **and** `j` is below the length (mirrors
    // `seq_extract`'s `select`). A constant `i` outside `[0, m)` matches no slot,
    // so `in_bounds` folds to false (the out-of-bounds branch).
    let mut elem = arena.bv_const(ew, 0)?;
    let mut in_bounds = arena.bool_const(false);
    for j in 0..m {
        let jconst = arena.int_const(i128::from(j));
        let is_j = arena.eq(i, jconst)?;
        let jbv = arena.bv_const(len_width(m), u128::from(j))?;
        let j_active = arena.bv_ult(jbv, len_field)?;
        let hit = arena.and(is_j, j_active)?;
        let ej = seq_elem_m(arena, s, j, m, ew)?;
        elem = arena.ite(hit, ej, elem)?;
        in_bounds = arena.or(in_bounds, hit)?;
    }
    // Fresh, unconstrained out-of-bounds value, registered for congruence.
    let oob = seq_nth_oob_value(arena, s, i, ew)?;
    seq.register_nth(s, i, oob);
    // The packed element: in-bounds → mux; out-of-bounds → fresh free value.
    let packed = arena.ite(in_bounds, elem, oob)?;
    seq_lift_elem(arena, packed, es)
}

/// `(seq.at s i)` — the **total** unit-sub-sequence at index `i`: in-bounds
/// (`0 ≤ i < len(s)`) the length-1 sequence holding `s[i]`, out-of-bounds the
/// empty sequence (`seq.at` is total, unlike `seq.nth`; it mirrors `str.at`). The
/// result is a packed `(Seq E)` in `s`'s own max-length layout.
fn seq_at(arena: &mut TermArena, seq: &SeqInfo, s: TermId, i: TermId) -> Result<TermId, SmtError> {
    let (ew, m) = seq_max_len(arena, seq, s)?;
    let len_field = seq_len_field(arena, s, m)?;
    // The selected element (0 when out-of-bounds) and the in-bounds flag.
    let mut elem = arena.bv_const(ew, 0)?;
    let mut in_bounds = arena.bool_const(false);
    for j in 0..m {
        let jconst = arena.int_const(i128::from(j));
        let is_j = arena.eq(i, jconst)?;
        let jbv = arena.bv_const(len_width(m), u128::from(j))?;
        let j_active = arena.bv_ult(jbv, len_field)?;
        let hit = arena.and(is_j, j_active)?;
        let ej = seq_elem_m(arena, s, j, m, ew)?;
        elem = arena.ite(hit, ej, elem)?;
        in_bounds = arena.or(in_bounds, hit)?;
    }
    // Pack the result in `s`'s own layout: content element 0 = `elem` (the rest
    // zero), length = `1` in-bounds else `0`. Out-of-bounds the element is already
    // zero, so the empty sequence's canonical (all-zero) pattern falls out.
    let lwm = len_width(m);
    let one_len = arena.bv_const(lwm, 1)?;
    let zero_len = arena.bv_const(lwm, 0)?;
    let rlen = arena.ite(in_bounds, one_len, zero_len)?;
    let mut content: Option<TermId> = None;
    let zero = arena.bv_const(ew, 0)?;
    for p in (0..m).rev() {
        let e = if p == 0 { elem } else { zero };
        content = Some(match content {
            None => e,
            Some(acc) => arena.concat(acc, e)?,
        });
    }
    let content = content.expect("m ≥ 1");
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// `(seq.rev s)` — the **total** reversal of `s`: the first `len(s)` elements in
/// reverse order, `len(s)` unchanged, padding (above the length) zero. Per
/// SMT-LIB Sequences / cvc5 `STRING_REV` this is a pure permutation of the
/// present elements (`out[j] = s[len−1−j]` for `j < len(s)`), so it is
/// denotation-preserving within the bound and packs back into `s`'s own
/// max-length layout (length field copied verbatim).
///
/// Each output slot `j` selects its source element by a bounded **pure-BV** mux
/// over the `≤ m` source slots `k`: `out[j] = s[k]` exactly when `k + j + 1 = len`
/// (i.e. `k = len − 1 − j`), which already implies `j < len` and `k < len`. The
/// match `k + j + 1 = len` is decided as a plain bit-vector equality (no `bv2nat`
/// / integer bridge — keeping the result a ground BV problem the bit-blaster can
/// close). Slots at or above the length match no `k`, so the slot folds to the
/// zero default, preserving the canonical well-formed padding so `=`/`distinct`
/// keep deciding via plain BV equality.
fn seq_rev(arena: &mut TermArena, seq: &SeqInfo, s: TermId) -> Result<TermId, SmtError> {
    let (ew, m) = seq_max_len(arena, seq, s)?;
    let lwm = len_width(m);
    let len_field = seq_len_field(arena, s, m)?;
    // Compare `k + j + 1` (a small constant, ≤ 2m) against `len` in a width wide
    // enough to hold `2m` so the constant never overflows: `len_width(2m)` bits.
    let cw = len_width(2 * m);
    let len_w = if cw > lwm {
        arena.zero_ext(cw - lwm, len_field)?
    } else {
        len_field
    };
    // `out[j]` for `j = 0..m`, low slot first; assembled high-to-low below.
    let mut out_elems = Vec::with_capacity(m as usize);
    for j in 0..m {
        // Mux: pick `s[k]` when `k + j + 1 == len`. This is the (unique) source
        // index `len−1−j`; it also forces `j < len` (else `k+j+1 > len` for all k).
        let mut elem = arena.bv_const(ew, 0)?;
        for k in 0..m {
            let kj1 = arena.bv_const(cw, u128::from(k + j + 1))?;
            let hit = arena.eq(kj1, len_w)?;
            let ek = seq_elem_m(arena, s, k, m, ew)?;
            elem = arena.ite(hit, ek, elem)?;
        }
        out_elems.push(elem);
    }
    let mut content: Option<TermId> = None;
    for j in (0..m as usize).rev() {
        let e = out_elems[j];
        content = Some(match content {
            None => e,
            Some(acc) => arena.concat(acc, e)?,
        });
    }
    let content = content.expect("m ≥ 1");
    // Length is unchanged by reversal.
    arena.concat(content, len_field).map_err(SmtError::Ir)
}

/// `(seq.update s i t)` — `s` with the span starting at index `i` overwritten by
/// the sequence `t`, **truncated to fit within `s`** (length unchanged); the
/// SMT-LIB Sequences / cvc5 `STRING_UPDATE` **total** function. Out of bounds
/// (`i < 0` or `i ≥ len(s)`) it is `s` **unchanged** (a no-op). In bounds, output
/// slot `j` is `t[j − i]` for `i ≤ j < i + len(t)` (and `j < len(s)`, so any
/// overhang of `t` past the end is dropped), else `s[j]`. The corpus's
/// `seq.update`s are span replacements (`(seq.update s i (seq.unit e))`, the
/// length-1 case), but `t` may be any `(Seq E)`; this models the general span,
/// not just the single element. The result is packed in `s`'s own layout (length
/// field copied verbatim, padding preserved).
// `s` (target), `i` (index), `t` (replacement) mirror the SMT-LIB argument order.
#[allow(clippy::many_single_char_names)]
fn seq_update(
    arena: &mut TermArena,
    seq: &SeqInfo,
    s: TermId,
    i: TermId,
    t: TermId,
) -> Result<TermId, SmtError> {
    let (ews, m) = seq_max_len(arena, seq, s)?;
    let (ewt, mt) = seq_max_len(arena, seq, t)?;
    if ews != ewt {
        return Err(SmtError::Unsupported(format!(
            "seq.update replacement element width ({ewt}) differs from the target's ({ews})"
        )));
    }
    let ew = ews;
    // Constant index → a pure-BV encoding (no `bv2nat`/integer bridge), so a
    // ground `seq.update` stays a bit-blastable BV problem the solver can decide.
    if let TermNode::IntConst(iv) = arena.node(i) {
        return seq_update_const(arena, s, t, *iv, ew, m, mt);
    }
    let lwm = len_width(m);
    let len_field = seq_len_field(arena, s, m)?;
    let len_i = arena.bv2nat(len_field)?;
    let tlen_field = seq_len_field(arena, t, mt)?;
    // `in_bounds(i)`: `0 ≤ i < len(s)`. Out of bounds the whole op is a no-op.
    let zero_i = arena.int_const(0);
    let i_nonneg = arena.int_ge(i, zero_i)?;
    let i_below = arena.int_lt(i, len_i)?;
    let i_in_bounds = arena.and(i_nonneg, i_below)?;
    let mut out_elems = Vec::with_capacity(m as usize);
    for j in 0..m {
        let s_elem = seq_elem_m(arena, s, j, m, ew)?;
        // `rel = j − i`: the index into `t` for this output slot (valid only when
        // `0 ≤ rel < len(t)`). Pick `t[rel]` by a bounded `Int`-equality mux over
        // `t`'s `≤ mt` source slots, gated by `rel < len(t)` (truncate overhang).
        let jconst = arena.int_const(i128::from(j));
        let rel = arena.int_sub(jconst, i)?;
        let mut t_elem = arena.bv_const(ew, 0)?;
        let mut from_t = arena.bool_const(false);
        for k in 0..mt {
            let kconst = arena.int_const(i128::from(k));
            let is_k = arena.eq(rel, kconst)?;
            let kbv = arena.bv_const(len_width(mt), u128::from(k))?;
            let k_active = arena.bv_ult(kbv, tlen_field)?;
            let hit = arena.and(is_k, k_active)?;
            let ek = seq_elem_m(arena, t, k, mt, ew)?;
            t_elem = arena.ite(hit, ek, t_elem)?;
            from_t = arena.or(from_t, hit)?;
        }
        // This slot takes `t`'s element only when `i` is in bounds, `j` is within
        // `s`'s length (so the slot is real content, not padding), and `j` falls
        // in the replacement span `[i, i+len(t))` (`from_t`). Otherwise it keeps
        // `s[j]` (the slot's existing value, padding included).
        let jbv = arena.bv_const(lwm, u128::from(j))?;
        let j_active = arena.bv_ult(jbv, len_field)?;
        let take0 = arena.and(i_in_bounds, j_active)?;
        let take = arena.and(take0, from_t)?;
        let slot = arena.ite(take, t_elem, s_elem)?;
        out_elems.push(slot);
    }
    let mut content: Option<TermId> = None;
    for j in (0..m as usize).rev() {
        let e = out_elems[j];
        content = Some(match content {
            None => e,
            Some(acc) => arena.concat(acc, e)?,
        });
    }
    let content = content.expect("m ≥ 1");
    // Length is unchanged by update.
    arena.concat(content, len_field).map_err(SmtError::Ir)
}

/// `(seq.update s i t)` for a **constant** index `iv`, encoded in pure BV (no
/// `bv2nat`/integer bridge) so a ground update stays bit-blastable. The index is
/// resolved against the literal directly: `iv < 0` or `iv ≥ m` (≥ the max length,
/// hence ≥ `len(s)`) is the no-op (return `s`); otherwise each affected output
/// slot `j ∈ [iv, iv+len(t))` (with `j < m`) takes `t[j−iv]` exactly when `iv` is
/// truly in bounds (`iv < len(s)`), the slot is real content (`j < len(s)`), and
/// `t`'s source slot is present (`j−iv < len(t)`) — all decided in BV. Slots
/// outside the span keep `s[j]`. Length and padding are `s`'s, copied verbatim.
fn seq_update_const(
    arena: &mut TermArena,
    s: TermId,
    t: TermId,
    iv: i128,
    ew: u32,
    m: u32,
    mt: u32,
) -> Result<TermId, SmtError> {
    // Out of bounds for **every** possible `len(s) ≤ m`: a no-op. (`iv ≥ m ⇒ iv ≥
    // len(s)`; `iv < 0` is the negative-index no-op.)
    if iv < 0 || iv >= i128::from(m) {
        return Ok(s);
    }
    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    let iu = iv as u32; // 0 ≤ iv < m, fits.
    let lwm = len_width(m);
    let len_field = seq_len_field(arena, s, m)?;
    // `iv < len(s)` (truly in bounds): a BV comparison against the literal `iv`.
    let iv_bv = arena.bv_const(lwm, u128::from(iu))?;
    let i_in_bounds = arena.bv_ult(iv_bv, len_field)?;
    let tlen_field = seq_len_field(arena, t, mt)?;
    let mut content: Option<TermId> = None;
    for j in (0..m).rev() {
        let s_elem = seq_elem_m(arena, s, j, m, ew)?;
        let out = if j >= iu && (j - iu) < mt {
            // `j` is inside the span `[iv, iv+mt)` and reads `t`'s slot `k = j−iv`.
            let k = j - iu;
            let t_elem = seq_elem_m(arena, t, k, mt, ew)?;
            // The slot takes `t[k]` only when `iv` is in bounds, `j` is below
            // `len(s)` (real content), and `k` is below `len(t)` (`t` has that
            // element — truncates any overhang). All three in BV.
            let jbv = arena.bv_const(lwm, u128::from(j))?;
            let j_active = arena.bv_ult(jbv, len_field)?;
            let kbv = arena.bv_const(len_width(mt), u128::from(k))?;
            let k_active = arena.bv_ult(kbv, tlen_field)?;
            let take0 = arena.and(i_in_bounds, j_active)?;
            let take = arena.and(take0, k_active)?;
            arena.ite(take, t_elem, s_elem)?
        } else {
            // Outside the replacement span: keep `s`'s slot verbatim.
            s_elem
        };
        content = Some(match content {
            None => out,
            Some(acc) => arena.concat(acc, out)?,
        });
    }
    let content = content.expect("m ≥ 1");
    arena.concat(content, len_field).map_err(SmtError::Ir)
}

/// Selects content element at an **`Int`** index `i` of a packed sequence `s`
/// (max length `m`, element width `ew`): returns `(elem, in_range)` with
/// `in_range` exactly when `0 ≤ i < len(s)` (else `(0, false)`). The sequence
/// analogue of [`string_byte_at_int`] — an `Int`-equality mux over the `≤ m`
/// slots gated by the length field, so any out-of-bound `i` matches no slot.
fn seq_elem_at_int(
    arena: &mut TermArena,
    s: TermId,
    i: TermId,
    m: u32,
    ew: u32,
) -> Result<(TermId, TermId), SmtError> {
    let len_field = seq_len_field(arena, s, m)?;
    let mut elem = arena.bv_const(ew, 0)?;
    let mut in_range = arena.bool_const(false);
    for k in 0..m {
        let kconst = arena.int_const(i128::from(k));
        let is_k = arena.eq(i, kconst)?;
        let kbv = arena.bv_const(len_width(m), u128::from(k))?;
        let k_active = arena.bv_ult(kbv, len_field)?;
        let hit = arena.and(is_k, k_active)?;
        let ek = seq_elem_m(arena, s, k, m, ew)?;
        elem = arena.ite(hit, ek, elem)?;
        in_range = arena.or(in_range, hit)?;
    }
    Ok((elem, in_range))
}

/// The concrete length of a **ground** packed sequence `v` (max length `m`), or
/// `0` if `v` is symbolic (so a symbolic operand is treated as possibly empty —
/// the conservative bound). A `seq.unit`/`seq.++` construction is an `Op::Concat`
/// tree, *not* a folded `BvConst`, so we evaluate its length field with the empty
/// assignment: a ground term folds to a concrete length; anything referencing a
/// symbol returns `0` (conservative).
fn seq_const_len(arena: &mut TermArena, v: TermId, m: u32) -> u32 {
    let Ok(len_field) = seq_len_field(arena, v, m) else {
        return 0;
    };
    match axeyum_ir::eval(arena, len_field, &axeyum_ir::Assignment::new()) {
        Ok(axeyum_ir::Value::Bv { value, .. }) => u32::try_from(value).unwrap_or(0).min(m),
        _ => 0,
    }
}

/// `(seq.replace s a b)` — replace the **first leftmost** occurrence of the
/// sub-sequence `a` in `s` with `b` (SMT-LIB Sequences total function), the
/// element-wise analogue of [`string_replace`]. Corner cases verbatim: `a` not
/// occurring → `s` unchanged; `a` the **empty** sequence → `b ++ s` (`b`
/// prepended); result length `len(s) − len(a) + len(b)` when found.
///
/// Encoding: identical to [`string_replace`] over `ew`-bit elements instead of
/// bytes — a bounded first-match mux (`match(p)` aligns `a` at `p` with `p +
/// len(a) ≤ len(s)`) feeding a byte-wise (here element-wise) splice keyed by the
/// symbolic boundaries `P` and `P + len(b)`. Sound for literal or symbolic
/// `a`/`b`. The result max length is `rm = m_s + m_b`; if `rm` exceeds the
/// soft/total caps the op is **declined** (`Unsupported`), never truncated.
#[allow(clippy::too_many_lines, clippy::similar_names)]
fn seq_replace(
    arena: &mut TermArena,
    seq: &SeqInfo,
    s: TermId,
    a: TermId,
    b: TermId,
) -> Result<TermId, SmtError> {
    let (ews, ms) = seq_max_len(arena, seq, s)?;
    let (ewa, ma) = seq_max_len(arena, seq, a)?;
    let (ewb, mb) = seq_max_len(arena, seq, b)?;
    if ews != ewa || ews != ewb {
        return Err(SmtError::Unsupported(format!(
            "seq.replace over differing element widths (s={ews}, a={ewa}, b={ewb})"
        )));
    }
    let ew = ews;
    // Result max length: `max(m_s, m_s − len(a)_min + m_b)` (see `string_replace`).
    // A **constant** `a` (a `BvConst` packed sequence) pins `len(a)_min` to its
    // exact length, tightening the bound; a symbolic `a` can be empty (prepend),
    // so `len(a)_min = 0`.
    let a_const_len = seq_const_len(arena, a, ma);
    let rm = ms.max(ms.saturating_sub(a_const_len) + mb);
    if rm > SEQ_LEN_SOFT_CAP || seq_total(ew, rm) > SEQ_TOTAL_BITS_CAP {
        return Err(SmtError::Unsupported(format!(
            "seq.replace result of bounded max length {rm} (over {ew}-bit elements) exceeds the \
             packed-sequence bound (ADR-0029)"
        )));
    }
    let len_s_f = seq_len_field(arena, s, ms)?;
    let len_a_f = seq_len_field(arena, a, ma)?;
    let len_b_f = seq_len_field(arena, b, mb)?;
    let len_s = arena.bv2nat(len_s_f)?;
    let len_a = arena.bv2nat(len_a_f)?;
    let len_b = arena.bv2nat(len_b_f)?;
    let zero = arena.bv_const(ew, 0)?;

    // `match(p)`: `a` fits at `p` (`p + len(a) ≤ len(s)`) and aligns element-wise.
    let match_at = |arena: &mut TermArena, p: u32| -> Result<TermId, SmtError> {
        let pconst = arena.int_const(i128::from(p));
        let p_plus_la = arena.int_add(pconst, len_a)?;
        let mut fits = arena.int_le(p_plus_la, len_s)?;
        for j in 0..ma {
            let jconst = arena.int_const(i128::from(j));
            let j_lt_la = arena.int_lt(jconst, len_a)?;
            let src = arena.int_add(pconst, jconst)?;
            let (selem, _sin) = seq_elem_at_int(arena, s, src, ms, ew)?;
            let aelem = seq_elem_m(arena, a, j, ma, ew)?;
            let eeq = arena.eq(selem, aelem)?;
            let nj = arena.not(j_lt_la)?;
            let ok = arena.or(nj, eeq)?;
            fits = arena.and(fits, ok)?;
        }
        Ok(fits)
    };

    let mut found = arena.bool_const(false);
    let mut pos_i = arena.int_const(0);
    let mut none_before = arena.bool_const(true);
    for p in 0..=ms {
        let mp = match_at(arena, p)?;
        let first_p = arena.and(none_before, mp)?;
        let pconst = arena.int_const(i128::from(p));
        pos_i = arena.ite(first_p, pconst, pos_i)?;
        found = arena.or(found, first_p)?;
        let nmp = arena.not(mp)?;
        none_before = arena.and(none_before, nmp)?;
    }

    let found_len0 = arena.int_sub(len_s, len_a)?;
    let found_len = arena.int_add(found_len0, len_b)?;
    let result_len = arena.ite(found, found_len, len_s)?;

    let mut content: Option<TermId> = None;
    for o in (0..rm).rev() {
        let oconst = arena.int_const(i128::from(o));
        let (s_o, _s_o_in) = seq_elem_at_int(arena, s, oconst, ms, ew)?;
        let o_lt_p = arena.int_lt(oconst, pos_i)?;
        let p_plus_lb = arena.int_add(pos_i, len_b)?;
        let o_lt_p_lb = arena.int_lt(oconst, p_plus_lb)?;
        let o_minus_p = arena.int_sub(oconst, pos_i)?;
        let (b_elem, _b_in) = seq_elem_at_int(arena, b, o_minus_p, mb, ew)?;
        let tail_idx0 = arena.int_sub(oconst, len_b)?;
        let tail_idx = arena.int_add(tail_idx0, len_a)?;
        let (tail_elem, _t_in) = seq_elem_at_int(arena, s, tail_idx, ms, ew)?;
        let mid_or_tail = arena.ite(o_lt_p_lb, b_elem, tail_elem)?;
        let found_elem = arena.ite(o_lt_p, s_o, mid_or_tail)?;
        let o_lt_len = arena.int_lt(oconst, result_len)?;
        let chosen = arena.ite(found, found_elem, s_o)?;
        let out_elem = arena.ite(o_lt_len, chosen, zero)?;
        content = Some(match content {
            None => out_elem,
            Some(acc) => arena.concat(acc, out_elem)?,
        });
    }
    let content = content.expect("rm ≥ 1");
    let rlen = arena.int2bv(len_width(rm), result_len)?;
    arena.concat(content, rlen).map_err(SmtError::Ir)
}

/// `(seq.indexof s t i)` — the position of the **first** occurrence of the
/// sub-sequence `t` in `s` at or after offset `i`, or `-1` if none (SMT-LIB
/// Sequences total function; `Int` result), the element-wise analogue of
/// [`string_indexof`]. Corner cases verbatim: `i < 0` → `-1`; `i > len(s)` →
/// `-1`; `t = ε` (empty) → `i` when `0 ≤ i ≤ len(s)`; not found → `-1`. The
/// 2-argument form is offset `0`. Encoding: the first-match cascade of
/// [`seq_replace`]/[`string_indexof`] over `ew`-bit elements restricted to
/// eligible `p ≥ i`; a pure position search (no length-changing rebuild), sound
/// for literal or symbolic `s`/`t`/`i`.
#[allow(clippy::similar_names)]
fn seq_indexof(
    arena: &mut TermArena,
    seq: &SeqInfo,
    s: TermId,
    t: TermId,
    i: TermId,
) -> Result<TermId, SmtError> {
    let (ews, ms) = seq_max_len(arena, seq, s)?;
    let (ewt, mt) = seq_max_len(arena, seq, t)?;
    if ews != ewt {
        return Err(SmtError::Unsupported(format!(
            "seq.indexof over differing element widths (s={ews}, t={ewt})"
        )));
    }
    let ew = ews;
    let len_s_f = seq_len_field(arena, s, ms)?;
    let len_t_f = seq_len_field(arena, t, mt)?;
    let len_s = arena.bv2nat(len_s_f)?;
    let len_t = arena.bv2nat(len_t_f)?;

    let match_at = |arena: &mut TermArena, p: u32| -> Result<TermId, SmtError> {
        let pconst = arena.int_const(i128::from(p));
        let p_plus_lt = arena.int_add(pconst, len_t)?;
        let mut fits = arena.int_le(p_plus_lt, len_s)?; // p + len(t) ≤ len(s)
        for j in 0..mt {
            let jconst = arena.int_const(i128::from(j));
            let j_lt_lt = arena.int_lt(jconst, len_t)?;
            let src = arena.int_add(pconst, jconst)?;
            let (selem, _sin) = seq_elem_at_int(arena, s, src, ms, ew)?;
            let telem = seq_elem_m(arena, t, j, mt, ew)?;
            let eeq = arena.eq(selem, telem)?;
            let nj = arena.not(j_lt_lt)?;
            let ok = arena.or(nj, eeq)?;
            fits = arena.and(fits, ok)?;
        }
        Ok(fits)
    };

    let mut found = arena.bool_const(false);
    let mut pos_i = arena.int_const(0);
    let mut none_before = arena.bool_const(true);
    for p in 0..=ms {
        let pconst = arena.int_const(i128::from(p));
        let p_ge_i = arena.int_le(i, pconst)?; // p ≥ i
        let mp = match_at(arena, p)?;
        let eligible = arena.and(p_ge_i, mp)?;
        let first_p = arena.and(none_before, eligible)?;
        pos_i = arena.ite(first_p, pconst, pos_i)?;
        found = arena.or(found, first_p)?;
        let neli = arena.not(eligible)?;
        none_before = arena.and(none_before, neli)?;
    }

    let zero = arena.int_const(0);
    let i_ge_0 = arena.int_le(zero, i)?; // i < 0 ⇒ -1
    let valid = arena.and(found, i_ge_0)?;
    let neg_one = arena.int_const(-1);
    arena.ite(valid, pos_i, neg_one).map_err(SmtError::Ir)
}

/// The concrete element list of a **ground** packed sequence `v` (max length `m`,
/// element width `ew`), or `None` if `v` is symbolic. Evaluates the length field
/// and each content element under the empty assignment: a `seq.unit`/`seq.++`
/// tree (an `Op::Concat`, not a folded `BvConst`) folds to concrete values;
/// anything referencing a symbol returns `None` (the caller declines).
fn seq_const_elems(arena: &mut TermArena, v: TermId, m: u32, ew: u32) -> Option<Vec<u128>> {
    let len_field = seq_len_field(arena, v, m).ok()?;
    let asg = axeyum_ir::Assignment::new();
    let len = match axeyum_ir::eval(arena, len_field, &asg) {
        Ok(axeyum_ir::Value::Bv { value, .. }) => u32::try_from(value).ok()?.min(m),
        _ => return None,
    };
    let mut elems = Vec::with_capacity(len as usize);
    for k in 0..len {
        let elem = seq_elem_m(arena, v, k, m, ew).ok()?;
        match axeyum_ir::eval(arena, elem, &asg) {
            Ok(axeyum_ir::Value::Bv { value, .. }) => elems.push(value),
            _ => return None,
        }
    }
    Some(elems)
}

/// Packs a concrete element list into the canonical packed-sequence `BvConst`
/// (max length `m`, element width `ew`): length in the low `len_width(m)` bits,
/// elements above it, padding zero — the same layout `seq_unit`/`seq.++` produce.
fn seq_pack_const(
    arena: &mut TermArena,
    elems: &[u128],
    m: u32,
    ew: u32,
) -> Result<TermId, SmtError> {
    let lwm = len_width(m);
    let mut packed = u128::from(u32::try_from(elems.len()).unwrap_or(0));
    let mask = if ew >= 128 {
        u128::MAX
    } else {
        (1u128 << ew) - 1
    };
    for (k, &e) in elems.iter().enumerate() {
        let shift = lwm + u32::try_from(k).expect("len ≤ m") * ew;
        packed |= (e & mask) << shift;
    }
    arena
        .bv_const(seq_total(ew, m), packed)
        .map_err(SmtError::Ir)
}

/// `(seq.replace_all s a b)` — replace **all** non-overlapping, left-to-right
/// occurrences of the sub-sequence `a` in `s` with `b` (SMT-LIB Sequences total
/// function), the element-wise analogue of [`string_replace_all`]. Corner cases
/// verbatim: `a = ε` → `s` unchanged (empty-pattern `replace_all` is the identity,
/// unlike single `seq.replace`); not found → `s`; matches consumed left-to-right,
/// the scan resuming **after** each inserted `b`.
///
/// This slice wires the **fully-ground** case exactly (all of `s`, `a`, `b` are
/// packed constants) by folding the replacement and re-packing the literal; the
/// result must still fit the max length `m` for the element width (an over-bound
/// ground result declines). A symbolic operand is **declined** (`Unsupported` →
/// `unknown`), never truncated.
#[allow(clippy::similar_names)]
fn seq_replace_all(
    arena: &mut TermArena,
    seq: &SeqInfo,
    s: TermId,
    a: TermId,
    b: TermId,
) -> Result<TermId, SmtError> {
    let (ews, ms) = seq_max_len(arena, seq, s)?;
    let (ewa, ma) = seq_max_len(arena, seq, a)?;
    let (ewb, mb) = seq_max_len(arena, seq, b)?;
    if ews != ewa || ews != ewb {
        return Err(SmtError::Unsupported(format!(
            "seq.replace_all over differing element widths (s={ews}, a={ewa}, b={ewb})"
        )));
    }
    let ew = ews;
    let (Some(sv), Some(av), Some(bv)) = (
        seq_const_elems(arena, s, ms, ew),
        seq_const_elems(arena, a, ma, ew),
        seq_const_elems(arena, b, mb, ew),
    ) else {
        return Err(SmtError::Unsupported(
            "seq.replace_all over a non-constant operand is outside the wired sound subset \
             (a symbolic moving-cursor splice is bounded only for a concrete len(a); ADR-0029)"
                .to_owned(),
        ));
    };
    // `a = ε` is the identity (empty-pattern replace_all leaves `s` unchanged).
    if av.is_empty() {
        return seq_pack_const(arena, &sv, ms, ew);
    }
    let mut out: Vec<u128> = Vec::new();
    let mut k = 0usize;
    while k < sv.len() {
        if k + av.len() <= sv.len() && sv[k..k + av.len()] == av[..] {
            out.extend_from_slice(&bv);
            k += av.len();
        } else {
            out.push(sv[k]);
            k += 1;
        }
    }
    if u32::try_from(out.len()).unwrap_or(u32::MAX) > ms {
        return Err(SmtError::Unsupported(format!(
            "seq.replace_all ground result of length {} exceeds the packed max length {ms} \
             (ADR-0029)",
            out.len()
        )));
    }
    seq_pack_const(arena, &out, ms, ew)
}

/// Coerces a `seq.unit` element argument to a `BitVec(ew)`: an `Int` element is
/// `int2bv`-narrowed to the bounded width (its low `ew` bits, two's-complement),
/// a `Bool` element becomes a 1-bit value, and a `BitVec(ew)` passes through.
/// A symbolic `Int` additionally records the signed-range guard that makes the
/// narrowing injective for every admitted SAT model; the bounded-UNSAT gate
/// removes that guard from its source-theory abstraction. An element of any
/// other shape (or a mismatched BV width) is declined.
fn seq_coerce_elem(
    arena: &mut TermArena,
    lenabs: &LenAbs,
    e: TermId,
    ew: u32,
) -> Result<TermId, SmtError> {
    match arena.sort_of(e) {
        Sort::BitVec(w) if w == ew => Ok(e),
        Sort::Int => {
            // An `Int` **literal** outside the signed `ew`-bit range is declined
            // (never silently wrapped into a wrong value, which could alias a
            // distinct element and force a wrong `unsat`).
            if let TermNode::IntConst(v) = arena.node(e) {
                let v = *v;
                let lo = -(1i128 << (ew - 1));
                let hi = (1i128 << (ew - 1)) - 1;
                if v < lo || v > hi {
                    return Err(SmtError::Unsupported(format!(
                        "sequence Int element literal {v} is outside the signed {ew}-bit range \
                        (ADR-0029)"
                    )));
                }
            } else {
                // `int2bv` is periodic outside this signed window. Without the
                // guard, distinct mathematical integers such as `0` and `65536`
                // become the same sequence element and can fabricate SAT for an
                // actually-UNSAT source formula. Restrict the bounded SAT search
                // to the injective window; StringGate removes this restriction
                // before certifying any UNSAT.
                let lo = arena.int_const(-(1i128 << (ew - 1)));
                let hi = arena.int_const((1i128 << (ew - 1)) - 1);
                let lower = arena.int_le(lo, e)?;
                let upper = arena.int_le(e, hi)?;
                let guard = arena.and(lower, upper)?;
                lenabs.note_encoding_guard(arena, guard);
            }
            arena.int2bv(ew, e).map_err(SmtError::Ir)
        }
        Sort::Bool if ew == 1 => {
            let one = arena.bv_const(1, 1)?;
            let zero = arena.bv_const(1, 0)?;
            arena.ite(e, one, zero).map_err(SmtError::Ir)
        }
        s => Err(SmtError::Unsupported(format!(
            "seq.unit element of sort {s:?} cannot be packed into a {ew}-bit element"
        ))),
    }
}

/// Dispatches a `seq.*` operator over its packed-sequence/element arguments.
/// Returns `None` if `op` is not a sequence operator (so the caller continues its
/// normal dispatch). A modeled-but-unsound corner declines via `Err(Unsupported)`.
#[allow(clippy::too_many_lines)]
fn apply_seq_op(
    arena: &mut TermArena,
    seq: &SeqInfo,
    lenabs: &LenAbs,
    op: &str,
    args: &[TermId],
) -> Result<Option<TermId>, SmtError> {
    // P2.7 A.2: any `seq.*` operator marks the bounded encoding as used.
    if op.starts_with("seq.") {
        lenabs.mark_used();
    }
    let need = |k: usize| -> Result<(), SmtError> {
        if args.len() == k {
            Ok(())
        } else {
            Err(SmtError::Syntax(format!("`{op}` expects {k} arguments")))
        }
    };
    let term = match op {
        "seq.len" => {
            need(1)?;
            let r = seq_len(arena, seq, args[0])?;
            // P2.7 A.2: bridge to the shared unbounded length expression.
            lenabs.mark_used();
            let e = lenabs.len_expr_seq(arena, args[0])?;
            lenabs.note_repl(r, e);
            r
        }
        "seq.++" | "seq.concat" => {
            let r = seq_concat(arena, seq, args)?;
            // P2.7 A.2: `len(x ++ y) = len(x) + len(y)` in the abstraction.
            lenabs.mark_used();
            let mut sum = lenabs.len_expr_seq(arena, args[0])?;
            for &a in &args[1..] {
                let e = lenabs.len_expr_seq(arena, a)?;
                sum = arena.int_add(sum, e)?;
            }
            lenabs.note_len(r, sum);
            r
        }
        "seq.unit" => {
            need(1)?;
            // The element type is not recoverable from the element alone (an `Int`
            // element is just `Int`). Use the script's sole sequence element width
            // (the common case); a script mixing element widths declines cleanly.
            let ew = seq.sole_elem_width().ok_or_else(|| {
                SmtError::Unsupported(
                    "seq.unit element width is not determined (the script declares no \
                     single sequence element type); ADR-0029"
                        .to_owned(),
                )
            })?;
            let elem = seq_coerce_elem(arena, lenabs, args[0], ew)?;
            let r = seq_unit(arena, elem)?;
            lenabs.mark_used();
            let one = arena.int_const(1);
            lenabs.note_len(r, one);
            r
        }
        "seq.extract" => {
            need(3)?;
            seq_extract(arena, seq, args[0], args[1], args[2])?
        }
        "seq.prefixof" => {
            need(2)?;
            let atom = seq_prefixof(arena, seq, args[0], args[1])?;
            lenabs.mark_used();
            let lx = lenabs.len_expr_seq(arena, args[0])?;
            let ly = lenabs.len_expr_seq(arena, args[1])?;
            let fact = arena.int_le(lx, ly)?;
            lenabs.note_atom_fact(arena, atom, fact)?;
            atom
        }
        "seq.suffixof" => {
            need(2)?;
            let atom = seq_suffixof(arena, seq, args[0], args[1])?;
            lenabs.mark_used();
            let lx = lenabs.len_expr_seq(arena, args[0])?;
            let ly = lenabs.len_expr_seq(arena, args[1])?;
            let fact = arena.int_le(lx, ly)?;
            lenabs.note_atom_fact(arena, atom, fact)?;
            atom
        }
        "seq.contains" => {
            need(2)?;
            let atom = seq_contains(arena, seq, args[0], args[1])?;
            lenabs.mark_used();
            let ly = lenabs.len_expr_seq(arena, args[1])?;
            let lx = lenabs.len_expr_seq(arena, args[0])?;
            let fact = arena.int_le(ly, lx)?;
            lenabs.note_atom_fact(arena, atom, fact)?;
            atom
        }
        // `(seq.nth s i)` — the `i`-th element, the SMT-LIB **partial** function:
        // in-bounds the element, out-of-bounds a fresh *unconstrained* value with
        // eager congruence (slice 2). Zero-padding here would force a wrong
        // `unsat`, so the out-of-bounds case is modeled, not faked.
        "seq.nth" => {
            need(2)?;
            let r = seq_nth(arena, seq, args[0], args[1])?;
            if arena.sort_of(r) == Sort::Int {
                lenabs.note_bridge_free(arena, r)?;
            } else {
                lenabs.mark_used();
            }
            r
        }
        // `(seq.at s i)` — the **total** unit-sub-sequence at `i` (empty when
        // out-of-bounds); mirrors `str.at` (slice 2).
        "seq.at" => {
            need(2)?;
            seq_at(arena, seq, args[0], args[1])?
        }
        // `(seq.update s i t)` — `s` with the span at `i` overwritten by `t`,
        // truncated to fit (length unchanged); out-of-bounds `i` is a no-op. A
        // total function with no unconstrained-OOB subtlety (slice 3).
        "seq.update" => {
            need(3)?;
            seq_update(arena, seq, args[0], args[1], args[2])?
        }
        // `(seq.rev s)` — the total reversal of `s` (length unchanged), a
        // permutation of the present elements (slice 3).
        "seq.rev" => {
            need(1)?;
            seq_rev(arena, seq, args[0])?
        }
        // `(seq.replace s a b)` — replace the FIRST occurrence of `a` in `s` with
        // `b` (first leftmost; `a` empty → prepend; not found → `s`); a bounded
        // match + element-wise splice, sound for literal or symbolic `a`/`b`,
        // declined when the result could exceed the cap (ADR-0029 slice 4).
        "seq.replace" => {
            need(3)?;
            seq_replace(arena, seq, args[0], args[1], args[2])?
        }
        // `(seq.indexof s t i)` / `(seq.indexof s t)` — the position of the FIRST
        // occurrence of `t` in `s` at-or-after offset `i` (0 in the 2-arg form),
        // else `-1`. A pure first-match position search over the packed elements,
        // the `Int` result composing with arithmetic; sound for literal or symbolic
        // operands (ADR-0029 slice 5).
        "seq.indexof" => {
            if args.len() == 2 {
                let zero = arena.int_const(0);
                seq_indexof(arena, seq, args[0], args[1], zero)?
            } else {
                need(3)?;
                seq_indexof(arena, seq, args[0], args[1], args[2])?
            }
        }
        // `(seq.replace_all s a b)` — replace ALL non-overlapping occurrences of
        // `a` with `b` (`a = ε` is the identity; not found → `s`). Wired for the
        // ground case; symbolic operands decline cleanly (ADR-0029 slice 5).
        "seq.replace_all" => {
            need(3)?;
            seq_replace_all(arena, seq, args[0], args[1], args[2])?
        }
        // Declined: the remaining partial-`nth` total variant.
        "seq.nth_total" => {
            return Err(SmtError::Unsupported(format!(
                "sequence operator `{op}` is outside the wired sound subset (ADR-0029)"
            )));
        }
        _ => return Ok(None),
    };
    Ok(Some(term))
}

const MAX_EQRANGE_POINTS: i128 = 1024;

fn constant_int_value(arena: &TermArena, term: TermId) -> Option<i128> {
    match arena.node(term) {
        TermNode::IntConst(value) => Some(*value),
        TermNode::App { op, args } => match (*op, args.as_ref()) {
            (Op::IntNeg, [a]) => constant_int_value(arena, *a)?.checked_neg(),
            (Op::IntAdd, [a, b]) => {
                constant_int_value(arena, *a)?.checked_add(constant_int_value(arena, *b)?)
            }
            (Op::IntSub, [a, b]) => {
                constant_int_value(arena, *a)?.checked_sub(constant_int_value(arena, *b)?)
            }
            (Op::IntMul, [a, b]) => {
                constant_int_value(arena, *a)?.checked_mul(constant_int_value(arena, *b)?)
            }
            _ => None,
        },
        _ => None,
    }
}

fn constant_int_bound(arena: &TermArena, term: TermId, context: &str) -> Result<i128, SmtError> {
    match constant_int_value(arena, term) {
        Some(value) => Ok(value),
        _ => Err(SmtError::Unsupported(format!(
            "{context} requires constant integer bounds"
        ))),
    }
}

fn array_eqrange(
    arena: &mut TermArena,
    array_a: TermId,
    array_b: TermId,
    lo: TermId,
    hi: TermId,
) -> Result<TermId, SmtError> {
    let sort_a = arena.sort_of(array_a);
    let sort_b = arena.sort_of(array_b);
    let Sort::Array { index, element } = sort_a else {
        return Err(SmtError::Unsupported(format!(
            "eqrange expects array operands, got {sort_a:?}"
        )));
    };
    if sort_b != sort_a {
        return Err(SmtError::Unsupported(format!(
            "eqrange expects matching array operands, got {sort_a:?} and {sort_b:?}"
        )));
    }
    if index != ArraySortKey::Int {
        return Err(SmtError::Unsupported(format!(
            "eqrange currently supports only Int-indexed arrays, got {index:?}"
        )));
    }

    let lo = constant_int_bound(arena, lo, "eqrange")?;
    let hi = constant_int_bound(arena, hi, "eqrange")?;
    if lo > hi {
        return Ok(arena.bool_const(true));
    }
    let points = hi
        .checked_sub(lo)
        .and_then(|delta| delta.checked_add(1))
        .ok_or_else(|| SmtError::Unsupported("eqrange bound span overflows".to_owned()))?;
    if points > MAX_EQRANGE_POINTS {
        return Err(SmtError::Unsupported(format!(
            "eqrange finite expansion is capped at {MAX_EQRANGE_POINTS} points, got {points}"
        )));
    }

    let mut acc = arena.bool_const(true);
    for point in lo..=hi {
        let idx = arena.int_const(point);
        let lhs = arena.select(array_a, idx)?;
        let rhs = arena.select(array_b, idx)?;
        debug_assert_eq!(arena.sort_of(lhs), element.to_sort());
        let eq = arena.eq(lhs, rhs)?;
        acc = arena.and(acc, eq)?;
    }
    Ok(acc)
}

fn self_store_array_equality(
    arena: &mut TermArena,
    lhs: TermId,
    rhs: TermId,
) -> Result<Option<TermId>, SmtError> {
    if let Some(term) = self_store_array_equality_direction(arena, lhs, rhs)? {
        return Ok(Some(term));
    }
    self_store_array_equality_direction(arena, rhs, lhs)
}

fn self_store_array_equality_direction(
    arena: &mut TermArena,
    target: TermId,
    store_chain: TermId,
) -> Result<Option<TermId>, SmtError> {
    if !matches!(
        arena.sort_of(target),
        Sort::Array {
            index: ArraySortKey::Int,
            ..
        }
    ) {
        return Ok(None);
    }

    let mut current = store_chain;
    let mut reversed_writes = Vec::new();
    while let TermNode::App {
        op: Op::Store,
        args,
    } = arena.node(current)
    {
        reversed_writes.push((args[1], args[2]));
        current = args[0];
    }
    if current != target || reversed_writes.is_empty() {
        return Ok(None);
    }

    let mut final_writes = BTreeMap::new();
    for (index, value) in reversed_writes.into_iter().rev() {
        let Some(point) = constant_int_value(arena, index) else {
            return Ok(None);
        };
        final_writes.insert(point, (index, value));
    }

    let mut acc = arena.bool_const(true);
    for (_point, (index, value)) in final_writes {
        let selected = arena.select(target, index)?;
        let eq = arena.eq(selected, value)?;
        acc = arena.and(acc, eq)?;
    }
    Ok(Some(acc))
}

/// Applies an operator list head to evaluated arguments.
// Flat dispatch over the operator vocabulary; length is inherent.
#[allow(clippy::too_many_lines)]
fn apply_op(
    arena: &mut TermArena,
    seq: &SeqInfo,
    ff: &FfInfo,
    lenabs: &LenAbs,
    items: &[SExpr],
    args: &[TermId],
) -> Result<TermId, SmtError> {
    // Parameterized head: ((_ extract h l) x) etc.
    if let Some(head_items) = items[0].list() {
        return apply_parameterized(arena, head_items, args);
    }
    let op = items[0].atom().expect("list head checked");
    // Bounded finite-sequence operators (`seq.*`, ADR-0029): dispatched only when
    // the script declares a sequence sort (else `seq` is empty and this returns
    // `None`, leaving the normal dispatch untouched).
    if !seq.is_empty()
        && let Some(t) = apply_seq_op(arena, seq, lenabs, op, args)?
    {
        return Ok(t);
    }
    // Finite-field operators (`ff.*`, QF_FF): dispatched only when the script
    // declares a finite-field sort (else `ff` is empty and this returns `None`,
    // leaving the normal dispatch untouched).
    if !ff.is_empty()
        && let Some(t) = apply_ff_op(arena, ff, op, args)?
    {
        return Ok(t);
    }
    let need = |n: usize| -> Result<(), SmtError> {
        if args.len() == n {
            Ok(())
        } else {
            Err(SmtError::Syntax(format!(
                "`{op}` expects {n} arguments, got {}",
                args.len()
            )))
        }
    };
    let fold = |arena: &mut TermArena,
                f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>|
     -> Result<TermId, SmtError> {
        if args.len() < 2 {
            return Err(SmtError::Syntax(format!("`{op}` expects >= 2 arguments")));
        }
        let mut acc = args[0];
        for &next in &args[1..] {
            acc = f(arena, acc, next)?;
        }
        Ok(acc)
    };
    // P2.7 A.2: any `str.*` operator marks the script as using the bounded
    // string encoding, activating the bounded-`unsat` confirmation gate — the
    // ops without dedicated abstraction hooks (substr, replace, at, …) must
    // still flag the bound.
    if op.starts_with("str.") {
        lenabs.mark_used();
    }
    Ok(match op {
        "not" => {
            need(1)?;
            match arena.node(args[0]) {
                TermNode::BoolConst(value) => arena.bool_const(!value),
                _ => arena.not(args[0])?,
            }
        }
        // `str.len` over a packed bounded string (ADR-0029): the length field as
        // an `Int`, so it composes with the existing integer arithmetic
        // (`(>= (str.len s) 3)`, `(= (str.len s) 0)`, …).
        "str.len" => {
            need(1)?;
            let m = string_max_len(arena, args[0])?;
            let len = string_len_field(arena, args[0], m)?;
            let r = arena.bv2nat(len)?;
            // P2.7 A.2: the Int-valued bridge maps to the shared *unbounded*
            // length expression of its operand in the length abstraction.
            lenabs.mark_used();
            let e = lenabs.len_expr_string(arena, args[0])?;
            lenabs.note_repl(r, e);
            r
        }
        // `str.prefixof x y` — pure BV/Bool over packed strings; decides both
        // directions (no Int bridge, no theory-combination gap).
        "str.prefixof" => {
            need(2)?;
            let atom = string_prefixof(arena, args[0], args[1])?;
            // P2.7 A.2: `prefixof(x, y) ⟹ len(x) ≤ len(y)` (unbounded).
            lenabs.mark_used();
            let lx = lenabs.len_expr_string(arena, args[0])?;
            let ly = lenabs.len_expr_string(arena, args[1])?;
            let fact = arena.int_le(lx, ly)?;
            lenabs.note_atom_fact(arena, atom, fact)?;
            atom
        }
        // `str.contains x y` — y occurs in x; pure BV/Bool, decides both directions.
        "str.contains" => {
            need(2)?;
            let atom = string_contains(arena, args[0], args[1])?;
            // P2.7 A.2: `contains(x, y) ⟹ len(y) ≤ len(x)` (unbounded).
            lenabs.mark_used();
            let ly = lenabs.len_expr_string(arena, args[1])?;
            let lx = lenabs.len_expr_string(arena, args[0])?;
            let fact = arena.int_le(ly, lx)?;
            lenabs.note_atom_fact(arena, atom, fact)?;
            atom
        }
        "str.suffixof" => {
            need(2)?;
            let atom = string_suffixof(arena, args[0], args[1])?;
            // P2.7 A.2: `suffixof(x, y) ⟹ len(x) ≤ len(y)` (unbounded).
            lenabs.mark_used();
            let lx = lenabs.len_expr_string(arena, args[0])?;
            let ly = lenabs.len_expr_string(arena, args[1])?;
            let fact = arena.int_le(lx, ly)?;
            lenabs.note_atom_fact(arena, atom, fact)?;
            atom
        }
        // `str.at s k` — a constant index folds directly; a non-constant `Int`
        // index is an Int-equality mux over the ≤`m` positions (ADR-0029 slice 3).
        // Returns a length-≤1 packed string.
        "str.at" => {
            need(2)?;
            let r = match ground_int_term(arena, args[1]) {
                Some(index) => string_at_const(arena, args[0], index)?,
                None => string_at_int(arena, args[0], args[1])?,
            };
            // P2.7 A.2: `len(str.at s k) ≤ 1` universally (empty when
            // out-of-bounds, one char otherwise).
            let lr = lenabs.len_expr_string(arena, r)?;
            let one = arena.int_const(1);
            let fact = arena.int_le(lr, one)?;
            lenabs.facts.borrow_mut().push(fact);
            r
        }
        // `str.substr s off n` — bounded substring, total function: "" unless
        // `0 ≤ off < |s|` and `n > 0`; else `s[off .. min(off+n,|s|)]`. The
        // `off`/`n` indices may be arbitrary `Int`s (ADR-0029 slice 3).
        "str.substr" => {
            need(3)?;
            let off_const = ground_int_term(arena, args[1]);
            let count_const = ground_int_term(arena, args[2]);
            let suffix_drop =
                u32::try_from(parse_int_literal(strip_subtracted_zero(&items[2])).unwrap_or(-1))
                    .ok()
                    .filter(|&dropped| len_minus_constant(&items[3], &items[1]) == Some(dropped));
            let r = if let Some(dropped) = suffix_drop {
                match string_suffix_const(arena, args[0], dropped)? {
                    Some(result) => result,
                    None => string_substr(arena, args[0], args[1], args[2])?,
                }
            } else if off_const == Some(0) {
                match count_const.and_then(|count| u32::try_from(count).ok()) {
                    Some(count) if count > 0 && count < string_max_len(arena, args[0])? => {
                        string_prefix_const(arena, args[0], count)?
                    }
                    _ => string_substr(arena, args[0], args[1], args[2])?,
                }
            } else {
                string_substr(arena, args[0], args[1], args[2])?
            };
            let ls = lenabs.len_expr_string(arena, args[0])?;
            // With ground bounds, substring length has an exact unbounded-LIA
            // expression:
            //
            //   off < 0 or count <= 0  =>  0
            //   otherwise              =>  min(count, max(len(s) - off, 0))
            //
            // Recording the expression (instead of only `len(r) <= len(s)`)
            // lets StringGate refute generated fixed-slice length conflicts
            // independently of the packed-string bound. The relation is exact
            // SMT-LIB totality, so it is safe under negation and arbitrary
            // Boolean structure.
            if let (Some(off), Some(count)) = (off_const, count_const) {
                let zero = arena.int_const(0);
                let exact = if off < 0 || count <= 0 {
                    zero
                } else {
                    let off = arena.int_const(off);
                    let count = arena.int_const(count);
                    let starts_past_end = arena.int_le(ls, off)?;
                    let remaining = arena.int_sub(ls, off)?;
                    let truncated = arena.int_le(remaining, count)?;
                    let clipped = arena.ite(truncated, remaining, count)?;
                    arena.ite(starts_past_end, zero, clipped)?
                };
                lenabs.note_len(r, exact);
            } else if let Some(dropped) = suffix_drop {
                let zero = arena.int_const(0);
                let dropped = arena.int_const(i128::from(dropped));
                let starts_past_end = arena.int_le(ls, dropped)?;
                let remaining = arena.int_sub(ls, dropped)?;
                let exact = arena.ite(starts_past_end, zero, remaining)?;
                lenabs.note_len(r, exact);
            }
            // P2.7 A.2: a substring is never longer than its string —
            // universally true, so a pinned over-bound substring result trips
            // the bite detector instead of a bound-induced `unsat`.
            let lr = lenabs.len_expr_string(arena, r)?;
            let fact = arena.int_le(lr, ls)?;
            lenabs.facts.borrow_mut().push(fact);
            r
        }
        // `str.update s i t` — overwrite the `len(t)` bytes of `s` starting at index
        // `i` with `t` (clipped to `s`; index out of `[0, len(s))` leaves `s`
        // unchanged). A byte-wise splice over the packed layout; sound for literal or
        // symbolic operands (ADR-0029). Result length is always `len(s)`.
        "str.update" => {
            need(3)?;
            let r = string_update(arena, args[0], args[1], args[2])?;
            // P2.7 A.2: `len(update(s, i, t)) = len(s)` universally (an update never
            // changes the length) — a tighter equality than the substr/replace bounds.
            let lr = lenabs.len_expr_string(arena, r)?;
            let ls = lenabs.len_expr_string(arena, args[0])?;
            let fact = arena.eq(lr, ls)?;
            lenabs.facts.borrow_mut().push(fact);
            r
        }
        // `str.replace s a b` — replace the FIRST occurrence of `a` in `s` with
        // `b` (first leftmost; `a` empty → prepend `b`; not found → `s`). A
        // bounded match + byte-wise splice over the packed layout, sound for
        // literal or symbolic `a`/`b`; declined (Unsupported) when the result
        // could exceed the cap (ADR-0029 slice 4).
        "str.replace" => {
            need(3)?;
            let r = string_replace(arena, args[0], args[1], args[2])?;
            // P2.7 A.2: `len(replace(s, a, b)) ≤ len(s) + len(b)` universally
            // (first occurrence replaced, `a = ""` prepends `b`, else no-op).
            let lr = lenabs.len_expr_string(arena, r)?;
            let ls = lenabs.len_expr_string(arena, args[0])?;
            let lb = lenabs.len_expr_string(arena, args[2])?;
            let cap = arena.int_add(ls, lb)?;
            let fact = arena.int_le(lr, cap)?;
            lenabs.facts.borrow_mut().push(fact);
            r
        }
        // `(str.indexof s t i)` / `(str.indexof s t)` — the position of the FIRST
        // occurrence of `t` in `s` at-or-after offset `i` (offset 0 in the 2-arg
        // form), else `-1`. A pure first-match position search over the packed
        // layout, the `Int` result composing with arithmetic; sound for literal or
        // symbolic operands (ADR-0029 slice 5).
        "str.indexof" => {
            let r = if args.len() == 2 {
                let zero = arena.int_const(0);
                string_indexof(arena, args[0], args[1], zero)?
            } else {
                need(3)?;
                string_indexof(arena, args[0], args[1], args[2])?
            };
            lenabs.note_bridge_free(arena, r)?;
            r
        }
        // `(str.replace_all s a b)` — replace ALL non-overlapping occurrences of
        // `a` with `b` (`a = ""` is the identity; not found → `s`). Wired for the
        // ground case; symbolic operands decline cleanly (ADR-0029 slice 5).
        "str.replace_all" => {
            need(3)?;
            string_replace_all(arena, args[0], args[1], args[2])?
        }
        // `str.to_code s` — the code point of the single char of `s`, else `-1`
        // (an `Int`, composes with arithmetic). Byte model: code is `s[0]`
        // (0..=255) when `|s| = 1` (ADR-0029 slice 3).
        "str.to_code" => {
            need(1)?;
            let r = string_to_code(arena, args[0])?;
            // P2.7 A.2 (code↔LIA): a code-domain + length-coupled abstraction
            // (not a wholly-free bridge), so the unbounded abstraction refutes
            // the code-range / code-arithmetic conflicts.
            lenabs.note_code_bridge(arena, args[0], r)?;
            r
        }
        // `str.from_code i` — the length-1 byte string of code point `i` for a
        // constant `0 ≤ i ≤ 255` (exact, round-trips `str.to_code`), `""` for an
        // invalid code point (`i < 0` or `i > 0x2FFFF`), and a decline (Unknown)
        // for the valid-but-unrepresentable `256..=0x2FFFF` window or any symbolic
        // argument. The partial inverse of `str.to_code` (task #46).
        "str.from_code" => {
            need(1)?;
            let r = string_from_code(arena, args[0])?;
            // `len(str.from_code i) ≤ 1` universally.
            let lr = lenabs.len_expr_string(arena, r)?;
            let one = arena.int_const(1);
            let fact = arena.int_le(lr, one)?;
            lenabs.facts.borrow_mut().push(fact);
            r
        }
        // `str.<` / `str.<=` — lexicographic order over the packed bytes; pure
        // BV/Bool, decides both directions (ADR-0029 slice 3).
        "str.<" => {
            need(2)?;
            let atom = string_lt(arena, args[0], args[1])?;
            // No sound length implication from lexicographic order, but a
            // *symbolic* atom must still be relaxed to a free Boolean in the
            // abstraction (kept verbatim it would smuggle the encoding bound
            // back in). A ground atom (both operands literal) is exact at
            // every bound — keep it, don't mark the script coarse.
            if !(packed_const(arena, args[0]) && packed_const(arena, args[1])) {
                lenabs.note_atom_free(arena, atom)?;
            }
            atom
        }
        "str.<=" => {
            need(2)?;
            let atom = string_le(arena, args[0], args[1])?;
            if !(packed_const(arena, args[0]) && packed_const(arena, args[1])) {
                lenabs.note_atom_free(arena, atom)?;
            }
            atom
        }
        // `str.to_int s` — the decimal value of a non-empty all-ASCII-digit `s`,
        // else `-1` (SMT-LIB total function; leading zeros valid). A bounded Horner
        // fold over the packed bytes; the result is an `Int` (ADR-0029 slice 4).
        // An over-bound string literal (> STRING_MAX_LEN bytes) already declined at
        // pack time, so `string_to_int` only ever sees a representable operand.
        "str.to_int" => {
            need(1)?;
            let r = string_to_int(arena, args[0])?;
            lenabs.note_bridge_free(arena, r)?;
            r
        }
        // `str.from_int i` — the canonical decimal string of `i ≥ 0` (no leading
        // zeros, `0 → "0"`), else `""` for `i < 0` (SMT-LIB total function). A
        // **constant** argument folds exactly and declines (Unsupported) when the
        // decimal expansion needs more than FROM_INT_MAX_DIGITS bytes (over-bound,
        // never a wrong string). A symbolic argument builds the bounded packed
        // string, faithful for every model the bounded int bit-blast can produce
        // (ADR-0029 slice 4).
        "str.from_int" => {
            need(1)?;
            match arena.node(args[0]) {
                TermNode::IntConst(v) => string_from_int_const(arena, *v)?,
                _ => string_from_int(arena, args[0])?,
            }
        }
        // `str.++` — variable concatenation grows into a wider packed sort; a run
        // of constant operands folds to a literal (ADR-0029 slice 2).
        "str.concat" | "str.++" => {
            let r = if let Some(result_max) =
                proved_concat_bound(arena, items, args, lenabs.admit_split_replace_rejoin)
            {
                string_concat_with_proved_bound(arena, args, result_max)?
            } else {
                string_concat(arena, args)?
            };
            // P2.7 A.2: `len(x ++ y) = len(x) + len(y)` in the abstraction.
            lenabs.mark_used();
            let mut sum = lenabs.len_expr_string(arena, args[0])?;
            for &a in &args[1..] {
                let e = lenabs.len_expr_string(arena, a)?;
                sum = arena.int_add(sum, e)?;
            }
            lenabs.note_len(r, sum);
            r
        }
        // `(and x)` / `(or x)` with a single operand denote `x`: an n-ary
        // connective folded over one argument is that argument (the identity of
        // `∧`/`∨`). SMT-LIB's `:left-assoc` grammar nominally wants ≥2 operands,
        // but cvc5/Z3 both accept the unary form, so we mirror them. Zero or ≥2
        // operands keep the existing `fold` path (which rejects 0 and folds ≥2).
        "and" | "or" if args.len() == 1 => args[0],
        "and" => fold(arena, TermArena::and)?,
        "or" => fold(arena, TermArena::or)?,
        "xor" => fold(arena, TermArena::xor)?,
        "=>" => {
            // Right-associative.
            if args.len() < 2 {
                return Err(SmtError::Syntax("`=>` expects >= 2 arguments".to_owned()));
            }
            let mut acc = *args.last().expect("nonempty");
            for &prev in args[..args.len() - 1].iter().rev() {
                acc = arena.implies(prev, acc)?;
            }
            acc
        }
        "=" => {
            // n-ary chaining: pairwise equalities conjoined. Coerce integer
            // constants to `Real` when any operand is real (numeral coercion).
            if args.len() < 2 {
                return Err(SmtError::Syntax("`=` expects >= 2 arguments".to_owned()));
            }
            let eq_args = if args.iter().any(|&a| arena.sort_of(a) == Sort::Real) {
                numeric_args(arena, args)?.1
            } else {
                args.to_vec()
            };
            let eq_pair =
                |arena: &mut TermArena, p: TermId, q: TermId| -> Result<TermId, SmtError> {
                    if p == q {
                        return Ok(arena.bool_const(true));
                    }
                    if let Some(result) = int_ite_const_equality(arena, p, q)? {
                        return Ok(result);
                    }
                    if let Some(result) = int_ite_const_equality(arena, q, p)? {
                        return Ok(result);
                    }
                    // P2.7 A.2: `x = y ⟹ len(x) = len(y)` (unbounded). Sound
                    // even for a string-*shaped* user bit-vector (equal BVs have
                    // equal decoded fields), so this hook does not `mark_used`.
                    if let Some(e) = seq_aware_eq(arena, seq, p, q)? {
                        let lp = lenabs.len_expr_seq(arena, p)?;
                        let lq = lenabs.len_expr_seq(arena, q)?;
                        let fact = arena.eq(lp, lq)?;
                        lenabs.note_atom_fact(arena, e, fact)?;
                        return Ok(e);
                    }
                    if let Some(e) = string_aware_eq(arena, p, q)? {
                        string_eq_len_hook(arena, lenabs, e, p, q)?;
                        return Ok(e);
                    }
                    if let Some(e) = self_store_array_equality(arena, p, q)? {
                        return Ok(e);
                    }
                    let e = arena.eq(p, q).map_err(SmtError::Ir)?;
                    if string_shaped(arena, p) && string_shaped(arena, q) {
                        string_eq_len_hook(arena, lenabs, e, p, q)?;
                    }
                    Ok(e)
                };
            let mut acc = eq_pair(arena, eq_args[0], eq_args[1])?;
            for pair in eq_args.windows(2).skip(1) {
                let e = eq_pair(arena, pair[0], pair[1])?;
                acc = arena.and(acc, e)?;
            }
            acc
        }
        "distinct" => {
            if args.len() < 2 {
                return Err(SmtError::Syntax(
                    "`distinct` expects >= 2 arguments".to_owned(),
                ));
            }
            let mut acc = None;
            for i in 0..args.len() {
                for j in i + 1..args.len() {
                    // P2.7 A.2: the pairwise equality atoms enter the length
                    // abstraction exactly like the `=` operator's (equal
                    // strings have equal lengths; the fact is sound under the
                    // enclosing negation — see `LenAbs`).
                    let e = if let Some(e) = seq_aware_eq(arena, seq, args[i], args[j])? {
                        let lp = lenabs.len_expr_seq(arena, args[i])?;
                        let lq = lenabs.len_expr_seq(arena, args[j])?;
                        let fact = arena.eq(lp, lq)?;
                        lenabs.note_atom_fact(arena, e, fact)?;
                        e
                    } else if let Some(e) = string_aware_eq(arena, args[i], args[j])? {
                        string_eq_len_hook(arena, lenabs, e, args[i], args[j])?;
                        e
                    } else {
                        let e = arena.eq(args[i], args[j])?;
                        if string_shaped(arena, args[i]) && string_shaped(arena, args[j]) {
                            string_eq_len_hook(arena, lenabs, e, args[i], args[j])?;
                        }
                        e
                    };
                    let ne = arena.not(e)?;
                    acc = Some(match acc {
                        Some(prev) => arena.and(prev, ne)?,
                        None => ne,
                    });
                }
            }
            acc.expect("args length checked")
        }
        "ite" => {
            need(3)?;
            arena.ite(args[0], args[1], args[2])?
        }
        "bvnot" => {
            need(1)?;
            arena.bv_not(args[0])?
        }
        "bvneg" => {
            need(1)?;
            arena.bv_neg(args[0])?
        }
        "bvand" => fold(arena, TermArena::bv_and)?,
        "bvor" => fold(arena, TermArena::bv_or)?,
        "bvxor" => fold(arena, TermArena::bv_xor)?,
        "bvadd" => fold(arena, TermArena::bv_add)?,
        "bvmul" => fold(arena, TermArena::bv_mul)?,
        "concat" => fold(arena, TermArena::concat)?,
        "bvsub" => {
            need(2)?;
            arena.bv_sub(args[0], args[1])?
        }
        "bvnand" => bin(arena, TermArena::bv_nand, args, op)?,
        "bvnor" => bin(arena, TermArena::bv_nor, args, op)?,
        "bvxnor" => bin(arena, TermArena::bv_xnor, args, op)?,
        "bvudiv" => bin(arena, TermArena::bv_udiv, args, op)?,
        "bvurem" => bin(arena, TermArena::bv_urem, args, op)?,
        "bvsdiv" => bin(arena, TermArena::bv_sdiv, args, op)?,
        "bvsrem" => bin(arena, TermArena::bv_srem, args, op)?,
        "bvsmod" => bin(arena, TermArena::bv_smod, args, op)?,
        "bvshl" => bin(arena, TermArena::bv_shl, args, op)?,
        "bvlshr" => bin(arena, TermArena::bv_lshr, args, op)?,
        "bvashr" => bin(arena, TermArena::bv_ashr, args, op)?,
        "bvult" => bin(arena, TermArena::bv_ult, args, op)?,
        "bvule" => bin(arena, TermArena::bv_ule, args, op)?,
        "bvugt" => bin(arena, TermArena::bv_ugt, args, op)?,
        "bvuge" => bin(arena, TermArena::bv_uge, args, op)?,
        "bvslt" => bin(arena, TermArena::bv_slt, args, op)?,
        "bvsle" => bin(arena, TermArena::bv_sle, args, op)?,
        "bvsgt" => bin(arena, TermArena::bv_sgt, args, op)?,
        "bvsge" => bin(arena, TermArena::bv_sge, args, op)?,
        "bvcomp" => bin(arena, TermArena::bv_comp, args, op)?,
        // Overflow-detection predicates (SMT-LIB 2.6).
        "bvuaddo" => bin(arena, TermArena::bv_uaddo, args, op)?,
        "bvsaddo" => bin(arena, TermArena::bv_saddo, args, op)?,
        "bvusubo" => bin(arena, TermArena::bv_usubo, args, op)?,
        "bvssubo" => bin(arena, TermArena::bv_ssubo, args, op)?,
        "bvumulo" => bin(arena, TermArena::bv_umulo, args, op)?,
        "bvsmulo" => bin(arena, TermArena::bv_smulo, args, op)?,
        "bvnego" => {
            need(1)?;
            arena.bv_nego(args[0])?
        }
        // Unary BV→BitVec(1) reductions (SMT-LIB 2.6), desugared to existing BV
        // ops per cvc5/bitwuzla's authoritative elimination rules. See
        // [`bv_reduce`] for the exact desugaring and soundness note. The result
        // is always one bit wide.
        "bvredor" | "bvredand" | "bvredxor" => {
            need(1)?;
            bv_reduce(arena, op, args[0])?
        }
        // Floating-point: a value is its bit-vector pattern carried by a
        // `Sort::Float` (ADR-0026); the format is recovered from the operand sort.
        // Rounding-mode-free ops only; `(fp s e m)` assembles a literal.
        "fp" => {
            need(3)?;
            // sign(1) · exp(eb) · significand(sb-1)  →  Float { exp: eb, sig: sb }.
            let eb = arena.sort_of(args[1]).lowered_width().ok_or_else(|| {
                SmtError::Syntax("fp exponent field must be a bit-vector".to_owned())
            })?;
            let sig_field = arena.sort_of(args[2]).lowered_width().ok_or_else(|| {
                SmtError::Syntax("fp significand field must be a bit-vector".to_owned())
            })?;
            let sb = sig_field + 1;
            // Concatenate sign·exp·significand MSB-first. When all three fields are
            // constant, fold to a single `BvConst` so constant-folding ops
            // (`fp.to_real`, `fp.roundToIntegral`, …) see a literal value.
            let as_const = |t: TermId| match arena.node(t) {
                &TermNode::BvConst { width, value } => Some((width, value)),
                _ => None,
            };
            let bv = if let (Some((ws, vs)), Some((we, ve)), Some((wm, vm))) =
                (as_const(args[0]), as_const(args[1]), as_const(args[2]))
            {
                let total = ws + we + wm;
                let value = (vs << (we + wm)) | (ve << wm) | vm;
                arena.bv_const(total, value)?
            } else {
                let se = arena.concat(args[0], args[1])?;
                arena.concat(se, args[2])?
            };
            arena.fp_from_bits(bv, eb, sb)?
        }
        // FP ops: read the format from the (float-typed) operand, then run the
        // bit-vector builders on the unwrapped bits (ADR-0026). FP-valued results
        // are re-stamped to `Float`; predicates/`to_real` are Bool/Real.
        "fp.abs" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            let r = axeyum_fp::abs(arena, fmt, x)?;
            as_float(arena, fmt, r)?
        }
        "fp.neg" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            let r = axeyum_fp::neg(arena, fmt, x)?;
            as_float(arena, fmt, r)?
        }
        "fp.eq" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::eq(arena, fmt, a, b)?
        }
        "fp.lt" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::lt(arena, fmt, a, b)?
        }
        "fp.leq" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::leq(arena, fmt, a, b)?
        }
        "fp.gt" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::gt(arena, fmt, a, b)?
        }
        "fp.geq" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            axeyum_fp::geq(arena, fmt, a, b)?
        }
        "fp.min" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            let r = axeyum_fp::min(arena, fmt, a, b)?;
            as_float(arena, fmt, r)?
        }
        "fp.max" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            let r = axeyum_fp::max(arena, fmt, a, b)?;
            as_float(arena, fmt, r)?
        }
        "fp.rem" => {
            need(2)?;
            let fmt = fp_format(arena, args[0])?;
            let (a, b) = (to_bits(arena, args[0])?, to_bits(arena, args[1])?);
            let r = if let Some(folded) = axeyum_fp::rem(arena, fmt, a, b)? {
                folded
            } else {
                axeyum_fp::rem_sym(arena, fmt, a, b)?
            };
            as_float(arena, fmt, r)?
        }
        "fp.isNaN" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_nan(arena, fmt, x)?
        }
        "fp.isInfinite" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_infinite(arena, fmt, x)?
        }
        "fp.isZero" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_zero(arena, fmt, x)?
        }
        "fp.isNormal" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_normal(arena, fmt, x)?
        }
        "fp.isSubnormal" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_subnormal(arena, fmt, x)?
        }
        "fp.isNegative" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_negative(arena, fmt, x)?
        }
        "fp.isPositive" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            axeyum_fp::is_positive(arena, fmt, x)?
        }
        "fp.to_real" => {
            need(1)?;
            let fmt = fp_format(arena, args[0])?;
            let x = to_bits(arena, args[0])?;
            if let Some(constant) = axeyum_fp::to_real(arena, fmt, x)? {
                constant
            } else {
                let exceptional = unspecified_to_real_value(arena, args[0])?;
                axeyum_fp::to_real_sym(arena, fmt, x, exceptional)?
            }
        }
        "select" => {
            need(2)?;
            arena.select(args[0], args[1])?
        }
        "store" => {
            need(3)?;
            arena.store(args[0], args[1], args[2])?
        }
        // cvc5 `:arrays-exp` extension: arrays are equal on the inclusive
        // integer interval `[lo, hi]`. Keep this parse-only expansion finite.
        "eqrange" => {
            need(4)?;
            array_eqrange(arena, args[0], args[1], args[2], args[3])?
        }
        // --- linear arithmetic, sort-directed Int/Real (ADR-0014/0015) ----
        // `+`/`-`/`*`/comparisons are polymorphic: if any operand is `Real`,
        // integer-constant operands are coerced to `Real` and the real builders
        // are used; otherwise the integer builders.
        "+" => {
            let (real, a) = numeric_args(arena, args)?;
            if real {
                fold_args(arena, &a, op, TermArena::real_add)?
            } else {
                if a.is_empty() {
                    return Err(SmtError::Syntax("`+` expects >= 1 argument".to_owned()));
                }
                let nonzero = a
                    .iter()
                    .copied()
                    .filter(|&term| !matches!(arena.node(term), TermNode::IntConst(0)))
                    .collect::<Vec<_>>();
                match nonzero.as_slice() {
                    [] => arena.int_const(0),
                    [term] => *term,
                    terms => fold_args(arena, terms, op, TermArena::int_add)?,
                }
            }
        }
        "*" => {
            let (real, a) = numeric_args(arena, args)?;
            if real {
                fold_args(arena, &a, op, TermArena::real_mul)?
            } else {
                fold_args(arena, &a, op, TermArena::int_mul)?
            }
        }
        "-" => {
            let (real, a) = numeric_args(arena, args)?;
            match a.len() {
                1 if real => arena.real_neg(a[0])?,
                1 => arena.int_neg(a[0])?,
                0 => return Err(SmtError::Syntax("`-` expects >= 1 argument".to_owned())),
                _ => {
                    let mut acc = a[0];
                    for &next in &a[1..] {
                        acc = if real {
                            arena.real_sub(acc, next)?
                        } else if acc == next {
                            arena.int_const(0)
                        } else if matches!(arena.node(next), TermNode::IntConst(0)) {
                            acc
                        } else {
                            arena.int_sub(acc, next)?
                        };
                    }
                    acc
                }
            }
        }
        "/" => {
            // `/` is always Real-typed (SMT-LIB `Reals_Ints`): every operand is
            // coerced to `Real`, including the all-integer-constant case
            // `(/ 177 366500000)`, which `numeric_args` would leave as `Int`.
            let a = real_args(arena, args)?;
            real_division(arena, &a)?
        }
        "div" | "mod" => {
            // SMT-LIB integer Euclidean division/modulo (binary, left-assoc for div).
            let (_, a) = numeric_args(arena, args)?;
            if a.len() < 2 {
                return Err(SmtError::Syntax(format!("`{op}` expects >= 2 arguments")));
            }
            let f = if op == "div" {
                TermArena::int_div
            } else {
                TermArena::int_mod
            };
            let mut acc = a[0];
            for &next in &a[1..] {
                acc = f(arena, acc, next)?;
            }
            acc
        }
        "@int_div_by_zero" | "@mod_by_zero" => {
            // cvc5's parse-skolem (`:parse-skolem-definitions`) for the
            // underspecified value of division/modulo by zero:
            // `@int_div_by_zero(x) ≡ (div x 0)`, `@mod_by_zero(x) ≡ (mod x 0)`. Map
            // it straight back to axeyum's TOTAL div/mod-by-zero — the congruent
            // uninterpreted convention (ADR / task #40) — so a script that names the
            // skolem decides identically to one that writes `(div x 0)` directly, and
            // the same congruence (`@f(x) = @f(y) ⟺ x = y`) is preserved.
            let (_, a) = numeric_args(arena, args)?;
            if a.len() != 1 {
                return Err(SmtError::Syntax(format!("`{op}` expects 1 argument")));
            }
            let zero = arena.int_const(0);
            if op == "@int_div_by_zero" {
                arena.int_div(a[0], zero)?
            } else {
                arena.int_mod(a[0], zero)?
            }
        }
        "abs" => {
            let (_, a) = numeric_args(arena, args)?;
            if a.len() != 1 {
                return Err(SmtError::Syntax("`abs` expects 1 argument".to_owned()));
            }
            arena.int_abs(a[0])?
        }
        // cvc5 native `(int.pow2 x)` — total integer power-of-two (`2^x` for
        // `x ≥ 0`, the defined value `0` for `x < 0`; see [`Op::IntPow2`]). Unary,
        // `Int → Int`. `int_pow2` rejects a non-integer argument.
        "int.pow2" => {
            need(1)?;
            arena.int_pow2(args[0])?
        }
        // Int↔Real coercions. Constant operands fold exactly; symbolic operands
        // need cross-sort (Nelson-Oppen) reasoning and are not yet supported.
        "to_real" => {
            need(1)?;
            match *arena.node(args[0]) {
                TermNode::IntConst(n) => arena.real_const(Rational::integer(n)),
                _ => arena.int_to_real(args[0])?,
            }
        }
        "to_int" => {
            need(1)?;
            match *arena.node(args[0]) {
                TermNode::RealConst(r) => {
                    arena.int_const(r.numerator().div_euclid(r.denominator()))
                }
                _ => arena.real_to_int(args[0])?,
            }
        }
        "is_int" => {
            need(1)?;
            match *arena.node(args[0]) {
                TermNode::RealConst(r) => arena.bool_const(r.denominator() == 1),
                _ => arena.real_is_int(args[0])?,
            }
        }
        // `bv2nat` (SMT-LIB 2.6) and `ubv_to_int` (the SMT-LIB 2.7 / cvc5 spelling)
        // are the *same* operator: the unsigned (natural) value of a bit-vector.
        // Both map to [`TermArena::bv2nat`] verbatim.
        "bv2nat" | "ubv_to_int" => {
            if args.len() != 1 {
                return Err(SmtError::Syntax(format!("`{op}` expects 1 argument")));
            }
            arena.bv2nat(args[0])?
        }
        "<" | "<=" | ">" | ">=" => {
            let (real, a) = numeric_args(arena, args)?;
            let int_f = match op {
                "<" => TermArena::int_lt,
                "<=" => TermArena::int_le,
                ">" => TermArena::int_gt,
                _ => TermArena::int_ge,
            };
            let real_f = match op {
                "<" => TermArena::real_lt,
                "<=" => TermArena::real_le,
                ">" => TermArena::real_gt,
                _ => TermArena::real_ge,
            };
            if real {
                chain_args(arena, &a, op, real_f)?
            } else {
                chain_args(arena, &a, op, int_f)?
            }
        }
        // A declared uninterpreted function applied to arguments (ADR-0013).
        // Builtins above take priority, matching SMT-LIB reserved names.
        other => {
            // String/regex operators outside the wired bounded subset
            // (`str.replace_re`, `str.indexof_re`, the `re.comp`/`re.diff`
            // constructors, …) are declined cleanly (ADR-0029) so a benchmark using
            // them returns `Unknown`/`Unsupported` — never a wrong verdict, never a
            // confusing "unknown operator".
            if other.starts_with("str.") || other.starts_with("re.") {
                return Err(SmtError::Unsupported(format!(
                    "string/regex operator `{other}` is outside the wired bounded subset \
                     (ADR-0029); supported: str.len, str.prefixof, str.contains, str.suffixof, \
                     str.at, str.substr, str.replace, str.replace_all (ground), str.indexof, \
                     str.to_code, str.from_code, str.to_int, str.from_int, str.< , str.<=, \
                     str.++ (variable, bounded), = / distinct over String"
                )));
            }
            if let Some(func) = arena.find_function(other) {
                arena.apply(func, args)?
            } else if let Some(ctor) = arena.find_constructor(other) {
                // Datatype constructor application `(C a …)` (ADR-0022).
                arena.construct(ctor, args)?
            } else if let Some((ctor, field)) = find_selector(arena, other) {
                // Selector application `(sel x)`: project a constructor's field.
                need(1)?;
                arena.dt_select(ctor, field, args[0])?
            } else {
                return Err(SmtError::Unsupported(format!("operator `{other}`")));
            }
        }
    })
}

/// Resolves a datatype selector name to its `(constructor, field index)`, by
/// scanning the constructors' field lists. `None` if no constructor has a field
/// with that name.
fn find_selector(arena: &TermArena, name: &str) -> Option<(axeyum_ir::ConstructorId, u32)> {
    for dt in arena.datatype_ids() {
        for &ctor in arena.datatype_constructors(dt) {
            if let Some(field) = arena
                .constructor_fields(ctor)
                .iter()
                .position(|(fname, _)| fname == name)
            {
                return Some((ctor, u32::try_from(field).expect("field index fits u32")));
            }
        }
    }
    None
}

/// Parses a non-negative decimal literal `d.ddd` into an exact rational, or
/// `None` if `a` is not a decimal numeral.
fn parse_decimal(a: &str) -> Option<Rational> {
    let (int_part, frac_part) = a.split_once('.')?;
    if int_part.is_empty() && frac_part.is_empty() {
        return None;
    }
    let digits = |s: &str| s.bytes().all(|b| b.is_ascii_digit());
    if !digits(int_part) || !digits(frac_part) {
        return None;
    }
    let combined = format!("{int_part}{frac_part}");
    let num: i128 = combined.parse().ok()?;
    let mut den: i128 = 1;
    for _ in 0..frac_part.len() {
        den = den.checked_mul(10)?;
    }
    Some(Rational::new(num, den))
}

/// Classifies numeric `args` as real (any operand `Real`) and, if real, coerces
/// integer operands to `Real` (SMT-LIB numeral coercion). Integer *constants*
/// fold directly to a `RealConst`; non-constant `Int` terms are wrapped in the
/// exact `Int → Real` embedding (`arena.int_to_real`, the `to_real` operator).
///
/// This is the SMT-LIB / Z3 `Reals_Ints` mixed-arithmetic rule: an `Int`
/// subterm appearing in a `Real` context is embedded via `to_real`
/// (`to_real n = n`), which is denotation-preserving. The coercion fires *only*
/// when at least one operand is already `Real` (a genuine Real context);
/// pure-`Int` calls return early below, so `div`/`mod`/`abs`/comparisons over
/// `Int` keep their integer semantics untouched.
fn numeric_args(arena: &mut TermArena, args: &[TermId]) -> Result<(bool, Vec<TermId>), SmtError> {
    let is_real = args.iter().any(|&a| arena.sort_of(a) == Sort::Real);
    if !is_real {
        return Ok((false, args.to_vec()));
    }
    let mut out = Vec::with_capacity(args.len());
    for &a in args {
        match arena.sort_of(a) {
            Sort::Real => out.push(a),
            Sort::Int => match *arena.node(a) {
                // Integer constant: fold to the exact real constant.
                TermNode::IntConst(value) => out.push(arena.real_const(Rational::integer(value))),
                // Non-constant Int term: embed via the exact `to_real` operator.
                _ => out.push(arena.int_to_real(a)?),
            },
            _ => {
                return Err(SmtError::Syntax(
                    "mixed real and non-arithmetic operands".to_owned(),
                ));
            }
        }
    }
    Ok((true, out))
}

/// Coerces *every* numeric operand to `Real`, for the always-`Real` operator
/// `/` (SMT-LIB `Reals_Ints` real division). Unlike [`numeric_args`], this
/// fires even when no operand is already `Real` — e.g. `(/ 177 366500000)` over
/// two integer constants, which denotes the rational `177/366500000`. Integer
/// constants fold to `RealConst`; non-constant `Int` terms use the exact
/// `to_real` embedding. The coercion is denotation-preserving, matching Z3/cvc5.
fn real_args(arena: &mut TermArena, args: &[TermId]) -> Result<Vec<TermId>, SmtError> {
    let mut out = Vec::with_capacity(args.len());
    for &a in args {
        match arena.sort_of(a) {
            Sort::Real => out.push(a),
            Sort::Int => match *arena.node(a) {
                TermNode::IntConst(value) => out.push(arena.real_const(Rational::integer(value))),
                _ => out.push(arena.int_to_real(a)?),
            },
            _ => {
                return Err(SmtError::Syntax(
                    "`/` expects real or integer operands".to_owned(),
                ));
            }
        }
    }
    Ok(out)
}

/// Folds a binary arithmetic builder over `args` (left-associative), requiring
/// at least one argument.
fn fold_args(
    arena: &mut TermArena,
    args: &[TermId],
    op: &str,
    f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> Result<TermId, SmtError> {
    let mut iter = args.iter();
    let Some(&first) = iter.next() else {
        return Err(SmtError::Syntax(format!("`{op}` expects >= 1 argument")));
    };
    let mut acc = first;
    for &next in iter {
        acc = f(arena, acc, next)?;
    }
    Ok(acc)
}

/// Real division `(/ a b ...)`; only constant operands are in the linear
/// fragment, so each must be a real constant.
fn real_division(arena: &mut TermArena, args: &[TermId]) -> Result<TermId, SmtError> {
    if args.len() < 2 {
        return Err(SmtError::Syntax("`/` expects >= 2 arguments".to_owned()));
    }
    let value = |arena: &TermArena, t: TermId| -> Option<Rational> {
        match *arena.node(t) {
            TermNode::RealConst(r) => Some(r),
            _ => None,
        }
    };
    // Constant-fold when every operand is a real constant (and no zero divisor);
    // otherwise build symbolic `RealDiv` terms (left-associative), decided by the
    // NRA layer.
    if let Some(mut acc) = value(arena, args[0]) {
        let mut all_const = true;
        for &next in &args[1..] {
            match value(arena, next) {
                Some(divisor) if !divisor.is_zero() => acc = acc / divisor,
                _ => {
                    all_const = false;
                    break;
                }
            }
        }
        if all_const {
            return Ok(arena.real_const(acc));
        }
    }
    let mut acc = args[0];
    for &next in &args[1..] {
        acc = arena.real_div(acc, next)?;
    }
    Ok(acc)
}

/// Chains a comparison over `args` pairwise, conjoining the results: `(< a b c)`
/// becomes `(and (< a b) (< b c))` (SMT-LIB chainable relations).
fn chain_args(
    arena: &mut TermArena,
    args: &[TermId],
    op: &str,
    f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
) -> Result<TermId, SmtError> {
    if args.len() < 2 {
        return Err(SmtError::Syntax(format!("`{op}` expects >= 2 arguments")));
    }
    let mut acc = f(arena, args[0], args[1])?;
    for pair in args.windows(2).skip(1) {
        let next = f(arena, pair[0], pair[1])?;
        acc = arena.and(acc, next)?;
    }
    Ok(acc)
}

fn bin(
    arena: &mut TermArena,
    f: fn(&mut TermArena, TermId, TermId) -> Result<TermId, axeyum_ir::IrError>,
    args: &[TermId],
    op: &str,
) -> Result<TermId, SmtError> {
    if args.len() != 2 {
        return Err(SmtError::Syntax(format!(
            "`{op}` expects 2 arguments, got {}",
            args.len()
        )));
    }
    Ok(f(arena, args[0], args[1])?)
}

/// Desugars a unary BV reduction (`bvredor` / `bvredand` / `bvredxor`) over the
/// `w`-bit operand `x` into a one-bit (`BitVec(1)`) result using existing BV
/// operators only. The semantics follow SMT-LIB 2.6 verbatim, matching the
/// authoritative elimination rules in cvc5
/// (`src/theory/bv/rewrites-elimination`) and bitwuzla
/// (`BV_RED{OR,AND,XOR}_ELIM`):
///
/// - `(bvredor x)`  = `#b1` iff `x != 0`. Desugared as `(bvnot (bvcomp x 0))`:
///   `bvcomp x 0` is the one-bit equality `#b1` iff `x = 0`, so the `bvnot`
///   flips it to `#b1` iff `x != 0`.
/// - `(bvredand x)` = `#b1` iff every bit of `x` is set, i.e. `x` equals the
///   all-ones value of its width. Desugared as `(bvcomp x (bvnot 0))`, where
///   `(bvnot 0)` is the `w`-bit all-ones constant.
/// - `(bvredxor x)` = the parity of `x` (XOR of all its bits). Desugared as the
///   left-fold `(bvxor … (bvxor (extract 0 0 x) (extract 1 1 x)) …)` over every
///   single-bit slice `((_ extract i i) x)` for `i` in `0..w`, each itself a
///   `BitVec(1)`.
///
/// All three desugarings are denotation-preserving by construction (each named
/// op is replaced by its definitional expansion in terms of ops axeyum already
/// decides), so they can never produce a wrong `sat`/`unsat`.
fn bv_reduce(arena: &mut TermArena, op: &str, x: TermId) -> Result<TermId, SmtError> {
    let Sort::BitVec(w) = arena.sort_of(x) else {
        return Err(SmtError::Syntax(format!(
            "`{op}` expects a bit-vector operand, got {:?}",
            arena.sort_of(x)
        )));
    };
    Ok(match op {
        "bvredor" => {
            let zero = arena.bv_const(w, 0)?;
            let eq = arena.bv_comp(x, zero)?;
            arena.bv_not(eq)?
        }
        "bvredand" => {
            let zero = arena.bv_const(w, 0)?;
            let ones = arena.bv_not(zero)?;
            arena.bv_comp(x, ones)?
        }
        "bvredxor" => {
            let mut acc = arena.extract(0, 0, x)?;
            for i in 1..w {
                let bit = arena.extract(i, i, x)?;
                acc = arena.bv_xor(acc, bit)?;
            }
            acc
        }
        _ => unreachable!("bv_reduce called with non-reduction op `{op}`"),
    })
}

/// Desugars `((_ iand N) a b)` — the SMT-LIB integer bitwise-AND at bit-width
/// `N` — into existing Int↔BV ops. Per the SMT-LIB `Ints` theory definition,
/// for integer operands `a`, `b`:
///
/// ```text
/// ((_ iand N) a b) = bv2nat( bvand( ((_ int2bv N) a), ((_ int2bv N) b) ) )
/// ```
///
/// `((_ int2bv N) x)` reduces `x` modulo `2^N` to an `N`-bit two's-complement
/// pattern (axeyum's [`TermArena::int2bv`] is exactly "the operand integer
/// reduced mod `2^N`"), `bvand` is the bitwise AND of those patterns, and
/// `bv2nat` ([`TermArena::bv2nat`]) reinterprets the `N`-bit result as the
/// non-negative integer in `[0, 2^N)`. This is the operator's *definition*, so
/// the desugaring is denotation-preserving and cannot yield a wrong verdict.
///
/// The index `N` must be a positive numeral; the application is binary.
///
/// # Errors
///
/// [`SmtError::Syntax`] for a missing/non-numeric/zero index, a wrong argument
/// count, or non-integer operands.
fn apply_iand(arena: &mut TermArena, head: &[SExpr], args: &[TermId]) -> Result<TermId, SmtError> {
    if head.len() != 3 {
        return Err(SmtError::Syntax(format!(
            "`iand` expects 1 index, got {}",
            head.len().saturating_sub(2)
        )));
    }
    let n = head
        .get(2)
        .and_then(SExpr::atom)
        .and_then(|s| s.parse::<u32>().ok())
        .filter(|&n| n > 0)
        .ok_or_else(|| SmtError::Syntax("`iand` index must be a positive numeral".to_owned()))?;
    if args.len() != 2 {
        return Err(SmtError::Syntax(format!(
            "`(_ iand {n})` expects 2 arguments, got {}",
            args.len()
        )));
    }
    if arena.sort_of(args[0]) != Sort::Int || arena.sort_of(args[1]) != Sort::Int {
        return Err(SmtError::Syntax(
            "`iand` expects two integer arguments".to_owned(),
        ));
    }
    let a_bv = arena.int2bv(n, args[0])?;
    let b_bv = arena.int2bv(n, args[1])?;
    let anded = arena.bv_and(a_bv, b_bv)?;
    Ok(arena.bv2nat(anded)?)
}

#[allow(clippy::too_many_lines)]
fn apply_parameterized(
    arena: &mut TermArena,
    head: &[SExpr],
    args: &[TermId],
) -> Result<TermId, SmtError> {
    // Constant array `((as const (Array I E)) v)`.
    if head.first().and_then(SExpr::atom) == Some("as") {
        if head.get(1).and_then(SExpr::atom) == Some("const") && head.len() == 3 && args.len() == 1
        {
            // The `as const` sort is the explicit array form; sort aliases are
            // resolved at declaration sites, not threaded into term conversion,
            // so an empty alias map is correct here.
            let no_aliases: HashMap<String, Sort> = HashMap::new();
            let Sort::Array { index, element } = parse_sort(arena, &no_aliases, &head[2])? else {
                return Err(SmtError::Unsupported(format!(
                    "`as const` non-array sort {head:?}"
                )));
            };
            let actual = arena.sort_of(args[0]);
            let expected = element.to_sort();
            if actual != expected {
                return Err(SmtError::Ir(axeyum_ir::IrError::SortsDiffer(
                    actual, expected,
                )));
            }
            return Ok(arena.const_array_with_index_sort(index.to_sort(), args[0])?);
        }
        return Err(SmtError::Unsupported(format!("`as` form {head:?}")));
    }
    // `((_ iand N) a b)` — integer bitwise-AND at bit-width `N` (QF_NIA,
    // SMT-LIB). This is the one indexed op here that is *binary*, so it is
    // handled before the unary-arity guard below. See [`apply_iand`].
    if head.first().and_then(SExpr::atom) == Some("_")
        && head.get(1).and_then(SExpr::atom) == Some("iand")
    {
        return apply_iand(arena, head, args);
    }
    if head.first().and_then(SExpr::atom) != Some("_") || args.len() != 1 {
        return Err(SmtError::Unsupported(format!("application head {head:?}")));
    }
    let name = head
        .get(1)
        .and_then(SExpr::atom)
        .ok_or_else(|| SmtError::Syntax("indexed operator name".to_owned()))?;
    let expect_head_len = |n: usize| -> Result<(), SmtError> {
        if head.len() == n {
            Ok(())
        } else {
            Err(SmtError::Syntax(format!(
                "`{name}` expects {} indices, got {}",
                n.saturating_sub(2),
                head.len().saturating_sub(2)
            )))
        }
    };
    let index = |i: usize| -> Result<u32, SmtError> {
        head.get(i)
            .and_then(SExpr::atom)
            .and_then(|s| s.parse::<u32>().ok())
            .ok_or_else(|| SmtError::Syntax(format!("`{name}` index {i}")))
    };
    Ok(match name {
        "extract" => {
            expect_head_len(4)?;
            arena.extract(index(2)?, index(3)?, args[0])?
        }
        "zero_extend" => {
            expect_head_len(3)?;
            arena.zero_ext(index(2)?, args[0])?
        }
        "sign_extend" => {
            expect_head_len(3)?;
            arena.sign_ext(index(2)?, args[0])?
        }
        "rotate_left" => {
            expect_head_len(3)?;
            arena.rotate_left(index(2)?, args[0])?
        }
        "rotate_right" => {
            expect_head_len(3)?;
            arena.rotate_right(index(2)?, args[0])?
        }
        "repeat" => {
            expect_head_len(3)?;
            let n = index(2)?;
            if n == 0 {
                return Err(SmtError::Syntax("`repeat` index must be >= 1".to_owned()));
            }
            let mut acc = args[0];
            for _ in 1..n {
                acc = arena.concat(acc, args[0])?;
            }
            acc
        }
        "divisible" => {
            expect_head_len(3)?;
            let n: i128 = head
                .get(2)
                .and_then(SExpr::atom)
                .and_then(|s| s.parse().ok())
                .ok_or_else(|| SmtError::Syntax("`divisible` index".to_owned()))?;
            arena.int_divisible(args[0], n)?
        }
        // `(_ int2bv N)` (SMT-LIB 2.6) and `(_ int_to_bv N)` (the SMT-LIB 2.7 /
        // cvc5 spelling) are the *same* indexed operator: the `N`-bit two's-
        // complement pattern of an integer reduced modulo `2^N`. Both map to
        // [`TermArena::int2bv`] verbatim.
        "int2bv" | "int_to_bv" => {
            expect_head_len(3)?;
            arena.int2bv(index(2)?, args[0])?
        }
        "to_fp" => {
            expect_head_len(4)?;
            let (eb, sb) = (index(2)?, index(3)?);
            // `((_ to_fp eb sb) x)` over a single bit-vector argument is an IEEE
            // bit-pattern reinterpret to a `Float { eb, sb }` (ADR-0026). The
            // rounding-mode forms (from FP, real, or signed BV) take a leading
            // `RoundingMode` and are handled in `apply_fp_rounded_indexed`.
            if args.len() != 1 {
                return Err(SmtError::Unsupported(
                    "(_ to_fp …) bit reinterpret expects exactly one bit-vector operand".to_owned(),
                ));
            }
            match arena.sort_of(args[0]) {
                Sort::BitVec(bw) if bw == eb + sb => arena.fp_from_bits(args[0], eb, sb)?,
                s => {
                    return Err(SmtError::Syntax(format!(
                        "(_ to_fp {eb} {sb}) bit reinterpret expects a BitVec({}), got {s:?}",
                        eb + sb
                    )));
                }
            }
        }
        // Datatype tester `((_ is C) x)` → is `x` built by constructor `C`?
        "is" => {
            expect_head_len(3)?;
            let cname = head
                .get(2)
                .and_then(SExpr::atom)
                .ok_or_else(|| SmtError::Syntax("`(_ is C)` constructor name".to_owned()))?;
            let ctor = arena
                .find_constructor(cname)
                .ok_or_else(|| SmtError::Unsupported(format!("unknown constructor `{cname}`")))?;
            arena.dt_test(ctor, args[0])?
        }
        other => return Err(SmtError::Unsupported(format!("indexed operator `{other}`"))),
    })
}

#[cfg(test)]
mod string_escape_tests {
    use std::collections::BTreeSet;

    use super::{
        ExactEqualityFacts, ExactFixedWordLanguage, ExactLengthEmptiness, ExactRewriteTerm,
        decimal_code_points, decode_string_code_points, eval_pinned_word_semantics,
        exact_affine_equalities_equal, exact_affine_orderings_equal,
        exact_affine_zero_forces_nonpositive, exact_affine_zero_forces_positive,
        exact_from_int_empty_condition, exact_length_emptiness_consequence,
        exact_order_assignments_conflict, exact_rewrite_app, exact_rewrite_concat_at,
        exact_rewrite_concat_substr, exact_rewrite_equality, exact_rewrite_fixed_word_language,
        exact_rewrite_prefix_substr_emptiness, exact_rewrite_replace_preserves_subject,
        exact_rewrite_replace_singleton_equality, exact_rewrite_small_subject_indexof,
        exact_rewrite_term, exact_rewrite_under_assignments, guaranteed_boolean_literal_conflict,
        guaranteed_top_level_conjuncts, parse_script, replace_first_code_points,
        source_string_semantic_facts, substr_code_points,
    };
    use crate::sexpr::{SExpr, read_all};

    #[test]
    fn replace_emptiness_matches_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for subject in &words {
            for needle in &words {
                for replacement in &words {
                    let actual = replace_first_code_points(subject, needle, replacement).is_empty();
                    let characterized = (subject.is_empty()
                        && (!needle.is_empty() || replacement.is_empty()))
                        || (subject == needle && replacement.is_empty());
                    assert_eq!(
                        actual, characterized,
                        "subject={subject:?}, needle={needle:?}, replacement={replacement:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn replace_emptiness_boolean_forms_normalize_only_when_tautological() {
        for text in [
            r#"(not (= (= "" (str.replace x y "B")) (= "" (str.replace x y "A"))))"#,
            r#"(not (= (str.replace "" (str.replace x y "A") y) (str.replace "" x y)))"#,
            r#"(not (= (str.replace "" (str.replace x y "A") x) ""))"#,
        ] {
            let expression = read_all(text)
                .expect("read replacement-emptiness theorem")
                .pop()
                .expect("one replacement-emptiness theorem");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }

        for text in [
            r#"(not (= (= "" (str.replace x y r)) (= x "")))"#,
            r#"(not (= (str.replace "" (str.replace x y "") x) ""))"#,
            r#"(not (= (= x "") (= x "A")))"#,
        ] {
            let expression = read_all(text)
                .expect("read replacement-emptiness control")
                .pop()
                .expect("one replacement-emptiness control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }
    }

    #[test]
    fn exact_rewriter_separates_decimal_and_letter_alphabets() {
        let expression = read_all(r#"(= "A" (str.from_int z))"#)
            .expect("read exact rewrite expression")
            .pop()
            .expect("one expression");
        assert_eq!(
            exact_rewrite_term(&expression, 0),
            ExactRewriteTerm::Bool(false)
        );
    }

    #[test]
    fn exact_rewriter_normalizes_symmetric_equality_atoms() {
        for text in [r"(= (= x y) (= y x))", r#"(= (= x "A") (= "A" x))"#] {
            let expression = read_all(text)
                .expect("read symmetric equality expression")
                .pop()
                .expect("one expression");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(true),
                "{text}"
            );
        }

        let control = read_all(r"(= (str.prefixof x y) (str.prefixof y x))")
            .expect("read asymmetric relation control")
            .pop()
            .expect("one expression");
        assert_ne!(
            exact_rewrite_term(&control, 0),
            ExactRewriteTerm::Bool(true)
        );
    }

    #[test]
    fn exact_equality_paths_close_transitively_and_reject_conflicts() {
        let term = |text: &str| {
            let expression = read_all(text)
                .expect("read equality-path expression")
                .pop()
                .expect("one equality-path expression");
            exact_rewrite_term(&expression, 0)
        };
        let x_equals_y = term("(= x y)");
        let y_equals_a = term(r#"(= y "A")"#);
        let x_equals_a = term(r#"(= x "A")"#);
        let x_equals_b = term(r#"(= x "B")"#);

        let transitive = vec![(x_equals_y, true), (y_equals_a, true)];
        let facts = ExactEqualityFacts::from_assignments(&transitive);
        assert!(!facts.conflict);
        assert_eq!(
            exact_rewrite_under_assignments(&x_equals_a, &transitive, 0),
            ExactRewriteTerm::Bool(true)
        );

        for conflicting in [
            vec![(x_equals_a.clone(), true), (x_equals_b, true)],
            vec![
                (term("(= x y)"), true),
                (term(r#"(= x "A")"#), true),
                (term(r#"(= y "A")"#), false),
            ],
        ] {
            assert!(ExactEqualityFacts::from_assignments(&conflicting).conflict);
        }
        assert!(
            !ExactEqualityFacts::from_assignments(&[
                (term(r#"(= x "A")"#), true),
                (term(r#"(= x "B")"#), false),
            ])
            .conflict
        );
    }

    #[test]
    fn self_expanded_replace_needles_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }
        for subject in &words {
            for expanded_needle in &words {
                for replacement in &words {
                    let inner =
                        replace_first_code_points(expanded_needle, subject, expanded_needle);
                    assert_eq!(
                        replace_first_code_points(subject, &inner, replacement),
                        replace_first_code_points(subject, expanded_needle, replacement),
                        "subject={subject:?}, expanded_needle={expanded_needle:?}, replacement={replacement:?}"
                    );
                }
            }
        }

        let identity = read_all("(= (str.replace x (str.replace y x y) z) (str.replace x y z))")
            .expect("read self-expanded needle identity")
            .pop()
            .expect("one self-expanded needle identity");
        assert_eq!(
            exact_rewrite_term(&identity, 0),
            ExactRewriteTerm::Bool(true)
        );
        let near_miss = read_all("(= (str.replace x (str.replace y z y) w) (str.replace x y w))")
            .expect("read self-expanded needle control")
            .pop()
            .expect("one self-expanded needle control");
        assert_ne!(
            exact_rewrite_term(&near_miss, 0),
            ExactRewriteTerm::Bool(true)
        );
    }

    #[test]
    fn one_code_point_word_boundaries_match_reference_semantics_exhaustively() {
        let mut prefixes = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                prefixes.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }
        for word in [Vec::new(), vec![u32::from(b'A')], vec![u32::from(b'B')]] {
            for boundary in &prefixes {
                let empty_or_equal = boundary.is_empty() || boundary == &word;
                assert_eq!(
                    word.starts_with(boundary),
                    empty_or_equal,
                    "prefix={boundary:?}, word={word:?}"
                );
                assert_eq!(
                    word.ends_with(boundary),
                    empty_or_equal,
                    "suffix={boundary:?}, word={word:?}"
                );
            }
        }

        for head in ["str.prefixof", "str.suffixof"] {
            let identity = read_all(&format!(
                "(= ({head} x (str.at y z)) (or (= x \"\") (= x (str.at y z))))"
            ))
            .expect("read one-code-point boundary identity")
            .pop()
            .expect("one boundary identity");
            assert_eq!(
                exact_rewrite_term(&identity, 0),
                ExactRewriteTerm::Bool(true),
                "{head}"
            );
        }
        let near_miss = read_all(r#"(= (str.prefixof x y) (or (= x "") (= x y)))"#)
            .expect("read unbounded boundary control")
            .pop()
            .expect("one unbounded boundary control");
        assert_ne!(
            exact_rewrite_term(&near_miss, 0),
            ExactRewriteTerm::Bool(true)
        );
    }

    #[test]
    fn affine_one_code_point_views_match_integer_semantics_exhaustively() {
        let term = |text: &str| {
            let expression = read_all(text)
                .expect("read affine expression")
                .pop()
                .expect("one affine expression");
            exact_rewrite_term(&expression, 0)
        };
        for (left, right) in [
            (r"(= (- 0 z) 0)", r"(= z 0)"),
            (r"(= (- z 1) 0)", r"(= (- 1 z) 0)"),
            (r"(= (+ z z) 0)", r"(= z 0)"),
            (r"(= (+ (* 2 z) 4) 0)", r"(= (+ z 2) 0)"),
        ] {
            let left = term(left);
            let right = term(right);
            assert!(exact_affine_equalities_equal(&left, &right));
            for value in -8_i128..=8 {
                let assignment = [(
                    exact_rewrite_app("=", vec![term("z"), ExactRewriteTerm::Int(value)]),
                    true,
                )];
                assert_eq!(
                    exact_rewrite_under_assignments(&left, &assignment, 0),
                    exact_rewrite_under_assignments(&right, &assignment, 0),
                    "value={value}, left={left:?}, right={right:?}"
                );
            }
        }
        for (left, right) in [
            (r"(= (+ z 1) 0)", r"(= z 0)"),
            (r"(= (+ z z) 1)", r"(= z 0)"),
        ] {
            assert!(!exact_affine_equalities_equal(&term(left), &term(right)));
        }
        assert!(exact_affine_equalities_equal(
            &term("(= (+ (* 2 x) (* 4 y) 6) 0)"),
            &term("(= (+ x (* 2 y) 3) 0)")
        ));
        assert!(!exact_affine_equalities_equal(
            &term("(= (+ x y) 0)"),
            &term("(= (+ x (* 2 y)) 0)")
        ));
        let overflow = format!("(= (* {} (+ z z)) 0)", i128::MAX);
        assert!(!exact_affine_equalities_equal(
            &term(&overflow),
            &term("(= z 0)")
        ));

        for (offset, length) in [
            ("z", "(- z 1)"),
            ("z", "(+ z z)"),
            ("(+ 1 z)", "z"),
            ("(+ z z)", "z"),
        ] {
            assert!(exact_affine_zero_forces_nonpositive(
                &term(offset),
                &term(length)
            ));
        }
        assert!(!exact_affine_zero_forces_nonpositive(
            &term("z"),
            &term("(+ z 1)")
        ));
        assert!(exact_affine_zero_forces_nonpositive(
            &term("(+ x y)"),
            &term("(+ (* 2 x) (* 2 y) -1)")
        ));
        assert!(!exact_affine_zero_forces_nonpositive(
            &term("(+ x y)"),
            &term("(+ (* 2 x) (* 2 y) 1)")
        ));
        assert!(exact_affine_zero_forces_nonpositive(
            &term("(+ (* 2 z) 1)"),
            &term("(+ w 1)")
        ));
        for value in -8_i128..=8 {
            for (offset, length) in [
                (value, value - 1),
                (value, value * 2),
                (value + 1, value),
                (value * 2, value),
            ] {
                assert!(
                    substr_code_points(&[u32::from(b'A')], offset, length).is_empty(),
                    "value={value}, offset={offset}, length={length}"
                );
            }
        }
    }

    #[test]
    fn opposite_order_cycles_are_exact_and_exhaustively_sound() {
        use ExactRewriteTerm::{App, Opaque};

        let x = Opaque(SExpr::Atom("x".to_owned()));
        let y = Opaque(SExpr::Atom("y".to_owned()));
        let descriptors: Vec<_> = ["<", "<=", ">", ">="]
            .into_iter()
            .flat_map(|relation| {
                [false, true].into_iter().flat_map(move |reversed| {
                    [false, true]
                        .into_iter()
                        .map(move |required| (relation, reversed, required))
                })
            })
            .collect();
        let atom = |relation: &str, reversed: bool| {
            App(
                relation.to_owned(),
                if reversed {
                    vec![y.clone(), x.clone()]
                } else {
                    vec![x.clone(), y.clone()]
                },
            )
        };
        let evaluate = |relation: &str, reversed: bool, left: i128, right: i128| {
            let (left, right) = if reversed {
                (right, left)
            } else {
                (left, right)
            };
            match relation {
                "<" => left < right,
                "<=" => left <= right,
                ">" => left > right,
                ">=" => left >= right,
                _ => unreachable!(),
            }
        };

        for first in &descriptors {
            for second in &descriptors {
                let assignments = vec![
                    (atom(first.0, first.1), first.2),
                    (atom(second.0, second.1), second.2),
                ];
                let facts = ExactEqualityFacts::from_assignments(&assignments);
                if exact_order_assignments_conflict(&assignments, &facts) {
                    assert!(
                        !(-2_i128..=2).any(|left| (-2_i128..=2).any(|right| {
                            evaluate(first.0, first.1, left, right) == first.2
                                && evaluate(second.0, second.1, left, right) == second.2
                        })),
                        "first={first:?}, second={second:?}"
                    );
                }
            }
        }

        let contradictory = read_all(
            r"(declare-const p Int)
(declare-const negative Bool)
(declare-const positive Bool)
(assert (= negative (not (<= 0 p))))
(assert negative)
(assert (= positive (< 0 p)))
(assert positive)
(check-sat)",
        )
        .expect("read opposite-order contradiction");
        assert!(source_string_semantic_facts(&contradictory).conflict);
    }

    #[test]
    fn affine_substr_views_match_integer_semantics_exhaustively() {
        let term = |text: &str| {
            let expression = read_all(text)
                .expect("read affine expression")
                .pop()
                .expect("one affine expression");
            exact_rewrite_term(&expression, 0)
        };
        for (left, right) in [
            (r"(> (+ z z) 0)", r"(> z 0)"),
            (r"(< 0 (+ z z))", r"(> z 0)"),
            (r"(<= (+ z z) 0)", r"(<= z 0)"),
            (r"(>= 0 (+ z z))", r"(<= z 0)"),
        ] {
            assert!(exact_affine_orderings_equal(&term(left), &term(right)));
        }
        for (left, right) in [
            (r"(> (+ z z) 0)", r"(> (- 0 z) 0)"),
            (r"(> (+ z z) 0)", r"(>= z 0)"),
            (r"(> (+ z 1) 0)", r"(> z 0)"),
        ] {
            assert!(!exact_affine_orderings_equal(&term(left), &term(right)));
        }
        for (offset, length) in [("z", "(+ z 1)"), ("(- z 1)", "z")] {
            assert!(exact_affine_zero_forces_positive(
                &term(offset),
                &term(length)
            ));
        }
        assert!(!exact_affine_zero_forces_positive(&term("z"), &term("z")));

        for text in [
            r#"(= (str.substr "A" 0 (+ z z)) (str.substr "A" 0 z))"#,
            r#"(= (str.substr "A" z (+ 1 z)) (str.at "A" z))"#,
            r#"(= (str.substr "A" (- z 1) z) (str.at "A" (- 1 z)))"#,
            r"(= (str.substr (str.substr y 0 1) 0 1)
                   (str.at (str.replace x x y) 0))",
            r"(= (str.substr (str.substr y 1 1) 0 1)
                   (str.at (str.replace x x y) 1))",
            r"(= (str.substr (str.substr y z 1) 0 1)
                   (str.at (str.replace x x y) z))",
        ] {
            assert_eq!(term(text), ExactRewriteTerm::Bool(true), "{text}");
        }
        for text in [
            r#"(= (str.substr "A" 0 (+ z z 1)) (str.substr "A" 0 z))"#,
            r#"(= (str.substr "A" z z) (str.at "A" z))"#,
            r#"(= (str.substr "A" (- z 1) (- z 1)) (str.at "A" (- 1 z)))"#,
        ] {
            assert_ne!(term(text), ExactRewriteTerm::Bool(true), "{text}");
        }
        let one = [u32::from(b'A')];
        for value in -8_i128..=8 {
            assert_eq!(
                substr_code_points(&one, 0, value * 2),
                substr_code_points(&one, 0, value)
            );
            assert_eq!(
                substr_code_points(&one, value, value + 1),
                substr_code_points(&one, value, 1)
            );
            assert_eq!(
                substr_code_points(&one, value - 1, value),
                substr_code_points(&one, value - 1, 1)
            );
        }
    }

    #[test]
    fn exact_rewriter_closes_small_subject_indexof_totality() {
        for text in [
            r#"(= (str.from_int (str.indexof "" x 1)) "")"#,
            r#"(= (str.at x (str.indexof "A" x 1)) "")"#,
        ] {
            let expression = read_all(text)
                .expect("read small-subject indexof expression")
                .pop()
                .expect("one expression");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(true),
                "{text}"
            );
        }
    }

    #[test]
    fn small_subject_indexof_table_matches_reference_semantics_exhaustively() {
        let subjects = [Vec::new(), vec![u32::from(b'A')], vec![u32::from(b'B')]];
        let needles = [
            Vec::new(),
            vec![u32::from(b'A')],
            vec![u32::from(b'B')],
            vec![u32::from(b'A'), u32::from(b'A')],
            vec![u32::from(b'A'), u32::from(b'B')],
        ];
        for subject in subjects {
            for needle in &needles {
                for offset in -2_i128..=3 {
                    let expected = usize::try_from(offset).ok().and_then(|offset| {
                        if offset > subject.len() {
                            return None;
                        }
                        if needle.is_empty() {
                            return Some(offset);
                        }
                        subject[offset..]
                            .windows(needle.len())
                            .position(|candidate| candidate == needle)
                            .map(|position| offset + position)
                    });
                    let expected = expected
                        .and_then(|index| i128::try_from(index).ok())
                        .unwrap_or(-1);
                    assert_eq!(
                        exact_rewrite_small_subject_indexof(
                            &subject,
                            &ExactRewriteTerm::String(needle.clone()),
                            &ExactRewriteTerm::Int(offset),
                        ),
                        ExactRewriteTerm::Int(expected),
                        "subject={subject:?}, needle={needle:?}, offset={offset}"
                    );
                }
            }
        }
    }

    #[test]
    fn exact_index_totality_views_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=3 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }
        let indexof = |subject: &[u32], needle: &[u32], offset: i128| {
            let Ok(offset) = usize::try_from(offset) else {
                return -1;
            };
            if offset > subject.len() {
                return -1;
            }
            if needle.is_empty() {
                return i128::try_from(offset).expect("small offset");
            }
            subject[offset..]
                .windows(needle.len())
                .position(|candidate| candidate == needle)
                .and_then(|position| i128::try_from(offset + position).ok())
                .unwrap_or(-1)
        };
        let at = |subject: &[u32], index: i128| substr_code_points(subject, index, 1);
        let one = [u32::from(b'A')];

        for subject in &words {
            for needle in &words {
                for offset in -2_i128..=5 {
                    let index = indexof(subject, needle, offset);
                    if offset >= 1 {
                        assert!(at(&one, index).is_empty());
                        assert!(substr_code_points(&one, index, 3).is_empty());
                    }
                    assert!(substr_code_points(&one, index, offset).is_empty());
                    if needle.is_empty() {
                        assert_eq!(at(&one, index), at(&one, offset));
                        assert_eq!(
                            substr_code_points(subject, index, offset),
                            substr_code_points(subject, offset, index)
                        );
                        if offset == 1 {
                            for start in -2_i128..=5 {
                                assert_eq!(
                                    substr_code_points(subject, start, index),
                                    at(subject, start)
                                );
                                assert_eq!(
                                    substr_code_points(&one, start, index),
                                    substr_code_points(
                                        &one,
                                        start,
                                        i128::try_from(subject.len()).expect("small length")
                                    )
                                );
                            }
                            assert_eq!(substr_code_points(subject, 1, index), at(subject, index));
                        }
                    }
                }
            }
            for offset in -2_i128..=5 {
                let self_index = indexof(subject, subject, offset);
                assert_eq!(at(subject, self_index), at(&at(subject, offset), offset));
            }
        }

        for value in
            (-20_i128..=10_000).chain([i128::MAX, i128::MIN, 10_i128.pow(37), 10_i128.pow(38)])
        {
            let self_index = if value == 0 { 0 } else { -1 };
            assert_eq!(
                decimal_code_points(self_index),
                at(&decimal_code_points(0), value)
            );
            assert_eq!(
                at(&decimal_code_points(value), value),
                at(&decimal_code_points(0), value)
            );
        }
    }

    #[test]
    fn exact_index_totality_symbolic_forms_close_and_near_misses_decline() {
        for text in [
            r#"(= (str.at "A" (str.indexof x "" z)) (str.at "A" z))"#,
            r"(= (str.at (str.at x 0) 0) (str.at x 0))",
            r#"(= (str.substr x z (str.indexof x "" 1)) (str.at x z))"#,
            r#"(= (str.substr x (str.indexof y "" z) z)
                   (str.substr x z (str.indexof y "" z)))"#,
            r#"(= (str.from_int (str.indexof x x z)) (str.at "0" z))"#,
        ] {
            let expression = read_all(text)
                .expect("read exact index-totality identity")
                .pop()
                .expect("one index-totality identity");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(true),
                "{text}"
            );
        }
        for text in [
            r#"(= (str.at "AB" (str.indexof x "" z)) (str.at "AB" z))"#,
            r#"(= (str.substr "AB" z (str.indexof x "" 1))
                   (str.substr "AB" z (str.len x)))"#,
        ] {
            let expression = read_all(text)
                .expect("read exact index-totality control")
                .pop()
                .expect("one index-totality control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(true),
                "{text}"
            );
        }
    }

    #[test]
    fn exact_concat_index_routes_match_reference_semantics_exhaustively() {
        let symbol = |name: &str| {
            let expression = read_all(name)
                .expect("read symbolic concat route argument")
                .pop()
                .expect("one symbolic concat route argument");
            exact_rewrite_term(&expression, 0)
        };
        let suffix = symbol("suffix");
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for prefix in [
            vec![u32::from(b'A')],
            vec![u32::from(b'A'), u32::from(b'B')],
        ] {
            let subject = ExactRewriteTerm::App(
                "str.++".to_owned(),
                vec![ExactRewriteTerm::String(prefix.clone()), suffix.clone()],
            );
            for suffix_word in &words {
                let assignment = [(
                    exact_rewrite_app(
                        "=",
                        vec![
                            suffix.clone(),
                            ExactRewriteTerm::String(suffix_word.clone()),
                        ],
                    ),
                    true,
                )];
                let mut joined = prefix.clone();
                joined.extend(suffix_word);
                for index in 0_i128..=7 {
                    let routed = exact_rewrite_concat_at(&subject, &ExactRewriteTerm::Int(index))
                        .expect("fixed index routes through exact prefix length");
                    assert_eq!(
                        exact_rewrite_under_assignments(&routed, &assignment, 0),
                        ExactRewriteTerm::String(substr_code_points(&joined, index, 1)),
                        "prefix={prefix:?}, suffix={suffix_word:?}, index={index}"
                    );
                }
            }
            assert!(
                exact_rewrite_concat_at(&subject, &ExactRewriteTerm::Int(-1)).is_none(),
                "negative indices stay with the ordinary totality fold"
            );
        }

        let repeated =
            ExactRewriteTerm::App("str.++".to_owned(), vec![suffix.clone(), suffix.clone()]);
        let routed = exact_rewrite_concat_at(&repeated, &ExactRewriteTerm::Int(0))
            .expect("index zero routes through repeated components");
        for suffix_word in &words {
            let assignment = [(
                exact_rewrite_app(
                    "=",
                    vec![
                        suffix.clone(),
                        ExactRewriteTerm::String(suffix_word.clone()),
                    ],
                ),
                true,
            )];
            assert_eq!(
                exact_rewrite_under_assignments(&routed, &assignment, 0),
                ExactRewriteTerm::String(substr_code_points(suffix_word, 0, 1)),
                "suffix={suffix_word:?}"
            );
        }
    }

    #[test]
    fn exact_concat_substr_routes_match_reference_semantics_exhaustively() {
        let symbol = |name: &str| {
            let expression = read_all(name)
                .expect("read symbolic concat route argument")
                .pop()
                .expect("one symbolic concat route argument");
            exact_rewrite_term(&expression, 0)
        };
        let suffix = symbol("suffix");
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }
        let one = vec![u32::from(b'A')];
        let subject = ExactRewriteTerm::App(
            "str.++".to_owned(),
            vec![ExactRewriteTerm::String(one.clone()), suffix.clone()],
        );
        for suffix_word in &words {
            let assignment = [(
                exact_rewrite_app(
                    "=",
                    vec![
                        suffix.clone(),
                        ExactRewriteTerm::String(suffix_word.clone()),
                    ],
                ),
                true,
            )];
            let mut joined = one.clone();
            joined.extend(suffix_word);
            for offset in 1_i128..=7 {
                for length in -2_i128..=7 {
                    let routed = exact_rewrite_concat_substr(
                        &subject,
                        &ExactRewriteTerm::Int(offset),
                        &ExactRewriteTerm::Int(length),
                    )
                    .expect("positive substring start routes past one-code-point prefix");
                    assert_eq!(
                        exact_rewrite_under_assignments(&routed, &assignment, 0),
                        ExactRewriteTerm::String(substr_code_points(&joined, offset, length)),
                        "suffix={suffix_word:?}, offset={offset}, length={length}"
                    );
                }
            }
        }

        let z = symbol("z");
        let routed = exact_rewrite_concat_substr(&subject, &z, &z)
            .expect("equal symbolic offset and length satisfy the zero boundary premise");
        for suffix_word in &words {
            for value in -3_i128..=7 {
                let assignments = [
                    (
                        exact_rewrite_app(
                            "=",
                            vec![
                                suffix.clone(),
                                ExactRewriteTerm::String(suffix_word.clone()),
                            ],
                        ),
                        true,
                    ),
                    (
                        exact_rewrite_app("=", vec![z.clone(), ExactRewriteTerm::Int(value)]),
                        true,
                    ),
                ];
                let mut joined = one.clone();
                joined.extend(suffix_word);
                assert_eq!(
                    exact_rewrite_under_assignments(&routed, &assignments, 0),
                    ExactRewriteTerm::String(substr_code_points(&joined, value, value)),
                    "suffix={suffix_word:?}, value={value}"
                );
            }
        }
    }

    #[test]
    fn exact_concat_routes_and_unary_commutativity_close_symbolic_forms() {
        for text in [
            r"(= (str.at (str.++ x x) 0) (str.at x 0))",
            r#"(= (str.at (str.++ "A" x) 0) "A")"#,
            r#"(= (str.at (str.++ "A" x) 1) (str.at x 0))"#,
            r#"(= (str.at (str.replace y "" "A") 1)
                   (str.at (str.replace x x y) 0))"#,
            r#"(= (str.substr (str.++ "A" x) 1 z) (str.substr x 0 z))"#,
            r#"(= (str.substr (str.++ "A" x) z z)
                   (str.substr x (- z 1) z))"#,
            r#"(= (str.++ (str.at "A" z) "A")
                   (str.++ "A" (str.at "A" z)))"#,
            r#"(= (str.++ (str.substr "B" 0 z) "B")
                   (str.++ "B" (str.substr "B" 0 z)))"#,
            r#"(= (str.++ (str.replace "A" x "") "A")
                   (str.++ "A" (str.replace "A" x "")))"#,
        ] {
            let expression = read_all(text)
                .expect("read concat routing identity")
                .pop()
                .expect("one concat routing identity");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(true),
                "{text}"
            );
        }

        for code_point in [u32::from(b'A'), u32::from(b'B')] {
            for left_len in 0..=5 {
                for right_len in 0..=5 {
                    let left = vec![code_point; left_len];
                    let right = vec![code_point; right_len];
                    let mut left_then_right = left.clone();
                    left_then_right.extend(&right);
                    let mut right_then_left = right;
                    right_then_left.extend(&left);
                    assert_eq!(left_then_right, right_then_left);
                }
            }
        }

        for text in [
            r"(= (str.++ x y) (str.++ y x))",
            r#"(= (str.++ (str.at "A" z) "B")
                   (str.++ "B" (str.at "A" z)))"#,
            r#"(= (str.substr (str.++ "A" x) 0 z)
                   (str.substr x (- 1) z))"#,
        ] {
            let expression = read_all(text)
                .expect("read concat routing control")
                .pop()
                .expect("one concat routing control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(true),
                "{text}"
            );
        }
    }

    #[test]
    fn symbolic_one_code_point_views_match_reference_semantics_exhaustively() {
        let symbol = |name: &str| {
            let expression = read_all(name)
                .expect("read symbolic view argument")
                .pop()
                .expect("one symbolic argument");
            exact_rewrite_term(&expression, 0)
        };
        let index = symbol("index");
        let length = symbol("length");
        let subject = ExactRewriteTerm::String(vec![u32::from(b'A')]);
        let at = exact_rewrite_app("str.at", vec![subject.clone(), index.clone()]);
        let substr = exact_rewrite_app(
            "str.substr",
            vec![subject.clone(), index.clone(), length.clone()],
        );

        for concrete_index in -2_i128..=3 {
            let index_assignment = (
                exact_rewrite_app(
                    "=",
                    vec![index.clone(), ExactRewriteTerm::Int(concrete_index)],
                ),
                true,
            );
            let expected_at = if concrete_index == 0 {
                subject.clone()
            } else {
                ExactRewriteTerm::String(Vec::new())
            };
            assert_eq!(
                exact_rewrite_under_assignments(&at, std::slice::from_ref(&index_assignment), 0),
                expected_at,
                "index={concrete_index}"
            );

            for concrete_length in -2_i128..=3 {
                let assignments = [
                    index_assignment.clone(),
                    (
                        exact_rewrite_app(
                            "=",
                            vec![length.clone(), ExactRewriteTerm::Int(concrete_length)],
                        ),
                        true,
                    ),
                ];
                let expected_substr = if concrete_index == 0 && concrete_length > 0 {
                    subject.clone()
                } else {
                    ExactRewriteTerm::String(Vec::new())
                };
                assert_eq!(
                    exact_rewrite_under_assignments(&substr, &assignments, 0),
                    expected_substr,
                    "index={concrete_index}, length={concrete_length}"
                );
            }
        }
    }

    #[test]
    fn exact_rewriter_closes_one_code_point_predicate_views() {
        for text in [
            r#"(not (= (str.contains "B" (str.at "A" z))
                        (str.contains "A" (str.at "B" z))))"#,
            r#"(not (= (str.contains "B" (str.substr "A" 0 z))
                        (str.contains "A" (str.substr "B" 0 z))))"#,
        ] {
            let expression = read_all(text)
                .expect("read one-code-point predicate view")
                .pop()
                .expect("one expression");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }
    }

    #[test]
    fn one_code_point_concat_views_match_reference_semantics_exhaustively() {
        let symbol = |name: &str| {
            let expression = read_all(name)
                .expect("read symbolic concat component")
                .pop()
                .expect("one symbolic component");
            exact_rewrite_term(&expression, 0)
        };
        let left = symbol("left");
        let right = symbol("right");
        let concat = exact_rewrite_app("str.++", vec![left.clone(), right.clone()]);
        let mut words = vec![Vec::new()];
        for _ in 0..2 {
            let prior = words.clone();
            for word in prior {
                for code_point in [u32::from(b'A'), u32::from(b'B')] {
                    let mut extended = word.clone();
                    extended.push(code_point);
                    words.push(extended);
                }
            }
        }

        for left_word in &words {
            for right_word in &words {
                let mut joined = left_word.clone();
                joined.extend(right_word);
                let assignments = [
                    (
                        exact_rewrite_app(
                            "=",
                            vec![left.clone(), ExactRewriteTerm::String(left_word.clone())],
                        ),
                        true,
                    ),
                    (
                        exact_rewrite_app(
                            "=",
                            vec![right.clone(), ExactRewriteTerm::String(right_word.clone())],
                        ),
                        true,
                    ),
                ];
                for view_word in [Vec::new(), vec![u32::from(b'A')], vec![u32::from(b'B')]] {
                    let view = ExactRewriteTerm::String(view_word.clone());
                    for (head, expected) in [
                        ("str.prefixof", joined.starts_with(&view_word)),
                        ("str.suffixof", joined.ends_with(&view_word)),
                        (
                            "str.contains",
                            view_word.is_empty()
                                || joined
                                    .windows(view_word.len())
                                    .any(|candidate| candidate == view_word),
                        ),
                        ("=", joined == view_word),
                    ] {
                        let expression = if head == "str.contains" {
                            exact_rewrite_app(head, vec![concat.clone(), view.clone()])
                        } else {
                            exact_rewrite_app(head, vec![view.clone(), concat.clone()])
                        };
                        assert_eq!(
                            exact_rewrite_under_assignments(&expression, &assignments, 0),
                            ExactRewriteTerm::Bool(expected),
                            "head={head}, left={left_word:?}, right={right_word:?}, view={view:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn fixed_word_languages_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=5 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for word in words.iter().filter(|word| word.len() <= 4) {
            for candidate in &words {
                for (name, language, expected) in [
                    (
                        "prefix",
                        ExactFixedWordLanguage::Prefixes,
                        word.starts_with(candidate),
                    ),
                    (
                        "suffix",
                        ExactFixedWordLanguage::Suffixes,
                        word.ends_with(candidate),
                    ),
                    (
                        "substring",
                        ExactFixedWordLanguage::Substrings,
                        candidate.is_empty()
                            || word
                                .windows(candidate.len())
                                .any(|window| window == candidate),
                    ),
                ] {
                    assert_eq!(
                        exact_rewrite_fixed_word_language(
                            word,
                            &ExactRewriteTerm::String(candidate.clone()),
                            language,
                        ),
                        Some(ExactRewriteTerm::Bool(expected)),
                        "language={name}, word={word:?}, candidate={candidate:?}"
                    );
                }
            }
        }
        assert!(
            exact_rewrite_fixed_word_language(
                &[u32::from(b'A'); 5],
                &ExactRewriteTerm::String(Vec::new()),
                ExactFixedWordLanguage::Substrings,
            )
            .is_none()
        );
    }

    #[test]
    fn fixed_word_languages_close_symbolic_forms_and_conflicting_paths() {
        for text in [
            r#"(= (str.suffixof x "AA") (str.prefixof x "AA"))"#,
            r#"(= (str.contains "AA" x) (str.prefixof x "AA"))"#,
            r#"(= (str.prefixof "A" (str.at x 0)) (str.prefixof "A" x))"#,
            r#"(= (str.contains "A" (str.++ x x)) (= x ""))"#,
            r#"(= (str.contains (str.replace "A" x "A") y)
                   (str.prefixof y (str.replace "A" x "A")))"#,
            r#"(= (str.contains "A" (str.replace "A" x "")) true)"#,
            r#"(= (str.replace "A" (str.++ x x) x) "A")"#,
            r#"(= (str.replace "A" (str.++ x x) y)
                   (str.++ (str.replace "" x y) "A"))"#,
            r#"(= (str.replace "A" (str.++ y x) "B")
                   (str.replace "A" (str.++ x y) "B"))"#,
            r#"(and (= x "A") (= x "B"))"#,
            r#"(and (= x y) (= y "A") (= x "B"))"#,
        ] {
            let expression = read_all(text)
                .expect("read fixed-word language theorem")
                .pop()
                .expect("one fixed-word language theorem");
            let expected = if text.starts_with("(and") {
                ExactRewriteTerm::Bool(false)
            } else {
                ExactRewriteTerm::Bool(true)
            };
            assert_eq!(exact_rewrite_term(&expression, 0), expected, "{text}");
        }

        for text in [
            r#"(= (str.suffixof x "AB") (str.prefixof x "AB"))"#,
            r#"(= (str.contains "AB" x) (str.prefixof x "AB"))"#,
            r#"(= (str.prefixof "AB" x) (= (str.at x 0) "AB"))"#,
            r#"(= (str.replace "A" (str.++ x y) "B")
                   (str.replace "A" (str.++ x x) "B"))"#,
        ] {
            let expression = read_all(text)
                .expect("read fixed-word language control")
                .pop()
                .expect("one fixed-word language control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(true),
                "{text}"
            );
        }
        let consistent = read_all(r#"(and (= x "A") (not (= x "B")))"#)
            .expect("read consistent equality conjunction")
            .pop()
            .expect("one consistent equality conjunction");
        assert_ne!(
            exact_rewrite_term(&consistent, 0),
            ExactRewriteTerm::Bool(false)
        );

        let mut needles = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                needles.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }
        for subject in [vec![u32::from(b'A')], vec![u32::from(b'B')]] {
            for needle in &needles {
                let doubled_needle = [needle.as_slice(), needle.as_slice()].concat();
                for replacement in &needles {
                    let left = replace_first_code_points(&subject, &doubled_needle, replacement);
                    let right = [
                        replace_first_code_points(&[], needle, replacement).as_slice(),
                        subject.as_slice(),
                    ]
                    .concat();
                    assert_eq!(
                        left, right,
                        "subject={subject:?}, needle={needle:?}, replacement={replacement:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn boolean_ac_word_views_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=3 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for code_point in *b"AB" {
            let subject = vec![u32::from(code_point)];
            for left in &words {
                for right in &words {
                    let left_right = left.iter().chain(right.iter()).copied().collect::<Vec<_>>();
                    let right_left = right.iter().chain(left.iter()).copied().collect::<Vec<_>>();
                    assert_eq!(left_right == subject, right_left == subject);
                    assert_eq!(
                        left_right.contains(&u32::from(code_point)),
                        right_left.contains(&u32::from(code_point))
                    );
                    for replacement in &words {
                        assert_eq!(
                            replace_first_code_points(&subject, &left_right, replacement),
                            replace_first_code_points(&subject, &right_left, replacement),
                            "subject={subject:?}, left={left:?}, right={right:?}, replacement={replacement:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn one_code_point_replace_views_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=3 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }
        let indexof = |subject: &[u32], needle: &[u32], offset: i128| {
            let Ok(offset) = usize::try_from(offset) else {
                return -1;
            };
            if offset > subject.len() {
                return -1;
            }
            if needle.is_empty() {
                return i128::try_from(offset).expect("small offset");
            }
            subject[offset..]
                .windows(needle.len())
                .position(|candidate| candidate == needle)
                .and_then(|index| i128::try_from(offset + index).ok())
                .unwrap_or(-1)
        };

        for base_code in *b"AB" {
            let base = vec![u32::from(base_code)];
            for replacement_code in *b"AB" {
                let replacement = vec![u32::from(replacement_code)];
                for needle in &words {
                    let replaced = replace_first_code_points(&base, needle, &replacement);
                    for offset in -3_i128..=5 {
                        assert_eq!(
                            substr_code_points(&replaced, 1, offset),
                            substr_code_points(
                                &base,
                                i128::try_from(needle.len()).expect("small length"),
                                offset
                            )
                        );
                        for probe_code in *b"AB" {
                            let probe = [u32::from(probe_code)];
                            assert_eq!(
                                substr_code_points(&replaced, offset, offset),
                                substr_code_points(&base, 0, indexof(&probe, needle, offset))
                            );
                        }
                    }
                }
            }
        }

        for source in &words {
            for needle_code in *b"AB" {
                let needle = [u32::from(needle_code)];
                let removed = replace_first_code_points(source, &needle, &[]);
                for replacement_code in *b"AB" {
                    let replacement = [u32::from(replacement_code)];
                    assert_eq!(
                        replace_first_code_points(&[], &removed, &replacement),
                        substr_code_points(&replacement, indexof(&needle, source, 0), 1)
                    );
                }
            }
        }
    }

    #[test]
    fn head_totality_views_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for subject in &words {
            for index in 0_i128..=6 {
                let at = substr_code_points(subject, index, 1);
                let prefix = substr_code_points(subject, 0, index);
                assert_eq!(at.is_empty(), prefix == *subject);
            }
            for index in -2_i128..=6 {
                for length in -2_i128..=6 {
                    let at = substr_code_points(subject, index, 1);
                    assert_eq!(
                        substr_code_points(&at, 0, length),
                        substr_code_points(&substr_code_points(subject, index, length), 0, 1),
                        "subject={subject:?}, index={index}, length={length}"
                    );
                }
            }

            let head = substr_code_points(subject, 0, 1);
            assert_eq!(
                replace_first_code_points(subject, &head, &[]),
                substr_code_points(
                    subject,
                    1,
                    i128::try_from(subject.len()).expect("small word")
                )
            );
            for needle in [[u32::from(b'A')], [u32::from(b'B')]] {
                for replacement in [[u32::from(b'A')], [u32::from(b'B')]] {
                    assert_eq!(
                        substr_code_points(
                            &replace_first_code_points(subject, &needle, &replacement),
                            0,
                            1
                        ),
                        replace_first_code_points(&head, &needle, &replacement),
                        "subject={subject:?}, needle={needle:?}, replacement={replacement:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn head_totality_symbolic_forms_close_and_near_misses_decline() {
        for text in [
            r#"(not (= (= "" (str.at x 0)) (= x "")))"#,
            r#"(not (= (= "" (str.at x 1)) (= x (str.at x 0))))"#,
            r"(not (= (str.substr (str.at x i) 0 n) (str.at (str.substr x i n) 0)))",
            r#"(not (= (str.replace x (str.at x 0) "") (str.substr x 1 (str.len x))))"#,
            r#"(not (= (str.replace (str.at x 0) "A" "B") (str.at (str.replace x "A" "B") 0)))"#,
        ] {
            let expression = read_all(text)
                .expect("read head-totality theorem")
                .pop()
                .expect("one head-totality theorem");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }

        for text in [
            r#"(not (= (= "" (str.at x (- 1))) (= x (str.substr x 0 (- 1)))))"#,
            r"(not (= (str.substr (str.at x i) 1 n) (str.at (str.substr x i n) 0)))",
            r#"(not (= (str.replace x (str.at x 1) "") (str.substr x 1 (str.len x))))"#,
            r#"(not (= (str.replace (str.at x 0) "A" "BC") (str.at (str.replace x "A" "BC") 0)))"#,
            r"(not (= (str.len x) 1))",
        ] {
            let expression = read_all(text)
                .expect("read head-totality control")
                .pop()
                .expect("one head-totality control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }
    }

    #[test]
    fn one_code_point_deletion_languages_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for source in &words {
            for needle_code in *b"AB" {
                let needle = vec![u32::from(needle_code)];
                let deleted = replace_first_code_points(source, &needle, &[]);
                assert_eq!(deleted.is_empty(), source.is_empty() || source == &needle);
                for target_code in *b"AB" {
                    let target = vec![u32::from(target_code)];
                    let mut sources = BTreeSet::new();
                    if needle == target {
                        sources.insert([needle.as_slice(), target.as_slice()].concat());
                    } else {
                        sources.insert(target.clone());
                        sources.insert([needle.as_slice(), target.as_slice()].concat());
                        sources.insert([target.as_slice(), needle.as_slice()].concat());
                    }
                    assert_eq!(deleted == target, sources.contains(source));
                    assert_eq!(
                        deleted.is_empty() || deleted == target,
                        source.is_empty() || source == &needle || sources.contains(source)
                    );
                }
            }
        }
    }

    #[test]
    fn one_code_point_deletion_boundaries_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for needle in &words {
            for base_code in *b"AB" {
                let base = [u32::from(base_code)];
                let deleted = replace_first_code_points(&base, needle, &[]);
                assert_eq!(deleted.starts_with(needle), needle.is_empty());
                assert_eq!(deleted.ends_with(needle), needle.is_empty());
            }
        }
        for source in &words {
            for needle_code in *b"AB" {
                let needle = vec![u32::from(needle_code)];
                let doubled = [needle.as_slice(), needle.as_slice()].concat();
                let deleted = replace_first_code_points(source, &needle, &[]);
                assert_eq!(deleted.starts_with(&needle), source.starts_with(&doubled));
                let replacement = vec![u32::from(if needle_code == b'A' { b'B' } else { b'A' })];
                let replaced = replace_first_code_points(source, &needle, &replacement);
                assert_eq!(deleted.ends_with(&needle), replaced.ends_with(&needle));
            }
        }
    }

    #[test]
    fn boolean_path_facts_close_correlated_empty_replacements() {
        for text in [
            r#"(= (str.replace "" (str.++ x y) x) "")"#,
            r#"(= (str.replace "" (str.++ x y) y) "")"#,
            r#"(= (str.replace "" (str.replace x "" y) x) "")"#,
            r#"(= (str.replace "" (str.replace x "" y) y) "")"#,
        ] {
            let expression = read_all(text)
                .expect("read correlated empty replacement theorem")
                .pop()
                .expect("one correlated empty replacement theorem");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(true),
                "{text}"
            );
        }

        for text in [
            r#"(= (str.replace "" (str.++ x y) "A") "")"#,
            r#"(= (str.replace "" (str.replace x "" y) "A") "")"#,
        ] {
            let expression = read_all(text)
                .expect("read correlated empty replacement control")
                .pop()
                .expect("one correlated empty replacement control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(true),
                "{text}"
            );
        }

        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }
        for left in &words {
            for right in &words {
                let needle = [left.as_slice(), right.as_slice()].concat();
                for replacement in [left, right] {
                    assert_eq!(
                        replace_first_code_points(&[], &needle, replacement),
                        Vec::<u32>::new(),
                        "left={left:?}, right={right:?}, replacement={replacement:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn concat_replace_decomposition_matches_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for _ in 0..3 {
            let prior = words.clone();
            for word in prior {
                for code_point in [u32::from(b'A'), u32::from(b'B')] {
                    let mut extended = word.clone();
                    extended.push(code_point);
                    words.push(extended);
                }
            }
        }

        for prefix in &words {
            for suffix in &words {
                let mut subject = prefix.clone();
                subject.extend(suffix);
                for replacement in &words {
                    for needle in [[u32::from(b'A')], [u32::from(b'B')]] {
                        let expected = replace_first_code_points(&subject, &needle, replacement);
                        let mut decomposed = if prefix.contains(&needle[0]) {
                            replace_first_code_points(prefix, &needle, replacement)
                        } else {
                            prefix.clone()
                        };
                        if prefix.contains(&needle[0]) {
                            decomposed.extend(suffix);
                        } else {
                            decomposed.extend(replace_first_code_points(
                                suffix,
                                &needle,
                                replacement,
                            ));
                        }
                        assert_eq!(decomposed, expected);
                    }
                }
            }
        }

        for needle in &words {
            for suffix in &words {
                let mut subject = needle.clone();
                subject.extend(suffix);
                for replacement in &words {
                    let mut expected = replacement.clone();
                    expected.extend(suffix);
                    assert_eq!(
                        replace_first_code_points(&subject, needle, replacement),
                        expected
                    );
                }
            }
        }
    }

    #[test]
    fn length_dominated_replace_matches_reference_semantics_exhaustively() {
        let symbol = |name: &str| {
            let expression = read_all(name)
                .expect("read symbolic replace argument")
                .pop()
                .expect("one symbolic argument");
            exact_rewrite_term(&expression, 0)
        };
        let subject = symbol("subject");
        let needle_part = symbol("needle_part");
        let replacement = symbol("replacement");
        let needles = [
            exact_rewrite_app("str.++", vec![subject.clone(), needle_part.clone()]),
            exact_rewrite_app(
                "str.replace",
                vec![subject.clone(), needle_part.clone(), subject.clone()],
            ),
        ];
        let rewritten = needles.map(|needle| {
            exact_rewrite_app(
                "str.replace",
                vec![subject.clone(), needle, replacement.clone()],
            )
        });
        let mut words = vec![Vec::new()];
        for _ in 0..2 {
            let prior = words.clone();
            for word in prior {
                for code_point in [u32::from(b'A'), u32::from(b'B')] {
                    let mut extended = word.clone();
                    extended.push(code_point);
                    words.push(extended);
                }
            }
        }

        for subject_word in &words {
            for needle_part_word in &words {
                for replacement_word in &words {
                    let assignments = [
                        (
                            exact_rewrite_app(
                                "=",
                                vec![
                                    subject.clone(),
                                    ExactRewriteTerm::String(subject_word.clone()),
                                ],
                            ),
                            true,
                        ),
                        (
                            exact_rewrite_app(
                                "=",
                                vec![
                                    needle_part.clone(),
                                    ExactRewriteTerm::String(needle_part_word.clone()),
                                ],
                            ),
                            true,
                        ),
                        (
                            exact_rewrite_app(
                                "=",
                                vec![
                                    replacement.clone(),
                                    ExactRewriteTerm::String(replacement_word.clone()),
                                ],
                            ),
                            true,
                        ),
                    ];
                    let mut concat_needle = subject_word.clone();
                    concat_needle.extend(needle_part_word);
                    let self_replace_needle =
                        replace_first_code_points(subject_word, needle_part_word, subject_word);
                    for (expression, concrete_needle) in
                        rewritten.iter().zip([concat_needle, self_replace_needle])
                    {
                        assert_eq!(
                            exact_rewrite_under_assignments(expression, &assignments, 0),
                            ExactRewriteTerm::String(replace_first_code_points(
                                subject_word,
                                &concrete_needle,
                                replacement_word,
                            )),
                            "subject={subject_word:?}, needle={concrete_needle:?}, replacement={replacement_word:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn self_replacement_views_match_reference_semantics_exhaustively() {
        let symbol = |name: &str| {
            let expression = read_all(name)
                .expect("read symbolic self-replacement argument")
                .pop()
                .expect("one symbolic argument");
            exact_rewrite_term(&expression, 0)
        };
        let subject = symbol("subject");
        let needle = symbol("needle");
        let self_replacement = exact_rewrite_app(
            "str.replace",
            vec![subject.clone(), needle.clone(), subject.clone()],
        );
        let at_zero = exact_rewrite_app(
            "str.at",
            vec![self_replacement.clone(), ExactRewriteTerm::Int(0)],
        );
        let contains_subject = exact_rewrite_app(
            "str.contains",
            vec![self_replacement.clone(), subject.clone()],
        );
        let contains_needle = exact_rewrite_app(
            "str.contains",
            vec![self_replacement.clone(), needle.clone()],
        );
        let equals_empty =
            exact_rewrite_equality(&self_replacement, &ExactRewriteTerm::String(Vec::new()));
        let mut words = vec![Vec::new()];
        for _ in 0..4 {
            let prior = words.clone();
            for word in prior {
                for code_point in [u32::from(b'A'), u32::from(b'B')] {
                    let mut extended = word.clone();
                    extended.push(code_point);
                    words.push(extended);
                }
            }
        }

        for subject_word in &words {
            for needle_word in &words {
                let assignments = [
                    (
                        exact_rewrite_app(
                            "=",
                            vec![
                                subject.clone(),
                                ExactRewriteTerm::String(subject_word.clone()),
                            ],
                        ),
                        true,
                    ),
                    (
                        exact_rewrite_app(
                            "=",
                            vec![
                                needle.clone(),
                                ExactRewriteTerm::String(needle_word.clone()),
                            ],
                        ),
                        true,
                    ),
                ];
                let replaced = replace_first_code_points(subject_word, needle_word, subject_word);
                let contains = |subject: &[u32], needle: &[u32]| {
                    needle.is_empty()
                        || subject
                            .windows(needle.len())
                            .any(|candidate| candidate == needle)
                };
                assert_eq!(replaced == *needle_word, subject_word == needle_word);
                assert_eq!(
                    replaced.starts_with(needle_word),
                    subject_word.starts_with(needle_word)
                );
                assert_eq!(
                    needle_word.starts_with(&replaced),
                    needle_word.starts_with(subject_word)
                );
                assert_eq!(
                    replaced.ends_with(needle_word),
                    subject_word.ends_with(needle_word)
                );
                assert_eq!(
                    needle_word.ends_with(&replaced),
                    needle_word.ends_with(subject_word)
                );
                assert_eq!(
                    contains(&replaced, needle_word),
                    contains(subject_word, needle_word)
                );
                assert_eq!(
                    contains(needle_word, &replaced),
                    contains(needle_word, subject_word)
                );
                let expected_at = replaced
                    .first()
                    .copied()
                    .map_or_else(Vec::new, |code_point| vec![code_point]);
                assert_eq!(
                    exact_rewrite_under_assignments(&at_zero, &assignments, 0),
                    ExactRewriteTerm::String(expected_at),
                    "at-zero subject={subject_word:?}, needle={needle_word:?}"
                );
                assert_eq!(
                    exact_rewrite_under_assignments(&contains_subject, &assignments, 0),
                    ExactRewriteTerm::Bool(true),
                    "contains-subject subject={subject_word:?}, needle={needle_word:?}"
                );
                let expected_contains_needle = needle_word.is_empty()
                    || subject_word
                        .windows(needle_word.len())
                        .any(|candidate| candidate == needle_word);
                assert_eq!(
                    exact_rewrite_under_assignments(&contains_needle, &assignments, 0),
                    ExactRewriteTerm::Bool(expected_contains_needle),
                    "contains-needle subject={subject_word:?}, needle={needle_word:?}"
                );
                assert_eq!(
                    exact_rewrite_under_assignments(&equals_empty, &assignments, 0),
                    ExactRewriteTerm::Bool(replaced.is_empty()),
                    "empty subject={subject_word:?}, needle={needle_word:?}"
                );

                for view_word in [Vec::new(), vec![u32::from(b'A')], vec![u32::from(b'B')]] {
                    let view = ExactRewriteTerm::String(view_word.clone());
                    for (head, expected) in [
                        ("str.prefixof", replaced.starts_with(&view_word)),
                        ("str.suffixof", replaced.ends_with(&view_word)),
                        (
                            "str.contains",
                            view_word.is_empty()
                                || replaced
                                    .windows(view_word.len())
                                    .any(|candidate| candidate == view_word),
                        ),
                    ] {
                        let expression = if head == "str.contains" {
                            exact_rewrite_app(head, vec![self_replacement.clone(), view.clone()])
                        } else {
                            exact_rewrite_app(head, vec![view.clone(), self_replacement.clone()])
                        };
                        assert_eq!(
                            exact_rewrite_under_assignments(&expression, &assignments, 0),
                            ExactRewriteTerm::Bool(expected),
                            "head={head}, subject={subject_word:?}, needle={needle_word:?}, view={view_word:?}"
                        );
                    }
                }
            }
        }

        for needle_word in [[u32::from(b'A')], [u32::from(b'B')]] {
            let self_replacement = exact_rewrite_app(
                "str.replace",
                vec![
                    subject.clone(),
                    ExactRewriteTerm::String(needle_word.to_vec()),
                    subject.clone(),
                ],
            );
            for view_word in [Vec::new(), vec![u32::from(b'A')], vec![u32::from(b'B')]] {
                let equality = exact_rewrite_equality(
                    &self_replacement,
                    &ExactRewriteTerm::String(view_word.clone()),
                );
                for subject_word in &words {
                    let assignments = [(
                        exact_rewrite_app(
                            "=",
                            vec![
                                subject.clone(),
                                ExactRewriteTerm::String(subject_word.clone()),
                            ],
                        ),
                        true,
                    )];
                    let replaced =
                        replace_first_code_points(subject_word, &needle_word, subject_word);
                    assert_eq!(
                        exact_rewrite_under_assignments(&equality, &assignments, 0),
                        ExactRewriteTerm::Bool(replaced == view_word),
                        "equality subject={subject_word:?}, needle={needle_word:?}, view={view_word:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn self_replacement_and_boolean_equivalence_forms_normalize_conservatively() {
        for text in [
            r"(not (= (= x (str.replace y x y)) (= x y)))",
            r"(not (= (str.prefixof x (str.replace y x y)) (str.prefixof x y)))",
            r"(not (= (str.suffixof x (str.replace y x y)) (str.suffixof x y)))",
            r"(not (= (str.contains x (str.replace y x y)) (str.contains x y)))",
            r"(not (= (str.prefixof (str.replace x y x) y) (str.prefixof x y)))",
            r"(not (= (str.suffixof (str.replace x y x) y) (str.suffixof x y)))",
            r#"(not (= (= "" (str.replace x "A" y)) (str.prefixof x (str.replace "" y "A"))))"#,
            r#"(not (= (str.contains "" (str.replace x "A" y)) (str.prefixof x (str.replace "" y "A"))))"#,
            r#"(not (= (= "" (str.replace x "B" y)) (str.prefixof x (str.replace "" y "B"))))"#,
            r#"(not (= (str.contains "" (str.replace x "B" y)) (str.prefixof x (str.replace "" y "B"))))"#,
            r#"(not (= (str.contains (str.replace "A" x "") x) (= x "")))"#,
            r#"(not (= (str.contains (str.replace "B" x "") x) (= x "")))"#,
        ] {
            let expression = read_all(text)
                .expect("read self-replacement/Boolean theorem")
                .pop()
                .expect("one self-replacement/Boolean theorem");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }

        for text in [
            r"(not (= (str.prefixof z (str.replace y x y)) (str.prefixof z y)))",
            r"(not (= (= y (str.replace y x y)) (= x y)))",
            r#"(not (= (= x "") (= x "A")))"#,
        ] {
            let expression = read_all(text)
                .expect("read self-replacement/Boolean control")
                .pop()
                .expect("one self-replacement/Boolean control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }
    }

    #[test]
    fn one_code_point_prefixed_self_needles_normalize_conservatively() {
        for text in [
            r#"(not (= (str.replace (str.++ "A" x) x "A") (str.++ "A" "A")))"#,
            r#"(not (= (str.replace (str.++ "A" x) x "") "A"))"#,
            r#"(not (= (str.replace (str.++ "B" x) x "B") (str.++ "B" "B")))"#,
            r#"(not (= (str.replace (str.++ "B" x) x "") "B"))"#,
        ] {
            let expression = read_all(text)
                .expect("read one-code-point prefixed-self theorem")
                .pop()
                .expect("one theorem");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }

        for text in [
            // A multi-code-point prefix may contain an earlier overlapping x.
            r#"(not (= (str.replace (str.++ "AB" x) x "") "AB"))"#,
            r#"(not (= (str.replace (str.++ "AB" x) x "AB") "ABAB"))"#,
            // A different replacement does not commute with an overlap.
            r#"(not (= (str.replace (str.++ "A" x) x "B") "AB"))"#,
        ] {
            let expression = read_all(text)
                .expect("read prefixed-self near miss")
                .pop()
                .expect("one control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }
    }

    #[test]
    fn one_code_point_prefixed_self_needles_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=6 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for prefix in [[u32::from(b'A')], [u32::from(b'B')]] {
            for needle in &words {
                let subject = [prefix.as_slice(), needle].concat();
                assert_eq!(
                    replace_first_code_points(&subject, needle, &[]),
                    prefix,
                    "delete prefix={prefix:?}, needle={needle:?}"
                );
                assert_eq!(
                    replace_first_code_points(&subject, needle, &prefix),
                    prefix.repeat(2),
                    "replace prefix={prefix:?}, needle={needle:?}"
                );
            }
        }
    }

    #[test]
    fn singleton_replace_inverse_closes_symbolic_families_conservatively() {
        for text in [
            r#"(not (= (str.replace "A" (str.replace x y x) x) "A"))"#,
            r#"(not (= (str.replace "A" (str.replace x y "B") x) "A"))"#,
            r#"(not (= (str.replace "A" (str.replace x "A" "B") y) (str.++ (str.replace "" x y) "A")))"#,
            r#"(not (= (= "A" (str.replace x "A" "B")) false))"#,
            r#"(not (= (str.contains "A" (str.replace x "A" "B")) (= x "")))"#,
            r#"(not (= (str.contains "B" (str.replace x "A" ""))
                        (str.contains "A" (str.replace x "B" ""))))"#,
        ] {
            let expression = read_all(text)
                .expect("read singleton inverse theorem")
                .pop()
                .expect("one singleton inverse theorem");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }

        for text in [
            // Replacing a larger self-containing needle can change the source.
            r#"(not (= (str.replace x (str.replace y "A" y) y) x))"#,
            r#"(not (= (str.replace x (str.replace y "B" y) y) x))"#,
            r"(not (= (str.replace (str.replace x y x) y x)
                       (str.replace x y (str.replace x y x))))",
            r#"(not (= (str.replace (str.replace x y x) y "")
                        (str.replace x y (str.replace x y ""))))"#,
            // The inverse rule is deliberately restricted to a fixed singleton.
            r#"(not (= (str.replace x y z) "AB"))"#,
            // A different singleton target is not an identity.
            r#"(not (= (str.replace "A" (str.replace x y x) x) "B"))"#,
        ] {
            let expression = read_all(text)
                .expect("read singleton inverse control")
                .pop()
                .expect("one singleton inverse control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }
    }

    #[test]
    fn one_code_point_path_normalization_closes_symbolic_families_conservatively() {
        for text in [
            r#"(not (= (str.replace "A" (str.substr "A" 0 z) "") (str.substr "A" 0 (- 1 z))))"#,
            r#"(not (= (str.replace "" (str.substr "A" 0 z) x) (str.replace "" (str.substr x 0 z) x)))"#,
            r#"(not (= (str.replace "A" (str.++ x "A") x) (str.substr "A" 0 (str.len x))))"#,
            r#"(not (= (str.replace "" (str.replace "" x "A") "B") (str.substr "B" 0 (str.len x))))"#,
            r#"(not (= (= x (str.replace x "A" "")) (= x (str.replace x "A" "B"))))"#,
            r#"(not (= (= x (str.replace x "B" "")) (= x (str.replace x "B" "A"))))"#,
            r#"(not (= (not (str.contains x "A")) (= x (str.replace x "A" "B"))))"#,
            r#"(not (= (not (str.contains x "B")) (= x (str.replace x "B" "A"))))"#,
            r#"(not (= (str.prefixof "A" (str.replace x "A" "B")) false))"#,
            r#"(not (= (str.prefixof "B" (str.replace x "A" "B"))
                        (str.prefixof "A" (str.replace x "B" "A"))))"#,
            r#"(not (= (str.prefixof "B" (str.replace x "B" "A")) false))"#,
            r#"(not (= (str.replace x (str.replace x "A" "B") "A")
                        (str.replace x (str.replace x "A" x) "A")))"#,
            r#"(not (= (str.replace x (str.replace x "B" "A") "B")
                        (str.replace x (str.replace x "B" x) "B")))"#,
            r#"(not (= (str.replace "A" (str.++ x "A") "") (str.substr "A" 0 (str.len x))))"#,
            r#"(not (= (str.replace "B" (str.substr "B" 0 z) "") (str.substr "B" 0 (- 1 z))))"#,
            r#"(not (= (str.replace "B" (str.++ x "B") x) (str.substr "B" 0 (str.len x))))"#,
            r#"(not (= (str.replace "B" (str.++ x "B") "") (str.substr "B" 0 (str.len x))))"#,
            r#"(not (= (str.replace "" (str.substr "A" 0 z) "A") (str.substr "A" 0 (- 1 z))))"#,
            r#"(not (= (str.replace "" (str.substr "A" 0 z) "B") (str.substr "B" 0 (- 1 z))))"#,
            r#"(not (= (str.replace "" (str.substr "B" 0 z) x) (str.replace "" (str.substr x 0 z) x)))"#,
        ] {
            let expression = read_all(text)
                .expect("read one-code-point theorem")
                .pop()
                .expect("one theorem");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }

        for text in [
            r#"(not (= (= x (str.replace x "A" "")) (= x (str.replace x "B" ""))))"#,
            r#"(not (= (str.prefixof "A" (str.replace x "A" "A")) false))"#,
            r#"(not (= (str.replace "A" (str.substr "A" 1 z) "") (str.substr "A" 0 (- 1 z))))"#,
            r#"(not (= (str.replace "A" (str.++ x "A") x) (str.substr "A" 0 (str.len y))))"#,
        ] {
            let expression = read_all(text)
                .expect("read one-code-point control")
                .pop()
                .expect("one control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }
    }

    #[test]
    fn replacement_preservation_matches_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for subject in &words {
            for needle in &words {
                for value in &words {
                    let replacement = ExactRewriteTerm::App(
                        "str.replace".to_owned(),
                        vec![
                            ExactRewriteTerm::String(subject.clone()),
                            ExactRewriteTerm::String(needle.clone()),
                            ExactRewriteTerm::String(value.clone()),
                        ],
                    );
                    assert_eq!(
                        exact_rewrite_replace_preserves_subject(
                            &replacement,
                            &ExactRewriteTerm::String(subject.clone()),
                        ),
                        Some(ExactRewriteTerm::Bool(
                            replace_first_code_points(subject, needle, value) == *subject
                        )),
                        "subject={subject:?}, needle={needle:?}, value={value:?}"
                    );
                }
            }
        }
    }

    #[test]
    fn nested_replacement_needles_match_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=8 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for subject in &words {
            for (needle, alternate) in [(b'A', b'B'), (b'B', b'A')] {
                let needle = [u32::from(needle)];
                let alternate = [u32::from(alternate)];
                let changed_needle = replace_first_code_points(subject, &needle, &alternate);
                let expanded_needle = replace_first_code_points(subject, &needle, subject);
                assert_eq!(
                    replace_first_code_points(subject, &changed_needle, &needle),
                    replace_first_code_points(subject, &expanded_needle, &needle),
                    "subject={subject:?}, needle={needle:?}, alternate={alternate:?}"
                );
            }
        }
    }

    #[test]
    fn singleton_prefix_replacement_matches_reference_semantics_exhaustively() {
        let mut words = vec![String::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| if bits & (1 << shift) == 0 { 'A' } else { 'B' })
                        .collect(),
                );
            }
        }
        for subject in &words {
            for (needle, replacement) in [('A', 'B'), ('B', 'A')] {
                for probe in ['A', 'B', 'C'] {
                    let text = format!(
                        r#"(str.prefixof "{probe}" (str.replace "{subject}" "{needle}" "{replacement}"))"#
                    );
                    let expression = read_all(&text)
                        .expect("read singleton-prefix expression")
                        .pop()
                        .expect("one expression");
                    let expected = subject
                        .replacen(needle, &replacement.to_string(), 1)
                        .starts_with(probe);
                    assert_eq!(
                        exact_rewrite_term(&expression, 0),
                        ExactRewriteTerm::Bool(expected),
                        "{text}"
                    );
                }
            }
        }
    }

    #[test]
    fn prefix_substring_emptiness_matches_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }
        for subject in &words {
            for length in -4_i128..=6 {
                let substring = ExactRewriteTerm::App(
                    "str.substr".to_owned(),
                    vec![
                        ExactRewriteTerm::String(subject.clone()),
                        ExactRewriteTerm::Int(0),
                        ExactRewriteTerm::Int(length),
                    ],
                );
                assert_eq!(
                    exact_rewrite_prefix_substr_emptiness(
                        &substring,
                        &ExactRewriteTerm::String(Vec::new()),
                    ),
                    Some(ExactRewriteTerm::Bool(
                        substr_code_points(subject, 0, length).is_empty()
                    )),
                    "subject={subject:?}, length={length}"
                );
            }
        }
    }

    #[test]
    fn symbolic_from_int_views_close_decimal_families_conservatively() {
        for text in [
            r#"(not (= (str.contains "B" (str.from_int z)) (str.contains "A" (str.from_int z))))"#,
            r#"(not (= (= "" (str.from_int z)) (str.contains "A" (str.from_int z))))"#,
            r#"(not (= (str.contains "" (str.from_int z)) (str.contains "A" (str.from_int z))))"#,
            r#"(not (= (str.substr (str.from_int z) z z) ""))"#,
            r#"(not (= (str.replace "" (str.from_int z) "A") (str.substr "A" 0 (- 0 z))))"#,
            r#"(not (= (str.replace "" (str.from_int z) "B") (str.substr "B" 0 (- 0 z))))"#,
        ] {
            let expression = read_all(text)
                .expect("read symbolic from-int theorem")
                .pop()
                .expect("one theorem");
            assert_eq!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }

        for text in [
            r#"(not (= (str.contains "1" (str.from_int z)) (str.contains "A" (str.from_int z))))"#,
            r"(not (= (str.contains (str.from_int z) x) (str.suffixof x (str.from_int z))))",
            r#"(not (= (str.substr (str.from_int z) 0 z) ""))"#,
            r#"(not (= (str.replace "" (str.from_int z) "A") (str.substr "A" 0 (- 1 z))))"#,
        ] {
            let expression = read_all(text)
                .expect("read symbolic from-int control")
                .pop()
                .expect("one control");
            assert_ne!(
                exact_rewrite_term(&expression, 0),
                ExactRewriteTerm::Bool(false),
                "{text}"
            );
        }
    }

    #[test]
    fn symbolic_from_int_views_match_reference_semantics_exhaustively() {
        let values = (-128_i128..=2_048)
            .chain([i128::MIN, -1, 0, 1, i128::MAX])
            .collect::<BTreeSet<_>>();
        for value in values {
            let decimal = decimal_code_points(value);
            let from_int = ExactRewriteTerm::App(
                "str.from_int".to_owned(),
                vec![ExactRewriteTerm::Int(value)],
            );
            assert_eq!(
                exact_from_int_empty_condition(&from_int),
                Some(ExactRewriteTerm::Bool(decimal.is_empty())),
                "value={value}"
            );
            for fixed in [Vec::new(), vec![u32::from(b'A')], vec![u32::from(b'B')]] {
                assert_eq!(
                    exact_rewrite_app(
                        "str.contains",
                        vec![ExactRewriteTerm::String(fixed.clone()), from_int.clone(),],
                    ),
                    ExactRewriteTerm::Bool(
                        decimal.is_empty()
                            || fixed
                                .windows(decimal.len())
                                .any(|candidate| candidate == decimal),
                    ),
                    "value={value}, fixed={fixed:?}"
                );
            }
            let replacement = vec![u32::from(b'A')];
            assert_eq!(
                exact_rewrite_app(
                    "str.replace",
                    vec![
                        ExactRewriteTerm::String(Vec::new()),
                        from_int.clone(),
                        ExactRewriteTerm::String(replacement.clone()),
                    ],
                ),
                ExactRewriteTerm::String(replace_first_code_points(&[], &decimal, &replacement,)),
                "value={value}"
            );
            assert_eq!(
                exact_rewrite_app(
                    "str.substr",
                    vec![
                        from_int,
                        ExactRewriteTerm::Int(value),
                        ExactRewriteTerm::Int(value),
                    ],
                ),
                ExactRewriteTerm::String(substr_code_points(&decimal, value, value)),
                "value={value}"
            );
        }
    }

    #[test]
    fn singleton_replace_inverse_matches_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }

        for target in [vec![u32::from(b'A')], vec![u32::from(b'B')]] {
            for subject in &words {
                for needle in &words {
                    for replacement in &words {
                        let replace = ExactRewriteTerm::App(
                            "str.replace".to_owned(),
                            vec![
                                ExactRewriteTerm::String(subject.clone()),
                                ExactRewriteTerm::String(needle.clone()),
                                ExactRewriteTerm::String(replacement.clone()),
                            ],
                        );
                        let characterized = exact_rewrite_replace_singleton_equality(
                            &replace,
                            &ExactRewriteTerm::String(target.clone()),
                        )
                        .expect("a singleton target must be characterized");
                        assert_eq!(
                            characterized,
                            ExactRewriteTerm::Bool(
                                replace_first_code_points(subject, needle, replacement) == target
                            ),
                            "subject={subject:?}, needle={needle:?}, replacement={replacement:?}, target={target:?}"
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn pinned_word_evaluator_matches_reference_semantics_exhaustively() {
        let mut words = vec![Vec::new()];
        for length in 1..=4 {
            for bits in 0..(1_usize << length) {
                words.push(
                    (0..length)
                        .map(|shift| u32::from(if bits & (1 << shift) == 0 { b'A' } else { b'B' }))
                        .collect(),
                );
            }
        }
        let symbol = SExpr::Atom("s".to_owned());
        let nodes = vec![symbol];
        let parent = [0];

        for subject in &words {
            let values = [Some(subject.clone())];
            for index in -2_i128..=6 {
                let at = read_all(&format!("(str.at s {index})"))
                    .expect("read at")
                    .pop()
                    .expect("one at");
                assert_eq!(
                    eval_pinned_word_semantics(&at, &nodes, &parent, &values, 0),
                    Some(substr_code_points(subject, index, 1))
                );
                for length in -2_i128..=6 {
                    let substr = read_all(&format!("(str.substr s {index} {length})"))
                        .expect("read substr")
                        .pop()
                        .expect("one substr");
                    assert_eq!(
                        eval_pinned_word_semantics(&substr, &nodes, &parent, &values, 0),
                        Some(substr_code_points(subject, index, length))
                    );
                }
            }
            let tail = read_all("(str.substr s 1 (- (str.len s) 1))")
                .expect("read length-relative tail")
                .pop()
                .expect("one length-relative tail");
            assert_eq!(
                eval_pinned_word_semantics(&tail, &nodes, &parent, &values, 0),
                Some(substr_code_points(
                    subject,
                    1,
                    i128::try_from(subject.len()).expect("small length") - 1,
                ))
            );
            let rebuilt =
                read_all("(str.++ (str.substr s 0 1) (str.substr s 1 (- (str.len s) 1)))")
                    .expect("read length-relative reconstruction")
                    .pop()
                    .expect("one length-relative reconstruction");
            assert_eq!(
                eval_pinned_word_semantics(&rebuilt, &nodes, &parent, &values, 0),
                Some(subject.clone())
            );
            for needle in &words[..7] {
                for replacement in &words[..7] {
                    let needle_text: String =
                        needle.iter().filter_map(|&cp| char::from_u32(cp)).collect();
                    let replacement_text: String = replacement
                        .iter()
                        .filter_map(|&cp| char::from_u32(cp))
                        .collect();
                    let replace = read_all(&format!(
                        "(str.replace s \"{needle_text}\" \"{replacement_text}\")"
                    ))
                    .expect("read replace")
                    .pop()
                    .expect("one replace");
                    assert_eq!(
                        eval_pinned_word_semantics(&replace, &nodes, &parent, &values, 0),
                        Some(replace_first_code_points(subject, needle, replacement))
                    );
                }
            }
        }
    }

    #[test]
    fn pinned_source_operations_refute_only_concrete_conflicts() {
        for script in [
            r#"(declare-const s String)
(assert (= s "abc"))
(assert (= (str.at s 1) "c"))
(check-sat)"#,
            r#"(declare-const s String)
(assert (= s "abc"))
(assert (= (str.substr s 1 1) "c"))
(check-sat)"#,
            r#"(declare-const s String)
(assert (= s "xy"))
(assert (str.prefixof s "abc"))
(check-sat)"#,
            r#"(declare-const s String)
(assert (= s "xy"))
(assert (str.suffixof s "abc"))
(check-sat)"#,
        ] {
            let expressions = read_all(script).expect("read pinned conflict");
            assert!(
                source_string_semantic_facts(&expressions).conflict,
                "{script}"
            );
        }

        for script in [
            r#"(declare-const s String)
(assert (= s "abc"))
(assert (= (str.at s 1) "b"))
(check-sat)"#,
            r#"(declare-const s String)
(assert (= (str.at s 1) "c"))
(check-sat)"#,
            r#"(declare-const s String)
(assert (= s "xy"))
(assert (not (str.prefixof s "abc")))
(check-sat)"#,
            r#"(declare-const s String)
(assert (= s "xy"))
(assert (not (str.suffixof s "abc")))
(check-sat)"#,
        ] {
            let expressions = read_all(script).expect("read pinned control");
            assert!(
                !source_string_semantic_facts(&expressions).conflict,
                "{script}"
            );
        }
    }

    #[test]
    fn top_level_boolean_aliases_expose_only_forced_equality_conflicts() {
        let contradictory = read_all(
            r#"(declare-const s String)
(declare-const empty_path Bool)
(declare-const nonempty_path Bool)
(assert (= empty_path (= s "")))
(assert empty_path)
(assert (= nonempty_path (not (= s ""))))
(assert nonempty_path)
(check-sat)"#,
        )
        .expect("read contradictory alias path");
        assert!(source_string_semantic_facts(&contradictory).conflict);

        for script in [
            r#"(declare-const s String)
(declare-const path Bool)
(assert (= path (not (= s ""))))
(assert path)
(check-sat)"#,
            r#"(declare-const s String)
(declare-const left Bool)
(declare-const right Bool)
(assert (= left (= s "long-enough-to-exceed-the-packed-bound")))
(assert left)
(assert (= right (not (= s ""))))
(assert right)
(check-sat)"#,
        ] {
            let expressions = read_all(script).expect("read satisfiable alias control");
            assert!(
                !source_string_semantic_facts(&expressions).conflict,
                "{script}"
            );
        }
    }

    #[test]
    fn boolean_alias_conflict_survives_long_literal_capacity_fallback() {
        let script = parse_script(
            r#"(set-logic QF_SLIA)
(declare-const s String)
(declare-const unrelated String)
(declare-const empty_path Bool)
(declare-const nonempty_path Bool)
(assert (= unrelated "long-enough-to-exceed-the-packed-bound"))
(assert (= empty_path (= s "")))
(assert empty_path)
(assert (= nonempty_path (not (= s ""))))
(assert nonempty_path)
(check-sat)"#,
        )
        .expect("exact contradiction should survive the packed capacity decline");
        assert!(script.word_only_fallback.is_some());
        assert!(script.source_string_semantic_unsat);
    }

    #[test]
    fn aliased_length_and_emptiness_paths_share_one_exact_boundary() {
        for script in [
            r#"(declare-const s String)
(declare-const n Int)
(declare-const nonempty Bool)
(declare-const no_positive_length Bool)
(assert (= nonempty (not (= s ""))))
(assert nonempty)
(assert (= n (str.len s)))
(assert (= no_positive_length (not (< 0 n))))
(assert no_positive_length)
(check-sat)"#,
            r#"(declare-const s String)
(declare-const n Int)
(declare-const at_least_four Bool)
(assert (= s ""))
(assert (= n (str.len s)))
(assert (= at_least_four (not (< n 4))))
(assert at_least_four)
(check-sat)"#,
        ] {
            let expressions = read_all(script).expect("read contradictory length alias path");
            assert!(
                source_string_semantic_facts(&expressions).conflict,
                "{script}"
            );
        }

        for script in [
            r#"(declare-const s String)
(declare-const nonempty Bool)
(assert (= nonempty (< 0 (str.len s))))
(assert nonempty)
(assert (not (= s "")))
(check-sat)"#,
            r#"(declare-const s String)
(declare-const empty Bool)
(assert (= empty (<= (str.len s) 0)))
(assert empty)
(assert (= s ""))
(check-sat)"#,
        ] {
            let expressions = read_all(script).expect("read satisfiable length alias control");
            assert!(
                !source_string_semantic_facts(&expressions).conflict,
                "{script}"
            );
        }
    }

    #[test]
    fn selected_string_path_propagates_nonempty_concat_conflicts() {
        for script in [
            r#"(declare-const input String)
(declare-const prefix String)
(declare-const position Int)
(declare-const selected Bool)
(assert (= input ""))
(assert (= selected (not (= position (- 1)))))
(assert (ite selected
  (= input (str.++ prefix "GASO="))
  (= position (- 1))))
(assert (< (- 1) position))
(check-sat)"#,
            r#"(declare-const input String)
(declare-const empty-view String)
(declare-const branch-view String)
(declare-const prefix String)
(declare-const position Int)
(declare-const selected Bool)
(declare-const empty Bool)
(declare-const positive Bool)
(assert (= empty-view (str.++ "" input)))
(assert (= empty (= "" empty-view)))
(assert empty)
(assert (= branch-view (str.++ "" input)))
(assert (= selected (not (= position (- 1)))))
(assert (ite selected
  (= branch-view (str.++ prefix "GASO="))
  (= position (- 1))))
(assert (= positive (< (- 1) position)))
(assert positive)
(check-sat)"#,
        ] {
            let contradictory = read_all(script).expect("read selected concat conflict");
            assert!(
                source_string_semantic_facts(&contradictory).conflict,
                "{script}"
            );
        }

        for script in [
            r#"(declare-const input String)
(declare-const prefix String)
(declare-const position Int)
(declare-const selected Bool)
(assert (= input ""))
(assert (= position (- 1)))
(assert (= selected (not (= position (- 1)))))
(assert (ite selected
  (= input (str.++ prefix "GASO="))
  (= position (- 1))))
(check-sat)"#,
            r#"(declare-const input String)
(declare-const prefix String)
(declare-const position Int)
(declare-const selected Bool)
(assert (= input "GASO="))
(assert (= prefix ""))
(assert (= selected (not (= position (- 1)))))
(assert (ite selected
  (= input (str.++ prefix "GASO="))
  (= position (- 1))))
(assert (< (- 1) position))
(check-sat)"#,
        ] {
            let expressions = read_all(script).expect("read selected concat control");
            assert!(
                !source_string_semantic_facts(&expressions).conflict,
                "{script}"
            );
        }
    }

    #[test]
    fn fixed_segments_at_exact_relative_offsets_must_overlap_consistently() {
        let contradictory = read_all(
            r#"(declare-const source String)
(declare-const prefix String)
(declare-const suffix String)
(declare-const before String)
(declare-const after String)
(declare-const first Int)
(declare-const second Int)
(declare-const active Bool)
(assert (= source (str.++ prefix "ABC" suffix)))
(assert (= first (str.len prefix)))
(assert (= second (+ first 1)))
(assert (= source (str.++ before "X" after)))
(assert (= second (str.len before)))
(assert (= active (not (= source ""))))
(assert active)
(check-sat)"#,
        )
        .expect("read conflicting fixed overlap");
        assert!(source_string_semantic_facts(&contradictory).conflict);

        for script in [
            r#"(declare-const source String)
(declare-const prefix String)
(declare-const suffix String)
(declare-const before String)
(declare-const after String)
(declare-const first Int)
(declare-const second Int)
(declare-const active Bool)
(assert (= source (str.++ prefix "ABC" suffix)))
(assert (= first (str.len prefix)))
(assert (= second (+ first 1)))
(assert (= source (str.++ before "B" after)))
(assert (= second (str.len before)))
(assert (= active (not (= source ""))))
(assert active)
(check-sat)"#,
            r#"(declare-const source String)
(declare-const prefix String)
(declare-const suffix String)
(declare-const before String)
(declare-const after String)
(declare-const first Int)
(declare-const second Int)
(declare-const active Bool)
(assert (= source (str.++ prefix "ABC" suffix)))
(assert (= first (str.len prefix)))
(assert (= second (+ first 3)))
(assert (= source (str.++ before "X" after)))
(assert (= second (str.len before)))
(assert (= active (not (= source ""))))
(assert active)
(check-sat)"#,
        ] {
            let expressions = read_all(script).expect("read satisfiable fixed overlap control");
            assert!(
                !source_string_semantic_facts(&expressions).conflict,
                "{script}"
            );
        }
    }

    #[test]
    fn length_emptiness_consequences_are_exhaustively_sound_at_small_thresholds() {
        use ExactLengthEmptiness::{Conflict, Requires};
        use ExactRewriteTerm::{App, Int, Opaque};

        let subject = Opaque(SExpr::Atom("s".to_owned()));
        let length = App("str.len".to_owned(), vec![subject.clone()]);
        for relation in ["=", "<", "<=", ">", ">="] {
            for bound in -2_i128..=3 {
                let condition = App(relation.to_owned(), vec![length.clone(), Int(bound)]);
                for required in [false, true] {
                    let consequence = exact_length_emptiness_consequence(&condition, required, &[]);
                    for length in 0_i128..=6 {
                        let actual = match relation {
                            "=" => length == bound,
                            "<" => length < bound,
                            "<=" => length <= bound,
                            ">" => length > bound,
                            ">=" => length >= bound,
                            _ => unreachable!(),
                        };
                        if actual != required {
                            continue;
                        }
                        match &consequence {
                            Some(Conflict) => {
                                panic!("{length} satisfies len {relation} {bound} = {required}")
                            }
                            Some(Requires {
                                subject: derived,
                                empty,
                            }) => {
                                assert_eq!(derived, &subject);
                                assert_eq!(*empty, length == 0);
                            }
                            None => {}
                        }
                    }
                }
            }
        }
    }

    fn assert_boolean_path_conflicts(scripts: &[&str], expected: bool) {
        for script in scripts {
            let expressions = read_all(script).expect("read Boolean path fixture");
            assert_eq!(
                guaranteed_boolean_literal_conflict(&guaranteed_top_level_conjuncts(&expressions)),
                expected,
                "{script}"
            );
        }
    }

    #[test]
    fn contradictory_boolean_path_literals_are_exact_and_fail_closed() {
        assert_boolean_path_conflicts(
            &[
                r#"(declare-const s String)
(assert (not (= (ite (str.contains s "A") 1 0) 0)))
(assert (= (ite (str.contains s "A") 1 0) 0))
(check-sat)"#,
                r#"(declare-const s String)
(assert (str.contains s "A"))
(assert (not (str.contains s "A")))
(check-sat)"#,
                r#"(declare-const s String)
(assert (str.contains s "A"))
(assert (= (str.indexof s "A" 0) (- 1)))
(check-sat)"#,
                r#"(declare-const s String)
(assert (not (= (ite (not (= (str.indexof s "A" 0) (- 1))) 1 0) 0)))
(assert (not (str.contains s "A")))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.len s) 0))
(assert (not (= (str.indexof s "A" 0) (- 1))))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.len s) 0))
(assert (= (str.at s 7) "A"))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.at s 7) "A"))
(assert (not (str.contains s "A")))
(check-sat)"#,
            ],
            true,
        );

        assert_boolean_path_conflicts(
            &[
                r#"(declare-const s String)
(assert (not (= (ite (str.contains s "A") 1 0) 0)))
(assert (= (ite (str.contains s "B") 1 0) 0))
(check-sat)"#,
                r#"(declare-const s String)
(assert (str.contains s "A"))
(assert (not (not (str.contains s "A"))))
(check-sat)"#,
                r#"(declare-const s String)
(assert (str.contains s "A"))
(assert (= (str.indexof s "B" 0) (- 1)))
(check-sat)"#,
                r#"(declare-const s String)
(assert (str.contains s "A"))
(assert (= (str.indexof s "A" 1) (- 1)))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.len s) 0))
(assert (= (str.indexof s "A" 0) (- 1)))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.at s 7) "A"))
(assert (not (str.contains s "B")))
(check-sat)"#,
                r#"(declare-const s String)
(assert (not (= (str.at s 7) "A")))
(assert (not (str.contains s "A")))
(check-sat)"#,
            ],
            false,
        );
    }

    #[test]
    fn one_code_point_boundary_paths_are_exact_and_fail_closed() {
        assert_boolean_path_conflicts(
            &[
                r#"(declare-const s String)
(assert (= (str.len (str.substr s 0 (- (str.len s) 1))) 0))
(assert (= (str.at s 0) "A"))
(assert (not (= (str.at s (- (str.len s) 1)) "A")))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.len (str.substr s 0 (- (str.len s) 1))) 0))
(assert (= (str.at s 0) "A"))
(assert (= (str.at s (- (str.len s) 1)) "B"))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.at (str.substr s 0 (- (str.len s) 1)) 0) "A"))
(assert (not (= (str.at s 0) "A")))
(check-sat)"#,
                r#"(declare-const s String)
(assert (not (= (str.len (str.substr s 0 (- (str.len s) 1))) 0)))
(assert (not (= (str.at (str.substr s 0 (- (str.len s) 1)) 0) "A")))
(assert (= (str.at s 0) "A"))
(check-sat)"#,
            ],
            true,
        );

        assert_boolean_path_conflicts(
            &[
                r#"(declare-const s String)
(assert (= (str.len (str.substr s 0 (- (str.len s) 1))) 0))
(assert (= (str.at s 0) "A"))
(assert (not (= (str.at s (- (str.len s) 1)) "B")))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.len (str.substr s 0 (- (str.len s) 1))) 0))
(assert (not (= (str.at s 0) "A")))
(assert (not (= (str.at s (- (str.len s) 1)) "A")))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.len (str.substr s 0 (- (str.len s) 2))) 0))
(assert (= (str.at s 0) "A"))
(assert (= (str.at s (- (str.len s) 1)) "B"))
(check-sat)"#,
                r#"(declare-const s String)
(assert (not (= (str.at (str.substr s 0 (- (str.len s) 1)) 0) "A")))
(assert (= (str.at s 0) "A"))
(check-sat)"#,
                r#"(declare-const s String)
(assert (= (str.at (str.substr s 1 (- (str.len s) 1)) 0) "A"))
(assert (not (= (str.at s 0) "A")))
(check-sat)"#,
            ],
            false,
        );
    }

    #[test]
    fn braced_escape_decodes_to_code_point() {
        // `\u{62}` is U+0062 = 'b', a single code point — not six raw bytes.
        assert_eq!(decode_string_code_points("\\u{62}"), Some(vec![0x62]));
        assert_eq!(decode_string_code_points("\\u{0a}"), Some(vec![0x0a]));
        // Equal to the plain letter.
        assert_eq!(
            decode_string_code_points("\\u{62}"),
            decode_string_code_points("b")
        );
    }

    #[test]
    fn four_digit_escape_decodes_to_code_point() {
        assert_eq!(decode_string_code_points("\\u0062"), Some(vec![0x62]));
        assert_eq!(
            decode_string_code_points("a\\u0062c"),
            Some(vec![0x61, 0x62, 0x63])
        );
    }

    #[test]
    fn non_escape_backslash_is_literal() {
        // A `\` not starting a valid `\u` escape is a literal backslash (Z3 semantics).
        assert_eq!(
            decode_string_code_points("\\n"),
            Some(vec![0x5c, u32::from(b'n')])
        );
        assert_eq!(decode_string_code_points("\\"), Some(vec![0x5c]));
    }

    #[test]
    fn code_point_above_max_declines() {
        // U+30000 exceeds the SMT-LIB maximum U+2FFFF — decline (None), never truncate.
        assert_eq!(decode_string_code_points("\\u{30000}"), None);
    }
}
