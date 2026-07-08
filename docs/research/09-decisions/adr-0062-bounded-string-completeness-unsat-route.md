# ADR-0062: Bounded-completeness UNSAT route for the packed-BV string model

Status: accepted
Date: 2026-07-08

## Context

The bounded packed-BV string model (ADR-0029) is incomplete on **two**
independent axes — the int-blast width (≤ 32 bits) and the per-symbol string
length (`STRING_MAX_LEN = 8`, `STRING_BOUND_CAP = 16`). When the bounded
encoding of a string query is UNSAT but any `Int` was blasted, the combined
solver conservatively downgrades to
`Unknown("no model within the bounded integer width N; widen the bound")`
(`combined.rs`) rather than claim `unsat` — because a longer string or a wider
int might satisfy the query in the real theory. This left a class of genuinely
UNSAT bounded string queries undecided, most visibly the two cvc5 `update-ex2`
targets that task #74's `str.update` encoding produced but the int-blast could
not refute.

The question: **when may a bounded string `unsat` be trusted as a real
`unsat`?** It must be closed now because getting it wrong is a wrong-unsat (the
worst bug class), and a tempting-but-wrong answer ("upgrade when the query has
no free `Int`") shipped a latent trap — the string-length axis has no `Int`
symbol at all yet still breaks the upgrade. See research note
`docs/research/01-foundations/bounded-string-completeness-unsat.md` and tasks
#75/#76.

## Decision

**A bounded string `unsat` is upgraded to a real `unsat` only when the query is
provably *bounded-complete* under a conservative syntactic test C1∧C2∧C3, run as
a final escalator route in `solve_smtlib`.**

- The route `apply_bounded_completeness_unsat` (crates/axeyum-solver/src/smtlib.rs)
  fires last, keyed on the exact `"no model within the bounded integer width"`
  `Unknown` (which is exactly a bounded-encoding UNSAT), and calls the syntactic
  analyzer `axeyum_smtlib::is_bounded_complete` (new module
  crates/axeyum-smtlib/src/bounded_completeness.rs).
- **C1** — no free unbounded `Int` (no declaration returns `Int`/`Real`; any
  n-ary function declines). **C2** — every free `String` var carries a
  top-level asserted upper length bound `(str.len s) </<=/= k` with
  `k ≤ STRING_MAX_LEN` (a ground query satisfies C2 vacuously). **C3** — every
  `Int` quantity provably `< 2³¹`: no `str.to_int`/`str.from_int`, no nonlinear
  `*`/`div`/`mod`/`rem`, no integer literal `≥ 2²⁰`, no binder/definition/
  quantifier/`match`.
- The analyzer **declines (returns `false`) on any construct it does not
  explicitly recognise as safe** — soundness over completeness.
- **Corollary fix (#76):** the same length axis leaked a *pre-existing*
  wrong-unsat through a different door — `str.at s k` for a constant `k ≥ cap`
  on a symbolic `s` folded to a hard `""` with no `Int` channel, so
  `combined.rs` reported the contradiction as exact. `string_at_const` now routes
  `k ≥ m` through the `Int`-index mux (sound `unknown`, mirroring `str.substr`);
  `k < 0` keeps the always-`""` fold (bound-independent). The bounded-complete
  cases still decide `unsat` via this route.

## Evidence

- Decides 4 bounded-complete corpus unsats matching cvc5 + `:status`, including
  both cvc5 `update-ex2` targets (`r1_QF_SLIA_update-ex2` QF_S,
  `cli__regress1_update-ex2` QF_SLIA) and the ground `str.update` unsats.
- **cvc5 whole-corpus differential (184 QF_S + QF_SLIA files): DISAGREE = 0**
  (both vs cvc5 and vs `:status`), before and after the #76 fix; post-fix decided
  sat 74 / unsat 39 / unknown 10, no regression (no corpus file uses the changed
  `str.at var K≥8` shape).
- Soundness-negative fuzz (`bounded_completeness_fuzz.rs`): 500
  real-sat-but-bounded-no-model queries (free `Int`, unbounded `String` probed
  past cap, `str.to_int`, large literal, nonlinear, hidden binder) — the analyzer
  rejects every one; 300 genuinely bounded-complete queries still accepted.
- 15 analyzer unit tests + 7 end-to-end tests; z3 `string_differential_fuzz`
  DISAGREE = 0; `corpus_regression`, `--lib`, `progress_frontier` (8/8), clippy
  all green.

## Alternatives

- **"Upgrade when no free `Int`" (the scoping agent's first cut)** — rejected:
  a wrong-unsat trap. `(> (str.len s) 100)` and `(= (str.at s 100) "x")` are
  real-sat with *no* `Int` symbol; the string-length axis is a second
  incompleteness source, so C2 is mandatory.
- **Gate every bounded-string `unsat` through `is_bounded_complete`** — rejected:
  the conservative analyzer says `false` for many correct length-independent
  unsats (word-clash, regex-emptiness routes), so a blanket gate would *regress*
  the decide-rate. The route is additive (Unknown→Unsat only); it never
  downgrades a route-produced verdict.
- **A term-graph (post-lowering) analysis** — rejected for the syntactic pass:
  lowering erases the `str.len` bound and string structure; a raw-text syntactic
  analysis is decoupled and easier to keep sound.
- **Widen the int-blast width / string cap** — rejected: no completeness
  guarantee (a query can need any width/length), and cap widening regresses the
  decide-rate (measured, ADR-0029 slice notes).

## Consequences

- **Easier:** a whole class of bounded-complete string unsats now decides
  soundly; `is_bounded_complete` is a reusable predicate for future bounded-string
  soundness gating (e.g. the #76-class constant-fold guards).
- **Harder / revisit:** the analyzer is deliberately conservative — broadening
  it (C2 to accept `(= s literal)` pins, C3 to allow linear const-mult /
  `str.to_int` of ≤ 9-byte strings) has **0 measured corpus ROI** today (the
  remaining unknown-unsats are length-*independent* word-level identities), so it
  is **not** pursued under the measure-don't-seed discipline. Revisit only if a
  future corpus surfaces bounded-complete rows the current C1∧C2∧C3 misses.
- **Standing rule:** every bounded-string verdict change must re-run the cvc5
  whole-corpus differential (DISAGREE = 0 is absolute), because the two
  incompleteness axes make wrong-unsats easy to reintroduce.

## Backlinks

- Research note: `docs/research/01-foundations/bounded-string-completeness-unsat.md`.
- Tasks #74 (str.update), #75 (this route), #76 (str.at corollary fix), #77
  (next lever — word-equation SAT).
- Related: ADR-0029 (bounded packed-BV strings), ADR-0053 (word-equation core),
  ADR-0061 (string evidence certification boundary).
