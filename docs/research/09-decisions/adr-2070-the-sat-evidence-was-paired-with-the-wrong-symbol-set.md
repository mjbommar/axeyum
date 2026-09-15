# ADR-2070: the `sat` evidence was paired with the wrong symbol set, and the population splits

Status: accepted
Index-summary: [ADR-2010] handed off a choice — (a) clear `assertions` so the string routes' pairing is honestly "no replay available", or (b) lift the source-level `Seq` model into the packed space — and a measurement, **5 of 109 `sat` results over 217 string-division files**. Both halves were re-derived here and both moved. **The mismatch named concretely: the packed vector's free symbols are the DECLARED names at `BitVec(100)` (`x` `#0`, `y` `#1`, `z` `#2`); the model binds DIFFERENT symbols — `!weq!x` `#13`, `!weq!y` `#14`, `!weq!z` `#15` at `Seq(BitVec(18))`, the parser's word-skeleton mirrors.** Different `SymbolId`s, names and sorts, so `check_model` never had anything to evaluate; shared `Int` symbols ARE bound, so the arenas overlap partially. **Per route the corpus rows are `fd:word-route` (4) and `fd:membership` (1) — NOT `fd:length-lia`, which ADR-2010's handoff named**; its synthetic witness reaches that route and no corpus file does, so a repair validated on the corpus alone would have shipped it unfixed. **The escalation ADR-2010 declined to claim was RUN here through the built `axeyum-py` extension and is worse than the static trace: four rows answer `Outcome.replay() == False` — what its own docs call "a soundness signal" — on five verdicts that are all correct, and the fifth answers `True` over an all-empty SUBSTITUTED model, a vacuous pass. A second face nobody had named: the REPORTED MODEL was wrong, not just unreplayable** — `r1_QF_SLIA_type002` came back `{x: '', y: '', z: '', i: 500}` for a query whose witness is `x="500" y="5" z="0"`. **Neither repair is right wholesale, because the population SPLITS 4/1:** four rows lift and replay `Ok(true)`, and one cannot be lifted by anything — `r1_QF_SLIA_re-inter-stack-ovf` asserts `(<= 15 (str.len var0))` against `STRING_MAX_LEN = 12`, and running `check_auto` on that packed vector **alone returns `unsat`**, so no lift exists and pairing any model with it would replay `false` on a correct `sat`. Shipped: lift where the encoding can express the witness, withhold where it cannot. **Evidence goes UP, not down** — A/B with one instrument, same cores, back to back: `replay Err(..)` **5 → 0**, `replay Ok(true)` **71 → 75**, withheld 33 → 34, every verdict and the 35 parse-`Err` unchanged. The guard is **completeness of the binding, never satisfaction**, so the downstream `check_model` keeps its power to reject. Mutation: **9 guards, 6 killed, 3 survivors reported and labelled in the code rather than counted**; two killed guards share a death-set. The suite's FIRST version reached none of the routes it named — `(= (str.len x) 10)` is decided by the flat path — and deleting the entire lift survived all nine tests; every test now pins its deciding stage through `RouteAttributionGuard`. Also fixed: `collect_free_symbols`, on the shipped hot path, was the obvious recursive DAG walk and did not finish ONE benchmark in 13 minutes.
Index-status: accepted
Date: 2026-09-14

## Context

[ADR-2010] audited the `sat`-side replay against the SMT-LIB front door and
found the general guarantee unachievable for parser rewrites. It closed with a
handoff it deliberately did not decide:

> `solve_smtlib_with_model` returns `sat` with `assertions` = the packed flat
> vector and `model` = a **source-level `Seq`** model, so `check_model` returns
> `Err("no value bound for symbol #0")`. … Two repairs, and **they are not
> equivalent**: (1) *clear `assertions`* — small, matches the sibling routes,
> and makes the false alarm go away **by removing the evidence rather than by
> fixing it**; (2) *lift the source-level model into the packed space* so the
> replay actually runs.

It also handed off a number (5 of 109) and an explicit non-claim: the escalation
to a false soundness signal through `axeyum-py` "is a static trace; this lane
did not run the Python path."

This ADR re-derives the number, names the mismatch, runs the Python path, and
decides.

## 1. The exposure, re-derived

`crates/axeyum-solver/examples/replay_pairing_census.rs`, 3 s per file, over
`QF_S` / `QF_SLIA` / `QF_SEQ` (134 + 50 + 33 = 217 files):

| | base `e0efc4a5a` |
|---|---:|
| files examined (denominator) | 217 |
| undecided (`Unknown`) | 33 |
| front door returned `Err` (parse declines) | 35 |
| `unsat` | 40 |
| **`sat`** | **109** |
| `sat` withholding replay state (honest) | 33 |
| `sat` carrying a model | 76 |
| replay `Ok(true)` | 71 |
| replay `Ok(false)` | **0** |
| replay `Err(..)` — symbol-set mismatch | **5** |

ADR-2010's 5 of 109 **reproduces exactly**, denominator for denominator. The
`68 undecided` it reported is split here into 33 genuine `Unknown` and 35
front-door `Err`, because [ADR-2045]'s arm read `losses=0` by verdict while
creating five new aborts and a single lumped denominator cannot show that.

### 1a. Per route — and this is not where the handoff pointed

| deciding front-door stage | `Ok(true)` | `Ok(false)` | `Err` | withheld |
|---|---:|---:|---:|---:|
| `fd:word-route` | 2 | 0 | **4** | 0 |
| `fd:membership` | 0 | 0 | **1** | 0 |
| `fd:source-string` | 0 | 0 | 0 | 30 |
| `fd:word-only-fallback` | 0 | 0 | 0 | 3 |
| `bv2nat-blast` / `int-blast-ladder` / `qf-bv` / `nia-bounded-blast` / `euf-online` | 69 | 0 | 0 | 0 |

**`fd:length-lia` does not appear.** ADR-2010's headline witness
(`(= (str.len x) 20)`) reaches it, and **nothing in the 217-file corpus does**.
A repair validated against the corpus alone would have shipped that route
unrepaired with every aggregate reading clean. It is fixed and tested here
because the route was enumerated from the source, not from the corpus.

## 2. The mismatch, named

`no value bound for symbol #0` is the symptom. `--explain` prints the two symbol
sets. On `r1_QF_SLIA_type002`:

```
free symbols of the PACKED assertion vector:
  #0    x        BitVec(100)       UNBOUND
  #1    y        BitVec(100)       UNBOUND
  #2    z        BitVec(100)       UNBOUND
  #3    i        Int               bound
what the model actually binds:
  #3    i        Int               used by the assertions             = Int(500)
  #13   !weq!x   Seq(BitVec(18))   NOT REFERENCED by the assertions   = Seq([53, 48, …])
  #14   !weq!y   Seq(BitVec(18))   NOT REFERENCED by the assertions   = Seq([53])
  #15   !weq!z   Seq(BitVec(18))   NOT REFERENCED by the assertions   = Seq([48])
```

So this is **neither a re-index nor a missing binding on the same symbol**. The
declared `String` lowers to `(_ BitVec string_total(m))` (ADR-0029); the source
routes reason over the parser's `!weq!<name>` sequence mirrors. Distinct
`SymbolId`s, distinct names, distinct sorts. The arenas overlap **partially** —
the shared `Int` symbol `i` is bound — which is why the failure is a per-symbol
`Err` and not a wholesale one.

That answers the question the handoff left open, "is (b) a lift, a re-index, or
a genuine re-solve?": it is a **lift**, and one whose machinery already existed
in `axeyum-py`'s `lift_onto_arena` for the *other*, re-solving code path.

## 3. The escalation, RUN rather than traced

ADR-2010 was careful: "That escalation is a static trace; this lane did not run
the Python path." Built here with `maturin develop --release` and run, with a
plain `QF_BV` row as the control that makes the rest readable.

| row | `replay()` before | `model` before |
|---|---|---|
| control `QF_BV` | `True` | `{x: 42}` |
| `r0_QF_SLIA_issue4376` | **`False`** | `{Str9: '', Str15: '', …}` |
| `r1_QF_SLIA_issue4379` | `True` | `{Str8: '', Str17: '', i7: 6}` |
| `r1_QF_SLIA_re-inter-stack-ovf` | **`False`** | `{var0: ''}` |
| `r1_QF_SLIA_type002` | **`False`** | `{x: '', y: '', z: '', i: 500}` |
| `cli__regress1__strings__type002` | **`False`** | `{x: '', y: '', z: '', i: 500}` |
| synthetic `(= (str.len x) 20)` | **`False`** | `{x: ''}` |

**The escalation is confirmed live, and it is worse than the trace.** Four rows
answer `False` — which `Outcome.replay`'s own documentation defines as "the
model was replayed and does NOT satisfy the assertions — a soundness signal" —
on five verdicts that are every one of them correct. The fifth answers `True`,
and that is not a reprieve: its model is all-empty, so it is a **vacuous pass**
over a model `complete_with_defaults` substituted, not over the witness the
solver found.

**And a second face nobody had named.** The `model` column above is the
user-facing `(get-model)`. Before the repair it reported `x: ''`, `y: ''`,
`z: ''` for a query whose witness is `x="500"`, `y="5"`, `z="0"`. A consumer
asking for the model got values that **do not satisfy the query** — a wrong
model, not a missing one, produced by `complete_with_defaults` filling the
unbound packed symbol with a well-founded zero that decodes to the empty string.
`replay_available` was `True` and `replay_unavailable_reason` was `None`
throughout, so the honest channel existed and was never reached.

## 4. The decision: the population splits, so neither repair wholesale

Pre-registered rule: if any row's witness is outside the packed encoding by
construction, (b) is impossible for that row and the cost of withholding must be
named. Dry-run of the lift on all five:

| row | lift | `check_model` after |
|---|---|---|
| `r0_QF_SLIA_issue4376` | 4 symbols packed | `Ok(true)` |
| `r1_QF_SLIA_issue4379` | 2 symbols packed | `Ok(true)` |
| `r1_QF_SLIA_type002` | 3 symbols packed | `Ok(true)` |
| `cli__regress1__strings__type002` | 3 symbols packed | `Ok(true)` |
| `r1_QF_SLIA_re-inter-stack-ovf` | **UNLIFTABLE** — 15 bytes, cap 12 | still `Err` |

**Four of five lift and the replay holds.** So (a) — clear `assertions` — would
have thrown away four real replays to silence one, which is precisely why the
handoff warned about picking the cheaper diff.

**The fifth is not "too hard to lift".** Its source is

```smt2
(assert (str.in_re var0 …))
(assert (<= 15 (str.len var0)))
```

and `STRING_MAX_LEN` is 12. Running `check_auto` over that packed vector
**alone** returns **`unsat`**: there is no model in the packed space at all, so
no lift can exist, and pairing **any** model with those assertions would replay
`false` on a correct `sat`. Deciding a query whose witness exceeds the bound is
exactly what the source routes exist for, so this class is **permanent**. It is
pinned by `past_the_cap_the_packed_vector_has_no_model_at_all`, whose control is
the same regex one numeral below the cap and must be `sat` — without that half,
a parser that produced a trivially unsatisfiable vector for every string query
would pass and the conclusion would be wrong.

**Decision: lift where the packed encoding can express the witness; withhold
honestly where it cannot.**

### The cost, named and accepted

One row per 109 `sat` (Wilson 95% [0.0, 3.4]% for the arm's zero) stops carrying
flat-replay evidence — evidence it **never actually had**, since what it carried
was an `Err`. In exchange four rows gain a replay that runs. The fraction of
`sat` results carrying a checked replay rises from **71/109 to 75/109**. This is
the opposite of what option (a) would have done, and it is why the handoff's
steer against (a) was right.

## 5. What keeps the checker able to fail

`pair_replay_state` guards on **completeness of the binding** — is every free
symbol of `assertions` bound after the lift — and **deliberately does not
consult `check_model`** before shipping a pair. Verifying satisfaction there
would make every downstream replay a tautology, and a checker that cannot fail
is worse than no checker. `the_replay_can_still_answer_false` takes the lifted
word-route row, rebinds every string to the packing of the empty string, and
requires `Ok(false)`. The empty model is not a strawman: it is exactly what
`complete_with_defaults` substituted before the repair.

Every packing step **declines rather than truncating or masking** — a code point
above a byte, a witness past the cap, a width that is not a packed layout, and a
packing the public `decode_packed_string` does not return unchanged. Truncating
to `max_len` is the tempting bug: a shorter string is a different string and
would replay as a model of a query that demanded the long one.

## 6. Cost: measured, one instrument, same cores, back to back

Base is `e0efc4a5a` extracted with `lane-snapshot.sh` and rebuilt with **the arm's
census example copied in**, so both arms run the identical instrument and only
the solver differs.

| | base | arm |
|---|---:|---:|
| files examined (denominator) | 217 | 217 |
| undecided (`Unknown`) | 33 | 33 |
| front door returned `Err` | 35 | 35 |
| `unsat` | 40 | 40 |
| `sat` | 109 | 109 |
| withholding replay state | 33 | **34** |
| carrying a model | 76 | 75 |
| replay `Ok(true)` | 71 | **75** |
| replay `Ok(false)` | 0 | 0 |
| replay `Err(..)` | **5** | **0** |

Per route: `fd:word-route` 2/0/**4**/0 → **6**/0/0/0; `fd:membership`
0/0/**1**/0 → 0/0/0/**1**.

**No verdict moves.** The exit-status channel is carried separately and is
identical (35 parse declines, byte-identical reasons), so the arm did not trade
a wrong pairing for a crash.

Wilson 95%: base mispaired 5/109 = 4.59% [1.98, 10.29]; arm 0/109 = 0 [0, 3.40].
Of model-carrying rows, base 5/76 = 6.58% [2.84, 14.49]; arm 0/75 [0, 4.87]. The
`Ok(true)` rates (65.14% [55.81, 73.43] → 68.81% [59.60, 76.74]) **overlap**, and
that is reported rather than hidden: this is a census of a fixed corpus, not a
sample, so the interval speaks to generalizing beyond these 217 files. The five
rows are named individually and fixed individually.

**The arm measures this lane's branch** (`ca636bc5c`, merge-base = `e0efc4a5a` =
main's HEAD at branch time). Predicted post-merge value: **0 mispaired of 109**,
unchanged, unless another lane moves the string ladder or `STRING_MAX_LEN` —
`replay_pairing_census --require-paired` is the check, and it exits nonzero on
any regression.

## 7. Guard deletion: 9 mutated, 6 killed, 3 survivors reported not hidden

`scripts/tests/mutation_controls.py replay-pairing-packing` (11 tests) and
`replay-pairing-state` (11 tests). Each mutation asserts its anchor matched
exactly once, so an unmatched edit reports `MISSING SUBJECT` rather than the
previous build's result.

| mutation | guard removed | tests killed |
|---|---|---:|
| `the packed-length cap` | a witness longer than `max_len` declines | 1 |
| `the byte-width decline on a code point` | a code point above `0xff` declines | 1 |
| `the length-field width mirror` | `len_width` matches the parser's layout | 4 |
| `the round-trip through the public decoder` | the packing decodes back unchanged | **SURVIVED** |
| `the width must be a packed-string layout` | a non-layout width declines | **SURVIVED** |
| `the completeness guard` | every free symbol of `assertions` is bound | 3 |
| `the source-string lift runs at all` | the lift executes | 3 |
| `the !weq! naming` | the witness is found under its mirror name | 3 |
| `an already-bound symbol is left alone` | the lift never overwrites | **SURVIVED** |

**Three survivors, and they are labelled in the code rather than counted as
covered:**

* The **round-trip** guard is the backstop that *absorbs* the layout-validity
  mutant, and the **layout** guard is unreachable from its only caller (which
  packs widths taken from `declared_strings`, always layouts). Given the other
  three guards the encode is exactly the decoder's inverse, so **no single
  mutation can isolate it**. What it really guards is the `len_width` **mirror**:
  the parser's copy is `pub(crate)` in another crate, and this is the runtime
  check that a drift declines rather than shipping a different string. This is
  the "six of seven guards rejecting through one shared check" shape, found by
  running the table rather than by inspection.
* `an already-bound symbol is left alone` needs a model binding **both** the
  packed symbol and its `!weq!` mirror; no fixture found here produces one. Kept
  because the alternative is silently overwriting an assignment the solver
  actually made, and *unkilled* is not *harmless*.

Two killed guards (`the source-string lift runs at all` and `the !weq! naming`)
share a death-set: disabling the lift and misnaming the witness have the same
effect, so they are **not independently separable**. Reported rather than
papered over.

## 8. The finding the mutation table produced that nothing else would have

**The suite's first version named three routes in its test names and reached
none of them.** `(= (str.len x) 10)` and a short `str.in_re` are both decided by
the FLAT path (`bv2nat-blast`): the bounded encoding represents a
ten-character witness perfectly well, and the string second chances only run
*after* the flat path declines. So three tests called "the … route ships a
replayable pair" passed while the lift never executed. Nothing in the suite
could say so — every test was green. The mutation table said it on its first
honest run: **deleting the entire `lift_source_strings_onto_packed` call
survived all nine tests**, as did the `!weq!` naming.

Every test now pins its deciding stage through `RouteAttributionGuard`, so a
fixture that drifts onto another route fails loudly instead of quietly testing
nothing. The generalizable rule: **a test that names a route must assert the
route, not just the verdict** — a fixture that falls through to a different code
path still answers `sat`.

A structural consequence worth recording: `fd:length-lia` and `fd:membership`
are reached only when the flat path declines, and on these shapes the flat path
declines exactly when the witness exceeds the cap. In this corpus and in these
fixtures **those two routes can only ever withhold**; the lift is exercised
through `fd:word-route`, whose witnesses can be short.

## 9. A defect found while building this, not inherited

`collect_free_symbols` was first written as the obvious recursive walk. An
assertion vector here is a **DAG** with heavy interning, so that re-expands
every shared node once per path and is exponential in the sharing depth. It did
not finish **one** benchmark in 13 minutes (killed at 100% CPU, RSS flat) where
the iterative walk with a visited set does the whole 217-file census in 52 s.
This runs on **every** front-door `sat`, so it was on the shipped hot path, not
in a test helper. Several sibling `collect_symbols` helpers in this crate
(`interpolant.rs`, `lia_interpolant.rs`, `bv_interpolant.rs`) have the same
recursive shape; they are not on this path and were not touched, but they are
worth an audit.

## Decision

1. `SmtLibSolved` ships `assertions` and `model` as a **genuine pair or not at
   all**. `pair_replay_state` lifts each declared `String` the model left
   unbound from its `!weq!<name>` source witness, then withholds **both** halves
   when any free symbol of `assertions` is still unbound.
2. The guard is **completeness of the binding, never satisfaction**, so a
   downstream `check_model` keeps its power to answer `Ok(false)`.
3. Every packing step **declines**; nothing truncates a witness or masks a code
   point. The packing is round-tripped through the **public**
   `decode_packed_string` before it is trusted.
4. A row whose witness exceeds `STRING_MAX_LEN` withholds **permanently**, and
   that permanence is pinned by a test asserting the packed vector is `unsat`,
   with a below-the-cap `sat` control.
5. **A soundness test that names a route must assert the route.** Registered at
   L0 in `hooks/pre-push` (`check-suite-gating.py` 38 → 39); ADR-2000's suite
   shipped registered nowhere.

## Open, and handed off

* **The sibling recursive `collect_symbols` walks** in `interpolant.rs`,
  `lia_interpolant.rs`, `lia_interpolant_cnf.rs` and `bv_interpolant.rs` share
  the shape that was exponential here. Not on the front-door `sat` path, not
  measured, and recorded at that confidence.
* **`len_width` is a mirror.** The parser's copy is `pub(crate)` in
  `axeyum-smtlib`. The round-trip guard makes a drift decline rather than ship a
  wrong string, but the right fix is to make the parser's helper public and
  delete the copy. Deliberately not done here — it widens a public surface and
  belongs in its own change.
* **`axeyum-py` has two replay paths** (`replay_state` from one front-door run,
  and an older re-lift through `solve_smtlib_model` + `lift_onto_arena`). The
  lift now exists on both sides of that boundary in two spellings. They agree
  today; nothing checks that they will.
* **The `fd:online-string` and `fd:source-string-sat-probe` routes** can also
  replace a verdict with a source-level model. Neither appears in this corpus's
  mispaired set and neither has a fixture here. The completeness guard covers
  them by construction — they would withhold rather than mispair — but whether
  their witnesses are *liftable* is unmeasured.
* **`r1_QF_SLIA_issue4379` passed vacuously before the repair** (`replay() ==
  True` over an all-empty substituted model). It now passes on a real binding,
  but its witness is genuinely empty for both strings, so the two are
  indistinguishable from the outside. Recorded because a row that looked green
  through the whole defect is the kind that hides the next one.

[ADR-2010]: adr-2010-the-sat-side-replay-cannot-see-the-parser.md
[ADR-2045]: adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
