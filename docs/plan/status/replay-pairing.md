# Lane: replay-pairing — the `sat` evidence was paired with the wrong symbol set

<!-- plan-section: lane-status -->

**Lane replay-pairing (`DONE`, replay-pairing, 2026-09-14).** Briefed to take
[ADR-2010]'s handoff: `solve_smtlib_with_model` ships `assertions` = the packed
flat vector beside `model` = a source-level `Seq` witness, so `check_model`
returns `Err("no value bound for symbol #0")`. The brief put a thumb on the
scale against the cheap repair (clear `assertions`) and asked for the expensive
one (lift into the packed space) to be costed rather than assumed. **The
measurement picks neither wholesale, because the population splits 4/1**
([ADR-2070], `88fc50f3e`, `983afc9cb`, `ca636bc5c`).

**Exposure reproduced exactly.** 217 files, 109 `sat`, 33 withheld, 76 carrying
a model, 71 `Ok(true)`, 0 `Ok(false)`, **5 `Err(..)`** — denominator for
denominator what ADR-2010 handed off. The `68 undecided` is split here into 33
genuine `Unknown` and 35 front-door `Err`, because [ADR-2045]'s arm read
`losses=0` by verdict while creating five new aborts.

**Per route, the handoff pointed at the wrong one.** The corpus rows are
`fd:word-route` (4) and `fd:membership` (1). **`fd:length-lia` never appears** —
ADR-2010's synthetic witness `(= (str.len x) 20)` reaches it and no corpus file
does, so a repair validated against the corpus alone would have shipped that
route unfixed with every aggregate reading clean. It is repaired and tested here
because the routes were enumerated from the source, not from the corpus.

**The mismatch is neither a re-index nor a missing binding on the same symbol.**
The packed vector's free symbols are the DECLARED names at `BitVec(100)` (`x`
`#0`, `y` `#1`, `z` `#2`); the model binds `!weq!x` `#13`, `!weq!y` `#14`,
`!weq!z` `#15` at `Seq(BitVec(18))` — the parser's word-skeleton mirrors.
Different `SymbolId`s, names and sorts. Shared `Int` symbols ARE bound, so the
arenas overlap partially, which is why the failure is a per-symbol `Err`. That
answers the handoff's open question: it is a **lift**.

**The escalation ADR-2010 declined to claim was RUN, and it is worse than the
static trace.** Through the built `axeyum-py` extension, with a plain `QF_BV`
control that replays `True`: **four of the five answer `Outcome.replay() ==
False`** — what its own documentation defines as "a soundness signal" — on five
verdicts that are every one correct. The fifth answers `True` over an all-empty
SUBSTITUTED model, which is a **vacuous pass** and worse than the alarm.

**A second face nobody had named: the reported MODEL was wrong, not just
unreplayable.** `r1_QF_SLIA_type002` came back `{x: '', y: '', z: '', i: 500}`
for a query whose witness is `x="500" y="5" z="0"` — empty strings manufactured
by `complete_with_defaults` over the unbound packed symbol. A consumer asking
for `(get-model)` got values that **do not satisfy the query**.
`replay_available` was `True` and `replay_unavailable_reason` `None` throughout,
so the honest channel existed and was never reached. Both faces are fixed.

**Why neither repair wholesale.** Dry-run of the lift on all five: **four lift
and replay `Ok(true)`**, so clearing `assertions` would have thrown away four
real replays to silence one. The fifth is not "too hard" —
`r1_QF_SLIA_re-inter-stack-ovf` asserts `(<= 15 (str.len var0))` against
`STRING_MAX_LEN = 12`, and running `check_auto` on that packed vector **alone
returns `unsat`**: no lift exists, and pairing any model with it would replay
`false` on a correct `sat`. Deciding a query whose witness exceeds the bound is
what the source routes are FOR, so the class is permanent — pinned by a test
asserting the `unsat`, with a below-the-cap `sat` control.

**Shipped: lift where the encoding can express the witness, withhold where it
cannot. Evidence goes UP, not down.** Cost accepted: one row per 109 `sat` stops
carrying flat-replay evidence it never actually had (it carried an `Err`).

**What keeps the checker able to fail.** `pair_replay_state` guards on
COMPLETENESS of the binding and **deliberately does not consult `check_model`**
before shipping — verifying satisfaction there would make every downstream
replay a tautology. `the_replay_can_still_answer_false` rebinds every string to
the empty packing and requires `Ok(false)`; the empty model is not a strawman,
it is exactly what `complete_with_defaults` substituted before the repair.

**The finding the mutation table produced that nothing else would have.** The
suite's first version named three routes and reached **none of them**:
`(= (str.len x) 10)` and a short `str.in_re` are decided by the FLAT path
(`bv2nat-blast`), because the bounded encoding represents a ten-character
witness perfectly well and the second chances only run after the flat path
declines. Nine green tests, and **deleting the entire lift survived all nine**.
Every test now pins its deciding stage through `RouteAttributionGuard`. The
generalizable rule: **a test that names a route must assert the route, not just
the verdict** — a fixture that falls through to another code path still answers
`sat`.

**A defect found while building this, not inherited.** `collect_free_symbols`
was first the obvious recursive walk over what is a heavily-interned **DAG**, so
it re-expanded every shared node once per path. It did not finish ONE benchmark
in 13 minutes where the iterative version does the whole 217-file census in 52 s
— and it runs on **every** front-door `sat`, so it was on the shipped hot path.

## A/B, one instrument, same cores, back to back

Base `e0efc4a5a` extracted with `lane-snapshot.sh` and rebuilt **with the arm's
census example copied in**, so only the solver differs.

| | base | arm |
|---|---:|---:|
| files examined | 217 | 217 |
| undecided (`Unknown`) | 33 | 33 |
| front door returned `Err` | 35 | 35 |
| `unsat` | 40 | 40 |
| `sat` | 109 | 109 |
| withholding | 33 | **34** |
| carrying a model | 76 | 75 |
| replay `Ok(true)` | 71 | **75** |
| replay `Ok(false)` | 0 | 0 |
| replay `Err(..)` | **5** | **0** |

No verdict moves; the exit-status channel is identical (35 parse declines,
byte-identical), so the arm did not trade a wrong pairing for a crash. Wilson
95%: base 5/109 = 4.59% [1.98, 10.29], arm 0/109 [0, 3.40]. The `Ok(true)` rates
**overlap** (65.14% [55.81, 73.43] → 68.81% [59.60, 76.74]) and that is reported
rather than hidden: this is a census of a fixed corpus, not a sample, and the
five rows are named and fixed individually.

## Guard deletion: 9 mutated, 6 killed, 3 survivors REPORTED not hidden

`replay-pairing-packing` (11 tests): the packed-length cap **killed 1**, the
byte-width decline **killed 1**, the `len_width` mirror **killed 4**, the
round-trip through the public decoder **SURVIVED**, the packed-layout width
check **SURVIVED**. `replay-pairing-state` (11 tests): the completeness guard
**killed 3**, the lift running at all **killed 3**, the `!weq!` naming **killed
3** (same death-set), the already-bound guard **SURVIVED**.

The two packing survivors are the "six of seven guards rejecting through one
shared check" shape, found by running the table: the round-trip guard **absorbs**
the layout mutant, and the layout guard is unreachable from its only caller, so
given the other three guards the encode is exactly the decoder's inverse and
**no single mutation can isolate it**. Both survivors are **labelled in the
code** as unkilled rather than counted as covered, with what each actually
defends against. Two killed guards sharing a death-set is likewise reported, not
papered over.

## Branch point

Branched at `e0efc4a5a`, which **was** `main`'s HEAD at branch time, so the base
arm measures a tree that shipped. `main` then advanced to `5319c9fdf` (lane
LRA-DENSE, [ADR-2055]) while this lane ran, so local `main` was **merged in**
(`f7587d4b6`) and the merge base is now `5319c9fdf` = `main`'s HEAD. The only
overlap was the two GENERATED files, which were regenerated rather than
hand-resolved; LRA-DENSE touched `lra.rs`/`lra_online.rs`/`lra_theory.rs`/
`simplex.rs` and this lane touched none of them.

**Re-verified on the MERGED tree**, because two green branches can fail to
compose: workspace check exit 0, `check-clippy-complete.sh` exit 0 at 889 of 889
with 0 diagnostics, `cargo fmt --all --check` exit 0, `check-suite-gating.py` 39
gated PASS, `check-merge-hygiene.sh` PASS, `replay_pairing_soundness` 11 passed,
and the census still **0 mispaired of 109** with
`--require-paired --expect-mismatch 0` exiting 0.

Predicted post-merge value: **0 mispaired of 109**, unless a later lane moves
the string ladder or `STRING_MAX_LEN`; `replay_pairing_census --require-paired`
exits nonzero on any regression.

## Compute

Local dev box only, `taskset -c 0-3`. **No s5/s6/s7 pairs taken** — the brief
allowed four and none were needed; the whole measurement is a 217-file division
at 3 s plus a 9-mutant sweep in a `lane-snapshot.sh` copy.

## Gates

`check-clippy-complete.sh` exit 0, **889 of 889** targets across 27 of 27 crates,
0 diagnostics (887 plus this lane's example and suite).
`RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps` exit
0. `cargo fmt --all --check` exit 0. `cargo check --workspace --all-targets`
exit 0. `cargo check -p axeyum-solver --all-targets` on DEFAULT features exit 0.
`corpus_regression` 2 passed; `online_string_front_door` 48;
`word_first_fallback` 13; `qf_slia_fixed_splice` 82; `stoi_len_abstraction` 13;
`-p axeyum-solver --lib --features full -- --test-threads=4` **1774 passed**
(1763 + 11 new). `check-suite-gating.py` 38 → **39 gated, PASS**.
`check-links.sh` all ok. **Not run:** `just check` / `scripts/check.sh` in full,
and the z3 differential fuzzes (no linear-arithmetic change in this diff).

[ADR-2010]: ../../research/09-decisions/adr-2010-the-sat-side-replay-cannot-see-the-parser.md
[ADR-2045]: ../../research/09-decisions/adr-2045-the-bound-is-not-the-wall-qf-lra-is-one-offline-dense-engine.md
[ADR-2070]: ../../research/09-decisions/adr-2070-the-sat-evidence-was-paired-with-the-wrong-symbol-set.md

<!-- plan-section: landed-changes -->

| 2026-09-14 | replay-pairing | [ADR-2010]'s string-route handoff, decided on a measurement rather than the preference it was handed with. **Exposure reproduced exactly** (217 files / 109 `sat` / 33 withheld / 76 carrying a model / 71 `Ok(true)` / 0 `Ok(false)` / **5 `Err(..)`**), with `undecided` split into 33 `Unknown` + 35 front-door `Err` because [ADR-2045]'s arm read `losses=0` by verdict while creating five new aborts. **The mismatch named**: the packed vector's free symbols are the DECLARED names at `BitVec(100)` (`x` `#0`, `y` `#1`, `z` `#2`) and the model binds DIFFERENT symbols — `!weq!x` `#13`, `!weq!y` `#14`, `!weq!z` `#15` at `Seq(BitVec(18))`, the parser's word-skeleton mirrors; shared `Int` symbols ARE bound, so the arenas overlap partially. **Per route the handoff pointed at the wrong one**: the corpus rows are `fd:word-route` (4) and `fd:membership` (1), and **`fd:length-lia` never appears** — its synthetic witness reaches it and no corpus file does, so a corpus-validated repair would have shipped it unfixed. **The escalation ADR-2010 declined to claim was RUN through the built `axeyum-py` extension and is worse than the trace: four rows answer `Outcome.replay() == False`** — its own docs call that "a soundness signal" — on five correct verdicts, and the fifth answers `True` over an all-empty SUBSTITUTED model, a vacuous pass. **A second face nobody had named: the reported MODEL was wrong, not merely unreplayable** — `{x: '', y: '', z: '', i: 500}` for a witness of `x="500" y="5" z="0"`, values that do not satisfy the query, while `replay_available` stayed `True`. **Neither repair is right wholesale because the population SPLITS 4/1**: four rows lift and replay `Ok(true)`, and `r1_QF_SLIA_re-inter-stack-ovf` asserts `(<= 15 (str.len var0))` against `STRING_MAX_LEN = 12` where `check_auto` on the packed vector **alone returns `unsat`** — no lift exists and pairing any model replays `false` on a correct `sat`. Shipped: **lift where the encoding can express the witness, withhold where it cannot**, so **evidence goes UP** — A/B with one instrument on the same cores, `Err(..)` **5 → 0** and `Ok(true)` **71 → 75**, every verdict and the 35 parse-`Err` unchanged (Wilson 95% arm [0, 3.40]%). The guard is **completeness of the binding, never satisfaction**, so the downstream `check_model` keeps its power to reject; every packing step **declines** rather than truncating a witness or masking a code point, and is round-tripped through the **public** `decode_packed_string`. **Guard deletion: 9 mutated, 6 killed, 3 SURVIVORS reported and labelled in the code rather than counted** — the round-trip guard absorbs the layout mutant and the layout guard is unreachable from its only caller, so no single mutation isolates either; two killed guards share a death-set. **The finding the table produced that nothing else would have: the suite's first version named three routes and reached NONE of them** — `(= (str.len x) 10)` is decided by the flat path — and **deleting the entire lift survived all nine tests**; every test now pins its deciding stage through `RouteAttributionGuard`, because *a test that names a route must assert the route, not just the verdict*. Also fixed, found while building and not inherited: `collect_free_symbols` was the obvious recursive walk over a heavily-interned **DAG** and did not finish ONE benchmark in 13 minutes where the iterative version does the whole 217-file census in 52 s — on the shipped hot path for every front-door `sat`. Registered at L0 (`check-suite-gating.py` 38 → 39). ADR-2070 |
