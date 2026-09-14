# Lane: replay-scope — the sat-side replay guarantee cannot see the parser

<!-- plan-section: lane-status -->

**Lane replay-scope (`DONE`, replay-scope, 2026-09-14).** Briefed to answer
whether CLAUDE.md's hard rule — *"every `sat` result must be checkable by
evaluating the original term against the lifted model"* — is real, given
[ADR-2000]'s observation that the front door replays
`check_model(&script.arena, &solved.assertions, model)` over the
**parser-produced** assertions. **It is not real for the parser, and the audit
found three reachable wrong verdicts proving it — all in unconditional
s-expression desugars, none behind a lever or a feature gate.** All three are
fixed ([ADR-2010], `d1ef34802`, `f86453178`).

**The headline is not the three bugs but why one guarantee missed all of them,
for two DIFFERENT structural reasons.** (A) A parse-level desugar has no
original to replay against: `desugar_sets` rewrites `(Set E)` to `BitVec` on the
s-expression tree *before any term is built*, so the source set terms never
become IR terms — and the obvious remedy, "keep the originally parsed assertions
and replay against those", is a **no-op**, because the original parse *is* the
encoding. (B) A strengthening rewrite produces wrong `unsat`, and a `sat`-side
replay cannot see that however it is implemented. **Blind spot A covers defect 1,
blind spot B covers defects 2 and 3.**

One framing correction worth keeping: it is **not** true that all three are
strengthening rewrites. Defect 1 is neither — it is a *non-homomorphic* encoding
that maps one element onto two bits, and it was measured producing a wrong `sat`
**and** a wrong `unsat` from the same defect.

**Defect 1 — the finite-set bit key was the literal's SPELLING.**
`set_element_key` returned the atom's raw text, so `#b0101`/`#x5`/`(_ bv5 4)`
were three elements and `1.5`/`1.50` two. `(set.member #b0101 s)` with
`(not (set.member #x5 s))` answered **`sat`** (cvc5 `unsat`) while both
same-spelling controls answered `unsat` — **a verdict depending on the spelling
of a literal**, which is oracle-free proof of unsoundness in one direction, with
the controls saying which. The dual `(set.member #x5 (set.singleton #b0101))`
encoded to `0 = 1`, a wrong `unsat`. The module note's condition 1 asserted the
false premise that made it look sound: *"two syntactically-distinct literals are
two distinct values"*.

**Defect 2 — const-array elimination ignored scope AND order.**
`desugar_const_arrays` collected `(assert (= s ((as const …) v)))` across all
top-level commands, then dropped it and inlined everywhere. A definition inside
a popped `push` gave **`unsat`** for a `sat` script; a definition placed *after*
a `check-sat` was inlined **backwards past it**, making the first of two queries
`unsat` when it is `sat` — and that variant needs no `push`/`pop` at all, just
ordinary SMT-LIB with two queries. The second is also the more robustly
demonstrable: the first query **in isolation** is `sat` on cvc5 and on ours, so
the wrong verdict is pinned without a reference solver needing to answer the
second query.

**Defect 3 — the universe was sized by a constant.** `width = d + MARGIN` with
`MARGIN = 2`, counting only *named literal* elements and never the free
`(Set E)` declarations, so N free sets could not be pairwise distinct past
`2^(d+2)`. Threshold measured exactly: 4 sets `sat`, **5 sets `unsat`** (cvc5
`sat`), 5 sets + one named literal `sat`. **The comment is part of this bug** —
it claimed equisatisfiability for *both* branches, but that converse is a claim
about the WIDTH and was argued only for the `set.card` branch; the
non-cardinality branch inherited the conclusion without the argument. The
comment did the arguing.

**Verification.** `parser_desugar_soundness.rs`, **18 tests**, registered in
`hooks/pre-push` (`check-suite-gating.py` L0, `gated=38 PASS`). Each aimed at
the direction where the defect has somewhere to go, each paired with a
non-vacuity control differing in one small term ([ADR-1976]: a satisfiable query
is a *vacuous* control). **Guard-deletion: 10 guards mutated, 0 untested, 10
distinct death-sets, separable**; 6 kill exactly one test. Replacing the width
decline with a `min()` clamp — the change that would reintroduce defect 3 at a
higher threshold *while looking like a fix* — kills exactly one test and nothing
else. `all-literals-one-bit` proves the controls bite: it kills three controls
and one aliasing test.

**Cost, measured rather than predicted.** 23 corpus files reach these desugars
(15 `set.*`, 8 `(as const`), run back to back through a `94389e480` binary and a
fixed one at 20 s: **decided 15 → 15, delta 0, 0 of 23 verdict strings differ**;
8 decline at parse in *both* arms with byte-identical messages, so no new
declines. A **freshness control was run first** — the base binary reproduces all
three wrong answers and the arm the corrected ones — because `delta=0` is
equally what measuring the same binary twice looks like.

**Can the guarantee be made real?** No, not as stated, and not for lack of
effort: replaying against the originally parsed assertions cannot work for a
parse-level desugar, and no `sat`-side replay sees a wrong `unsat`. **Per-rewrite
arguments are the right design; the work is making the arguments checkable.**
The rule should be read as covering the *solver*, where it genuinely holds —
array elimination, theory combination, word-level preprocessing, bit-blasting
and the warm incremental engine all project the model back and re-evaluate the
**pre-rewrite** caller vector, with a failed replay degrading to `Unknown` — and
as not covering the parser, where it never could.

## Scope actually covered, and what was not

The `parse.rs` inventory **did reach completion** as an enumeration (615 `fn`,
552 non-test; five independent strategies reconciled — function enumeration,
arena-builder head mismatch, symbol-minting sites, `Script` side-table writes, a
23-keyword comment scan) and every transformation between text and
`Script::assertions` is classified by direction in [ADR-2010] §7. But three
reachable bugs surfaced mid-audit and were fixed ahead of it, so **the
verification depth is uneven and deliberately so**: the three defects are
measured end to end with controls; the remaining classifications are
code-reading, and two inventory findings are recorded at that lower confidence
and explicitly **not reproduced by running anything** — the `args.is_empty()`
well-formedness gate for n-ary declarations returning `String`/`(Seq E)`/
`(_ FiniteField p)`, and the `!q.` quantifier-binder symbol living in the USER
namespace where `arena.declare` interns by name.

The eleven `weaker` side channels each have a **code gate**, not merely a
comment — so the weakening rewrites are, as a class, the ones already handled
correctly. That is the opposite of what the brief expected to find, and it is
why the finding is about direction B rather than about a weakening rewrite.

## Branch point

Branched at `94389e480`. `git merge-base main HEAD` is `94389e480`, which **is**
`main`'s HEAD, so the base arm measures the tree that ships.

## Compute

Local dev box only (load 0.41 at start, 16 cores, 123 G). **No s5/s6/s7 pairs
taken** — the brief allowed up to 6 and none were needed; the whole measurement
is 23 corpus files plus a 10-mutant guard-deletion sweep in a
`lane-snapshot.sh` copy. s7's board sweep untouched.

[ADR-1976]: ../../research/09-decisions/adr-1976-a-sat-side-reference-control-is-vacuous.md
[ADR-2000]: ../../research/09-decisions/adr-2000-the-front-door-refusal-was-not-the-binding-constraint.md
[ADR-2010]: ../../research/09-decisions/adr-2010-the-sat-side-replay-cannot-see-the-parser.md

<!-- plan-section: landed-changes -->

| 2026-09-14 | replay-scope | CLAUDE.md's hard rule — *"every `sat` result must be checkable by evaluating the original term against the lifted model"* — audited against the SMT-LIB front door, whose replay is `check_model(&script.arena, &solved.assertions, model)` over the **parser-produced** assertions. **Three reachable wrong verdicts found, all in UNCONDITIONAL s-expression desugars, none behind a lever or feature gate, and the replay could not have caught any of them.** (1) `desugar_sets` keyed each element bit on the literal's **raw text**, so `#b0101`/`#x5`/`(_ bv5 4)` and `1.5`/`1.50` were two elements each: `(set.member #b0101 s)` with `(not (set.member #x5 s))` answered **`sat`** (cvc5 `unsat`) while both same-spelling controls answered `unsat` — **a verdict depending on the SPELLING of a literal**, oracle-free proof of unsoundness; the dual `(set.member #x5 (set.singleton #b0101))` encoded to `0 = 1`, a wrong `unsat`. (2) `desugar_const_arrays` collected definitions across all top-level commands with **no notion of scope OR order**: one inside a popped `push` gave **`unsat`** for a `sat` script, and one placed after a `check-sat` was inlined **backwards past it** — the second needing no `push`/`pop`, and pinnable without a reference solver answering the second query since the first **in isolation** is `sat` on cvc5 and on ours. (3) `desugar_sets`'s universe was `d + MARGIN` with `MARGIN` a **constant 2**, so N free sets could not be pairwise distinct past `2^(d+2)`: **4 sets `sat`, 5 sets `unsat`** (cvc5 `sat`), 5 sets + one named literal `sat` — threshold exactly at `2^(0+2)`. **The headline is why ONE guarantee missed all three, for TWO different structural reasons**: a parse-level desugar has no original to replay against (the source set terms never become IR terms, so "replay against the originally parsed assertions" is a **no-op** — the original parse IS the encoding), and a strengthening rewrite yields wrong `unsat`, invisible to a `sat`-side replay however implemented. **Not all three are strengthening** — defect 1 is *non-homomorphic*, mapping one element onto two bits, and produced a wrong `sat` **and** a wrong `unsat`. **So the general guarantee is NOT achievable as stated and per-rewrite arguments are the right design**: 18 tests in `parser_desugar_soundness.rs`, registered at L0, each aimed at the direction where the defect can fail and each with a non-vacuity control ([ADR-1976]). **Guard-deletion: 10 guards, 0 untested, 10 distinct death-sets, separable**, 6 killing exactly one test; replacing the width decline with a `min()` clamp kills exactly one test and nothing else. **Corpus cost measured, not predicted: 23 files, decided 15 → 15, delta 0, 0 of 23 verdicts differ**, 8 declining in both arms with byte-identical messages — with a **freshness control run first** confirming the base binary reproduces all three wrong answers, since `delta=0` is equally what measuring one binary twice looks like. Two comment defects corrected **as part of the bug**: condition 1's false premise, and an equisatisfiability claim made for both branches whose converse was argued only for `set.card` — *the comment did the arguing*. Withdrawn as soundness issues because they fail **loudly**: `inline_aliases` has no binder awareness and a shadowing `let` dies with `syntax error: let name` (a robustness regression on legal SMT-LIB, handed off), and a self-referential const array declines with `unknown identifier` — right outcome by accident, recorded because it will not survive a refactor. Handed off with a warning: the string-route model pairing (`solve_smtlib_with_model` returns `sat` with a **source-level `Seq`** model beside the **packed** flat vector, so `check_model` returns `Err("no value bound for symbol #0")` while plain QF_BV controls replay `Ok(true)`) — the verdict is **correct** and only the evidence is mispaired, so the damage is a *false alarm* that would make `axeyum-py`'s `Outcome.replay()` call a correct `sat` a soundness violation; the cheap repair (clear `assertions`) **reduces the fraction of `sat` results carrying evidence** and must not be chosen by default. ADR-2010 |
