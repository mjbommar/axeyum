# ADR-2000: the front-door `distinct` refusal was never the binding constraint

Status: accepted
Index-summary: [ADR-1995] closed with five `UFNIA` rows dying at the front door in ~0.1 s on the `distinct` pair-expansion cap, **four of them refuted by z3 in 111-508 ms**, and a handoff proposing the linear injection encoding. **The sizing is 356 files, not 5** (438,631 scanned, 28,415 contain `distinct`, 356 carry an arity >= 363; `UFNIA` 309, `QF_NIA` 35, `QF_LIA` 12; 265 declare `unsat`; largest application **65,677 arguments**). **Two of the handoff's three structural claims are false, and each would have shipped a rewrite that fires on NOTHING.** Its proposed scoping -- the `distinct` is the whole body of an `(assert ...)` -- occurs **zero times in 356 files** (257 are `assert > and`, 52 `assert > let > not > or > not`, 47 sit in a `let` BINDING; all positive), so the site test had to become a polarity walk keyed on argument-slice ADDRESS, covering **309 of 356**; and "nullary constants of an uninterpreted sort" is true of the 257 `lahiri` files and false of the other 99, which are `Int` because Boogie's UFNIA encoding uses `Int` as a universal carrier -- the first implementation here scoped to uninterpreted sorts on the handoff's word and silently declined 99. Third: the front door's model replay is `check_model(&script.arena, &solved.assertions, ...)` over the REWRITTEN assertions, so it is **no safety net for this rewrite at all**; the `sat` direction is safe because the encoding is strictly STRONGER, proved, not because anything checks it. **Measured, one binary, two env values, back to back per file on six pinned core pairs: treatment 0 -> 1 decided over all 356, control `UFLIA` 68 -> 69, 0 losses and 0 sat<->unsat flips in 712 solves, mean 267 ms -> 21,175 ms.** BOTH `+1`s were re-run and they are different things: the control's is the MACHINE (`UFLIA`'s largest arity is 256, inside the cap, so the arm cannot change one parsed byte -- re-run 3x it is `unsat` 3/3 in both arms), and the treatment's is real (base `unknown` at a flat 109 ms is a deterministic ingest refusal) but came back UNSTABLE at 1/3; 15 further runs on a quiet core give **12/15, mean 14,727 ms of a 24 s budget** -- a refutation costing 61 % of the budget, which falls off the end whenever the box is busy. Noise floor **72/72/74, band 2**; and the A/B's own layout decided 69 of the same 200, so **a sweep's SHARD CONFIGURATION moves the count by more than repeating it does**. Mutation: 200 files x 4 arms, 0 decided base-vs-arm contradictions, the WEAKENING mutant kills 3 -- and **the STRENGTHENING mutant FAILS its criterion**, 0 decided contradictions, still 0 when given its 12 best-case files at 6x budget (12/12 CHANGED to `unknown`, 0/12 CONTRADICTED): it is never decisive at corpus scale, so that zero is evidence for one direction only. 6 of 6 authority comparisons agree (`:status`, z3, cvc5), 0 disagreements. **Ships OFF** -- and the reason is the lane's real finding: two files at a **600 s** budget, 25x the envelope, both hit the watchdog. **The front-door refusal was never the binding constraint; the quantified ladder is, at any budget.**
Index-status: accepted
Date: 2026-09-13

## Context

`crates/axeyum-smtlib/src/parse.rs` expands `(distinct t1 … tN)` into `N(N-1)/2`
pairwise disequalities and refuses above `MAX_DISTINCT_EXPANSION_PAIRS =
65_536`. [ADR-1995]'s closing paragraph, and the handoff beside it
(`bench-results/qbudget-20260913/DISTINCT-ENCODING.md`), named five `UFNIA` rows
that die there in ~0.1 s with no solver run — **four of them refuted by z3 in
111–508 ms** — and proposed the standard linear encoding through a fresh
uninterpreted `f : S → Int`:

    (distinct t1 … tN)   ~>   (and (= (f t1) 0) … (= (f tN) N-1))

`N` conjuncts instead of `N(N-1)/2`.

This ADR sizes that corpus-wide, builds it behind a lever, and measures it.

## 1. The sizing is 356 files, not 5

The handoff's 5 came from one division's pinned 200. `scan_distinct.py` reads
the whole corpus.

| | |
|---|---:|
| `.smt2` files scanned | 438,631 |
| containing `distinct` at all | 28,415 |
| carrying an application of arity ≥ 363 (the first refused arity) | **356** |

`UFNIA` 309, `QF_NIA` 35, `QF_LIA` 12. **265 declare `:status unsat`**, 90
`unknown`, 1 `sat`. The largest application has **65,677 arguments** — 2.16
billion pairwise disequalities, which is why raising the cap was never the fix.

## 2. Two of the handoff's claims are false, and each would have shipped a
   rewrite that fires on nothing

Both were found by building the lever and running it against the corpus. Neither
was visible from the handoff's five files.

### 2a. "the `distinct` is the whole body of an `(assert …)`"

The handoff proposed scoping the rewrite to that shape, because an assert body
is positive by construction and `parse_term` has no polarity context. Its
justification was that "the five rows above are all exactly this shape, because
that is how Boogie emits the axiom".

`polarity_scan.py` records the chain of enclosing heads for every over-cap
application. **That shape occurs zero times in 356 files.**

| chain from `assert` | files |
|---|---:|
| `assert > and` | 257 |
| `assert > let > not > or > not` | 52 |
| `assert > let > … > <a let BINDING> > and` | 47 |

All 356 are positive polarity; none is the body. A scoping test on the body
would have passed every unit test anyone thought to write and fired on nothing —
which is the sharpest form of the standing rule here: **ask what the change
would do if it were broken, and a rewrite that never fires looks exactly like a
rewrite that is not needed.**

The shipped site test is `LinearDistinctSites::for_assert`, a polarity walk from
the assert body through `and`, `or`, `not` (flipping), `=>` (flipping every
antecedent) and a `let`'s BODY, stopping at everything else. It records the
ADDRESS of each admissible argument slice; `apply_op`'s `distinct` case consults
that set, so the decision is made where polarity is known and applied where the
term is built, with no second parse. It is iterative with an explicit stack: the
deepest chain in the corpus is **4,310 nested `let`s**, which is why this parser
is iterative at all.

**Coverage: 309 of 356.** The 47 `let`-BINDING files stay on the pairwise path —
a bound name's polarity is the join over its uses, which this walk does not
resolve.

### 2b. "nullary uninterpreted constants of an uninterpreted sort"

True of the 257 `lahiri-cav09-storm-queries` files (`declare-sort boogieU 0`,
`declare-sort boogieT 0`). **False of the other 99.** `spec_sharp` and both
Dartagnan families carry no `declare-sort` at all and spell the whole query over
`Int`, because Boogie's UFNIA encoding uses `Int` as a universal carrier.

The first implementation here scoped to uninterpreted sorts on the handoff's
word. Measured, it fired on the 257 and silently declined 99 — and the only
symptom was a `--trace` line still showing `bound_by=fd:parse` with the lever
demonstrably on. The shipped scope is `Uninterpreted(_)` or `Int`: the two sorts
whose `=` is plain in the pairwise path, so no string/sequence length-abstraction
and no FP/numeric coercion hook is bypassed. A mixed application is excluded by
the same-sort test.

### 2c. and one more, about the safety net rather than the target

The handoff says "Model replay is unaffected, for a reason worth stating —
`check_model` evaluates the assertions the front door produced, which under this
rewrite are the rewritten ones". That is correct about the mechanism and wrong
about what it buys. `SmtLibSolved`'s replay is
`check_model(&solved.script.arena, &solved.assertions, model)`
(`crates/axeyum-solver/src/smtlib.rs:4426`), and `solved.assertions` **are** the
rewritten ones. A model of the encoding replayed against the encoding says
nothing about `distinct`.

So there is no replay-based safety net for this rewrite. The `sat` direction is
safe because the encoding is at least as STRONG as `distinct`, not because
anything downstream checks it. That is why the verdict assertions live in
`crates/axeyum-solver/tests/distinct_linear_soundness.rs`.

## 3. Why the encoding is exact, and what enforces each condition

For a positive-only occurrence of `φ = (distinct t1 … tN)` with GROUND arguments
and a FRESH `f`, with `ψ = ⋀ᵢ f(tᵢ) = i`:

* **No wrong `sat`.** `ψ ⊨ φ`, because `f` is a function: `tᵢ = tⱼ` forces
  `i = j`. The occurrence is positive, so `Φ` is monotone in it and
  `Φ[ψ] ⊨ Φ[φ]`.
* **No wrong `unsat`.** Any model `M` of `Φ[φ]` extends to a model of `Φ[ψ]`:
  interpret `f` as the injection when the `tᵢ` are distinct in `M`, and as `≡ 0`
  otherwise. Either way `ψ ↔ φ` in `M`. Each admitted application gets its own
  fresh `f`, so the choices are independent.

| condition | enforced by | tested by |
|---|---|---|
| positive polarity | the walk's whitelist | `every_positive_context_the_walk_admits_fires`, `every_context_the_walk_refuses_stays_pairwise` |
| ground arguments | quantifier bodies are not descended into | the `forall` case in the refusal test |
| fresh `f`, one per application | `declare_internal_fun`'s disjoint namespace, plus probing until the name is unused | `two_applications_get_two_injections`, `a_user_symbol_spelled_like_the_injection_does_not_collide`, and the verdict twin |
| assert bodies only | the empty plan at every other `parse_term` call | `only_an_assert_body_is_a_rewrite_site` |

The polarity hazard is **demonstrated rather than asserted**: the same query with
the encoding placed by hand under the negation is `sat` where the original is
`unsat` (`rewriting_under_a_negation_would_be_a_wrong_sat`). Without that, the
guard's test would be pinning a verdict nothing could move.

## 4. The mutation control — and the arm that FAILED it

[ADR-1976] measured that a sat-side reference control is vacuous: z3 and cvc5
agreed with a deliberately broken rewrite on 5 of 5 satisfiable files. The rule
that generalises is about DIRECTION — a weakening mutant can only be caught on
an `unsat`, a strengthening one only on a `sat`.

Four arms over 200 files drawn from the `QF_UF` and `UFLIA` `distinct`-bearing
populations, threshold lowered to 2 so the rewrite fires on benchmarks this
solver actually decides:

| | |
|---|---|
| `base` vs `arm`, both decided and differing | **0** |
| WEAKENING mutant (`mutant:vacuous`) decided contradictions | **3** — criterion met |
| STRENGTHENING mutant (`mutant:shared`) decided contradictions | **0** — criterion NOT met |

The strengthening arm **failed its criterion and the script exited non-zero**,
which is the point of writing the criterion before seeing the number.
`shared-mutant-probe.sh` then gave it its best chance: the 12 files where the
honest arm still decided `sat` AND ≥ 2 applications exist for the shared
injection to collide on, at six times the budget. **12 of 12 changed (`sat` →
`unknown`); 0 of 12 contradicted.**

So the mutant is not silent — it is never *decisive*. This solver cannot refute
the contradiction it introduces within budget, so at corpus scale the population
cannot distinguish "wrong" from "harder". **The strengthening mutant's decided
kill exists only at unit scale**
(`the_shared_injection_mutant_breaks_the_sat`, `sat` → `unsat` on a four-constant
query). The zero in the first row of that table is therefore evidence for the
weakening direction and NOT for the strengthening one, and the freshness guard
rests on the unit test plus the structural disjointness of the internal
namespace.

Also measured there, and the reason the shipped threshold is the cap rather than
a small number: at `on:2`, **60 of 80 `sat` rows became `unknown`**. Replacing a
cheap pairwise `distinct` with UF-into-`Int` machinery costs verdicts wherever
the pairwise path was working.

## 5. The A/B

One binary, two env values, both arms back to back per file on the same pinned
core, order alternating, 24 s wall, 8 GiB `ulimit -v`, six pinned core pairs
(`1,9` and `3,11` on s5, s6, s7). **This lever ships OFF**, so `base` is the
unset environment and `arm` sets `on`.

| | rows | base decided | arm decided | net | gains | losses | sat↔unsat |
|---|---:|---:|---:|---:|---:|---:|---:|
| treatment (all 356 over-cap) | 356 | 0 | 1 | **+1** | 1 | 0 | **0** |
| control (`UFLIA` pinned 200) | 200 | 68 | 69 | +1 | 1 | 0 | **0** |

All 712 solves exited 0; no `none`, no OOM, no crash. Mean time on the treatment
population: **267 ms → 21,175 ms**, because the base arm's 0.1 s is a refusal and
the arm's 24 s is a real search.

### The control's "+1" is a measurement of the machine, and says so

`UFLIA`'s largest `distinct` arity is **256** — inside the pairwise cap — so the
arm cannot change one byte of what is parsed there. The A/B still moved
`javafe.ast.DelegatingPrettyPrint.010` from `unknown` (24,233 ms) to `unsat`
(3,311 ms), back to back on the same core. Re-run 3× per arm it is
**STABLE-SAME**: `unsat` 3/3 in both arms. The A/B's base run lost to ambient
load, not to the encoding.

That is the whole argument for running a control division that the change
provably cannot touch, and for re-running every mover.

### The treatment's "+1" is real, attributable — and UNSTABLE

`UFNIA/spec_sharp/test14-CommandLineOptions.ssc.23….get_ProverNeedsTypes.smt2`:
base `unknown` at 109 ms (the deterministic cap refusal — there is no load
interpretation of a verdict the base arm structurally cannot produce), arm
`unsat` at 13,720 ms. Verified against three authorities: declared `:status`
`unsat`, z3 `unsat`, cvc5 `unsat` — **0 disagreements on a comparable
denominator of 3 of 3** (ADR-1957), and the same for the control mover, 6 of 6
overall.

But re-run 3× per arm it is **UNSTABLE**: the arm decided `unsat` on **1 of 3**,
with the base at 0 of 3 as it must be. Three runs give a rate whose 95 %
interval is `[2 %, 87 %]`, which is not a number, so `mover-rate.sh` ran 15 more
on a quiet pinned core:

    MOVER-RATE runs=15 arm_decided=12/15 base_decided=0/15 budget=24s
    MOVER-RATE arm mean_ms=14727

**12 of 15**, mean 14,727 ms against a 24 s budget; the base arm is 0 of 15 at a
flat 109 ms, as a deterministic ingest refusal must be. So this is not a coin
flip — it is a refutation that costs 61 % of the budget and therefore falls off
the end whenever the machine is busy, which is exactly what the 1-of-3 re-check
measured while five other shards were running.

**The honest headline is +1 that lands 12/15 idle and 1/3 under this lane's own
contention**, and the confirmed-at-the-measured-envelope gain is 0.

### Noise floor

One arm, one code state, the `UFLIA` pinned 200, three times on six pinned core
pairs: **72 / 72 / 74 decided — band 2.** Two files churn, both
`unknown unknown unsat`. So the control's `+1` is inside the band, as its
STABLE-SAME re-check already said.

A second spread is worth recording because it is LARGER than the band and a lane
that measured only the band would miss it: the A/B decided **69** of these same
200 files running 8 shards on 4 core pairs, and this floor decided **72–74**
running 6 shards on 6. Same binary, same arm, same files. **The CONFIGURATION of
a sweep moves the count by more than repeating the sweep does**, so a band
measured under one shard layout does not transfer to another — which is also why
the treatment mover reads 1/3 under the A/B's layout and 12/15 alone on a core.

### The front door was never the binding constraint

Two files, one from each family, run at a **600 s** budget (25× the board
envelope) with the arm on: **both hit the watchdog and returned `unknown`.** The
`lahiri` file z3 refutes in 508 ms; our quantified ladder spends ten minutes on
it and returns nothing. Neither is budget-bound at any budget worth giving it.

That is the finding this ADR exists to record. Clearing a deterministic ingest
refusal on 309 files bought **one unstable verdict**, because the refusal was
never what was stopping us — the quantified ladder is, and it is not
budget-bound on this family at any budget this lane could afford to give it.

## Decision

**Land the encoding, the polarity walk, the lever and the tests. Ship the lever
OFF.**

`AXEYUM_DISTINCT_LINEAR` unset is byte-identical to the pre-ADR-2000 parser, so
the default build cannot move a verdict.

The case for ON is not weak and is recorded so the next lane can re-take it:
under PAR-2 an `unknown` scores identically whenever it is returned, so the arm
costs nothing in score; and on the affected population a LOSS is structurally
impossible, because the base arm refuses every one of those files
deterministically — the arm can only gain. What defeats it today is arithmetic, not
doubt: the gain is **one file of 356 — 0.3 % — and it needs 61 % of the budget
to land**, so ON spends 20.9 s × 356 files of every sweep, on every lane's box,
to buy one verdict that disappears whenever that box is busy. [ADR-1970] and
[ADR-1995] both declined to ship on larger deltas than this.

**The condition for flipping the default is stated, and it is not about this
encoding:** when the quantified ladder decides *any* of these 309 files
reproducibly at the board envelope, the lever becomes a straight gain with no
loss mode, and should be turned on in the same commit. A lane that improves
`UFNIA` quantifier instantiation should re-run
`bench-results/distinct-linear-20260913/ab-run.sh` on
`lists/treatment-356.txt` before concluding its own sizing.

## Consequences

* The `distinct` cap stays. It is now documented in `config_registry.rs` with the
  measured 356 and the lever that bypasses it.
* `parse_script_with_distinct_lever` is new public surface on `axeyum-smtlib`. It
  exists because `DistinctLinear::from_env` latches a `OnceLock` — the
  determinism promise — so a soundness-negative suite that could only read the
  environment could only ever test the shipped arm.
* The next lane inherits a measured negative, not an open question: the five
  rows [ADR-1995] flagged are 356 rows, the front door is no longer what stops
  them, and the obstacle is named.
* A method note worth carrying: **a handoff's claim about the SHAPE of its
  target is as inheritable-and-wrong as its claim about the size.** Two of three
  structural claims here were false, both in the direction that would have made
  the fix look complete while doing nothing, and both were invisible until the
  built thing was run against the corpus rather than against the five files the
  handoff named.
