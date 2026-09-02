# ADR-1570: one operation closed four sibling facts, and the other six say exactly what is missing

Status: accepted
Date: 2026-09-02
Lane: `flywheel-3`

Index-summary: **The August exit criterion is met.** One registered operation,
`authoritative-mathlib-nat-bit-constructor-family-v1`, closes **four**
previously open sibling facts — `Nat.bit_false`, `Nat.bit_false_apply`,
`Nat.bit_true`, `Nat.bit_true_apply` — with **no per-target proof code**, each
an axiom-free kernel term checked by a fresh independent kernel and
independently rechecked by a gate whose exit depends on four separate
findings. `docs/top-three-focus-plan-2026-08.md` Priority 1 asked for three or
more; this is four, and the producer (`propose_bounded_induction`) was written
in August for a different family and **was not modified by this lane**. The
dispatch covered all ten members of the contract's live population:
**4 accepted, 6 declined, 0 errors**. The six declines are the deliverable's
other half and they are not a uniform "we tried": **four** are one missing
capability (`UnsupportedIffShape` — the producer has no `Iff.intro` leg and
stops at the shape test, never approaching its binder or induction budget),
**one** is genuine arithmetic the bounded chain cannot reach
(`Nat.bit b n / 2 = n` needs a `Nat.div` lemma), and **one** never reached the
producer at all (`TrustedDeclaration("dif_pos")` — `Nat.bitwise`'s
well-founded-recursion byproduct trips the importer's fail-closed policy,
the same structurally-earlier gate that took 15 of 27 dispatches on
2026-08-27, reconfirmed on a family neither seed contract covered).
**Two findings the lane did not go looking for.** First,
`docs/research/11-design-review/2026-09-02-what-the-frontier-is-shaped-like.md`
recommended *not* building a producer against this frontier on a measured
count of **4 targetable facts**; the frontier was refilled the same day and the
count is now **23**, so that recommendation was correct when written and is now
stale — a size-4 measurement should not be quoted as a standing property of the
frontier. Second, `scripts/check-development-partition.py` reports PASS on this
operation **because it cannot see it**: its `NURSERY` constant is
`nursery-v1.json` alone, all four closed facts live in
`nursery-v2-extension.json`, and the gate's own rule ("an operation that closes
a development fact must also close a train fact") would otherwise fire. This
lane does **not** fix that loader, and says why.

Index-status: accepted

## Context

[ADR-0602](adr-0602-operations-are-receipts-dispatch-needs-producer-contracts.md)
separated the retrospective receipt (an operation) from the prospective
capability claim (a producer contract).
[ADR-1510](adr-1510-a-contract-is-sized-by-the-frontier-and-a-decline-dies-with-its-fact.md)
added the lifecycle after all 27 dispatches of 2026-08-27 declined and both
seed contracts turned out to have been sized against families another route
finished within days. The design review
[2026-09-01-why-every-contract-dispatch-declined.md](../11-design-review/2026-09-01-why-every-contract-dispatch-declined.md)
found the two causes; the census
[2026-09-02-what-the-frontier-is-shaped-like.md](../11-design-review/2026-09-02-what-the-frontier-is-shaped-like.md)
then measured the frontier and recommended against building a third producer
at all, because the largest coarse bucket held **one** targetable fact.

Draw 19 ([ADR-1561](adr-1561-draw-19-is-authored-and-draw-10s-deferral-was-the-whole-refusal.md))
landed between those two measurements. Re-running
`scripts/frontier-shape-census.py` on 2026-09-02 reports **257 ready, 23
targetable**, and the largest recipe-coherent bucket is no longer size one but
size **ten**: draw 19's `natural-bit-constructor` development family
(`Mathlib.Data.Nat.BinaryRec`).

## The 23, by family and shape

Measured from `artifacts/autogenesis/frontier-shape-census-v1.json`
(ledger `7dc07046…`, 2,682 facts) cross-referenced against every
`artifacts/autogenesis/nursery*.json`. Held-out rows are excluded by the
census and the exclusion was re-verified here (`held_out_excluded: 206`,
`held_out_source_gap.known_only_to_*: 0`).

| family | partition | n | coarse shape |
| --- | --- | ---: | --- |
| `natural-bit-constructor` | development | **10** | `Nat`/`Bool` `Eq` (4) and `Iff` (4), zero-hypothesis; plus one `Eq` with 1 hypothesis and one `Bool` `Eq` |
| `natural-binomial-bounds` | train | **9** | `Nat` `le` (4) and `lt` (3), zero-to-two hypotheses; plus 2 `dvd` with 3–4 hypotheses |
| `fermat-numbers` | development | 1 | `Nat` `Eq`, 3 hypotheses (Euler on Fermat-number prime divisors) |
| `natural-factors-and-factorisation-properties` | development | 1 | `Nat` `Deficient`, 1 hypothesis |
| *(native, no nursery row)* | — | 2 | `Nat` `Exists` — Goldbach and the twin prime conjecture |

Two buckets carry more than two facts, and only two. The bit family is the
larger, and — unlike the binomial one — its members share a *recipe*, not
merely a carrier: they are all statements about one non-recursive constructor
`Nat.bit b n = cond b (2 * n + 1) (2 * n)`.

## What was dispatched, and what came back

`producer-contract-natural-bit-constructor-family-v1` (route `kernel-lane`,
shape `lean4-surface` × `Nat` × `statement_contains: "Nat.bit"`) matches
exactly those ten facts and nothing else: `Nat.testBit` — the divergence-blocked
neighbour — is not a match, because `Nat.bit` is not a substring of
`Nat.testBit`, and that is one of the contract's two named non-examples. All
ten were dispatched: one Lean adapter file, one `lake env lean` compile, ten
`lean4export` invocations, ten imports, ten producer runs.

| # | member | outcome | stage | typed reason |
| --- | --- | --- | --- | --- |
| 1 | `Nat.bit_false` | **accept** | producer | — |
| 2 | `Nat.bit_false_apply` | **accept** | producer | — |
| 3 | `Nat.bit_true` | **accept** | producer | — |
| 4 | `Nat.bit_true_apply` | **accept** | producer | — |
| 5 | `Nat.bit_eq_zero_iff` | decline | producer | `UnsupportedIffShape` |
| 6 | `Nat.bit_mod_two_eq_one_iff` | decline | producer | `UnsupportedIffShape` |
| 7 | `Nat.bit_mod_two_eq_zero_iff` | decline | producer | `UnsupportedIffShape` |
| 8 | `Nat.bit_ne_zero_iff` | decline | producer | `UnsupportedIffShape` |
| 9 | `Nat.bit_div_two` | decline | producer | `TerminalNotClosed` |
| 10 | `Nat.bitwise_zero` | decline | **import** | `TrustedDeclaration` |

**accepted 4 / declined 6 / error 0.** Every import except #10 was clean:
60 declarations admitted, **0 axioms**, into a fresh kernel that refuses any
proof-bearing or trusted declaration in the statement stream.

## Decision 1 — the exit criterion is met, and this is what met it

`authoritative-mathlib-nat-bit-constructor-family-v1` is registered over the
four accepts. The four facts are `proved`, route `kernel-lean`,
`axiom_footprint: []`, each with exactly one `checked` evidence row bound to
the operation.

Three properties are worth naming, because each is a way this could have been
a weaker result than it looks:

- **No per-target proof code exists, and none was written.** The producer is
  `axeyum_lean_import::producers::bounded_induction::propose_bounded_induction`,
  registered 2026-08-22 under
  `authoritative-mathlib-bounded-induction-factorial-family-v1` against
  *train* facts about `Nat.descFactorial`/`Nat.ascFactorial`. It was not
  touched by this lane. It never sees a theorem name: it peels the leading
  telescope, tries `Eq.refl` at the terminal, and where that is stuck attempts
  one bounded structural induction plus one congruence rewrite. Two of the four
  accepts came out at `binders_used=0, inductions_used=0` (a bare `Eq.refl`
  under a function-equality goal, which the kernel closes by going under the
  binder) and two at `binders_used=1, inductions_used=1`.
- **The proof is checked by a kernel that has never seen Mathlib's proof.**
  The import is statement-only; the proof term is constructed here and
  `Kernel::add_declaration` is the sole authority on it.
- **The recheck can fail, and was made to.** Four mutation controls, one per
  finding the gate claims, each applied to the committed tree and reverted:
  perturbing an accept's `proof_sha256`, making a closed fact's axiom footprint
  non-empty, marking a *declined* fact `proved`, and marking the FALSE mutation
  control `proved`. All four exit 1 with the specific error. The table is in
  the gate's own docstring.

## Decision 2 — the six declines are recorded as three distinct findings, not one

A decline census that says "six declined" is the coverage number this
repository keeps catching itself producing. The six partition:

**Four are one missing capability, and the budget was never approached.**
`UnsupportedIffShape` fires at the terminal *shape test*: the producer
recognises only an `Eq`-headed terminal, so an `Iff` goal stops before any
binder is peeled or any induction attempted. `max_binders=8` and
`max_inductions=2` were nowhere near. The correct reading is therefore **not**
"widen the bound" but "the producer has no `Iff.intro` leg". Adding one is a
bounded, well-specified next task with a **known** population: these four, plus
the 40 `Iff`-headed facts ADR-1510 counted in the wider pool. Two caveats,
measured rather than assumed: `Nat.bit_eq_zero_iff` would also need conjunction
introduction, and the two `% 2` members would need `Nat.mod` arithmetic behind
the `Iff` leg, so an `Iff` leg alone closes at most two of the four.

**One is genuine arithmetic.** `Nat.bit b n / 2 = n` has both a free `Bool` and
a free `Nat`; the induction leg splits `Nat` binders only, so the `cond b _ _`
head stays stuck, and even after a hypothetical `Bool` split each branch is a
division identity over a symbolic `n`. This needs a lemma-application leg, not
a wider bound.

**One never reached the producer.** `Nat.bitwise f 0 0 = 0` fails in
`import_statement_ndjson` with `TrustedDeclaration("dif_pos", Theorem)`:
elaborating the statement as a bare `Prop` drags in a theorem byproduct of
`Nat.bitwise`'s well-founded-recursion compilation, and the importer's
fail-closed policy refuses it. This is the same gate that took 15 of the 27
dispatches on 2026-08-27 (doc 292), and it is worth restating what it means for
contract design: **a shape predicate cannot see it.** Nothing in a fact's
`formal.statement` says whether that statement *elaborates* through a proved
theorem. A contract sized purely on statement text will therefore always carry
some members that fail before the producer runs, and the honest response is to
record them — as this family does, 1 in 10 — not to narrow the shape until the
number looks better.

Six decline artifacts are committed, each with a typed `decline_reason`, the
stage, the pinned export digest, and an `analysis` field saying what would have
to change. `scripts/validate-producer-contract-declines.py` passes at 33
declines.

## Decision 3 — the contract is development-only, and that is stated rather than omitted

`scripts/check-development-partition.py` enforces: *an operation that closes a
development fact must also close a train fact*, because a producer whose whole
applicability was authored against the evaluation set no longer measures
generalization. This operation closes four development facts and no train fact.

The reason is a property of the frontier, and it was measured before the
contract was written. The entire live train population is **17 open rows**:
5 outcome-blind mutation controls (FALSE by construction, and closing one would
be a soundness alarm), 2 divergence-blocked (`Nat.fastFib`, `Squarefree`), and
the 10 `natural-binomial-bounds` rows. So the only recipe-coherent train bucket
in existence is the binomial bounds one, and no reflexivity-or-bounded-induction
chain proves `Nat.choose n k ≤ 2 ^ n` — that fact is this contract's *second
named non-example*, chosen precisely because it is the bucket a size-ranked
selector would have merged with this one.

What keeps this from being the failure the rule exists to catch is that the
producer was **not** authored here. It was built in August against train facts,
and this lane's contribution is a contract, a dispatch, a checker, and a
decline census — not a line of producer code. That is the distinction the rule
is actually about, and it is checkable: `git log` on
`crates/axeyum-lean-import/src/producers/bounded_induction.rs` carries no
commit from this lane.

## Finding: the gate reports PASS because it cannot see this operation

`check-development-partition.py:64` sets `NURSERY = nursery-v1.json` and
`fact_partitions()` reads that file alone. All four facts closed here are
preregistered in `nursery-v2-extension.json` (measured: 0 occurrences in v1,
4 in v2), so `referenced = {s for s in _strings(operation) if s in partitions}`
is empty for this operation and `touched_dev` never becomes non-empty. **The
gate's PASS on this operation carries no information.**

This is the identical defect the shape-census review found in
`fact-frontier.py:held_out_fact_ids()` on 2026-09-02 — one reader hardcoding
v1 while `check-autogenesis-holdout-isolation.py` and
`check-dispatchable-frontier.py` read both — and it is now measured in a second
reader. It is disclosed here rather than repaired, for one reason stated
plainly: **fixing the loader in the same change that registers the operation
the fix would then flag is a lane clearing its own gate.** The repair and the
decision about what to do with this operation belong to a lane that is not this
one. Two options are open to it and both are legitimate: extend the loader and
then decide whether this operation needs an ADR-1563-style reviewed entry, or
decide that the rule should key on "was the producer authored here" (which is
the property it is really about) rather than on which partition the closed rows
happen to sit in.

Recorded so the next lane inherits a measurement instead of a green light.

## Finding: our own prelude already carries three of these propositions — about a DIFFERENT constant

Step 0 of a brief is "does it already exist?", and run properly it returns an
uncomfortable answer here. `shape_search --name-like` over the live kernel
(2,187 declarations, positive control `Int.quadraticReciprocity` FOUND):

| our declaration | its statement | the ml430 mirror it resembles |
| --- | --- | --- |
| `Nat.bit_false` (arity 1) | `∀ n, bit false n = mul 2 n` | `Nat.bit_false_apply` — **accepted** here |
| `Nat.bit_true` (arity 1) | `∀ n, bit true n = add (mul 2 n) 1` | `Nat.bit_true_apply` — **accepted** here |
| `Nat.bit_div_two` (arity 2) | `∀ b n, bit b n / 2 = n` | `Nat.bit_div_two` — **declined** here |
| `Nat.bit_mod_two` (arity 2) | `mod (bit test n) 2 = bool_select_nat test 1 0` | the two `% 2` `Iff` mirrors — declined |

The name collision is real and the reader deserves it stated: **our `Nat.bit`
is not Mathlib's `Nat.bit`.** Ours is
`fun test n => Nat.add (Nat.mul 2 n) (bool_select_nat test 1 0)`
(`crates/axeyum-lean-kernel/src/nat_prelude/bits.rs`), deliberately
`add`-outermost so several order lemmas fall out by δι-reduction; Mathlib's is
`cond b (2 * n + 1) (2 * n)`. The mirror facts quantify over *Mathlib's*
constant, and this dispatch proved them by importing Mathlib's definition into
a fresh kernel and constructing the term there. Nothing in the four evidence
rows cites a local `Nat.bit_*` theorem, and the import admits 60 declarations
with 0 axioms — our prelude is not in that environment at all.

Two consequences, neither of them comfortable:

- The four closures are **not novel mathematics**, and this ADR does not claim
  they are; their `external_status` was `proved` before and stays `proved`.
  What is new is the *mechanism* — a producer, not a person, put the term
  together, for four facts at once. That is the whole content of the exit
  criterion, and it is the only thing being claimed.
- `Nat.bit_div_two` is the sharper case: we hold that proposition about our own
  constructor and the producer still declined its Mathlib mirror. That is
  correct behaviour — a theorem about a different constant is not evidence for
  this row — but it does identify a cheaper route nobody has built: a
  **transport** producer that discharges a mirror by exhibiting the two
  constructions as definitionally equal and citing the local theorem. That is
  a different producer from an `Iff` leg, it would reach `bit_div_two` and
  probably the two `% 2` members, and this lane is not building it. Recorded
  as a named candidate rather than a plan.

## Finding: the census's "do not build a producer" recommendation is stale

`2026-09-02-what-the-frontier-is-shaped-like.md` closes with "**Do not build a
third target-agnostic producer against this frontier**", on the ground that the
largest coarse bucket held **one** targetable fact and the whole closable
population was four, two of them Goldbach and the twin prime conjecture.

That was correct on the ledger it measured (217 ready, 186 held out, 4
targetable). Draw 19 landed, and today's regeneration of the same script over
the same ledger path reports 257 ready, 206 held out, **23 targetable**, with a
ten-member recipe-coherent bucket. Four of those ten are now closed.

Neither number is wrong; they are measurements of different ledgers three days
apart. The general lesson is the one CLAUDE.md already states about absence
claims — a measured negative about a *frontier* expires when the frontier is
refilled, and the refill is a routine operation. A frontier measurement quoted
without its ledger digest is not a finding, it is a date-stamped snapshot.
Both the census artifact and this ADR carry the digest.

## Consequences

- The flywheel has produced its first multi-target closure since the August
  exit criterion was written: 4 facts, 1 operation, 0 lines of per-target proof.
  `validate-facts.py` reports 2,682 facts / 0 errors and 2,411 `proved`.
- The contract's live population is now **6** (the declines), so it stays
  un-retired under ADR-1510 rule 1 and remains falsifiable by re-dispatch.
  It retires when an `Iff` leg or a lemma-application leg empties it.
- **The single highest-value next task this lane can name is the `Iff`
  terminal leg**, and it comes with a pre-measured population, a pre-written
  contract, and a checker that will notice the day a decline turns into an
  accept — `check_declines()` fails loudly if the producer starts admitting a
  goal the family records as declined, so the follow-up cannot land silently.
- `scripts/check-autogenesis-nat-bit-constructor-family.py` joins the gate set
  and takes roughly four minutes (12 `cargo run --release` invocations: 4
  accepts, 6 declines, 2 control probes).

## Alternatives considered

- **Target the `natural-binomial-bounds` train family instead**, which would
  have satisfied the development/train rule directly. Rejected on measurement:
  its ten members are arithmetic bounds (`choose n k ≤ n ^ k`,
  `choose (2n+1) n ≤ 4 ^ n`, two prime-divisibility statements with three and
  four hypotheses). The kernel has `Nat.choose_le_two_pow` with a side
  condition and the `descFactorial = k! * choose` bridge, and nothing else in
  that direction; no existing producer closes one of them, so the honest
  outcome would have been 0 accepts and 10 declines. That is a legitimate
  deliverable, but it is a worse use of a dispatch than a bucket where the
  producer's own first leg was already known to fire.
- **Write a new producer with a `Bool` case-split leg**, the obvious extension
  for a family about a `Bool`-indexed constructor. Rejected after checking what
  it would buy: no member of the ten becomes closable. `bit_div_two`'s branches
  are still division identities; the `% 2` members' branches are still `Nat.mod`
  identities. A leg that closes nothing has no test population, which is the
  checker-that-cannot-fail defect one level up.
- **Register four single-target operations instead of one multi-target one.**
  Rejected: it would satisfy every validator and fail the actual exit criterion,
  which is about *one* operation closing *three or more* siblings. Four
  single-target receipts are four bespoke capsules wearing a family's name.
- **Fix `check-development-partition.py`'s nursery loader in this change.**
  Rejected; see the finding above.
- **Invent a `statement-reflexivity-multi-target-v1` executor driver.** The
  reflexivity producer closes exactly the same four targets (verified), but
  `execute-autogenesis-operation.py`'s own comment reserves the multi-target
  receipt schema for an ADR, and `validate-autogenesis-operations.py` would
  need a new arm. Reusing the existing, already-validated
  `bounded-induction-multi-target-v1` driver — whose producer subsumes
  reflexivity as its first leg — costs nothing and adds no schema.

## How to re-run this

```sh
python3 scripts/validate-producer-contracts.py
python3 scripts/validate-autogenesis-operations.py
python3 scripts/validate-producer-contract-declines.py
python3 scripts/check-autogenesis-nat-bit-constructor-family.py   # ~4 min
python3 scripts/validate-facts.py
python3 scripts/check-development-partition.py
python3 scripts/check-autogenesis-holdout-isolation.py
python3 scripts/check-dispatchable-frontier.py
python3 scripts/check-partition-edges.py
```

The mutation control is four edit/run/revert cycles over
`check-autogenesis-nat-bit-constructor-family.py`, one per finding, exactly as
tabulated in its docstring. The Mathlib exports are pinned by digest at
`/nas3/data/axeyum/autogenesis/sources/mathlib-v4.30.0-nat-bit-constructor-family-v1/`
and the adapter source is tracked at
`scripts/lean/autogenesis_statement_adapter_nat_bit_family_v1.lean`.
