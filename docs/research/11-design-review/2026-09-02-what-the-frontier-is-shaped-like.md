# What the frontier is shaped like

**2026-09-02, lane `shape-census`.** Measured, not estimated:
`scripts/frontier-shape-census.py`, artifact
`artifacts/autogenesis/frontier-shape-census-v1.json`, ledger sha
`d27c42ba1800`, 2,576 facts.

## Why this was measured

`scripts/fact-frontier.py --json` reports **217 dependency-ready open facts**,
of which **209 are `proof-route-only` with no producer contract that could
match them** (`diagnostics.unmatched_by_route_class`). Both existing producer
contracts are spent: the frontier's own diagnostics show
`producer-contract-int-modeq-family-v1` with 12 live declines and
`producer-contract-nat-coprime-family-v1` with 15, against 2 shape-matched and 1
admissible fact in the whole ledger.

*(The brief for this lane cited `ADR-1510` and
`docs/research/11-design-review/2026-09-01-why-every-contract-dispatch-declined.md`
for that conclusion. **Neither file is in this tree** — both are presumably on a
sibling branch — so nothing here rests on them; the sentence above is re-derived
from `fact-frontier.py --json`'s `diagnostics.declined_by_contract` in this
worktree. Do not cite them from here until they land.)*

The obvious next move is a third, target-agnostic producer aimed at the biggest
shape in those 209 — and nobody had measured what shape they are. This note is
that measurement.

## The number that matters

| population | count |
| --- | --- |
| dependency-ready open facts | 217 |
| **held-out blind evaluation population, excluded** | **186** |
| censused | 31 |
| primary population (proof-route-only, no matching contract) | 24 |
|   of which mutation controls — FALSE by construction | 11 |
|   of which divergence-blocked — not our proposition | 9 |
|   **genuinely targetable** | **4** |

Of those four, **two are famous open conjectures** — `F:goldbach-strong` and
`F:twin-prime-unbounded`. The population a target-agnostic producer could
actually work on is **two facts**:

- `F:ml430-nat-fermat-primefactors-one-lt-58343c6f` —
  `∀ (n p : ℕ), 1 < n → Nat.Prime p → p ∣ n.fermatNumber → ∃ k, p = k * 2^(n+2) + 1`
- `F:ml430-nat-prime-deficient-pow-9c5e1fef` —
  `∀ {n m : ℕ}, Nat.Prime n → (n ^ m).Deficient`

They share a carrier and nothing else: one is Euler's theorem on the prime
divisors of a Fermat number, the other a divisor-sum bound on a prime power.
Two facts with disjoint proof machinery are not a bucket.

**So the finding is plainly negative, and it is the deliverable.** The largest
coarse bucket holds **one** targetable fact. Under ten by a wide margin: the
frontier is not producer-shaped. There is no population here for a third
producer contract to generalize over.

## The ranked buckets

Coarse — carrier × conclusion head × hypothesis-count band. `mut` is mutation
controls, `div` is divergence-blocked; `targetable` is size minus both.

| rank | size | targetable | mut | div | carrier | conclusion | hyps |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 9 | **0** | 3 | 6 | Nat | `Eq` | 0 |
| 2 | 1 | 1 | 0 | 0 | Nat | `Eq` | 2+ |
| 3 | 1 | 1 | 0 | 0 | Nat | `Exists` | 0 |
| 4 | 1 | 1 | 0 | 0 | Nat | `Exists` | 2+ |
| 5 | 1 | 1 | 0 | 0 | Nat | `Deficient` | 1 |
| 6 | 1 | 0 | 1 | 0 | Int | `And` | 1 |
| 7 | 1 | 0 | 1 | 0 | Int | `Iff` | 0 |
| 8 | 1 | 0 | 1 | 0 | Int | `ModEq` | 0 |
| 9 | 1 | 0 | 0 | 1 | Nat | `Eq` | 1 |
| 10 | 1 | 0 | 1 | 0 | Nat | `Iff` | 0 |
| 11 | 1 | 0 | 0 | 1 | Nat | `Iff` | 2+ |
| 12 | 1 | 0 | 1 | 0 | Nat | `ModEq` | 0 |
| 13 | 1 | 0 | 1 | 0 | Nat | `lt` | 0 |
| 14 | 1 | 0 | 1 | 0 | Nat | `lt` | 1 |

Fine — the whole signature. Only the first seven; the remaining twelve are all
singletons of size 1.

| rank | size | targetable | signature |
| --- | --- | --- | --- |
| 1 | 3 | 0 | Nat `Eq`, no hypotheses, 3 bound vars, ml430 mirror, **divergence-blocked** |
| 2 | 2 | 0 | Nat `Eq`, no hypotheses, 1 bound var, ml430 mirror, **mutation control** |
| 3 | 2 | 0 | Nat `Eq`, no hypotheses, 1 bound var, ml430 mirror, **divergence-blocked** |
| 4 | 1 | 1 | Nat `Eq`, hyps `[lt, Prime, dvd]`, 2 bound vars, ml430 mirror |
| 5 | 1 | 1 | Nat `Deficient`, hyps `[Prime]`, 2 bound vars, ml430 mirror |
| 6 | 1 | 1 | Nat `Exists`, no hypotheses, 5 bound vars, native |
| 7 | 1 | 1 | Nat `Exists`, hyps `[le, dvd]`, 7 bound vars, native |

Every bucket of size greater than one is entirely unclosable. Every closable
fact is alone in its bucket.

## The largest coarse bucket, in prose

Nine facts, `Nat` equations with no hypotheses. Three are mutation controls
(`n.factorial = 0`, `n.choose n = 0`, `n ||| m = n &&& m`) — deliberately false
perturbations kept as negative controls, so proving one would be a soundness
alarm rather than a result.

The other six look, on the shape signature alone, like the best target on the
frontier: a tight family of bit-level equations over one carrier with no
hypotheses to discharge. Four of them are the same statement over different
operators.

Every one of them is **divergence-blocked**, confirmed independently by
`scripts/brief-step0.py` (six targets, six `DIVERGENCE-BLOCKED` verdicts):

- **`Nat.testBit` (codomain divergence), five facts** —
  `testbit_land`, `testbit_lor`, `testbit_ldiff`, `testbit_eq_inth`, plus
  `zero_of_testbit_eq_false` and `lt_of_testbit` outside this bucket. Our
  `Nat.testBit` returns a **`Nat`**; Mathlib's returns a **`Bool`**. The mirror
  statements are `Bool` equations (`… = (m.testBit k && n.testBit k)`), and no
  proof effort bridges a codomain difference. This is visible in the tree
  already: `Nat.testBit_land` **exists here as an admitted theorem**, stated
  with `AxNat.mul` where Mathlib has `&&`. The work is done; the mirror still
  cannot be flipped, because it is a different proposition.
- **`Nat.fastFib` (recursion-principle divergence), one fact** — and ADR-0840
  has already established that `Nat.fib` itself is independently divergent
  (ours is `fibAux n 0 1`, a curried-accumulator recursion). Two constructions
  apart, not one.
- **`Nat.multichoose` (definitional divergence), one fact** — we *define* what
  Mathlib *proves* about a three-case double recursion. Recorded in CLAUDE.md
  when a lane checked the Mathlib source at the pinned commit and correctly
  wrote no code.
- **`Squarefree` (codomain divergence), one fact** — outside this bucket.

So the honest answer to "what does a proof of a typical member need?" is: **not
a proof.** It needs a decision about whether to rebuild `Nat.testBit` over
`Bool`, which is a construction question with consequences for every existing
`testBit` theorem, and which no producer — target-agnostic or otherwise — can
take.

## What the size ranking would have done

Ranked on raw `size`, this bucket is rank 1 by a factor of three, it is
internally uniform, and four of its members are literally the same theorem over
different bitwise operators. It is exactly where a producer would have been
pointed, and it would have produced nothing. That is why the census computes
`targetable_size` and why the divergence registry is read: a bucket ranked
without it is a recommendation to spend a lane on a proposition we do not hold.

## Second finding: the queue's held-out warning is blind to 180 ready facts

Not asked for, and it changes how every number above should be read.

`fact-frontier.py:held_out_fact_ids()` reads `artifacts/autogenesis/nursery-v1.json`
**only** — 16 ids, 6 of them dependency-ready. The 2026-08-29 refill
preregistered **190 more held-out rows** in `nursery-v2-extension.json`, and
**180 of those are dependency-ready**. So of 217 ready facts, 186 are blind
evaluation population and the queue's own `⛔ HELD-OUT` annotation fires on six
of them.

`scripts/check-autogenesis-holdout-isolation.py:held_out_facts()` already reads
both, and says in a comment written for exactly this hazard that *"a gate
reading only v1 would report PASS while leaving every one of them unprotected."*
The gate got the fix; the queue a lane actually reads when picking work did not.
`scripts/check-dispatchable-frontier.py:load_partitions` also reads both.

The census excludes the **union** of both loaders — over-excluding costs a
bucket member, under-excluding spends a family — and reports the disagreement in
`population.held_out_source_gap`. Fixing `fact-frontier.py`'s loader is a
one-function change and is not this lane's to make; it is left as a named next
action.

This also reframes the headline the census was commissioned against. The "209
proof-route-only facts with no matching producer" is a real count of the
frontier's *rows*, but **186 of the 217 ready rows are population nobody may
touch**, so a producer aimed at the 209 would have been aimed almost entirely at
held-out facts. The census would have had to refuse most of what it was pointed
at even if the shapes had been uniform.

## Recommendation

**Do not build a third target-agnostic producer against this frontier.** The
bucket a producer would generalize over does not exist: the largest coarse
bucket has one targetable member, the largest fine bucket has one, and the total
closable population is four facts of which two are Goldbach and the twin prime
conjecture. A producer that worked perfectly on the best available bucket would
close **one** fact. ADR-0602's producer-contract machinery is not the
constraint; there is nothing for it to match.

Three things are worth doing instead, in this order:

1. **Refill the queue.** The frontier's ready rows are 86% held-out and most of
   the remainder is unclosable. This is a supply problem, not a producer-design
   problem, and every producer question is unanswerable until it is fixed.
   `scripts/propose-nursery-refill.py` and `gen-autogenesis-nursery-refill.py`
   exist for it.
2. **Decide the `Nat.testBit` codomain question.** Six ready facts and an
   unknown number of held-out ones hang on one construction decision: does
   `Nat.testBit` return `Nat` or `Bool` here? It is the single highest-leverage
   item the census surfaced, it is a one-time construction change rather than a
   proof, and today it silently blocks the largest uniform family on the
   frontier. Note the cost honestly: `Nat.testBit_land` and its siblings are
   already admitted over `Nat`, so a `Bool` codomain means restating them.
3. **Fix `fact-frontier.py:held_out_fact_ids()` to read both manifests**, so
   `just next` stops describing 180 blind rows as ordinary work.

If a producer must be built now, the only defensible target is the
`Nat.testBit` family — **six facts, four of them one statement over different
operators** — and it must be built *after* step 2, because until the codomain is
decided the producer's output cannot be admitted against the mirror it names.

## How to re-run this

```sh
python3 scripts/frontier-shape-census.py            # write + print
python3 scripts/frontier-shape-census.py --check    # 0 current, 1 stale, 2 unanswerable
```

`--check` is gated in `scripts/check-merge-hygiene.sh`, because the census is a
pure function of the fact ledger and a merge that lands or flips facts
invalidates it while touching neither the script nor the artifact.

**Two limits, stated so the numbers are not overread.** The `Squarefree`
constant carries no namespace dot, so `fact-frontier.py:candidate_identifiers`
cannot see it and its declared-constant flag is not evidence either way. And a
`prose` or SMT-LIB `formal.statement` is recorded as `unparsed` rather than
guessed at — four facts, all of them in the labeled `other` section and all
`no-route`.
