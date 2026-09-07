# ADR-1679: A production metric must see every channel that produces

Date: 2026-09-06
Status: Accepted
Lane: `production-metric`

Index-summary: The "hand proofs retired" total read 67 for three days while
roughly two hundred proved facts landed, because the work moved into producers
that emit theorems nobody ever wrote by hand and the metric counts *deletions*.
Retires it as a rate, replaces it with a three-layer producer-channel census
that prints its own coverage and blind spots, names the one ledger field
(`provenance.produced_by`) that would make the number readable without a source
scan, and prices a held-out family at 10 propositions — 4.9% of the remaining
blind rows — payable in full by naming one id in a producer contract.

Index-status: Accepted

## Context

The running production number this project quotes is **hand proofs retired**: a
hand-written prelude proof deleted and replaced by producer output. It read
**67** on 2026-09-03 and was still reading 67, unchanged, on 2026-09-06 — quoted
in four dated records and two `docs/math-department/` files. In the same window
roughly two hundred new `proved` facts landed, and zero retirement commits
touched the kernel crate after 2026-09-04.

The rate did not slow. **The work moved channel.** Producers now emit theorems
that were never hand-written, so there is no hand proof to retire, and a metric
defined as "hand proofs deleted" is structurally blind to every theorem that
never had a hand proof in the first place. `docs/math-department/12-the-chair.md`
struck the production-rate claim for exactly this and asked for a derived, gated
number.

The ledger could not answer the question either. Its `provenance.established_by`
names the **prelude builder** — `axeyum-lean-kernel build_nat_prelude` — never
the producer, on all 2,963 fact files. So "which of these did a producer make?"
had no reading anywhere.

## Decision

### 1. The rule

> **A production metric must be able to see every channel that produces, or it
> will read flat while the system accelerates.**

A metric defined by the *removal* of an artifact (a hand proof, an axiom, a
`TODO`) measures a channel that is closing. It cannot measure the channel that
replaces it, and its flatness is indistinguishable from a stall. Before quoting
any production number as a rate, name the channels that produce and check that
the metric has a reading for each. This applies to retirement counts, to
axiom-footprint reductions, and to anything else phrased as "N fewer X".

### 2. The metric: `scripts/measure-producer-channel.py`

Three layers, each printing its own coverage line, because they have different
strengths and a reader must be able to tell them apart.

| Layer | What it counts | Measured 2026-09-06 |
| --- | --- | --- |
| L1 site census | Producer entry-point calls outside the producer modules and outside test code, classified EMIT / ASSIST / CONFIG | 38 EMIT, 50 ASSIST, 44 CONFIG, 0 unclassified |
| L2 name resolution | Names-struct field → declaration leaf, EXTRACTED from `field: <binder>(ns, "leaf")` | 3,735 bindings; 1,808 (48.4%) have a leaf differing from the field; 92.1% of EMIT sites resolve |
| L3 ledger join | `proved` facts whose `formal.kernel_theorem` a producer emitted | **21**, against 2,455 proved facts carrying that field |

**EMIT** is `<producer>::…::declare*`: the producer builds the proof term *and*
adds the declaration. That is the channel the retirement metric cannot see.
**ASSIST** is `::prove*` / `::theorem` / `::run`: the producer builds a proof
term that a hand-authored declaration then adds. **CONFIG** is rule-set
plumbing and rendering, and builds no proof term.

Three properties are load-bearing.

**Fail-closed.** An entry point in none of the three buckets is an ERROR, never
an "other" bucket. That is what stops the next producer route from being
silently absorbed into a headline number — the same failure this ADR is about,
one level down.

**Extracted, not computed.** L2 never guesses a declaration name from the field
spelling. Measured, 1,808 of 3,735 bindings have a leaf that differs from its
field (`abs_i` → `abs_I`, `in_disc_of_real_offset` → `inDisc_ofReal_offset`), so
guessing would be wrong about half the time. The binder set is closed:
`kernel.name_str`, `k.name_str`, `self.name_str`, `self.name_str_anon`,
`self.lookup_name_str`, `child`. Missing `child` alone — 907 bindings, the whole
integer prelude — put L2 coverage at 39.5% instead of 92.1%.

**The number is a lower bound, and says so.** Leaves naming theorems in two
namespaces are dropped as ambiguous. ASSIST sites are not joined at all. A
producer reached through a bridge module is attributed to the bridge.

### 3. What it cannot see, printed on every run

* ASSIST counts **sites, not theorems**: a producer call in a helper invoked N
  times is one site and N proof terms.
* `ring::declare_ring_all` and `decide::declare_decidable_equality` emit several
  theorems from one site.
* The import-route producers in `crates/axeyum-lean-import/src/producers/` are a
  different channel with a different trust base, and are not counted.
* The CAS and SMT routes appear in no layer; `proof_route` separates them.

A number whose blind spots are not printed beside it becomes a number quoted
without them. That is how 67 travelled.

### 4. The one field that would fix this properly

L3 reaches through **source text** to answer a question the ledger should answer
on its own. One field, on one path, removes the source scan:

    fact.provenance.produced_by : string | null

* `null` means hand-authored — **asserted, not merely absent**, the same
  distinction `formal.kernel_theorem` already draws between an explicit `null`
  ("no single subject") and an absent key ("infer conservatively").
* The value names the producer entry point that built the proof term:
  `linarith::nat::declare`, `ring::int::prove_eq_at`, `tactic::run`.
* It is written where a fact flips to `proved` against a kernel-lean
  declaration, by the lane that already fills in `formal.kernel_theorem` — same
  moment, same knowledge, no new measurement.

With it, ASSIST becomes countable, the 48%-wrong field-name guess disappears,
and the metric stops depending on a Rust call-site grammar that a refactor can
move. This ADR does not add the field: the schema is `additionalProperties`-open
under `provenance`, so a lane can begin recording it immediately, and a
subsequent ADR should make it required once the write path is in place.

### 5. Retiring the old number where it is quoted

The four in-tree quotes are **dated records** — three lane status files and
ADR-1589 — and rewriting a dated record is falsifying it. Each keeps its
original figure and gains a forward note: correct on its date, not to be quoted
forward as a rate, not comparable with the channel metric, with a pointer to
`scripts/measure-producer-channel.py`. Two further quotes live in
`docs/math-department/`, which another session owns and which this lane reports
rather than edits.

"Not comparable" is precise, not a hedge. One counts *removals from the prelude
sources*; the other counts *producer-emitted declarations and the proved facts
that join to them*. A theorem can move the second without ever being able to
move the first, which is the entire finding.

### 6. The price of a held-out family

Nine held-out families have been spent since 2026-08-22, and each was priced
**after** the fact in an amendment that could only record the loss. Two of the
nine — 2026-09-03 (`ring-identity-v1`) and 2026-09-05
(`psatz-sum-of-squares-v1`) — were spent by a producer contract naming a
held-out row as a **non-example**. No proof attempted, no outcome consulted.

`scripts/price-holdout-family.py` prints the cost side before dispatch:

| | Measured 2026-09-06 |
| --- | --- |
| Blind population | 20 families, 206 rows (19 × 10, one × 16) |
| Spent | 9 families over 14 days = 0.64/day; ~31 days of runway |
| Cause mix | 2 producer contract cited a row; 1 operation registered against a row; 4 rows were never blind; 2 rows decided by the unblocking definition |
| **Price of one family** | **10 propositions — 4.9% of remaining rows, 5.0% of remaining families** |

There is **no partial spend**. The declared partition unit is
`whole-family-with-source-review-groups-indivisible`, so naming ONE row costs
exactly what proving all of them costs. The spend is irreversible and
machine-enforced (ADR-0542): reassigning an amended family to `held-out` is a
generator error.

What can never be claimed about a spent family afterwards, by anyone: that the
system closed a proposition it had never seen; an unbiased estimate of producer
coverage including its rows; a blind trial of any kind. One family is one
independent trial, and the trials are not replaceable — the catalog is a pinned
Mathlib slice, so a new family has to come from what is left of it.

The script never prints a held-out id. Naming one, even as an example of what
not to name, is itself the citation that spends a family; a guard checks its own
output before it exits.

Two derivation traps, both measured here. **Amendments are the authority over
the manifests' preregistered `family_partitions`**: `natural-elementary-bounds`
and `discrete-step-and-counting-bounds` still carry `held-out` in the extension's
preregistration block and are `development` by amendment, so reading the
preregistration alone overcounts the blind population by two families. And
`check-holdout-adjacency.py`'s 20 rows are one per **draw**, not an inventory of
what is held out — the two coincide today at 20 families, and nothing makes them
coincide in general.

## Alternatives considered

**Keep the retirement count and add producer emissions beside it.** Rejected:
the two are not commensurable and printing them adjacently invites a sum. The
retirement count is retired *as a rate* and preserved *as a dated record*.

**Count producer-emitted theorems at runtime by instrumenting the prelude
build.** The honest measurement, and eventually the right one. Not taken here:
this lane may not touch a crate, and a runtime count still would not answer the
ledger-side question ("which *facts*"). §4's field answers both and costs one
string per lane.

**Wait for `provenance.produced_by` and report nothing today.** Rejected: the
flat 67 was being quoted forward while the wait ran. A lower bound with printed
coverage beats an unbounded wait, and the brief's own instruction was that if
provenance is not recorded well enough to count this today, then naming the
missing field IS the deliverable — so both were done.

**Report a percentage — "N% of proved facts are producer-emitted".** Rejected:
the numerator is a lower bound with three named exclusions and the denominator
is the whole ledger across four proof routes. A ratio of those two reads as a
coverage claim it cannot support. Two absolute numbers with their coverage lines
are weaker-sounding and stronger.

## Consequences

* A lane may not quote a "hand proofs retired" figure as a current production
  rate. The channel metric is the number; the retirement figures stay as dated
  history.
* Any new producer entry point makes `measure-producer-channel.py --check` fail
  until it is classified, which is the intended cost of adding a channel.
* The floors in `scripts/producer-channel-baseline.json` are a ratchet. A drop
  means the producer channel shrank **or** the census stopped seeing part of it;
  the script cannot tell those apart, so it reports and fails rather than
  choosing. Re-pin deliberately, never to silence a red run.
* A brief that will produce a producer contract, an operation, a fixture or an
  example must consult `price-holdout-family.py` first, and must state the goal
  and the invariant instead of naming a row.

## External precedent

Reported by the coordinator from a landscape survey landing separately under
`docs/research/02-ecosystems/` (not yet in this worktree; the two points below
are recorded as received and should be re-checked against that document).

The termination and confluence competitions have required certification for
years and score the **checker separately from the prover**. That is direct
precedent for §2's refusal to collapse this into one figure: what the system
established, and what checking it covers, are different measurements and a
single number hides whichever is weaker. It also supports §4 — a per-fact
producer field is the join key that lets the two be scored apart.

The measured trusted-base gap for one prover in that world is about **8% of its
own answers**, the same shape as our axiom-footprint figure. Ours must be quoted
with its denominator, because the two available denominators differ by an order
of magnitude and only one of them is meaningful: `validate-facts.py` reports
**2,584 axiom-free on `kernel-lean`, of 2,586 on that route** — a 0.08% gap —
and prints "not comparable across routes" beside it, because `[]` is not
achievable on the SMT or CAS routes at all. The cross-route reading, 2,584 of
2,687 proved facts (a 3.8% gap), is the one `docs/math-department/12-the-chair.md`
quotes; it is arithmetically correct and mixes trust bases the schema exists to
keep apart. Quote the route-scoped figure, and say which route. Worth putting
beside the external number so ours reads as a normal engineering measurement
rather than an embarrassment. Note also that SMT-COMP
has had **no proof-exhibition track since 2023**, so there is no comparable
external pressure on that side, and our proof-carrying claim there is
uncontested rather than merely leading.

## Evidence

Every gate below was run; counts are nonzero and exit statuses are stated.

| Check | Result |
| --- | --- |
| `python3 scripts/measure-producer-channel.py --check` | exit 0; 38 EMIT / 50 ASSIST / 44 CONFIG / 0 unclassified; L2 92.1%; L3 21 of 2,455 |
| `python3 scripts/price-holdout-family.py --check` | exit 0; 20 families / 206 rows; cross-check against the isolation gate 206 = 206 |
| `python3 scripts/check-autogenesis-holdout-isolation.py` | `held_out=206 files_scanned=1133 verdict=PASS` |
| `scripts/tests/test-producer-channel-controls.sh` | 6 controls, 6 passed, exit 0 |
| `scripts/tests/test-producer-channel-controls.sh --guard-deletion` | 6 guards, each deletion kills EXACTLY 1 control, exit 0 |
| `scripts/tests/test-holdout-price-controls.sh` | 5 controls, 5 passed, exit 0 |
| `scripts/tests/test-holdout-price-controls.sh --guard-deletion` | 5 testable guards, each kills EXACTLY 1, exit 0; `empty-family` reported UNTESTED |

**Guard deletion, `measure-producer-channel.py`** — predicted 1 death each, ran 1
death each, and in every case the predicted control:

| Guard deleted | Control that died |
| --- | --- |
| `unclassified` | strip_noise disabled |
| `vacuous-emit` | EMIT set emptied |
| `vacuous-ledger` | empty fact directory |
| `blind-join` | `kernel_theorem` dropped |
| `floor-missing` | baseline key removed |
| `floor-breach` | floor raised by one |

**Guard deletion, `price-holdout-family.py`** — same, for `empty-population`,
`population-mismatch`, `recycled-family`, `id-leak`, `gate-unavailable`.
`empty-family` has no control and is reported UNTESTED rather than implied: in
this derivation a family exists only by having a held-out row, so a zero-row
held-out family is not constructible from the manifests.

**Defects the control suites found in their own subjects**, all fixed here:

1. Producer paths inside `.expect("linarith::generic (setoid) must …")` panic
   strings and `//!` module docs were being read as call sites — 2 false
   positives in `creal/linarith_bridge.rs`.
2. The METHOD line crashed with a `ValueError` from `relative_to` whenever the
   inputs were redirected.
3. The floor print crashed on a missing key once its own guard was removed, so
   guard deletion would have failed for the wrong reason.
4. Guard-deleted copies running from a scratch root moved `ROOT`, so the
   isolation gate went missing and **four of five** deletions blamed the wrong
   control. Found only because the deletion table demands *exactly one* death;
   a suite asserting "the mutant fails" would have called all five green.

All mutants are built in a scratch root. Nothing was mutated in a shared
worktree.

## Related

- [ADR-0542](adr-0542-held-out-partition-breach-repair.md) — whole-family
  amendment, the irreversibility this ADR prices.
- [ADR-0602](adr-0602-operations-are-receipts-dispatch-needs-producer-contracts.md)
  — operations are retrospective receipts; the producer contract is the
  prospective side, and is where two families were spent.
- [ADR-1589](adr-1589-decide-and-a-then-first-combinator-close-the-tactic-layer.md)
  — the tactic layer whose 62 is retired as a rate here.
- [Evidence and checker discipline](../../contributor-guide/evidence-and-checker-discipline.md)
  — the guard-deletion rule these two suites implement.
