# ADR-1674: one coverage number, one fact per capability, and a headline that says what it measures

Status: accepted
Date: 2026-09-06
Lane: `ledger-coverage`

Index-summary: Three ledger blind spots, closed by measurement. The kernel-vs-
ledger coverage figure had three irreconcilable values and its published one
(430) could not be reproduced by its own method; it becomes 721 of 3,079,
fixed in `gen-ledger-coverage.py` and defended by a `--ratchet` over registered
theorem NAMES that a fact naming nothing cannot satisfy. Four bodies of real
work with no fact row get one, at `computed` rather than `proved`, because
their evidence is `cas-internal` under ADR-0601. And the "empty axiom footprint
across every proved fact" headline is false as worded -- it is 2,584 of 2,687,
all on `kernel-lean`, with two named exceptions -- so it is reworded wherever
it appears unqualified. A regex gate for the false wording is NOT shipped, and
the measurement showing why is recorded here.
Index-status: Accepted

## Context

Three findings put this lane here. They are independent, and each is a case of
the same thing: a number that nobody could re-derive.

### 1. The coverage figure had three values and the published one did not reproduce

"How much of the kernel does the fact ledger claim?" had, on one tree, three
answers in circulation: 599 uncovered by one scan, 620 by "the name appears
nowhere", 973 by "no fact names it as its `kernel_declaration`". The figure the
documents actually published was a fourth, **430**
([ADR-1605](adr-1605-the-ledger-cannot-tell-uncharacterised-from-absent.md)
§ the coverage table, and
[`AUDIT-2026-09-04.md`](../../math-department/AUDIT-2026-09-04.md)), and
**neither source recorded the query that produced it**. It could not be
reproduced by its own method, because its own method was not written down.

There was already a script for this, `scripts/gen-ledger-coverage.py`, with a
carefully argued denominator. Two things were wrong with it, and both were
invisible:

* **Its committed artifact was stale.** It reported 2,539 kernel theorems; a
  fresh `--release prelude_theorem_inventory --include-constructed` on the same
  tree prints **3,079**. Nothing was broken — nobody had regenerated it.
* **`--check` was not a ratchet.** It compares the committed artifact against a
  fresh generation, so it fails on staleness and on nothing else. Regenerating
  satisfies it *however far coverage has fallen*. A lane could delete every
  fact in a prelude, run the generator, commit, and the gate would be green.

### 2. Four bodies of real work had no fact row at all

Zero facts existed for the CAS enclosure layer (7,759 lines), the matrix-group
work (3,161 lines), the character tables (1,615 lines), and five of the fifteen
committed geometry certificates — including
`tetrahedron-medians-concurrent` and
`tetrahedron-perpendicular-bisectors-concurrent`, which are the only solid
geometry in the system. ADR-1605's finding was that an unwritten fact is
indistinguishable from a theorem that does not exist; this is that finding at
its largest.

### 3. The axiom-free headline is false as worded

Measured independently for this ADR, over `artifacts/facts/*.json` and
cross-checked against `scripts/validate-facts.py`'s own summary line:

| | count |
|---|---|
| proved facts | **2,687** |
| carrying an empty `axiom_footprint` | **2,584** |
| non-empty | **103** |
| proved on `kernel-lean` | 2,586 |
| `kernel-lean` **with a non-empty footprint** | **2** |

The claim "empty axiom footprint across every proved fact" is therefore false,
and it is not merely a stale count. **It is the wrong shape.** Three of the six
proof routes structurally cannot report an empty footprint:
`AXIOM_FREE_CAPABLE` in `scripts/validate-facts.py` is the one-element set
`{kernel-lean}`, and the validator *fails* a `[]` on `cas-certificate`,
`smt-term-level`, `smt-clausal`, `search-certificate` and
`imported-kernel-lean`. So a universal over the ledger has never been available
and never will be.

This is a sharper statement than "the rest are CAS-internal residue labels",
which was the circulating description. Of the 103 non-empty: 60
`cas-certificate`, 17 `smt-term-level`, 10 `smt-clausal`, 7
`search-certificate`, 7 `imported-kernel-lean`, and 2 `kernel-lean`. Only 60
are CAS residue; 101 are "on a route that cannot claim it"; 2 are real
exceptions.

## Decision

### 1. One coverage number, with its method in a script and a ratchet under it

The denominator stays what `gen-ledger-coverage.py` already argued for: every
distinct `Declaration::Theorem` across every constructed prelude. It includes
`fo_*`, `metric_prod` and the list prelude to exactly the extent
`prelude_theorem_inventory --include-constructed` prints them — this ADR does
not add or remove a prelude, and the count moves when that tool's coverage
moves. **Measured 2026-09-06: 2,358 of 3,079 registered, 721 not.**

`--ratchet` is added, over `artifacts/ledger-coverage-baseline.json`, which
lists the registered theorem **names**. The gate fails when any baselined name
is no longer registered by any fact.

Three properties are deliberate:

* **It ratchets over a SET, not a count.** A swap — one theorem loses its fact,
  another gains one — leaves the count unchanged and fails the gate.
* **It cannot be satisfied by a fact that names nothing.** The population is the
  INTERSECTION of the kernel's theorem inventory with the names facts claim.
  Writing a fact about a declaration the kernel does not carry adds nothing to
  it. This is not an argument; it is control 2 in the mutation table below,
  run.
* **It is one-sided.** Coverage going up is not a finding. Requiring a lane to
  raise the baseline in the same commit as the fact it registers would make the
  path of least resistance *lowering the baseline*, which is the failure mode
  the gate exists to prevent.

Registered as `python3 scripts/gen-ledger-coverage.py --check --ratchet` in both
`justfile` and `scripts/check.sh` — one invocation, so it costs no extra
inventory build.

**430 is retired** wherever it was quoted, and the reason is recorded beside
each use rather than the number being silently swapped. ADR-1605's chosen
example survives the correction and is kept: `AlgS.Hom.firstIso` is still
unregistered, as are 101 of the 151 theorems in its `characterization` prelude.

### 2. One fact per unrecorded capability, at the status the evidence supports

Three land in this ADR's first pass, all `epistemic_status: computed`:

* `F:cas-enclosure-layer-certified-real-number-enclosures`
* `F:cas-matrix-groups-orders-and-isomorphisms`
* `F:cas-character-tables-verified-over-cyclotomic-fields`

`computed`, not `proved`, and **the row says so in its own `notes`** rather than
leaving a reader to infer it from the route. Every checker is
`cargo test -p axeyum-cas`, so `validate-facts.py` classifies the evidence
`cas-internal`, and under
[ADR-0601](adr-0601-three-producers-one-trust-anchor.md) §1 the CAS is a
producer of candidates, never of trust. Each carries a non-empty
`axiom_footprint` naming what it actually rests on, including the disclosure
that the certificate verifier shares a crate with the search that produced the
certificate.

The character-table row carries a second reason that outlives any future kernel
bridge, and it is written into the footprint as a named assumption: the six
verified conditions (orthogonality both ways, integral degrees, unique trivial
character, Galois consistency) **do not imply representability**. An accepted
table is consistent with being `G`'s character table; it is not proved to be
one, because none of the conditions exhibits a representation. A later lane
must not upgrade that row to `proved` on a bridge alone.

The five geometry certificates are filed the same way their ten committed
siblings are — `proof_route: cas-certificate`, no `cas_substance` block, since
none has a kernel bridge and `check-cas-substance.py` rejects the block on a
fact that is not kernel-reconstructed.

### 3. The headline says what it measures

The form to use, everywhere:

> 2,584 of the 2,687 proved facts carry an empty `axiom_footprint`, all of them
> on the `kernel-lean` route — the only route that can make the claim, since
> `validate-facts.py` rejects an empty footprint on the other five. Of the 103
> remaining, 101 are on those five routes and 2 are `kernel-lean` exceptions:
> `F:schedule-critical-chain-infeasible` and
> `F:nra-refutations-reconstruct-over-constructed-reals`.

Do **not** reach for "all `kernel-lean` facts are axiom-free" as the safe
qualified form. It is false by exactly two, which is the bug this rewording
exists to remove, running in the other direction.

This is not a retreat. termCOMP has required certification since 2007 and
scores the checker separately from the prover, and AProVE's certified
configuration recovers 946 of its own 1,030 uncertified YES answers — so ~8% of
its answers use techniques CeTA cannot check
([`competition-landscape-2026-09`](../02-ecosystems/competition-landscape-2026-09/adjacent-reasoning-arenas.md)).
Reporting a trusted-base gap precisely is the field's established practice. Our
103 of 2,687 is ~4%. The two numbers are **not** like for like — theirs counts
answers whose proof the checker cannot check at all, ours counts checked facts
whose footprint is non-empty — and no dominance claim is made on the
comparison.

### 4. No regex gate for the false wording. This is measured, not conceded.

The brief for this lane asked for a gate that fails when a document states the
unqualified claim, *if one can be written that cannot fire on a correct
sentence*. It cannot, and the reason is structural rather than a matter of
tuning the pattern: **the retraction and the offence are the same string.** A
document that corrects the claim does so by quoting it.

Measured, on this tree, with the obvious gate — a universal quantifier
(`every|all` + `proved|settled` + `fact|row|theorem`) in a two-line window with
`axiom-free|axiom footprint`, excused by an adjacent route name or count:

| | |
|---|---|
| raw hits | 8 |
| excused by the qualifier heuristic | 6 |
| would FAIL the gate | 2 |

It is wrong in **both directions, in the same file**:

* **False positive.** It fails on `docs/math-department/12-the-chair.md:121`,
  which is inside the section that *labels the claim as measured false*.
* **False negative.** It excuses `12-the-chair.md:284` — `every proved fact
  with an empty axiom footprint`, a genuinely false sentence — because the same
  line contains `2,668`, and "carries a count" was the exculpating signal.

A checker that passes the false sentence and fails the correction is worse than
no checker, which is this repository's standing rule. So the gate is skipped and
this measurement is the deliverable in its place. What defends the wording
instead is the `--ratchet` above (for the coverage number) and
`validate-facts.py`'s own `routes:` line, which already prints the honest form
and is the one command a referee should be pointed at.

## Consequences

* The coverage number is reproducible by one command and cannot silently go
  backwards. It is also, now, visibly bad: 721 of 3,079 kernel theorems are
  claimed by no fact, and `artifacts/ledger-coverage.json` names every one.
* `gen-ledger-coverage.py`'s per-prelude report was misfiling 151 theorems. The
  `characterization` and `list` preludes post-date its namespace map, so `AlgS`,
  `Alg`, `CatS` and `List` all fell through to the `logic` catch-all — reporting
  `logic` as 206 theorems for the 55 it owns. Invisible in the overall counts,
  because the denominator is a set of names and does not care which bucket
  prints them. Fixed, with a positive control asserting that `Acc`, `Decidable`,
  `Sigma` and the bare logic names still bucket to `logic`.
* **A mutation suite that had never run.** `scripts/tests/mutation_controls.py`
  contained two `SUITES["ledger-coverage"]` assignments 327 lines apart; the
  second replaced the first, discarding seven guards. Merged. This is the
  additive-merge hazard one level up from source: `lane-merge-additive.py` exists
  because "keep both sides" of a Rust file does not parse, but "keep both sides"
  of a dict assignment parses fine and silently discards one. The same file also
  holds three byte-identical `SUITES["self-demo"]` assignments and three
  definitions each of `main`, `run_demo` and `check_anchors` — reported, not
  fixed here, since they are other checkers' guards.
* Four unqualified sentences remain in `docs/math-department/`, which another
  session owns and was actively rewriting on the day this landed. They are
  listed in `docs/plan/status/ledger-coverage-2026-09-06.md` with line numbers
  and suggested replacements, for that owner to apply.

## Mutation table — RUN, not predicted

`python3 -m scripts.tests.mutation_controls ledger-coverage`, exit 0, baseline
green at **50 tests**. All 17 guards killed at least one test; none survived.
The six added by this ADR:

| guard deleted | tests killed |
|---|---|
| the registered population is intersected with the kernel inventory | 1 |
| `ratchet_lost` reports baselined names no longer registered | 3 |
| a lost baselined theorem makes the gate exit non-zero | 2 |
| an empty baseline is refused rather than silently passing | 1 |
| a missing baseline file is an error, not absent-therefore-green | 1 |
| the `characterization`/`list` namespaces are not swept into `logic` | 4 |

The two that kill more than one do so because an end-to-end `main()` test
exercises the same function as its unit test. Reported as measured rather than
filed down to one.

End-to-end controls on the real tree, all three in one harness run:

| control | result |
|---|---|
| 0 positive — untouched tree | `baseline=2358 registered=2358 lost=0`, rc 0 |
| 1 negative — remove `F:acc-inv` | `baseline=2358 registered=2357 lost=1`, rc **1**, stderr names `Acc.inv` |
| 2 gaming — add a fact naming a theorem the kernel does not declare | registered 2358 → 2358, ratchet unmoved |

Control 2 is the one that matters: it is the property the whole design rests
on, and it is run rather than argued.

## Alternatives rejected

* **Write a new `check-kernel-theorem-fact-coverage.py`.** Rejected:
  `gen-ledger-coverage.py` already existed with a better-argued denominator than
  a new script would have started with, and a second implementation of "which
  theorem is this fact about" is the silent divergence CLAUDE.md warns about —
  that script already imports `theorem_of` from `check-fact-depends-derived.py`
  for exactly this reason. The lane brief offered this option; the finding is
  that step 0 of a brief ("does it already exist?") answered it.
* **Ratchet on the unregistered COUNT, requiring it never to rise.** Rejected:
  it makes every newly admitted kernel theorem a build break for the lane that
  admitted it, and the cheapest fix would be a fact naming the theorem and
  saying nothing — precisely the empty-fact shape the ratchet is meant to
  exclude.
* **File the three CAS capability facts as `proved`.** Rejected under ADR-0601
  §1: the checkers never leave the CAS.
* **Ship the regex gate with an allowlist pinning the four sentences in
  `docs/math-department/`.** Rejected: those files were being rewritten by their
  owner the same day, so the pins would go red on their next edit, and a gate
  whose failure mode is "somebody else fixed a document" trains people to edit
  the allowlist.
