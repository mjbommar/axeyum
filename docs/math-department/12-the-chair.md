# 12 — The chair

Reviewer: the department head, doubling as an external referee
Verdict, 2026-09-06 (re-measured): **would sign the report, and would strike
three sentences from it before it goes out — the coverage claim, the
axiom-free headline as currently worded, and the production rate**
Last measured: 2026-09-06 at `0473d3ce8`

> "Eleven colleagues, and this time nine of them measured their own field
> instead of remembering it. Four verdicts moved up in two days. That is a
> healthy report. Now: the three numbers on your front page — are they the
> numbers you actually measured?"

> **AUDITED 2026-09-04.** Every absence claim in this file was re-checked
> against a freshly rebuilt kernel index. See
> [AUDIT-2026-09-04.md](AUDIT-2026-09-04.md) for the evidence, and the
> corrections marked **[AUDIT]** below. Across the twelve files, 11 of 76
> absence claims were false and 12 more overstated the gap; the cause is that
> the ledger characterises only 38% of its proved facts and does not cover 430
> kernel theorems at all (ADR-1605).
>
> **Correction, 2026-09-06.** Both of the audit's cause numbers have moved and
> one of them cannot be reproduced. Characterisation is now **40.7%**
> (1,093 curated of 2,687 proved, `check-fact-characterisation.py --report`).
> The **430** has no reproducible method: reviewer 10 reads today's kernel as
> 620 or 973 uncovered theorems depending on what "covered" means, and this
> chair's own count — an index theorem whose name appears nowhere in any file
> under `artifacts/facts/`, the loosest possible test — is **599 of 3,319
> (18.0%)**. Three numbers, three denominators, one direction: **the gap grew
> while the ledger grew.** Do not quote 430 again.

> **Retired 2026-09-06 (ADR-1674):** the 430 is not reproducible by its own
> method - three later readings give 599, 620, 721 and 973 on three different
> denominators. The measured, gated figure is **721 of 3,079 registered
> kernel theorem names uncovered**, ratcheted by `gen-ledger-coverage`.

## The persona

Does not do the mathematics. Reads the report, asks what is being claimed, and
asks whether an unfriendly reviewer could verify or deflate it in an
afternoon. Has seen many projects mistake volume for progress. Their two
questions are always the same: **what is assumed**, and **what did you do that
nobody else did**.

## What the ledger says

Every row re-run at `0473d3ce8`; the commands are in *How to re-measure*.

| metric | value | how it is read |
|---|---|---|
| facts in the ledger | 2,963 | `python3 scripts/validate-facts.py` |
| proved propositions | 2,687 (was 2,487 on 09-04) | same |
| **distinct** propositions established | **2,668** | 2,689 settled minus 21 that restate a sibling (`equivalent_to`) |
| open (declared frontier) | 267 | mostly transcribed Mathlib propositions as a work queue |
| refuted / conjectured / computed | 4 / 3 / 2 | boundary refutations; Collatz; two four-colour Rado numbers |
| axiom-free | **2,584 of 2,687**, all on one route | 2,586 `kernel-lean` facts, 2 of them non-empty; the other 101 proved facts are on routes that cannot claim axiom-freedom at all |
| kernel axiom census | **30, every one `AxReal.*`** | `shape_search --include-constructed --kind axiom`, 4,839 declarations |
| trusted core | **5,545 function lines**, 256 functions, 9 files (ceiling 5,900) | `check-kernel-trusted-core.py` → 5 guards, 0 failures |
| landmark facts | **1,585 of 2,687 = 59.0%** | `count-landmark-facts.py` (generated 1,095, imported 7) |
| characterised facts | **1,093 of 2,687 = 40.7%** | `check-fact-characterisation.py --report` |
| CAS residue | **45 `cas-internal` of 61**, 16 reconstructed | `check-cas-internal-residue.py --report`, floor 16 held |
| producer retirements | **67, unchanged since 2026-09-03** | the lane ledgers; zero retirement commits in the kernel crate since |
| validation errors | 0 | the ledger's own gate |
| kernel integration suites | **53** (35 here, 18 under `check-lean-gate.sh`) | `scripts/check-kernel-suites.sh --list` (was 32) |
| roadmap board | 52 items — **42 landed, 6 in progress, 4 already done, 0 not started** | recounted row by row from [00-roadmap.md](00-roadmap.md), agrees with its totals |

## The two questions

**What is assumed?** The honest sentence has changed, and the chair would
insist on the new wording. It is **not** "nothing, on every proved row". It is:

> Of 2,687 proved propositions, **2,584 carry an empty `axiom_footprint`, and
> all of them are on the `kernel-lean` route** — the only route the ledger's
> own validator permits to assert axiom-freedom. The remaining 103 are 60 CAS
> certificates, 27 SMT results, 7 labelled imports, 7 search certificates, and
> **two `kernel-lean` rows that are genuinely not axiom-free**:
> `F:schedule-critical-chain-infeasible`, which uses the whole 30-axiom
> `AxReal` shelf, and `F:nra-refutations-reconstruct-over-constructed-reals`,
> which names two construction assumptions.

That is still the strongest thing in the report and it is still checkable by a
hostile reader in one command. It is a *different* claim from the one three of
this department's documents currently make, and the difference is exactly the
kind a referee finds first. The qualifications that must travel with it are
unchanged: the kernel is a trusted base of 5,545 function lines inside a crate
of 482,185 that nobody has proved consistent (ADR-1600,
[10-logic-and-foundations.md](10-logic-and-foundations.md)), and the empty
footprint is a consequence of a design choice — no `Quot.sound`, no `funext`,
no choice — which is now *decided* rather than deferred (ADR-1595, ADR-1601)
and which two fields have since shown is not merely survivable but forced:
a polynomial ring over a function-space carrier is reachable **only** on the
setoid spine. **The metric and the limitation are the same fact**, and now the
limitation has a result attached.

**What did you do that nobody else did?** The chair's order has changed, and
one entry has been demoted.

1. **The constructive real analysis, and what grew out of it in two days.**
   Reviewer 02 — the specialist — reports 485 ℝ facts with zero open and zero
   non-empty footprints, and above them a metric layer (97), an ℝⁿ (58), an
   integration space with a *derived* measure and L¹ as a metric space (98), a
   pointfree topological carrier (53), and a power series with a radius
   carried as data because the order on ℝ is undecidable. This is now first
   because it is a body of mathematics that stands without the tooling
   argument.
2. **The metatheory with an audited encoding, which stopped being a gesture.**
   141 axiom-free `FO.*` declarations in three days: syntax, Tarski
   satisfaction, a seventeen-rule calculus, soundness, consistency, Gödel
   numbering with a proved decode round trip, Robinson's Q with a model, and Q
   with order. Plus the older IPC result with the rule set read out of the
   kernel rather than assumed. A logician can referee this.
3. **The production route — demoted, and see below.** 67 theorems retired to
   machine producers remains true and remains unmatched. It is demoted because
   it is a *rate* that has not moved for three days, and the chair will not
   lead with a rate that is flat.

## What they would not let through

- **Any coverage-parity claim against Mathlib.** Unchanged, and it survives
  four verdict upgrades. The defensible claim is per-statement dominance plus
  uncontested axes, as the cost-model note argues. Reviewer 03's finding is
  the sharpest form of why: `CC:creal-real` grades our IVT
  *constructively-stronger* than Mathlib's with footprints `[]` against
  `[propext, Classical.choice, Quot.sound]` — and grades EVT a deliberately
  non-dominant witness. A parity claim in analysis is not meaningful until it
  says which statement is meant.
- **"Empty axiom footprint on every proved row."** Measured false today, in
  the ledger's own reading: 2,584 of 2,687, and two of the exceptions are on
  the axiom-free route itself. The correct sentence is in *The two questions*
  and it is barely weaker. **A claim that is nearly true and stated as
  universal is the one a referee kills the whole paper with.**
- **"67 hand proofs retired in one week."** True on 2026-09-03 and quoted
  unchanged in five documents since. Zero retirement commits have touched the
  kernel crate since 2026-09-04, while roughly 200 new proved facts landed.
  The rate did not slow; the *work moved channel* — producers now emit
  theorems that were never hand-written, so there is nothing to retire — and
  the metric cannot see the new channel at all. Quoting a three-day-old flat
  number as a rate is the volume-for-progress mistake this chair exists to
  catch.
- **Counting all 2,687 as equivalent.** Now partly answered: 1,585 landmarks
  (59.0%) is reported beside the total and gated at push. Still to fix: the
  total itself is 2,687 while **2,668** is the number of distinct
  propositions, and this file's own last progress row printed 2,668 as the
  proved count. Two numbers, both real, one row apart.
- **The word "complete" about any shelf.** Unchanged, with one addition:
  reviewer 06 would not let "complete metric space" through either —
  `Metric.Complete` has exactly two witnesses in the whole index (reviewers 03
  and 06, measured independently of each other).
- **Treating `computed` as `proved`.** Down to two rows, both four-colour
  Rado numbers, both correctly `computed`, with the obstruction now measured
  and combinatorial (a term over 4⁶²⁵ colourings, and colourings are
  functions) rather than the numeral cost this file used to assert.
- **Anything resting on the SOS reconstruction route, until it is fixed.**
  Read on `main` at `crates/axeyum-solver/src/reconstruct.rs:3251-3297`:
  when the honest reconstruction fails with `UnsupportedTerm`, the route falls
  through to a wrapper that mints two axioms — one asserting an opaque `Prop`,
  one negating it — and renders the result under `LEAN_MODULE_THEOREM`, the
  **same** `axeyum_refutation` name the honest route uses. The minted axioms
  are visible to anyone who reads the module's axiom lines; they are invisible
  to anything that counts theorem names or exit statuses, which is what a
  consumer does. This is the one artefact in the building that is the opposite
  of the project's thesis, and the chair would hold the trust story until it
  names itself.

## The department-wide finding

**The two unwritten ADRs are written, and the thing that replaced them is not
mathematics — it is that the two instruments this department reads itself with
are both partially blind, and neither blindness is visible from inside.**

- **The retrieval index does not build the kernel.** The kernel exposes
  **31 `build_*_prelude` functions; `shape_search` calls 15.** Never built:
  the list prelude, the product metric (12 declarations reviewer 06 had to
  read out of source), and all **ten** `fo_*` modules — 141 declarations,
  reviewer 10's entire two-day shelf, invisible to the tool every other
  reviewer uses to prove an absence. Three separate files independently put
  "teach the index my shelf" on their Next Five this week. A false ABSENT
  manufactured this way is indistinguishable from a true one, and the
  2026-09-04 audit found eleven of them.
- **The ledger does not cover the kernel, and it is falling further behind.**
  599 of 3,319 index theorems (18.0%) are named nowhere in any fact file —
  including `AlgS.Hom.firstIsoClassical`, the classical form of reviewer 04's
  headline result. 1,594 proved facts (59.3%) carry no characterisation of
  their own. And *whole capabilities* have no row at all: **five of the
  fifteen committed geometry certificates** have zero facts (positive control:
  `euler-line`, 6), the 7,759-line validated-numerics enclosure layer has
  zero, and the CAS's matrix groups and character tables have zero (positive
  control: Smith normal form, 1). Under
  [ADR-0601](../research/09-decisions/adr-0601-three-producers-one-trust-anchor.md)
  those are correctly `cas-internal` and correctly count as zero proved — the
  defect is that the ledger cannot say they *exist*.
- **And the ledger's generated prose actively produces false readings.** It
  did it again this week, on the headline item of the file it hit: all seven
  power-series facts carry `[generated]` titles, which is how reviewer 02's
  own shelf came to be misdescribed by reviewer 02.

The chair's judgement: **the ledger is the product, and a product that cannot
enumerate itself cannot be refereed.** This is the same class of item as the
two ADRs were in September — a small amount of tooling work that six fields
are paying for — with one difference that makes it worse: an unwritten ADR
announces itself, and a blind index reports success.

**A second finding, smaller and about process.** Two held-out evaluation
families were spent in one week (2026-09-03, the `ring-identity-v1` producer
contract; 2026-09-05, `psatz-sum-of-squares-v1`), taking the split policy to
nine amendments. Reviewer 01 now has a theorem — Chebyshev's π(x) bounds —
that is briefable only by spending a third. Nobody has decided what a blind
family is worth against a theorem, so it is being decided one lane at a time,
by lanes that do not know they are deciding it.

## Next five, in their priority order

All five of the 2026-09-04 list are closed (kept below for the record). This
is the list the chair would write today, with a measurement behind each.

- [ ] **1. Make the axiom-free headline say what it measures, everywhere it
      appears.** "2,584 of 2,687 proved facts, all on the `kernel-lean`
      route", with the two non-empty `kernel-lean` rows named. Half a day of
      writing across this file, `README.md`, `docs/PROJECT-STATE.md` and
      `docs/plan/global/10-status.md`, then a checker that reads the number
      from `validate-facts.py` rather than from prose. Ranked first because it
      is the front-page claim and it is currently overstated.
- [ ] **2. Remove or rename the axiom-minting fallback in the SOS
      reconstruction route.** `reconstruct_sos_certificate_wrapper_to_lean_module`
      is entered exactly when reconstruction *fails* and renders under the
      honest route's theorem name. Make it a labelled decline, or give it its
      own name so no counter can conflate the two populations. Short, and it
      is the only place in the building where the evidence format hides a
      distinction its producer makes.
- [ ] **3. Teach the retrieval index the whole kernel, and derive its group
      list from the build calls.** 31 builders, 15 built. The list prelude,
      `metric_prod`, and all ten `fo_*` modules are unreachable by the tool
      every lane uses to prove an absence — and `shape_search.rs` already
      carries a cross-check that its group list matches, which passes because
      both halves omit the same modules. Asked for independently by reviewers
      02, 06 and 10 this week.
- [ ] **4. A ledger row for every capability, then a coverage ratchet.**
      Facts for the five orphan geometry certificates, the enclosure layer and
      the CAS group theory — classified `cas-internal` where that is the
      truth — and a gate that fails when the uncovered-theorem share rises.
      The share is 18.0% today by the loosest test; the audit's 430 could not
      be reproduced by its own method, which is itself the argument for
      making the number a gated measurement instead of a doc.
- [ ] **5. Replace the retirement count with a metric that measures the
      current channel, and decide the price of a held-out family.** 67 has not
      moved in three days while producers emitted theorems nobody ever wrote
      by hand; count what the producers *established*, not what they replaced.
      Beside it, one written rule for when a producer contract may cite a
      held-out row — nine amendments and two families spent in a week is a
      decision being made by default.

### The 2026-09-04 five, at 2026-09-06 — all closed

- [x] **1. The quotient and extensionality ADR.** — *done 2026-09-04, ADR-1595: setoid quotients, no `Quot.sound`; the first iso theorem cost three lines.* Add `Quot.sound`, commit to
      setoid quotients, or admit it in a labelled second tier with separately
      reported footprints. Unblocks or scopes reviewers 04, 05, 06, 09.
      *Verified 2026-09-06: the index carries **zero declarations of quotient
      kind**, which is stronger than the ADR's own claim, and reviewers 04, 05,
      06 and 09 have all since moved their verdicts up.*
- [x] **2. The classical-axiom policy ADR.** — *done 2026-09-04, ADR-1601: classical principles as hypotheses, 11 binders and 0 obligations.* Excluded middle as a labelled
      footprint entry, or as an explicit hypothesis discharged at use — the
      route `Nat.em_implies_lnp` already demonstrates. Unblocks or scopes
      reviewers 03, 08, 10. *Verified: monotone convergence landed in exactly
      that shape, and reviewer 03 says plainly it is not the answer they
      wanted — which is the honest outcome of a decision, not a failure of it.*
- [x] **3. A landmark count beside the total.** — *done 2026-09-04: `scripts/count-landmark-facts.py` with an exact-count baseline gated at push.* Define what counts as a named
      result, count them, and report both numbers. Their view: 2,487 is a real
      number that tells a reader nothing about depth, and the first hostile
      reviewer will say so. *Today: 1,585 of 2,687, 59.0%, up from 57.6%.*
- [x] **4. Close one `computed` result into a kernel statement.** — *done 2026-09-04 (W1-1): `IsRadoNumber` stated in-kernel and Schur's `R_2(x=y+z)=5` proved with both halves from search; the four-colour numbers stay `computed`, correctly.* The Rado
      number is the flagship candidate. It converts the project's thesis from
      an architecture diagram into a demonstrated result. *And the reason the
      remaining two stay `computed` is now measured (function-space
      enumeration), not asserted (numeral cost) — the file's old reason was
      wrong.*
- [x] **5. Write down the kernel's own metatheoretic status** — *done 2026-09-04, ADR-1600: the kernel's metatheoretic status, trusted base 5,526 lines.*, per reviewer
      10. What is trusted, what is cross-checked against official Lean, and
      what a relative consistency result would require. Nobody outside can
      assess the headline metric without it. *Re-measured today at **5,545**
      lines / 256 functions / 9 files, ceiling 5,900, 5 guards and 0 failures;
      ADR-1600's 5,526 is superseded twice over (5,534 on 09-05, 5,545 today).*

## Progress log

| date | change | evidence |
|---|---|---|
| 2026-09-04 | File created. Baseline: 2,487 proved / 262 open / 4 refuted, empty footprint throughout (**corrected 2026-09-06: 2,584 of 2,687, all on the `kernel-lean` route, ADR-1674**), 67 producer retirements in one week. Department-wide finding: two unwritten ADRs block six of twelve fields. | ledger snapshot at `1856cdb3c` |
| 2026-09-04 | **Next Five items 1, 3 and 5 landed.** W0-1 decided by measurement (ADR-1595, setoid quotients); the landmark count shipped as a registered checker with its own controls — 1,432 landmarks of 2,487 proved, 57.6%; ADR-1600 records the kernel's metatheoretic status. Item 2, the classical-axiom policy, remains the outstanding decision. Off-roadmap: the safety-matrix gate was found red on main since 2026-08-31 and regenerated. | `8b4f277d4`, `2a640c9b6` |
| 2026-09-06 | **Two days of the board, measured.** Ledger at `493045f00`: 2,668 proved / 267 open / 4 refuted, every proved fact with an empty axiom footprint (**corrected 2026-09-06: 2,584 of 2,687, ADR-1674**). Roadmap board: 52 items, **41 landed, 7 in progress, 4 already done, 0 not started** (the board's own totals table, recomputed from its rows). Landed since the chair's first reading, one line each: Schur's number and `R(3,3)=6` from search; the category of groups with products; Hall's marriage theorem (six slices); inclusion–exclusion; fields with apartness and vector spaces; L¹ as a metric space; the topological carrier as a frame; conics as a family; first-order soundness and consistency of Robinson's Q; Gödel numbering with the decode round trip; the incidence axioms with the rational and real planes as models; Fermat's two-squares theorem; a sum-of-squares producer whose theorems carry no hand-written proof; the first Hoeffding-class concentration rate. **What the chair would still not let through**: the coverage claim, unchanged — the department-wide finding (62% of proved facts uncharacterised, ADR-1605) is being worked by the characterisation gate but is not closed; and two evaluation families were spent this week by producer contracts citing held-out rows as non-examples (ADR-0542 amendments on 09-03 and 09-05), which the chair would count against process, not mathematics. Three coordinator sessions now share one push protocol; 63 history rows on the board record every landing by commit. | `493045f00`; `validate-facts.py` 0 errors |
| 2026-09-06 | **The whole file re-measured after the eleven fields were rewritten; the verdict gains two strikes.** Every number in *What the ledger says* re-run at `0473d3ce8`. **Three corrections to this file's own claims.** (a) *"Empty footprint on every proved row"* is false: **2,584 of 2,687**, all on `kernel-lean`, with two `kernel-lean` rows genuinely non-empty (`F:schedule-critical-chain-infeasible` names the 30-axiom `AxReal` shelf; `F:nra-refutations-reconstruct-over-constructed-reals` names two construction assumptions) and the other 101 on routes the validator forbids from claiming axiom-freedom at all. Reviewer 04's re-measure reported this could not be checked mechanically because footprints live in evidence prose — that is wrong, `axiom_footprint` is a **top-level structured field on all 2,687 proved facts** and the validator gates on it. (b) The previous row's *"2,668 proved"* at `493045f00` is a misquote: re-read from the tree at that commit, it is **2,678 proved / 267 open / 2,954 facts**. 2,668 is today's count of *distinct* propositions (2,689 settled minus 21 restatements). (c) The board is **42 landed / 6 in progress / 4 already done / 0 not started of 52**, recounted row by row — the previous row's 41/7 was off by one item; the board's own totals table is correct. **Numbers that moved since 09-04:** proved 2,487 → 2,687; landmark 1,432/57.6% → **1,585/59.0%**; characterisation 38% → **40.7%**; trusted core 5,526 → **5,545** lines; kernel integration suites 32 → **53**; CAS residue 46 of 60 → **45 of 61 (73.8%)**, floor 16 held; kernel axioms **30, all `AxReal.*`** in a 4,839-declaration index (3,319 theorems). **Not moved:** producer retirements, **67 since 2026-09-03**, with zero retirement commits in the kernel crate since 2026-09-04 — so the rate this file led with is three days flat and is struck from the front page. **The department-wide finding is replaced.** Both blocking ADRs are written; what replaced them is that the two instruments this department reads itself with are blind in ways success looks like: `shape_search` calls **15 of the kernel's 31 `build_*_prelude` functions** (no list prelude, no `metric_prod`, none of the ten `fo_*` modules — 141 declarations of reviewer 10's shelf), and the ledger names **none of 599 of 3,319 index theorems (18.0%)**, `AlgS.Hom.firstIsoClassical` among them, while five of fifteen geometry certificates, the whole 7,759-line enclosure layer and the CAS's matrix groups and character tables carry **zero facts** (positive controls in the same queries: `euler-line` 6 facts, Smith normal form 1). The audit's **430** uncovered theorems could not be reproduced by its own method and is retired. A second, process finding: nine amendments to the held-out split policy, two of them this week from producer contracts. New item 2 on the Next Five is read directly off `main`: the SOS reconstruction route's `UnsupportedTerm` fallback mints two axioms and renders under the honest route's `axeyum_refutation` name (`reconstruct.rs:3251-3297`, `LEAN_MODULE_THEOREM` at 2114). **Not re-measured here:** `footprint_closure_audit` (its prebuilt binary is dated 2026-08-30 and would describe an older kernel; the re-measure recipe below now says so), and the FO declaration count (141), the `metric_prod` count (12) and the enclosure layer's line count (7,759), which are reviewers 10, 06 and 11's numbers and are attributed as theirs — what this chair measured about all three is only that the index does not build them and the ledger does not name them. Ledger and kernel measurements were taken at `9f2489a1f` and re-confirmed valid at `0473d3ce8`: nothing under `artifacts/` or `crates/` differs between the two. | `0473d3ce8`; `validate-facts.py` 0 errors, `count-landmark-facts.py`, `check-fact-characterisation.py --report`, `check-kernel-trusted-core.py`, `check-cas-internal-residue.py --report`, `shape_search --include-constructed --kind axiom` (built 17:15, after the last kernel commit at 17:13) |

## How to re-measure

```sh
python3 scripts/validate-facts.py          # facts, routes, and the axiom-free count
python3 scripts/count-landmark-facts.py    # landmark share, generated and imported splits
python3 scripts/check-fact-characterisation.py --report
python3 scripts/check-kernel-trusted-core.py
python3 scripts/check-cas-internal-residue.py --report
scripts/check-kernel-suites.sh --list      # read the header line, not the row count

# The kernel's own axiom census. --include-constructed is REQUIRED (without it the
# CReal/Complex/Metric/Geo/Top groups are not built) and the index still omits the
# list prelude, metric_prod and all ten fo_* modules -- see the department-wide
# finding. Rebuild if the binary predates the newest kernel commit.
target/release/examples/shape_search --include-constructed --kind axiom

# Index theorems the ledger names nowhere (the loosest possible coverage test):
target/release/examples/shape_search --include-constructed --kind theorem --limit 8000 \
  | awk '$1=="MATCH"{print $2}' > /tmp/thms.txt
python3 - <<'PY'
import glob
blob="\n".join(open(p).read() for p in glob.glob('artifacts/facts/F-*.json'))
n=[l.strip() for l in open('/tmp/thms.txt')]
m=[x for x in n if x not in blob]
print(f"{len(m)} of {len(n)} index theorems named in no fact file")
PY
```

**Not a re-measure**: `git log --format=%s | grep -ciE 'retire|producer'` was in
this block until 2026-09-06. It counts commit *subjects* containing a word; it is
not the retirement count and it moves when a lane renames a commit. The
retirement total lives in the lane ledgers
(`docs/plan/status/481-structures-ordered-setoid.md`: ADR-1589's 62 plus 5) and
should become a derived, gated number — Next Five item 5.

**Also not run here**: `cargo run --release -p axeyum-lean-kernel --example
footprint_closure_audit`. It is the right check for the widened-footprint
question, and its prebuilt binary is dated 2026-08-30, so it describes an older
kernel in every direction — absent, present, and how big. Rebuild before quoting
it.

## Related

- [The cost model and Pareto position](../formalized-math-2026-08/07-the-cost-model-and-pareto-position.md)
  — why the claim is per-statement dominance, not coverage
- [README.md](README.md) — the full board and the shared snapshot
- [Computable knowledge](../research/00-orientation/computable-knowledge-world-graph.md)
  — where this library is proposed to go next
