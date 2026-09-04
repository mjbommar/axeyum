# ADR-1605: the ledger cannot tell "uncharacterised" from "absent"

Status: proposed
Date: 2026-09-04
Lane: `persona-absence-audit`

Index-summary: A fact whose prose was never written is indistinguishable, to a
reader, from a theorem that does not exist. Measured at 1,553 of 2,493 proved
facts, and it produced eleven false absence claims across the twelve persona
reviews. Characterisation becomes a derived, three-way, ratcheted measurement
with its own registered checker rather than a stored schema field; the larger
axis -- 430 kernel theorems and 762 definitions with no ledger fact at all --
is sized and left proposed.
Index-status: Proposed

## Context

`docs/math-department/` holds twelve persona reviews of the library, written
2026-09-04 by an assistant reading the fact ledger. Lane
`persona-absence-audit` re-checked **every** claim of absence in them against a
freshly rebuilt kernel index. The result is
[`AUDIT-2026-09-04.md`](../../math-department/AUDIT-2026-09-04.md): of 76
claims, **11 are false** — the thing is proved — and 12 more overstate the gap.

The eleven are not marginal. They include:

- `02`'s **number one** item, the fundamental theorem of calculus, both
  directions of which were admitted on 2026-08-27, a week before the review;
- `08`'s **number one** item, the weak law of large numbers, admitted
  2026-08-24;
- `02`'s uniform-convergence item, whose carrier *and* both interchange
  theorems landed 2026-08-27;
- `07`'s "no Stirling numbers", against ten proved theorems;
- `01`'s "no multiplicativity of the totient proved as a general property",
  against `Nat.totient_mul_of_coprime`.

Seven of the eleven landed on a single day, **2026-08-27**. Nothing about that
week was hidden. It was uncharacterised.

This is the second time the same failure has been recorded. `08`'s own file
carries a correction: its first pass reported the probability shelf as one
theorem against a real count near thirty. [ADR-1597](adr-1597-the-ftc-was-already-proved-and-the-ledger-could-not-say-so.md)
records the FTC instance. A third occurrence is a pattern with a cause.

### The cause, measured

`scripts/gen-kernel-facts.py` writes, for a kernel theorem nobody has written
prose for, a title of the form

> `[generated] kernel theorem CReal.hasDerivative_antiderivative (creal prelude, axiom-free, prose not curated)`

and a statement that begins, verbatim, "MECHANICALLY GENERATED, UNREVIEWED
PROSE -- this sentence deliberately makes NO mathematical characterisation of
the theorem."

**That refusal is correct and is why the ledger is trustworthy.** A generator
that guessed at meaning would produce a ledger nobody could cite. The defect is
not the refusal; it is that nothing marks the difference where somebody reads
it. Measured 2026-09-04 at `182d0dd7d`:

| | count | share |
|---|---|---|
| facts in the ledger | 2,764 | |
| `[generated]` titles | 1,054 | 38.1% |
| `[generated]` among **`CReal`** facts | 307 of 478 | **64.2%** |
| `Complex` / `CPoint` / `Str` | 83/128, 62/94, 64/64 | 64.8% / 66.0% / 100% |

And a class nobody had counted: **744 titles are "Mathlib v4.30 source
proposition `<Name>`"** (499 of them `proved`). Those characterise by
*reference* to an external name and add nothing of their own. A reader looking
for "Stirling numbers" does not find `Nat.stirlingFirst_succ_succ`; a reader
who already knows the Mathlib name did not need the ledger. Adding the two
classes:

> **1,553 of 2,493 proved facts — 62.3% — carry no mathematical
> characterisation of their own.**

### A second axis, larger, that nobody had measured

The ledger is not merely uninformative about what it holds. It does not hold
everything. Against the fresh kernel index (`declarations=3575`):

| | count |
|---|---|
| kernel **theorems** with no ledger fact at all | **430** |
| kernel **definitions** with no ledger fact at all | **762 of 789** |

`AlgS.Hom.firstIso` — the first isomorphism theorem, the headline result of
`04-algebra.md`, landed the same day the review was written — is one of the
430. A reviewer reading the ledger for the state of algebra sees no row for it
at all. That is worse than an uncurated row: an uncurated row at least says
something exists.

### Why the existing instruments do not close it

- `scripts/validate-facts.py` enforces structure and semantics (a `proved` fact
  with nothing `checked` fails). It has nothing to say about whether the prose
  means anything, and should not: that is not a soundness property.
- `scripts/count-landmark-facts.py` (ADR-1600, W1-4) already splits titles on
  `[generated]` and reports a landmark count. It is the right instrument for
  the question it asks — *how many results would a referee weigh?* — and the
  wrong one for this question in two ways. It counts a "Mathlib v4.30 source
  proposition" title as **characterised**, which is 499 proved facts and is
  exactly where the Stirling false absence hid. And its `--check` is an
  **exact-equality pin on four numbers**; measured on `main` at `182d0dd7d` it
  was **RED** (`baseline=2758 measured=2764`) because six facts landed and
  nobody bumped a generated file. A pin that goes red on every legitimate
  addition trains lanes to re-baseline reflexively, which is how a gate stops
  being read.

## Decision

**Characterisation is a derived, three-way, ratcheted measurement — not a
stored field.**

### 1. Three classes, derived from the artifact

A fact's characterisation class is computed from its title, not typed by hand:

- **`curated`** — prose somebody wrote, saying what the fact *is*.
- **`generated`** — the generator's `[generated]` prefix.
- **`transcribed`** — "Mathlib v4.30 source proposition `<Name>`";
  characterises by reference only.

### 2. `scripts/check-fact-characterisation.py`, registered in both gates

Implemented in this ADR's commit, registered in `scripts/check.sh`
(`fact-characterisation`, `fact-characterisation-controls`) and in the
`justfile`'s `check` recipe. Three guards, each with a distinct exit tag so two
failures are never confused:

| exit | tag | fires when |
|---|---|---|
| 2 | `MALFORMED` | a fact file is unreadable JSON, or missing `title` / `statement` / `epistemic_status`. **In every mode, including a bare report** — a report over a ledger the script could not fully read is not a measurement. |
| 1 | `PROSE_DISAGREEMENT` | a fact's title and statement disagree about generated-ness, in either direction. Also in every mode. |
| 1 | `CHARACTERISATION_REGRESSION` | (`--check`) some fragment's curated-proved count fell below the committed floor. |

**The `PROSE_DISAGREEMENT` guard found one live violation on its first honest
run.** `artifacts/facts/F-int-euler-totient-theorem.json` carried a full
curated statement of Euler's totient theorem — including the note that the
totient is this kernel's own `countRange` and not an import — under the title
"[generated] … prose not curated". Both this checker and the landmark count
scored a characterised fact as uncharacterised. The title is corrected in this
commit; `landmark` accordingly moves 1438 → 1439.

**A ratchet, not a pin.** The floor is per fragment on the **curated proved
count**, and it may only rise. Characterisation is monotone: adding
uncharacterised facts must stay allowed (the autogenesis producer has to be
able to run), removing characterisation must not. Only fragments at or above
ten curated facts get their own floor; the ledger carries about forty-five
one-fact CAS and solver fragments, and giving each a floor would make the
baseline a sixty-line file that every lane touching a CAS fact must edit —
the shared-append-point shape this repository has lost content to four times.
A single total floor covers them collectively.

### 3. No new schema field

Lane `ftc` proposed a `characterisation_status` axis in
`artifacts/ontology/fact.schema.json`, sitting beside `epistemic_status` and
`external_status`. **Considered and rejected**, for three reasons:

1. **It is derivable.** The generator already writes an unambiguous marker in
   both the title and the statement. A stored field would restate what the
   artifact already says.
2. **It would drift.** Two sources for one property is a synchronisation
   problem, and the euler-totient fact above is proof that the *existing* two
   sources already drifted. Adding a third makes the drift harder to see, not
   easier.
3. **It costs 1,054 file edits against a gated schema.**
   `fact.schema.json` sets `additionalProperties: false`, so the field must be
   added there first, and every generated fact rewritten. That is a large,
   conflict-prone diff across a directory every lane writes into, bought for
   information the checker computes in 0.2 seconds.

The narrow case a derived class cannot see — a title that *looks* curated and
says nothing, or one that is actively misleading — is real. The audit found
two: `Rat.bernoulli` is titled as if it were the Bernoulli **distribution** and
is Bernoulli's **inequality**; `Rat.markov_inequality` collides with Markov's
**principle** for anyone searching the logic shelf. Neither is fixed by a status
enum. Both are fixed by writing a better title, which the ratchet rewards and
nothing else needs to encode.

### 4. Axis two is proposed and sized, not implemented here

The kernel-vs-ledger coverage gate — 430 theorems and 762 definitions with no
fact — is the larger finding and is **not** implemented, for a stated reason:
it needs the kernel declaration index, which is a `--release` build measured
here at 2m 26s cold plus ~70 s of environment construction per query. That
cannot be a per-commit gate.

Sizing, for whoever takes it:

- **Half a day.** Add `--emit-index <path>` to
  `crates/axeyum-lean-kernel/examples/shape_search.rs` (the dump already exists
  as `--name-contains '' --limit 99999`; this only fixes a stable format).
- Commit the index as `artifacts/kernel-declaration-index.tsv`, regenerated by
  a named recipe rather than opportunistically, so the gate is cheap and
  deterministic.
- Add `scripts/check-kernel-ledger-coverage.py`: a ratchet on the *uncovered*
  theorem count (may fall, never rise), plus a hard guard that the committed
  index's declaration total matches the count the last regeneration recorded,
  so a stale index cannot report a false ABSENT — which is the exact hazard
  `docs/contributor-guide/finding-existing-lemmas.md` names.
- **The staleness guard is the hard part** and is why this is not a fifteen-
  minute job. A committed snapshot that silently lags the kernel would
  manufacture the very failure this ADR is about, at gate speed.

## Consequences

**What gets better.** The three numbers a reviewer needs are now printed by one
command that fails when they are wrong: how much of the ledger says what it
holds (940 curated proved), how much only names a declaration (1,054), and how
much only names somebody else's declaration (499). The share is 62.3% and it
can now only go down.

**What does not get better.** Nothing here writes prose. The ratchet makes
characterisation monotone; it does not make it happen. The 1,553 uncharacterised
proved facts are a real backlog and this ADR does not schedule it. What it does
is stop the backlog from being *invisible*, and stop a review being written off
a ledger that cannot say what it holds.

**Cost paid.** One new script (330 lines), one control suite (17 tests), one
four-key baseline file, two registrations, one fact title corrected. No schema
change, no fact migration, no build. Runtime 0.2 s.

**Cost deferred.** The coverage axis, sized above at roughly half a day, with
the staleness guard as the load-bearing part.

**A gate fixed in passing.** `scripts/count-landmark-facts.py --check` was red
on `main` at `182d0dd7d` and is re-baselined here (`2758→2764`, `2487→2493`,
`1432→1439`). It went red because two lanes landed six facts on 2026-09-04 and
neither bumped a generated file. If another lane bumps it concurrently the
conflict is four numbers and is trivially resolved — but the incident is the
argument for the ratchet, not an aside.

## Controls

`scripts/tests/test_check_fact_characterisation.py`, 17 tests, registered in
both gates. Mutation-verified in a scratch copy of the tree (never in the
shared worktree), unmutated suite green first:

| mutation | tests that died |
|---|---|
| A `classify` drops the `[generated]` branch | 2 (`test_generated_prefix_is_generated`, end-to-end report) |
| B `classify` drops the `transcribed` branch | 2 (`test_mathlib_transcription_is_its_own_class`, end-to-end report) |
| C `classify` falls through to `generated` | 4 (`test_written_prose_is_curated`, end-to-end, ratchet-pass, shipped-ledger) |
| D `load_facts` swallows a JSON error | 2 (`test_invalid_json_raises_and_names_the_file`, `test_malformed_ledger_exits_two_not_one`) |
| E `load_facts` drops the required-field loop | **1** (`test_missing_required_field_raises_and_names_it`) |
| F disagreement drops the generated-title direction | 2 (`test_generated_title_without_the_marker_is_reported`, bare-report) |
| G disagreement drops the marker-in-statement direction | **1** (`test_marker_under_a_curated_title_is_reported`) |
| H the ratchet never records a regression | **1** (`test_fewer_curated_than_the_baseline_fails…`) |
| I `main` ignores prose disagreements | **1** (`test_prose_disagreement_fails_the_BARE_REPORT_too`) |

Every mutation kills at least one test, and each has a **uniquely identifying**
test. Reported honestly: five mutations kill two or more, because the
end-to-end and shipped-ledger tests necessarily ride on the same predicates
they exercise. The property the rule protects — delete a guard and nothing
dies — does not occur anywhere in the table.

Two of the tests derive their subject from the authority rather than from a
fixture: `ShippedLedgerTests` runs every guard against
`artifacts/facts/` itself, so the suite fails when the real ledger regresses
and not only when a fixture does.

## Related

- [`AUDIT-2026-09-04.md`](../../math-department/AUDIT-2026-09-04.md) — the 76
  claims, the 11 false ones, and the method
- [ADR-1597](adr-1597-the-ftc-was-already-proved-and-the-ledger-could-not-say-so.md)
  — the FTC instance that started this
- [ADR-1600](adr-1600-the-kernels-metatheoretic-status-what-is-trusted-and-what-is-not.md)
  — the landmark count this sits beside
- [finding existing lemmas](../../contributor-guide/finding-existing-lemmas.md)
  — the retrieval discipline; this ADR is the ledger-side half of it
- [evidence and checker discipline](../../contributor-guide/evidence-and-checker-discipline.md)
  — the exit-status and mutation rules the checker is built to
