# ADR-1780: A reduction link carries the derivation AND the renaming

Status: accepted
Date: 2026-09-08
Index-summary: Closes ADR-1750's own named open item — `sat_bv_backend` checked its inprocessed `unsat` against the REDUCED formula, so the BVE link was trusted rather than checked. The obstacle ADR-1750 identified was right and was the whole of it: `compact` renumbers, so the passes' `DRAT` prefix (original variables) and the search's steps (compacted variables) could not be concatenated. `ReductionLink` (`axeyum_cnf::reduction_link`) carries both halves — a flat prefix always held in ORIGINAL space plus one composed variable bijection — so any number of weakening and renumbering passes, in any interleaving, collapse to one checkable object. Measured: an inprocessed `QF_BV` `unsat` now verifies against `encoding.formula()`, and the coverage flag is RETURNED by the call that chose the formula rather than asserted beside it, so the two cannot disagree. Two mutations kill it — corrupting one derived clause ("DRAT step 1808 is neither RUP nor RAT") and dropping the renaming — each killing exactly the two solver tests that decide an `unsat` under inprocessing and none of the other 28. A third finding: `xor_propagate`'s Gaussian-implied units are entailed but not `RUP`, so under `prove_unsat` they are dropped rather than allowed to force a `reduced` verdict nobody chose.
Index-status: accepted

## Context

[ADR-1750](adr-1750-a-reducing-pass-must-record-what-it-derived-not-what-it-deleted.md)
established the obligation a reducing pass owes — record what it **derived** —
and shipped it: `axeyum_cnf::inprocess::inprocess_into` streams each pass's
derivation into the caller's sink before the search writes a byte, and
`solve_with_drat_proof_inprocessed` emits one `DRAT` proof of the original
formula end to end.

It also named, in its own "Open" section, what it had not done:

> `sat_bv_backend` still checks its `unsat` against the reduced formula, so with
> `cnf_inprocessing` on the BVE link is trusted rather than checked. Not
> unsound — the chain holds by equisatisfiability — but the checkable artifact
> covers one link, which is exactly the shape ADR-1721 names. The machinery now
> exists; the obstacle is that the backend also `compact()`s, which renumbers
> variables and breaks the correspondence between prefix and searched formula.

That diagnosis was correct and complete. The backend did not lack a derivation;
it lacked a way to put the derivation and the search's steps in the same
variable space. Three separate lanes on 2026-09-07/08 independently named this
gap as the real blocker on enabling inprocessing — ahead of cost and ahead of
model reconstruction, the latter of which was re-measured as **not** broken
(`reconstruct_sat_result` composes compaction with reconstruction,
`handle_sat_result` replays the model against the ORIGINAL assertions, and a
bad model returns `Unknown`; 173 files cross-checked against declared `:status`
with zero disagreements).

## Decision

**1. A reduction link is one object carrying both halves, because there are
exactly two ways a pass can move the formula away from the caller's.**

| a pass … | owes | carried by |
|---|---|---|
| weakens (adds/deletes clauses) | a `DRAT` derivation of what it **added** | `ReductionLink::record` |
| renumbers (a variable bijection) | the bijection | `ReductionLink::rename` |
| neither, but changes the formula | nothing it can express | `ReductionLink::mark_unjustified` |

The prefix is stored in the **original** variable space at all times:
`record` maps incoming steps through whatever renaming is already composed, and
`rename` composes rather than replaces. So passes and renamings may interleave
in any order and the link stays one flat prefix plus one bijection. That is
what makes it reusable rather than a BVE special case — subsumption,
vivification and BVE already share it, and a blocked-clause elimination or a
second compaction would need no new machinery.

**2. The coverage flag is returned by the call that chose the formula, never
asserted beside it.** `ReductionLink::check_unsat` returns
`ProofCoverage::Original` or `ProofCoverage::Reduced(reason)` from the same
branch that selected which formula to check against. There is one place that
decides, so the flag and the check cannot disagree. `sat_bv_backend` translates
it into a **partition**: exactly one of
`unsat_proof_checked_against_original` / `unsat_proof_checked_against_reduced`
is emitted per checked `unsat`, so a consumer reading one key cannot mistake
its absence for a pass. Every fallback carries its cause as an enum variant
(`Unjustified`, `OverBudget { steps, budget }`, `RenamingOutOfRange`), not as
free-form prose, so a new cause cannot be added silently.

**3. `xor_propagate`'s Gaussian-implied units are dropped under `prove_unsat`,
not trusted.** The units the stage appends are entailed by the formula, but
they are derived by Gaussian elimination over the recovered XOR subsystem and a
Gaussian-implied unit is not `RUP` in general — ADR-1750 says the same about
the XOR route in its own words ("XOR reasoning is not RUP"). Under
`prove_unsat` the augmentation is therefore not applied
(`xor_propagate_skipped_for_proof`), rather than left to break the one link in
the chain no `DRAT` step can justify. **Which way this trade runs is the point:
the units only strengthen propagation, so dropping them costs speed, not
soundness — while keeping them would cost the certificate, and the certificate
is the product.** Emitting a `DRAT` derivation for them (via the resolution
chain `xor_gauss_drat_refutation` already builds for the empty clause) is the
route that would recover both, and is not taken here.

**4. Recording is gated on `prove_unsat`.** The prefix is proportional to the
FORMULA, not to the search: ADR-1750 measured BVE's at 37.7 M steps on a 3.1 M
variable instance against the search's ~36 k. A prefix nobody will check is
pure cost, and `InprocessOptions::OFF` remains the default everywhere.

**5. The in-RAM concatenation is bounded, and exceeding the bound is a visible
`reduced` verdict.** `MAX_LINKED_PROOF_STEPS` (8 M) exists because an unbounded
`Vec<DratStep>` at ADR-1750's measured prefix sizes is several gigabytes before
the checker allocates anything, which would turn a checked `unsat` into an OOM
on exactly the instances where inprocessing pays. Over the bound the check
falls back and reports `unsat_proof_reduced_reason = 2` with the step count it
would have needed. The streaming route past it already exists — a search
writing through `ReductionLink::lifting_sink` into a `TextProofSink`, checked
by `check_drat_backward_reader` — and is deliberately not wired. **The headroom
is thinner than the constant suggests**: over the 200-file `QF_BV` parity list
the largest prefix was 1,971,102 steps, so the cap clears the worst observed
instance by 4.06x, and the concatenation's peak allocation is about twice the
step count implies because `check_unsat` clones the stored prefix. A larger
corpus should be expected to cross it, and the right response is to wire the
streaming route, not to raise the constant.

**6. `cnf_inprocessing` stays OFF.** This ADR removes the certificate blocker;
it does not spend it. The flag is measured as not a net win at a 24 s budget
(186 decided / PAR-2 960.5 at best against the baseline's 184 / 926.8), and
ADR-1750's break-even table (59k–131k conflicts, median ~92k) is what a
scheduling decision should be made against. Whether the proofs check and
whether the passes pay are two questions, and only the first is answered here.

## What makes the test able to fail

The headline test is
`sat_bv_backend::tests::inprocessed_unsat_is_checked_against_the_original_formula`:
decide a `QF_BV` `unsat` with inprocessing and `prove_unsat` on, and require
`unsat_proof_checked_against_original`. On its own that assertion is true and
worthless if the reduction did nothing, so three anti-vacuity assertions sit
beside it — the passes must have derived steps, the compaction must actually
have dropped variables (or the lift never ran), and the search must have
contributed steps (or the prefix refuted alone, which ADR-1750 measured as a
real trap on small pigeonholes).

Two mutations, applied one at a time and reverted byte-for-byte:

| mutation | solver suite (30) | `reduction_link` suite (12) |
|---|---|---|
| corrupt the first **derived clause** (flip one literal of the first `Add`) | **killed 2** | killed 3 |
| **drop the renaming** (the ADR-1750 state) | **killed 2** | killed 7 |

Both killed exactly the two solver tests that decide an `unsat` under
inprocessing, and none of the other 28 — the 28 do not run that path. The
first mutation's failure names the mechanism: *"native unsat proof failed to
check against the original formula: DRAT step 1808 is neither RUP nor RAT"*.

**A first attempt at the same mutation SURVIVED the solver suite, and reporting
that as a finding would have been wrong.** It corrupted the first *step*, and
the first step a pass emits is typically a `Delete` from the normalization
prelude — so the mutant never fired at runtime. It was distinguishable from a
real survivor only by making the mutation print when it fires, which is the
generalizable rule: **a mutation with a runtime condition must announce that the
condition held, or `SURVIVED` and `NOT APPLIED` are the same observation.** This
is the same trap `scripts/tests/mutation_controls.py` documents for mutations
that fail to build or run zero tests.

At the `axeyum-cnf` level the load-bearing control is
`an_unlifted_search_proof_does_not_check_against_the_original`: it builds the
concatenation the OLD way (prefix ++ raw search steps) and requires the checker
to **reject** it while the lifted one verifies. Two vacuity guards on it fired
during development and are kept — the fixture must actually renumber (unshifted
pigeonhole compacts to the identity, so the first draft tested nothing), and
the prefix alone must not derive the empty clause.

## Consequences

- **The certificate now covers the reduction.** With `cnf_inprocessing` on and
  `prove_unsat` set, an accepted `unsat` is backed by a proof of the formula
  the backend encoded. The reduction is inside the certificate rather than
  underneath it, and ADR-1721's "one link covered" shape no longer applies to
  this path.
- **A failed check is a downgrade, never an acceptance.** The verdict becomes
  `Unknown` with a detail naming which formula the check ran against. That is
  unchanged in kind from before; what changed is which formula the sentence
  refers to.
- **The re-derivation fallback in `ensure_unsat_proof_checked` re-solves the
  formula the search ran over**, so when a reduction happened it certifies the
  REDUCED formula. It now emits the coverage keys saying so, because a missing
  key reads as "not applicable" and this is a real narrowing. On the current
  wiring the path is unreachable (`prove_unsat` implies the native core checked
  inline), but an unreachable honest branch is cheaper than a reachable silent
  one.
- **Open, and named rather than implied.**
  - *Streaming.* The 8 M-step ceiling has not been hit on the shipping path, so
    the file-backed route is built but not wired. The first instance that
    crosses it will report `reduced` with reason 2 rather than fail, which is
    the intended signal to wire it.
  - *XOR units.* Dropping them under `prove_unsat` is a cost, not a fix. A
    `DRAT` derivation of a Gaussian-implied unit would recover both the
    propagation and the certificate.
  - *In-search inprocessing* remains where ADR-1750 left it. The link is
    indifferent to when a pass runs — it composes — so the obstacle there is
    still `Cdcl`'s arena/watch-list rebuild, not the certificate.
