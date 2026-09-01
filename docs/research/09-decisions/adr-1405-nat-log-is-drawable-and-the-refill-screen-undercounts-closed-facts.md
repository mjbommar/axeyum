# ADR-1405: `Mathlib.Data.Nat.Log` is drawable; `propose-nursery-refill.py --names` undercounts already-closed facts

Date: 2026-09-01
Status: Accepted
Lane: `screen-nat-log-family`

Index-summary: Screened `Mathlib.Data.Nat.Log` (one of three hygiene-clean
refill candidates named in `refill-headroom-v1.json`) for drawability into
the nursery. `propose-nursery-refill.py --names` reported **37** unused
candidates; cross-checked against `mathlib-nat-int-fact-catalog-v1.json` (the
file the real generator's `select()` actually screens against) and directly
against `artifacts/facts/*.json`, **20 of the 37 are already `proved` facts**,
closed by direct flip on 2026-08-18/29 outside the nursery draw system — the
advisory tool's `used_source_names()` only reads nursery draw manifests, never
the fact ledger, so a directly-flipped mirror is permanently invisible to it.
True open count: **17**, still above the `PER_FAMILY = 10` floor. All 17 are
`FLIPPABLE` (ordinary extensional facts about `log`/`clog` values; none
reference Mathlib's private `log.go`/`clog.go` fuel-doubling internals) and
R9-clean by direct kernel name-registry check. No construction needs to be
declared — `Nat.log`/`Nat.logAux`/`Nat.clog`/`Nat.clogAux`/`Nat.log2` already
exist, fully proved, axiom-free. Full per-statement table and the draft
`FAMILY_MODULES`/`FAMILY_ROUTES` block:
[2026-09-01-screening-the-nat-log-family.md](../11-design-review/2026-09-01-screening-the-nat-log-family.md).
Corollary finding, load-bearing for nobody's verdict but worth fixing:
`log.rs`/`clog.rs`/`log2.rs`'s module docs describe Mathlib's `Nat.log`/
`Nat.clog` as naive well-founded recursion on `n / b`; the pinned commit's
actual `Nat.log`/`Nat.clog` are fuel-recursive base-doubling algorithms, a
different divergence shape than documented (both sides fuel-recurse; they
differ in which operand carries the fuel and how it shrinks).
Index-status: Accepted

## Context

`scripts/check-dispatchable-frontier.py` measured the dispatchable ml430
frontier down to 20 (floor 10) after this session's draws.
`scripts/propose-nursery-refill.py --remeasure` named three hygiene-clean
refill candidates — `Mathlib.Data.Nat.Log` (37), `Mathlib.Data.Nat.Bitwise`
(18), `Mathlib.NumberTheory.FactorisationProperties` (15) — explicitly
labeled an upper bound, not screened for R9 contamination or R11 adjacency
("draw 10 was DECLINED against this same shortlist"). Bitwise and
FactorisationProperties are contamination-exposed by other lanes' concurrent
work; `Nat.Log` was the one candidate no running lane touches, so this lane
screened it in isolation.

Per ADR-0653 (`docs/research/09-decisions/adr-0653*.md`, if numbered — see the
`natural-distance` incident this lane's brief cites): a screening lane must
not declare theorems whose names match Mathlib mirror names in the family
under review, because doing so spends the blind evaluation population it is
being sent to protect. This lane declared nothing; every finding below is
read-only measurement.

## Decision

1. **Treat `Mathlib.Data.Nat.Log` as drawable**, with the true open-candidate
   count corrected to 17 (not 37). It clears the `PER_FAMILY = 10` floor by a
   comfortable margin, and every one of the 17 is a plain value-level fact
   about `log`/`clog` reachable from existing kernel machinery
   (`log_aux_mono`, `log_aux_le_fuel`, `log_aux_antitone_base`,
   `clog_aux_mono`, `clog_aux_antitone_base`, `log_aux_le_clog_aux`, all
   already declared in `crates/axeyum-lean-kernel/src/nat_prelude/
   log_clog_order.rs`).

2. **Do not trust `propose-nursery-refill.py --names`'s count without
   cross-checking `mathlib-nat-int-fact-catalog-v1.json`.** The advisory
   tool's `used_source_names()` (`scripts/propose-nursery-refill.py:191`)
   reads only `entries[].source_name` from `nursery-v1.json` and
   `nursery-v2-extension.json` — names that went through an actual nursery
   draw. A proposition closed by **direct flip** (found already proved,
   matched to `formal.statement`, status flipped with no new proof work —
   the documented, honest route for an exact Mathlib-def match) never
   appears in either manifest and is therefore permanently counted as an
   "unused candidate" by this tool, regardless of how long ago it was
   proved. The real generator (`gen-autogenesis-nursery-refill.py`'s
   `select()`) does not have this gap: it screens against
   `mathlib-nat-int-fact-catalog-v1.json`'s `external-source` rows, which
   is regenerated from and stays current with the fact ledger. So a real
   draw run through the generator would not have redrawn the 20 — but any
   *count* quoted from the advisory tool alone, before this cross-check, is
   liable to overstate genuine headroom by however many mirrors have been
   flipped directly since the last nursery draw touched that module. This
   is not specific to `Nat.Log`; any module screened this way should get the
   same cross-check before its survivor count is trusted for planning.

3. **No construction work is needed to unblock this family**, unlike
   `Nat.dist`/`Nat.nth` (ADR-0653). `Nat.log`, `Nat.logAux`, `Nat.clog`,
   `Nat.clogAux`, `Nat.log2` are already declared and proved axiom-free.

## Consequences

- A draw author can add `"natural-logarithm": ("Mathlib.Data.Nat.Log",)` to
  `FAMILY_MODULES` and `("kernel-induction",
  "recursive-function-reconstruction")` to `FAMILY_ROUTES`, then run the real
  `select()`/`guard()` (R1–R11) to confirm — this ADR predicts the R9 result
  (clean) and the first-10 alphabetical slice by reading the generator's
  logic, but does not run it, so R11 in particular is unconfirmed here.
- This module alone does not clear the "the frontier floor is 10, so a draw
  needs 2 new families" bar this session's remeasurement stated; a second
  family is still needed and is out of scope for this screen.
- The screening report flags (but does not fix) a stale doc-comment claim in
  three `nat_prelude` source files about Mathlib's `Nat.log`/`Nat.clog`
  recursion shape. A follow-up lane not mid-screen should correct it.

## Alternatives considered

- **Trust the 37 as reported and hand it to a draw author unscreened.**
  Rejected: the brief this lane was given explicitly required verifying the
  candidate list against the tree rather than treating a headline number as
  fact, per this repository's own standing lesson about stale blocker
  claims. The cross-check found a 54% overcount within the first hour of
  work; skipping it would have handed the draw author a number that, if
  used to justify "this family alone clears the floor of 10 with room to
  spare," is still true (17 > 10) but for the wrong reason and by the wrong
  margin.
- **Fix `propose-nursery-refill.py`'s `used_source_names()` to also read the
  fact catalog.** Not done here — this is a screening lane, not a tooling
  lane, and the fix touches a script other lanes may be running concurrently
  for other modules' screens. Flagged as a real gap for a tooling lane to
  pick up; the real generator's own screen is unaffected.
