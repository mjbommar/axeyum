# ADR-0611: An absence claim in prose carries a marker and expires against the kernel

Status: accepted
Date: 2026-08-27
Index-summary: A document that records an obstacle ("X does not exist", "grepped for; absent") carries a machine-checkable `<!-- absent: Root.name -->` marker, and `scripts/check-absence-claims.py` fails the moment that declaration appears in `kernel.environment()` — the prose equivalent of `#[expect(dead_code)]`. The resolved form `<!-- was-absent: ... -->` is checked in the opposite direction so a historical record cannot start pointing at nothing. Claims naming no declaration are structurally uncheckable and are counted and reported rather than implied away.
Index-status: accepted

## Context

ADR-0608 made *retrieval* answer honestly: `shape_search` distinguishes a
genuine zero from a query the index cannot answer. It fixed the tool. It did
not fix the **documents**, and by the same day the documents were the more
expensive failure.

Measured on `main`, 2026-08-27:

| surface | count |
| --- | --- |
| docs making an absence claim | 231 |
| ...that also name a `CReal.`/`Rat.`/`Nat.`/`Int.`/`Complex.` declaration | 64 |
| Rust module docs making one | 150 |

**Nothing re-checks any of them when the thing lands.** An absence claim has
no expiry, and its authority is exactly what makes it expensive when it rots.
Five went stale in one day and two cost a full Opus lane each:

- `crates/axeyum-lean-kernel/src/creal/trig_fn.rs` said a `close_within` →
  `Within` bridge "does not exist as a public lemma today". The claim is
  literally true — `CReal.within_of_close_within` is still absent — but the
  *inference* readers drew from it was wrong: the forward
  `CReal.close_within_of_within` had landed and sufficed.
  <!-- absent: CReal.within_of_close_within -- the reverse close_within -> Within bridge trig_fn.rs:63 reports missing; this paragraph goes red the day it lands -->

- [`diary-exact-root-obstruction.md`](../../mathematics-2026-08/diary-exact-root-obstruction.md)
  said a transport lemma was "grepped for; absent".
  `CReal.converges_comp_eventually` existed, and *its own doc comment names
  that diary as what it repairs.*
- The same diary said the magnitude bound lived only mid-proof inside
  `declare_strict_mono_of_pos_deriv`. It had long since been extracted as
  `CReal.strict_mono_magnitude` and `CReal.diff_le_of_strict_mono_magnitude`.
- A deficiency note said `Rat.sumRange` had no diagonal/rectangle reindexing.
<!-- was-absent: Rat.sumRange -->
  `rat_prelude/diagonal.rs` had it, and `complex.rs` already ran the same
  argument over ℂ.
- `CLAUDE.md` said an inline step "blocks the Weierstrass M-test today".
  `CReal.weierstrassMTest` had landed in full generality six hours earlier.

The rule being violated is one this repository already states, for tests:
*"any test named 'every X' must derive its X from the authority, not from a
literal."* That is why `every_creal_declaration_is_checked_and_axiom_free`
works — it enumerates `kernel.environment()`, and found twelve unchecked
declarations on its first run. Every item above is that rule unapplied to
prose: **a claim about the tree that does not derive from the tree.**

## Decision

**An absence claim that names a declaration carries a marker, and the marker
is checked against the kernel.**

```text
<!-- absent: CReal.converges_comp_eventually -->
<!-- absent: CReal.foo, CReal.bar -- optional note after a double dash -->
<!-- was-absent: CReal.weierstrassMTest -->
```

`scripts/check-absence-claims.py` reads the whole prose surface (`docs/**/*.md`,
root Markdown, comments in `crates/**/*.rs`) and the kernel's own declaration
surface (`kernel_declaration_projection`, run fresh), and:

* **`absent:` FAILS when the named declaration is PRESENT.** That is the
  expiry. The moment the obstacle clears, the document that records it goes
  red and names its own file and line.
* **`was-absent:` FAILS when the named declaration is ABSENT.** A diary or a
  design review is a historical record, and deleting the obstacle deletes the
  reasoning — but a "this was fixed, see X" note that points at nothing after
  a rename is a stale claim of the opposite sign. Checked in both directions,
  the same discipline ADR-0608's sibling gate `check-shape-duplicates.py`
  applies to its allowlist.

Correcting a stale claim is therefore a **one-word edit** — `absent` becomes
`was-absent` — which *keeps* the record under the gate rather than removing it
from it.

### Why this shape and not the alternatives

**Why a colocated marker rather than a central registry.** The model already
in this tree is `#[expect(dead_code, reason = "…")]`, which `creal/integral.rs`
uses for exactly this purpose: silent while its condition holds, an error the
moment it clears, and *attached to the line it describes* so the error names
what to edit. A registry file would divorce the claim from its record and
become a shared append point across lanes — the failure mode CLAUDE.md
documents at length for `PLAN.md` and the ADR index. The one registry that
remains (`scripts/absence-claim-census.json`) holds three numbers and an
exclusion list with written reasons, not the claims.

**Why not an expiry date.** A date says when someone should look again; it
does not say what to look at, and it goes red on a schedule rather than on a
fact. The whole content of the defect is that the *world* changed, not that
time passed.

**Why not a doc-test.** Markdown here is not compiled, and the Rust half lives
in `//!` comments across 150 files in a crate five lanes are concurrently
editing. A gate that reads prose from outside touches nothing.

**Why the authority is a fresh run and never a snapshot.** The committed
`artifacts/autogenesis/kernel-dependency-projection-v1.json` held **1,644**
declarations against a live **1,861** the day this was written. A stale index
is wrong in the one direction that matters — it reports a newly-landed
declaration as *still absent*, so an expired claim reads as still valid. The
`authority_declaration_floor` guard rejects a projection that short.

### What it refuses to do

* **A marker naming a root the authority does not carry exits 2 —
  UNANSWERABLE, not absent.** ADR-0608's distinction, carried here: you cannot
  receive "still absent" about a subject the tool was never pointed at.
* **A marker matching only one spelling would produce a false green.** Measured
  over the 483 `CReal` declarations in the live environment, 324 carry an
  underscore, 243 an internal capital and 119 carry both; the kernel name is
  `CReal.congrOfUniformlyContinuous` while every design document writes
  `congr_of_uniformly_continuous`. Markers are resolved against the exact
  names *and* a spelling-normalized index, and a normalized-only hit fails
  while printing the kernel spelling.
* **It cannot pass vacuously.** Zero files scanned, zero claim sites detected,
  or zero markers each fail with a distinct message. A gate that scans nothing
  and exits 0 is the defect this repository audited at 40 of 162 checker runs.

## Consequences

**Adoption is partial, and the gate says so on every run.** Four records carry
markers today; the census counts every other claim site and prints
`N annotate / M do NOT` unconditionally. A partial rollout reported as
complete is the same defect one level up, so the number is in the output
rather than in a claim about the output.

**A population that cannot be checked is named rather than hidden.** Most
absence claims name no declaration at all ("the mesh toolkit is private", "no
in-tree tool does this"). No authority-derived gate can check those, and the
census reports them as `STRUCTURALLY UNCHECKABLE` instead of quietly
excluding them from a coverage ratio.

**The budget is a ratchet, not a target.** `bare_named_claim_budget` is a
maximum: a *new* unexpirable claim naming a declaration fails the gate.
Annotating one lowers it; `--update-budget` records a deliberate increase and
leaves a visible diff.

**It is not part of `just check`,** for the same reason `just claims` is not:
the authority is a `--release` kernel build. `just absence-claims` runs it;
`just absence-claims-controls` runs the 29 controls and the seeded-claim
demonstration.

## Alternatives rejected

* **Annotate all 231 + 150 sites now.** Not possible in one lane, and a
  handful annotated with coverage implied is the defect restated.
* **Ban absence claims in prose.** They are the most valuable thing a diary
  records. The problem is that they never expire, not that they exist.
* **Make the census a hard equality rather than a maximum.** Every doc edit in
  the repository would trip it, and a gate lanes disable is worse than none.

## References

- [ADR-0608](adr-0608-retrieval-is-by-shape-and-absence-is-distinct-from-unanswerable.md) —
  retrieval by shape; `absent` versus `unanswerable`.
- [`2026-08-27-retrieval-is-the-bottleneck.md`](../11-design-review/2026-08-27-retrieval-is-the-bottleneck.md)
  — the measured retrieval cost this ADR's defect sits downstream of.
- `scripts/check-shape-duplicates.py` — the both-directions allowlist this
  gate's `was-absent:` half is modelled on.
- `scripts/check-absence-claims.py`, `scripts/absence-claim-census.json`,
  `scripts/tests/test_check_absence_claims.py`,
  `scripts/tests/demo-absence-expiry-seeds.sh`.
