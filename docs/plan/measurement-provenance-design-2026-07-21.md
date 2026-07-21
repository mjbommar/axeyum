# Shared measurement provenance without a false parity aggregate

Status: prototype landed; policy proposed in ADR-0343
Date: 2026-07-21

## Question

How can the 35-row curated/regression scoreboard and the 228-file partial
public inventory use one provenance vocabulary without pretending that they
are one population, two independent samples, or an official SMT-COMP result?

This is G1 in the
[scoped gap program](gap-analysis-z3-lean-2026-07-21.md). The answer matters
because the existing headline denominators differ sharply: 753/992 decided in
the regression record versus 82/228 in the harder convenience inventory. A
single weighted average would hide both selection policies.

## External policy boundary

The official
[SMT-COMP 2026 Rules and Procedures](https://smt-comp.github.io/2026/rules.pdf)
is the reference policy, not a label these local runs inherit.

- Section 6 defines competition populations from a versioned SMT-LIB release,
  partitions logics into directory-derived families, applies track/status and
  difficulty filters, caps large logics, samples with a published seed, and
  publishes the selected set.
- Sections 7.1 and 7.2 score benchmark results and define division-local
  parallel, sequential, and PAR-2 aggregation. PAR-2 penalizes each unsolved
  case at twice the row's limit.
- Neither current Axeyum regime was selected by that complete process. The
  in-tree scoring replica can reproduce the rule, but a scoring implementation
  does not turn a hand-curated or partial source pack into an official
  selection.

The schema therefore records `official_selection = false` for both regimes.
It keeps official-style within-row PAR-2 while declining a cross-regime score.
The later [E1b runner audit](smtcomp-runner-e1b-audit-2026-07-21.md) also finds
that the local public-inventory executor suppresses timeout-observed responses.
Its two no-answer rows lack the stdout/termination evidence needed for
retroactive reclassification, which is an additional reason the row remains
local/non-official.

## Source audit

The checked prototype reads the same artifacts that produce the public claims:

- [`scripts/gen-scoreboard.py`](../../scripts/gen-scoreboard.py) and every
  committed baseline it selects;
- the public inventory's
  [`inventory.json`](../../bench-results/smtcomp-repro-20260721/inventory.json),
  [`inventory_raw.json`](../../bench-results/smtcomp-repro-20260721/inventory_raw.json),
  and [`provenance.json`](../../bench-results/smtcomp-repro-20260721/provenance.json);
  and
- exact benchmark bytes for every file-backed scoreboard row.

The result changes the interpretation materially:

| Quantity | Curated/regression | Partial public |
|---|---:|---:|
| Rows | 35 | 18 logic strata |
| Raw cases | 992 | 228 |
| File-backed occurrences | 927 | 228 |
| Unique normalized paths | 837 | 228 |
| Unique exact contents | 778 | 228 |
| Aggregate-only cases | 65 | 0 |
| Exact path-alias groups | 58 | 0 |
| Exact-content overlap between regimes | 99 | 99 |

The scoreboard first loses 90 repeated path occurrences and then 59 further
path identities across 58 byte-identical alias groups. One group contains three
paths; the rest contain two. The two synthetic graduated rows contribute 65
cases but publish no instance records, so they cannot receive fabricated hashes.

Most importantly, 99 of the public inventory's 228 exact contents already
appear in the scoreboard. That is 43.4% of the public inventory and 12.7% of
the scoreboard's 778 unique file-backed contents. The public run remains a
useful harder weighting, but it is not independent replication.

## V1 shared contract

The machine-readable
[`measurement-provenance-v1.json`](measurement-provenance-v1.json) freezes the
following distinctions:

1. **Raw occurrence:** every recorded case in its original row, including a
   repeated path or aggregate-only synthetic case.
2. **Normalized path identity:** a machine-independent path after a declared
   corpus marker. This catches repeated measurement of one named file.
3. **Exact-content identity:** SHA-256 over exact input bytes. This catches
   renamed byte-identical aliases.
4. **Near/semantic identity:** unmeasured in v1. No comment stripping, symbol
   alpha-renaming, option normalization, AST normalization, or semantic
   equivalence is implied by exact-byte hashing.
5. **Coverage class:** an Axeyum-relative label (`decide-strong`, `partial`, or
   `frontier`) derived from observed decide rate. It is not an intrinsic
   difficulty classifier.
6. **Oracle class:** benchmark status, Z3 library, Z3 binary, and a neutral
   non-Z3 oracle are distinct. A cvc5- or Bitwuzla-sourced regression file does
   not make that solver an oracle.
7. **PAR-2:** one mean per row under that row's recorded limit. V1 reports a
   deduplicated denominator, not deduplicated PAR-2, because choosing among
   repeated runs/configurations would introduce a new representative-selection
   policy.

The generated
[Markdown matrix](generated/measurement-provenance-matrix.md) exposes all 53
rows. Its [JSON twin](generated/measurement-provenance-matrix.json) retains the
full 99-content cross-regime overlap mapping for independent inspection.

## Neutral-oracle result

V1 records **zero neutral-oracle rows on these exact populations**. This does
not erase the useful 24-file Axeyum/cvc5/Bitwuzla head-to-head or the four-oracle
fuzzer. It prevents those different populations from being silently credited
to the 35 scoreboard rows or 18 inventory logic strata.

This finding joins G1 and G3 cleanly: G1 owns population identity and scoring;
G3 must produce matched non-Z3 results on an exact claimed population before a
row's neutral status can change.

## What the prototype deliberately does not do

- It does not publish one global parity percentage.
- It does not average 753/992 and 82/228.
- It does not call either population official, representative, random, or
  source-balanced.
- It does not use source-family names as statistical weights.
- It does not compute deduplicated PAR-2 without a representative-selection
  rule.
- It does not infer difficulty from filename, source solver, or Axeyum outcome.
- It does not treat zero observed disagreements as universal soundness.

## Remaining research sequence

1. Preserve the failed first 52-shard attempt with zero result credit. Before a
   rerun, advance proposed ADR-0344's landed E0/v2 contract and E1a local
   filesystem prototype through E1b-E3: integrate immutable records and strict
   resume identity with the active runner, add attempt and shard-completion
   manifests, fail-closed duplicate handling, leases, aggregate memory
   enforcement, and multi-host recovery. The [handoff](smtcomp-full-library-candidate-run-handoff-2026-07-21.md)
   freezes the 2,041-row/no-raw-artifact failure; the
   [resumable-run design](smtcomp-resumable-run-design-2026-07-21.md) freezes 18
   invariants and 28 executable v2 scenarios without authorizing the rerun; the
   [E1a result](smtcomp-resumable-filesystem-e1a-2026-07-21.md) adds 8/8 local
   forced-kill recoveries but explicitly declines shared-storage credit.
2. Extend its current cap/family sampler with the full eligibility/status/
   difficulty exclusions, official release and seed, corpus-tree digest, and
   per-selected-file hashes before calling it official-style.
3. Prototype syntax-normalized fingerprints as an additional identity layer;
   report merges and splits against exact bytes before considering semantic
   clustering. Add an operator/profile census so source and theory strata are
   not merely logic labels.
4. Run cvc5 and Bitwuzla on the exact admitted population, retaining per-case
   verdict direction and decision-set overlap.
5. Only then preregister source-balanced or deduplicated views. Keep raw,
   exact-deduplicated, official-selection, and source-stratified results side by
   side rather than replacing one with another.

Until those steps land, the correct strategic claim is: Axeyum has strong
curated regression coverage and weaker performance on a harder, overlapping,
partial public inventory. The exact amount of Z3-class population parity
remains unmeasured.

The live precursor for steps 1-2 is `scripts/smtcomp_repro/select_library.py`
at `d9e71e21`: it maps 438,631 files in an external 2024 tree to 64,345
cap/family-selected candidates across 84 logics. The external manifest is
operational state; the first distributed run terminated incomplete and is not
part of the generated v1 matrix.
