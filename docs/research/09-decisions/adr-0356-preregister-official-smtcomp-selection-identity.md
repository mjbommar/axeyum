# ADR-0356: Preregister official SMT-COMP selection identity

Status: proposed
Date: 2026-07-22

## Context

The first full-library candidate selected 64,345 files from an SMT-LIB 2024
tree with a local Python sampler. That artifact is deterministic, but it is not
the SMT-COMP 2026 Single Query selection: it does not bind the preceding-year
release, competition submissions and seed, competitive logics, historical
difficulty filter, official status metadata, or exact input bytes. It therefore
receives zero official-selection or representativeness credit.

SMT-COMP's rules and executable implementation also require separate
identities. Section 6 of the
[2026 rules](https://smt-comp.github.io/2026/rules.pdf) describes the selection
policy and a C `random()`/`srandom()` generator. The current organizer tool uses
Polars list sampling instead. The executable 2026 authority is upstream commit
[`401302678311593efcef8a79b614b33a3b853eac`](https://github.com/SMT-COMP/smt-comp.github.io/commit/401302678311593efcef8a79b614b33a3b853eac),
including `smtcomp/selection.py`, `smtcomp/defs.py`, the submission files, data,
and its locked Polars 1.39.2 environment. Reproducing only the prose algorithm
would silently produce a different population.

The exact corpus release is similarly easy to misidentify. Zenodo concept
record `15493089` has a May release with 450,474 non-incremental files and an
August release with 450,472. Upstream `data/benchmarks-2026.json.gz` contains
450,472 rows; the two configured explicit-removal identities match zero rows in
that pinned metadata, making the producer's anti-join idempotent. The matching authority is therefore
[SMT-LIB 2025 release 2025.08.04, record 16740866](https://zenodo.org/records/16740866),
not record 15493090.

This decision addresses the open measurement question in
[`research-questions.md`](../08-planning/research-questions.md) and is a
prerequisite to the next G1 full-population measurement in the
[`roadmap`](../08-planning/roadmap.md).

## Decision

**Treat official selection as an externally produced, independently audited,
content-addressed evidence artifact; do not replace the pinned organizer
implementation's sampling output with an Axeyum sampler.**

The first accepted artifact is only the SMT-COMP 2026 **Single Query** track.
It binds all of the following before a solver run can refer to it:

1. The rules PDF, organizer repository commit, relevant source files, lockfile,
   every submission JSON, benchmark metadata, and 2018--2024 Single Query result
   inputs by URL, byte count, and SHA-256.
2. Zenodo record `16740866`, version `2025.08.04`, DOI
   `10.5281/zenodo.16740866`, and all 90 release files by name, byte count, and
   published MD5. Download verification happens before extraction.
3. The organizer configuration: competition year 2026, old-result years
   2018--2024, difficulty threshold at CPU time less than or equal to 1.0 s,
   current `old_criteria=false`, no status completion from previous results,
   cap constants 300/0.5/1000/0.1, two configured explicit removals that match
   zero metadata rows, and new-family prefix `2025`.

For exact executable identity, the historical predicate is the pinned code's
`result != Unknown && cpu_time <= 1.0`, applied to every result in an admitted
year. The adjacent source comment and rules prose describe solved `sat`/`unsat`
rows more narrowly, but the code expression also treats any other answer enum
as non-`Unknown`. The auditor records this discrepancy and matches the
executable producer; it does not silently substitute the comment.
4. The complete competitive/noncompetitive submission ledger, participation
   expansion, competitive-logic derivation, and seed derivation. The frozen
   upstream snapshot currently yields 51 direct-child submission files, 36 competitive
   submissions, no missing competitive seed, submission-seed sum
   `9,684,066,201`, modulo-2^30 value `20,389,785`, NYSE component `2,341,289`,
   and final global seed `22,731,074`. The two JSON examples below
   `submissions/template/` are excluded because `Config.submissions` uses the
   non-recursive glob `../submissions/*.json`.
5. One normalized benchmark row for every metadata entry, with exact path,
   logic, complete family path, name, status, assertion count, archive identity,
   file size, and SHA-256. The metadata and extracted corpus must form an exact
   bijection; missing, extra, duplicate, symlink, non-regular, path-escaping, or
   byte-drifting entries fail closed.
6. One decision row for every non-incremental metadata entry. It records explicit
   removal, competitive-logic membership, new/old classification, historical
   run years, per-year coherence and competitiveness, derived triviality,
   eligibility, selection, and exactly one terminal exclusion or selection
   reason. Raw historical evidence remains separately addressable.
7. Per-logic stage counts and digests covering metadata, explicit removals,
   noncompetitive logic, triviality, eligible new/old pools, cap, selected
   new/old rows, and final selection. Integer IDs internal to the organizer tool
   are mapped back to normalized corpus paths through the pinned metadata order.
8. A canonical LF-terminated `selected.txt`, sorted decision ledger, selected-
   file ledger, summary, and completion record. All canonical JSON uses sorted
   keys, UTF-8, no insignificant whitespace, and a final LF; JSONL rows are
   sorted by normalized benchmark ID and use the same object encoding.

The organizer output is the authority for which eligible rows its Polars sampler
selected. The independent Axeyum auditor is authoritative for input identity,
eligibility facts, caps, membership invariants, and evidence completeness. It
must prove that every selected row is eligible, every per-logic count matches
the registered formula, all selected and excluded rows partition the metadata,
and a second execution of the pinned producer is byte-identical. It must not
claim to independently reproduce Polars' pseudorandom permutation.

The canonical external artifact root is
`/nas3/data/axeyum/harness/official-selection-2026-sq/`. Work occurs in a fresh
attempt directory. Only a self-hashed completion record may name a content-
addressed accepted directory. The existing SMT-LIB 2024 corpus and 64,345-file
candidate artifacts are preserved unchanged.

## Preregistered gates

The implementation must pass all of these gates in order:

1. **Authority fixture:** a tiny committed fixture exercises competitive-logic
   derivation, all four cap regions, new-before-old allocation, incoherent
   historical results, single-solver years, missing years, exactly-1.0-second
   triviality, explicit removal, unknown status, and normalized nested families.
2. **Mutation matrix:** source/data/submission/release hash drift; seed drift;
   missing, extra, duplicate, traversal, symlink, and byte-drift corpus rows;
   false triviality; wrong cap; ineligible selection; missing decision reason;
   producer/auditor disagreement; and incomplete publication all reject.
3. **Authority freeze:** every upstream and Zenodo input is downloaded and
   verified against a committed small authority manifest before extraction.
   Redirects or mutable URLs do not replace the pinned record/commit identity.
4. **Corpus closure:** the extracted non-incremental tree has exactly 450,472
   regular benchmark files matching the official metadata, before the two
   explicit selection removals. Each file's digest is computed from its bytes,
   not inferred from archive metadata.
5. **Official production:** the pinned organizer code runs twice in isolated
   locked environments with Polars 1.39.2 and seed `22,731,074`; normalized
   selections and per-logic counts are byte-identical.
6. **Independent audit:** a separate standard-library checker reconstructs the
   metadata IDs, competitive logics, historical difficulty facts, eligibility,
   caps, new/old quotas, and complete decision partition, then validates the
   official producer output without importing organizer code or Polars.
7. **Harness admission:** the E1b run manifest accepts only the completed
   selection artifact identity and exact selected-file ledger. Merely passing
   the legacy five selection tests grants no admission.
8. **Bounded repository gate:** focused unit/mutation tests, the SMT-COMP resume
   gate, generated foundational resources, documentation links, and clean
   lane-owned formatting/lints pass. Unrelated workspace failures remain
   separately reported rather than laundered as selection failures.

No solver execution, decide-rate, representativeness, or official competition
result is credited by this decision alone.

## Evidence

- `rules.pdf` has SHA-256
  `268e5c579ee9dd82bcf470f6c66f637c0656bf44f9488dd6347d1f25a2fb4974`.
- At the pinned organizer commit, `smtcomp/selection.py` has SHA-256
  `e4d5c9f9c8fc15ec500714f24e2c63aa439408109c9c9cc51b8243391223cdfb`,
  `smtcomp/defs.py` has
  `5c500314b6604fc763bede8de92cc4f9f913e42f771053ad737688e5f010bdc6`,
  `pyproject.toml` has
  `d3bcbdb9a058444d8720ae3c4aeefc923c0834ad105aa9e7a4091575d7083226`,
  and `poetry.lock` has
  `8f57e76984579d949d2679eddab2b5cda5c63740d4ca656637390966b1791e4b`.
- `data/benchmarks-2026.json.gz` has SHA-256
  `ba855e47e1ed88e2e6bb26272e84a20a0e8f0c320adc704b062f4c287e586a54`
  and contains 450,472 non-incremental rows across 89 logics, including 3,445
  rows whose first family component starts with `2025`.
- The seven pinned result files have byte sizes and SHA-256 values recorded in
  the execution plan. They are data inputs, not evidence inferred from the
  rules prose.
- The May and August Zenodo release manifests differ in exactly three benchmark
  archives plus `README.md`; the August README reports 450,472 files, matching
  the organizer metadata.
- The old local selector uses Python `random`, per-logic CRC-adjusted seeds,
  immediate-parent family approximation, all logic directories, and an
  optional no-op difficulty hook. Its manifest cannot satisfy this decision.
- The S1 fixture includes two sub-second `OutOfMemory` rows and confirms that
  the pinned executable expression classifies the file as trivial. This is an
  identity test for organizer behavior, not an endorsement of that predicate.
- Submission logic regexps expand against the complete organizer `Logic` enum;
  `Participation.get` then retains only matches present in the selected track's
  division table. The independent adapter preserves this two-stage filtering,
  including valid logics that are irrelevant to Single Query.
- Both configured explicit-removal IDs are absent from the pinned 450,472-row
  metadata. The producer still performs the anti-join before eligibility; the
  independent ledger records two configured and zero matched removals.
- The pinned metadata array is not in normalized path order. The independent
  auditor accepts its byte-frozen input order but uses a bounded external merge
  sort before emitting the canonical path-ordered eligibility ledger.
- The completed S1b audit is recorded in
  [`smtcomp-official-selection-input-audit-s1b-2026-07-22.md`](../../plan/smtcomp-official-selection-input-audit-s1b-2026-07-22.md).
  Its fifth fresh run verified 89 inputs, 450,472 metadata rows, and 5,345,294
  historical rows while keeping `selection_observed=false`.

## Alternatives

- **Repair the local Python sampler until its output looks similar.** Rejected:
  similar counts do not reproduce the organizer implementation or its RNG.
- **Implement the rules PDF literally with libc `random()`.** Rejected as the
  2026 executable identity because the pinned organizer uses Polars sampling;
  retain the prose/implementation discrepancy as explicit provenance.
- **Use the May 2025 release.** Rejected: its 450,474-file inventory does not
  match committed 2026 organizer metadata.
- **Trust only the organizer-selected list.** Rejected: it does not bind local
  corpus bytes or independently expose why every other benchmark was excluded.
- **Commit the full ledger to Git.** Rejected: large generated evidence belongs
  in the content-addressed external artifact; the repository retains its
  schema, generator/checker, fixture, input authority manifest, and compact
  result summary.

## Consequences

The next full-library run can name one exact, reviewable population without
confusing a local candidate with official selection. Selection remains a
separate policy identity from E1b's execution ledger, while the latter consumes
the former's selected-file digest.

The cost is a roughly 4.9 GB verified archive download, a complete extracted
tree hash pass, approximately 100 MB of historical result inputs, a pinned
Python/Polars producer environment, and a large external decision ledger. Any
upstream post-commit correction or different SMT-LIB release requires a new
artifact and, if it changes this policy, a follow-up ADR rather than an in-place
rewrite.
