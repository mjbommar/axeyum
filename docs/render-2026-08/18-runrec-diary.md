# 18 -- RUNREC diary (render strand, round 3 / P1)

Agent P1-RUNREC, 2026-08-21. Charge: close the one gap `13-facts-diary.md`
item 2 identified and refused to paper over -- a fact-ledger evidence row
carries a command and an assertion that somebody checked it, but no recorded
exit status, so a Doc-IR `claim` over it would have to forge the field the
whole fail-closed law flows through. The only sound way to close it is to run
the commands. This lane ran them.

Owns: `render/producers-runrec/facts_to_runrec.py`,
`render/examples-input/runrec/`, this file.

Epoch for every record here: `unix=1787319265 source=commit
commit=839d1e50a287f`.

## Headline

| quantity | value |
|---|---|
| facts surveyed | 19 (the 17 arith-pilot facts + the two Rado headline facts) |
| evidence rows | 38 |
| rows classified runnable | 38 |
| rows not runnable | 0 |
| DISTINCT commands (rows deduplicated by command text) | 22 |
| commands executed | 22 |
| green | 22 |
| red | 0 |
| timed out (>120s) | 0 |
| production run records written | 22 |
| negative-control records written | 1 |
| records that validate against `#/$defs/RunRecord` | 23 of 23 |
| slowest single command | 61.2 s (`check-claim-certificates.py`, and see finding 5) |
| whole sweep, wall clock | 1 m 13 s |

Nothing was skipped, and nothing was heavy. The Rado facts were weighed before
running, as the brief required: `F:rado-r4-a5-b3` costs 4.4 s + 0.1 s + 0.1 s
and `F:rado-r4-a5-b4` costs 61 s, all well inside the 120 s per-command budget,
so neither was skipped. The "certificate is deliberately not re-checked per
commit" note in `F:rado-r4-a5-b3`'s own axiom footprint is about its **DRAT
refutation**, which none of its three evidence rows replays -- see finding 6.

## Classification

Two axes decide runnability: does the row carry a `checker_command` at all, and
do the files the command names exist in this tree. Both are mechanical; nothing
is judged by eye.

| fact | rows | class | command family | measured |
|---|---|---|---|---|
| `F:nat-add-assoc` .. `F:nat-zero-add` (17 facts) | 17 `kernel-term` | runnable | `nat_theorem_inventory -- <thm> \| grep -q...` | 0.32-0.36 s each |
| the same 17 facts | 17 `exhaustive-enumeration` / `instance-pin` | runnable | `nat_axiom_inventory -- --require-axiom-free nat` | **one** command, 0.56 s |
| `F:rado-r4-a5-b3` | `claim-rado-r4-a5-b3` (`claim-ref`) | runnable | `python3 scripts/validate-claims.py` | 4.4 s |
| `F:rado-r4-a5-b3` | `lower-bound-replay` (`witness-replay`) | runnable | `akb2_frontier -- verify 5 3 4 <witness>` | 0.07 s |
| `F:rado-r4-a5-b3` | `deciding-instance-regeneration` (`instance-pin`) | runnable | `rado_dump_cnf` + `sha256sum` compare | 0.11 s |
| `F:rado-r4-a5-b4` | `claim-741` (`claim-ref`) | runnable | `python3 scripts/check-claim-certificates.py` | 61.2 s |

The classifier is not decoration: pointed at `F:fp32-doubling-add-equals-mul-two`
and `F:fp8-add-monotone-rne` it independently reproduces the two rows
`13-facts-diary.md` finding 1 reported, marks them `not-runnable -- no
checker_command in the ledger row`, and **exits 1**.

## One record per EXECUTION, never one per citation

Seventeen facts cite the same axiom-freedom command, byte for byte. Emitting
seventeen records from one execution would manufacture sixteen checks that
never happened -- the same discipline `fact.schema.json` already applies to its
`checkers` list, one level up. So rows are grouped by exact command text, the
group runs once, and the record carries one entry in `claims[]` per citing row.
`runrec-index.json` maps `(fact id, evidence row id) -> (record file, record id,
claim key, claim status, exit status)`, which is what a consumer resolves
against.

The shared record is therefore named for the checker and a digest of the
command (`R:shared-nat-axiom-inventory-b5515894`), never for whichever citing
row sorts first. The first version named it `R:shared-footprint-nat-add-assoc`,
which is both misleading (it covers seventeen facts, one of which is that one)
and unstable under a change of fact set. Singleton records keep the readable
`R:<fact-short-id>-<row-id>` form. **Known wart:** if a second fact later cites
a singleton's command, that record is renamed. That fails closed and loudly --
`EvidenceRef.record_id` mismatch is a build error -- but it is churn, and the
index is the authoritative mapping for exactly this reason.

## What `inputs` pins, and what it deliberately does not

`Provenance.inputs` gets the files the command NAMES: the example source or
script implementing the checker, and the artifact the row points at, each with
a SHA-256 that assembly re-hashes on every render (fail-closed law rule 4). It
does **not** pin the transitive closure -- the rest of the crate behind a
`cargo run --example`, or the other 103 claims a ledger-sweeping checker reads.
Those are named in the record's `notes` rather than silently omitted, because
an input list that looks complete and is not is worse than a short one that
says so.

Consequence worth stating: for a `kernel-term` row the record pins
`nat_theorem_inventory.rs` and nothing inside `axeyum-lean-kernel`, so a
theorem could leave the prelude without tripping rule 4. What would catch it is
re-running, which is the point of a record having a `replay` line and a
measured `expected_seconds`. A content-addressed checker-closure digest is the
right long answer and is queued below.

## Claims on fact cards -- THE BRIDGE SPEC

This is the one-page implementation task for the next round. It is a wiring
job, not a research problem, and the proof of that is
`render/examples-input/runrec/bridge-probe.doc.json`: a hand-written Doc-IR
document in this lane's own directory that cites these records and renders,
`exit 0`, through the real `axeyum-render`. Do not ship the probe; read it, and
delete it once the producer emits the real thing.

### Where the pieces are

* Records: `render/examples-input/runrec/R-*.json`.
* Mapping: `render/examples-input/runrec/runrec-index.json`, 38 entries keyed
  by `(fact_id, evidence_row)`. **Not a Doc-IR document and not a run record**
  -- do not pass it to `scripts/validate-docir.py`.
* Fact cards are emitted to `render/examples-input/facts/cards/`, so
  `EvidenceRef.run_record` (which resolves relative to the MANIFEST's
  directory) is `../../runrec/R-<...>.json`. `Provenance.inputs` paths inside
  the record resolve against the REPO ROOT instead; the two are different bases
  and mixing them up is the first thing that will go wrong.

### What `facts_to_docir.py` should do

For each fact card, after the existing `statement` / `status-axes` /
`trust-base` blocks and before the per-row `certificate` blocks:

1. Load `runrec-index.json` once. Select entries with `fact_id == this fact`.
   **If there are none, emit no claim block.** A fact with no replayed evidence
   keeps exactly today's behaviour, which is already correct.
2. Emit ONE claim block per fact, id `claim-evidence-replay`, citing every
   matching entry -- not one claim per row. The rows are joint evidence for one
   proposition; splitting them would render a page of near-duplicate badges and
   would lose the fact that a green kernel row plus a red footprint row is not
   a proved fact.
3. Fields:
   * `label`: `"<fact title>"`. The title, not the statement: `label` is the
     key of the cross-format property test, so it has to be short and stable.
   * `statement`: `{"source": "text", "text": <the fact's `statement` prose,
     verbatim>}`. Verbatim -- the ledger prose is the statement of record, and
     this is the one place a producer is allowed to copy it, because
     `BlockStatement` cannot carry text (`13-facts-diary.md` item 1).
   * `status`: the fact's `epistemic_status` through the EXISTING
     `EPISTEMIC_TO_BADGE` table. This is a **declared ceiling**, not a result.
     Do not compute anything here.
   * `evidence`: one `EvidenceRef` per index entry:
     `{"run_record": "../../runrec/" + entry.run_record,
       "record_id": entry.record_id, "claim_key": entry.claim_key,
       "role": <see below>}`.
   * `note`: a `RichText` saying which rows were replayed, when (the record
     epoch), and that a card whose rows have not been replayed carries no
     claim. Do NOT restate the status in prose -- the badge is computed and the
     prose is not, and that is precisely how the two drift apart.
4. `role` on each reference, by ledger evidence `kind`, because independence is
   the value and count is not:
   * `kernel-term` -> `primary`
   * `exhaustive-enumeration`, `instance-pin` -> `replication`
   * `witness-replay`, `claim-ref` -> `replay`
   * a row whose `checkers` names an oracle disjoint from the producing tool ->
     `cross-oracle`
   * never `negative-control` from this path; see below.
5. Nothing else changes. The `certificate` blocks stay exactly as they are:
   they render the ledger row as recorded, the claim renders what running it
   found, and a reader can see both.

### What the assembly guards give you for free -- MEASURED, not assumed

All four were exercised against these records through the real binary:

| you do | assembly does | measured |
|---|---|---|
| declare `status: proved` over a record whose claim caps at `checked` | renders `CHECKED` | `F:nat-add-comm` on the probe renders `[CHECKED]` against a `proved` declaration |
| point at a record whose declared input bytes moved | REFUSES the build | `BUILD REFUSED: ... hashed 5253659a... but the run recorded 000000... (fail-closed law rule 4)`, exit 1 |
| cite a `negative-control` record as support | REFUSES the build | `BUILD REFUSED: ... declares role: negative-control ... but it is cited as primary. A negative control never supports a claim`, exit 1 |
| label a production record `negative-control` | REFUSES the build | `BUILD REFUSED: ... the record does not: it is a production run`, exit 1 |

And a red run needs no special handling at all: a record with
`exit_status != 0` carries `outcome: inconclusive` and its per-row claim status
is `open`, so `rendered_status` demotes the card's claim to `open` without the
producer deciding anything. Verified end to end by running a deliberately
failing variant of a real ledger command (`nat_theorem_inventory --
add_comm_this_does_not_exist`): measured `exit_status 1`, `outcome
inconclusive`, claim `open`, and the record still validates.

### The consequence P1-CARDS must expect

**Every arith-pilot card will render `checked`, not `proved`.** Thirteen of the
seventeen `kernel-term` rows check the theorem's NAME and not its type
(finding 2), so this producer caps their record claims at `checked`, and a
ceiling of `proved` meets a cap of `checked` and loses. That downgrade is not a
bug to route around; it is the ledger's evidence being rendered at its actual
strength for the first time. If the ledger's rows are strengthened to pin the
canonical type -- four of them already do -- the cards go green again with no
render change at all.

The two Rado cards render `evidence`, which matches the existing
`computed -> evidence` mapping, so nothing moves there.

## Ledger-integrity findings

Handed to the coordinator for the ledger lanes. All measured on this run.

1. **`fact.schema.json` has no `sha256` property on an evidence row at all.**
   Ledger-wide: 200 evidence rows, **0** carrying a digest, and **104 of them
   name an artifact file** (52 `witness-replay`, 22 `exhaustive-enumeration`,
   12 `unsat-certificate`, 9 `kernel-term`, 7 `instance-pin`, 2 `claim-ref`).
   Nothing in the ledger binds a row to the bytes it points at, so "the
   artifact hash differs from the recorded sha256" -- one of the three findings
   this lane was asked to look for -- is not merely absent, it is
   unfalsifiable at the ledger level. The run records emitted here are the
   first digest binding for the three Rado artifacts, and `facts_to_docir.py`
   already recomputes hashes for its certificate blocks. Recommendation: an
   optional `sha256` on `evidence[]`, gated by `validate-facts.py` when the
   artifact is a file that exists.

2. **13 of the 17 `kernel-term` rows check the theorem's NAME, not its type,
   and this is measured rather than argued.**
   `grep -qE '^Nat\.add_comm[[:space:]]'` passes for any theorem of that name.
   `R:control-nat-add-comm-name-only-blind` is a `negative-control` record of
   the real pipeline with one `sed` inserted, which rewrites the printed type
   to `AxNat.le x0 x1` -- a different and false proposition -- before the row's
   own grep sees it. The line the grep receives is
   `Nat.add_comm<TAB>2<TAB>((x0 : AxNat) -> ((x1 : AxNat) -> AxNat.le x0 x1))`,
   and the ledger's checker **exits 0**. The four rows that use
   `grep -qxF '<name><TAB><arity><TAB><canonical type>'`
   (`euclid_lemma`, `exists_prime_dvd`, `exists_prime_gt`, `pow_add`) are
   immune. Fix is mechanical: `nat_theorem_inventory` already prints the
   canonical type, so the other thirteen rows can pin it the same way.
   *(Separately checked and clean: all 17 facts' `formal.statement` agrees with
   the kernel's admitted type up to alpha-renaming and parenthesisation. The
   statements are right; the checkers just would not notice if they stopped
   being right.)*

3. **Seventeen "footprint" rows are seventeen citations of one command.** They
   are byte-identical (`nat_axiom_inventory -- --require-axiom-free nat`), so
   the ledger currently displays seventeen independent-looking checks over one
   execution. Nothing is wrong with the check -- it is the right check, and it
   is the one that carries this project's headline metric -- but a reader
   counting evidence rows is counting citations.

4. **`check_status` still has zero discriminating power.** All 38 rows in this
   subgraph say `checked`, confirming `13-facts-diary.md` finding 4 on a set
   that has now actually been run. The field records that somebody once
   asserted a check; after this lane, `runrec-index.json` records that a check
   ran, when, and what it exited.

5. **`F:rado-r4-a5-b4`'s `claim-741` row runs a WHOLE-LEDGER SWEEP for one
   claim: 61 s, and its exit status does not depend on the claim it is
   evidence for.** `check-claim-certificates.py` already takes `--only`:
   `--only rado-r4-a5-b4-frontier` re-checks that claim's instance pin,
   witness, and 6241-cube tree cover in **0.84 s** -- 72x faster and, far more
   importantly, *scoped*. As recorded, if
   `artifacts/claims/rado/rado-r4-a5-b4-frontier/claim.json` vanished the sweep
   would still exit 0 over the remaining 103 claims, and the fact's evidence
   row would report green. That is the CLAUDE.md gotcha "an empty result from a
   tool that was never pointed at your subject" sitting in the ledger, on a
   headline fact. Recommendation: change the row's `checker_command` to the
   `--only` form. (`F:rado-r4-a5-b3`'s `claim-ref` row has the same shape;
   `validate-claims.py` has no `--only`, so that one needs the flag added
   before the row can be scoped.)

6. **Nothing in `F:rado-r4-a5-b3`'s evidence replays its DRAT refutation.** Its
   three rows cover the lower-bound colouring, the claim file's schema and
   semantics, and the deciding instance's regeneration. The upper bound -- the
   harder half of `R_4 = 625` -- rests on the certificate the fact's own
   `axiom_footprint` flags as `rado.certificate-not-re-checked-per-commit`. The
   fact is honest about it; what is new here is that a rendered page can now
   show precisely which halves were re-run today and which were not, instead of
   one badge over both. Note the contrast with `b4`, whose single row DOES
   re-check its 6241-cube tree cover.

7. **Minor: the `deciding-instance-regeneration` command hardcodes
   `/tmp/rb3.cnf`** and writes 6.6 MB there. `/tmp` on this fleet is a tmpfs
   (RAM) that CLAUDE.md already flags as a standing OOM contributor. It is 6.6
   MB, so this is a nit, not an incident -- but the row is a template other
   instance-pin rows copy.

8. **`F:rado-r4-a5-b4`'s row names no `checkers` at all** (`null`), where
   `b3`'s three rows name one or two each. Cross-oracle agreement is the
   strongest signal this repository has, and the field is optional, so a
   headline fact silently opts out of showing it.

## Fail-closed behaviour of this producer

The producer's own exit status depends on the finding, not on completion:

| condition | exit | demonstrated |
|---|---|---|
| every command ran, every record validated, no red | 0 | the main sweep |
| a run exited nonzero | 1 (unless `--allow-red`) | `add_comm_this_does_not_exist`: `exit_status 1`, `outcome inconclusive`, claim `open`, record still valid |
| a row could not be run | 1 (unless `--allow-skips`) | the two `fp32`/`fp8` rows with no `checker_command` |
| an emitted record fails `validate-docir.py --kind run-record` | 1 | validator is invoked on every write; 23 files, 69 check groups, 0 errors |
| nothing was written | 2 | an empty run is not a passing run |

A red run is still WRITTEN. Recording the reds is the job; the flags only
control whether the producer's own status treats them as a failure of the
sweep. And the record is faithful in both directions: nothing in the code path
can turn a nonzero exit into `outcome: established`, which is also the rule
`scripts/validate-docir.py` enforces independently.

Timeout discipline: 120 s per command (`--timeout`), enforced by
`subprocess.run`. A command that exceeds it is **skipped with a note and no
record is written** -- a timed-out run has no exit status, and inventing one
would be the forgery this whole lane exists to avoid.

## Determinism

These records are MEASUREMENTS, so they are not byte-reproducible and should
not be treated as golden files. Two runs of the same command produce records
identical in every field except `provenance.duration_ms`, `stats.wall_seconds`,
`replay.expected_seconds` and the elapsed time quoted in `summary` -- verified
by an A/B into two directories. Everything else (ids, claim keys, statuses,
input digests, epoch, notes) is byte-stable, and the epoch is an INPUT taken
from the current commit, never the wall clock; with no commit and no
`SOURCE_DATE_EPOCH` the producer refuses to run.

If `render/check.sh` ever grows a step over this directory it must compare
modulo those four fields, or pin the corpus and not regenerate it.

## Handoffs

* **To P1-CARDS / whoever owns `facts_to_docir.py`:** the bridge spec above.
  This lane did not touch `render/producers-py/` or
  `render/examples-input/facts/` -- ownership held. The change is confined to
  one new block emitter plus an index load.
* **To the coordinator:** findings 1-8, of which 2 and 5 are the two that
  change what the repository can claim.
* **To `render/check.sh`'s owner:** these 23 records are not in any gate. They
  should be, at least to the extent of `validate-docir.py --kind run-record`
  over `render/examples-input/runrec/R-*.json` -- and NOT over
  `runrec-index.json` or `bridge-probe.doc.json`, which are a lookup table and
  a scratch probe respectively.

## Left for the round after

1. **A content-addressed checker-closure digest**, so a record can pin "the
   bytes that could change this verdict" rather than the file the command
   happens to name.
2. **Re-run staleness as a rendered fact.** A record's epoch is a commit; a
   card could show how many commits old its evidence is, which is the honest
   version of `check_status: checked`.
3. **The rest of the ledger.** 200 evidence rows exist; 38 have been run. The
   producer takes `--facts-from` and `--fact`, so widening is a scheduling
   question (cost, not capability) -- but see finding 5 before running any
   sweep-shaped checker 100 times.
4. **A `--strict` corpus run.** `axeyum-render --strict` turns red evidence
   into a build error rather than a demoted claim; once cards carry claims,
   somebody has to decide which of the two the published corpus uses.
