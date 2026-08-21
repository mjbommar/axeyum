# 13 -- FACTS lane diary (P0-B: fact ledger -> Doc-IR)

Lane: FACTS, render strand round 1, 2026-08-21. Owns
`render/producers-py/`, `render/examples-input/facts/`, this file.

Producer: `render/producers-py/facts_to_docir.py` (python3 stdlib +
`jsonschema` when importable; a vendored subset validator otherwise -- see
"Dependency check" below).

## Counts (measured, this run)

| quantity | value |
|---|---|
| fact files read from `artifacts/facts/` | 324 |
| facts that failed to map | 0 |
| fact cards emitted | 324 |
| index documents emitted | 3 (`facts-atlas`, `facts-pilot`, `facts-pilot-arith`) |
| `depends_on` edges | 135 (0 dangling) |
| evidence rows carried | 200 (all `check_status: checked`) |
| certificate blocks emitted | 198 |
| evidence rows with no replay route | 2 (warned, see Findings) |
| output size | 6.9 MB total; atlas 990 KB, cards 5.8 MB, median card 14 KB |
| epoch | `unix=1787144076 source=commit commit=d637d83f77db` (last commit touching `artifacts/facts/`) |

Ledger shape as this producer sees it: epistemic `open=217 proved=99
refuted=3 conjectured=3 computed=2`; routes `kernel-lean=43
cas-certificate=19 smt-term-level=16 search-certificate=12 smt-clausal=9
imported-kernel-lean=5`, 104 facts carrying a route at all; external
`proved=296 unknown=12 open=5 refuted=3`, and 205 of those externally
proved facts are `open` here -- the import backlog is two thirds of the
ledger. 8 facts carry no `external_status` field at all (rendered
`unclassified`, deliberately NOT `unknown`, because the schema says an
absent field means nobody looked while `unknown` means we looked).

Nothing was skipped. Every fact validated against `fact.schema.json`,
every `depends_on` resolved, and every fact mapped to a card.

## The pilot subgraph

`facts-pilot.doc.json` -- 9 facts, 8 `depends_on` edges:

    F:ml430-nat-fib-add-two-b86e0c82            proved  kernel-lean, axiom_footprint []
    F:ml430-nat-fib-coprime-fib-succ-162fc738   open
    F:ml430-nat-fib-le-fib-succ-d1ef4a3d        open
    F:ml430-nat-fib-mono-cc6afe09               open
    F:ml430-nat-gcd-fib-add-self-5a92d5e3       open
    F:ml430-int-fib-natcast-d5886be4            open
    F:ml430-int-fib-add-two-739358dd            open
    F:ml430-int-fib-add-one-33f1b748            open
    F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d  open

Chosen by measurement, not by taste. Over the whole ledger (324 facts, 135
edges) there are 37 connected components of size >= 2 and exactly TWO of
them contain more than one distinct `epistemic_status`: this one (9 facts)
and `{excluded-middle, double-negation-elimination,
excluded-middle-not-intuitionistic}` (3 facts). Only this one is inside the
brief's 8-20 band. **The ledger's dependency graph is almost perfectly
status-homogeneous**, which is itself a finding: facts get proved in
clusters, and a mixed cluster is a frontier being worked.

That is exactly what this one is. One fact is proved here on the
`kernel-lean` route with an empty axiom footprint; all eight descendants
are `open` here and `external_status: proved`, so every one carries the
`import-backlog` flag. The page renders the self-extension frontier rather
than finished work.

Cost of the choice, stated plainly: the pilot is a 9-node TREE and eight of
its nine facts have zero evidence, so it exercises statements, badges and
the disagreement rule but almost nothing of the certificate machinery.

So a second document is emitted for round 2 to choose from:
`facts-pilot-arith.doc.json` -- the `depends_on` ancestor closure of
`F:nat-euclid-lemma`, `F:nat-exists-prime-gt`, `F:nat-pow-add` inside the
ledger's largest component: **17 facts, 27 edges**, real branching, and 34
checked evidence rows with replay commands. Uniformly `proved` /
`kernel-lean` / axiom-free, so it has no badge variety at all.

Recommendation for the round-2 page: `fact-pilot-arith` for a page that
must look rich (dense DAG + 34 certificates), `fact-pilot` for a page that
must demonstrate the two status axes and the fail-closed rule. The two
together cover what one connected subgraph of this ledger cannot.

## Doc-IR fit: what the schema forced, and what it does not cover

`docir.schema.json` landed while this producer was being written against
`03-architecture.md`. The first emission was validated against the real
schema and FAILED (that is the checker working, and it is why the output
check is on by default). What changed, and what is still awkward:

1. **`BlockStatement` has no `text` property.** Statement text is not
   copied into a card at all; the card carries `{"kind": "fact", "id":
   "F:..."}` plus a `show` projection, and assembly resolves the ledger
   entry. This is stronger than the brief asked for ("statement rendered
   faithfully, never altered") -- the text cannot be altered because it is
   not there. **Round-2 dependency: assembly must resolve fact refs and
   honour `show`, or the cards render empty.**
2. **No `claim` blocks are emitted, and that is not an omission.** A Doc-IR
   claim requires >= 1 `EvidenceRef`, and an `EvidenceRef` is a path to a
   RUN RECORD carrying `provenance.exit_status`. A fact ledger evidence row
   is not a run record: it carries `check_status: checked` (an assertion
   that someone checked it) and a command a reader can run, but no recorded
   exit status. Emitting a claim over that would fabricate the one field
   the whole fail-closed law flows through. So evidence renders as
   `certificate` blocks (which may legitimately have empty `evidence`) and
   the status comes from the resolved fact record.
   **This is the biggest structural gap between the ledger and the render
   strand: to put claims on fact pages, the ledger's checker commands have
   to actually RUN and emit run records.** That is a real piece of work
   (some of these checkers take hours; `F:rado-r4-a5-b3` says its
   certificate is deliberately not re-checked per commit) and it should be
   an explicit round-2/P1 decision, not something a producer papers over.
3. **Status vocabularies do not align.** The ledger's `epistemic_status` is
   `{axiom, proved, computed, empirical, conjectured, open, refuted}`; the
   Doc-IR `EvidenceStatus` is `{proved, checked, evidence, advisory,
   refuted, open}`. The producer maps conservatively and never upgrades:
   `computed -> evidence` (a finite computation carries no universal
   credit, which is what `evidence` means), `conjectured -> open`,
   `axiom`/`empirical -> evidence` (no such fact exists today). `checked`
   and `advisory` are unreachable from a fact by construction -- `checked`
   would mean this producer replayed the evidence, and it replays nothing.
   The mapping table lives in one place (`EPISTEMIC_TO_BADGE`) and the
   ledger value is always shown beside the badge in the `status-axes`
   table, so a reader can see the mapping rather than trust it. Round-2
   question for CORE: should the mapping live in the schema (a documented
   table) rather than in each producer?
4. **`external_status` has nowhere structural to go.** Doc-IR claims and
   figure nodes carry ONE status. The second axis is rendered as a table
   row plus, when the axes disagree, a prose block (`disagreement-novel` /
   `disagreement-import-backlog`) mirroring `validate-facts.py`'s `novel`
   and `backlog` reporting. Round-2 suggestion: an optional
   `external_status` on `FigureDepGraph.nodes` and on `BlockStatement`'s
   resolved projection would let the atlas colour "ours" and "the
   literature's" independently, which is the picture this project actually
   wants to show.
5. **`Cell` is a scalar, so a table cannot carry a link.** Links between
   cards therefore ride on `FigureDepGraph.nodes[].href` (per-card
   "dependency neighbourhood" figure, and the atlas graph), and the
   dependency tables carry the card path as a plain string cell for an
   emitter to linkify by convention. This is a deliberate schema
   constraint, but it means **the card-to-card link story depends entirely
   on the figure renderer**; if DESIGN's layout module does not emit
   `href`, the atlas has no navigation.
6. **`cert_kind` has 6 values against the ledger's 10 evidence kinds.**
   Mapped: `kernel-term -> kernel-admission`, `unsat-certificate ->
   unsat-drat`, `witness-replay -> witness-replay`,
   `cube-cover`/`cube-tree-cover -> cube-cover`, and the remaining four
   (`exhaustive-enumeration`, `published-value-replication`,
   `bound-citation`, `instance-pin`, `claim-ref`) collapse to `report-run`.
   Because that mapping is lossy, every certificate is accompanied by an
   `evidence-NNN-record` table carrying the ledger row verbatim: id, ledger
   kind, `cert_kind`, `check_status`, the named independent `checkers`,
   `supports`, artifact path/state/sha256, and any `measurement` /
   `checker_operation` / `checker_seconds`. Nothing is summarised away.
   `exhaustive-enumeration` is 68 of 200 rows -- the single most common
   kind in the ledger -- and it renders as `report-run`, which understates
   it. Worth an enum addition in round 2.
7. **`Certificate` has no field for `check_status` or `checkers`.** Same
   remedy (the record table). Cross-oracle agreement is the strongest
   signal this repository has -- 127 evidence rows name 2+ independent
   checkers -- and right now the renderer can only show it in a table cell.

## Fail-closed behaviour of the producer

Nothing is written unless every one of these passes, so `exit_status: 0` in
an emitted document's provenance means the checks found nothing, not that
the process completed.

| guard | demonstrated by | result |
|---|---|---|
| input fails `fact.schema.json` | temp copy, `formal.language` set to `coq` | exit 1, `NOTHING WAS WRITTEN`, 0 files |
| dangling `depends_on` | temp copy, added `F:does-not-exist` to `F:nat-add-comm` | exit 1, 0 files |
| green-badge guard: settled status with no `checked` evidence | temp copy, `F:nat-add-comm` evidence flipped to `replay-only` | exit 1, 0 files |
| `open` fact carrying evidence | same rule as `validate-facts.py` | (no such input in the ledger) |
| own output fails Doc-IR validation | in-process: block `tag` set to `verbose` | 1 error; restoring the tag gives 0 errors (the one-guard control) |
| Doc-IR schema absent | `--allow-missing-docir-schema` required to proceed | fails by default |

Two independent guards keep an unsupported fact off a settled badge: the
abort above, and a downgrade to `open` inside `badge_for_epistemic` if a
settled ledger status ever reached it with `checked == 0`.

One thing this producer deliberately does NOT do: put a ledger
`checker_command` into a `Provenance.command`. A Provenance asserts that
its command ran and exited with the recorded status, and this script runs
no checkers. Checker commands appear only as `Certificate.replay.line`,
which is an invitation to the reader, with `expected_exit_status: 0`.

## Determinism

Two builds into different directories are byte-identical (`diff -r`, 327
documents + manifest). Achieved by: sorted keys, sorted iteration,
`ensure_ascii=True`, no wall clock, and manifest paths recorded relative to
the output directory (the first version recorded repo-relative paths, which
made an out-of-tree A/B build report a difference the documents did not
have -- caught by the determinism check itself).

`meta.epoch` is an INPUT: `--epoch-unix` > `SOURCE_DATE_EPOCH` > the commit
time of the last commit touching `artifacts/facts/`. That last fallback is
what keeps regeneration stable in this shared checkout: the ledger's own
last commit does not move when an unrelated lane commits, so re-running on
an unchanged ledger reproduces the bytes. With no epoch available at all
the run FAILS rather than reading the clock.

## Dependency check (stdlib + jsonschema only)

`jsonschema` 4.19.2 is importable on this host, so it is used. The script
also carries a vendored subset validator for the case where it is not, and
the vendored path is exercised, not assumed:

- with `jsonschema` blocked (a stub module on `PYTHONPATH` that raises
  `ImportError`), the run emits documents **byte-identical** to the
  jsonschema-backed run, reporting `fact schema backend: vendored`;
- and it is not inert: the same `formal.language = coq` mutation is caught
  by the vendored backend, with the same exit 1 and nothing written.

The vendored validator implements the keywords these two schemas actually
use and REPORTS any keyword it does not implement rather than ignoring it.
A validator that silently skips what it does not understand is the
inert-gate defect in miniature.

## Sanity: three cards verified field by field

Verified against the source files after emission.

**`F-nat-add-comm.doc.json`** (proved / kernel-lean / axiom-free)
- `meta.title` equals `fact.title`; `meta.doc_id = fact-nat-add-comm`.
- `statement` block ref is `{kind: fact, id: F:nat-add-comm}` -- matches.
- The fact's `statement` prose is NOT inlined... except it *is* present in
  the file, twice, and both occurrences are correct: the ledger's evidence
  row `kernel-add-comm` has `supports` set to the same sentence, so it
  appears as the certificate `summary` and in the evidence record table.
  The `formal.statement` (the kernel type) appears nowhere in the card, as
  intended. Worth writing down because a naive "does the statement string
  appear in the output" check reports a false positive here.
- `status-axes` rows: `proved / proved / 2 of 2 evidence row(s) checked`
  and `proved / proved / copied from the ledger's external_status`. Both
  values copied; the badge is the mapping, shown beside the ledger value.
- `trust-base`: `kernel-lean`, `[] -- axiom-free; only kernel-lean can
  deliver this`. Ledger: `proof_route: kernel-lean`, `axiom_footprint: []`.
- 2 evidence rows -> 2 certificates, `cert_kind` `kernel-admission` and
  `report-run`; `replay.line` byte-equal to `checker_command` for both;
  `summary.text` byte-equal to `supports` for both.
- `depends_on` `[F:nat-succ-add, F:nat-zero-add]` -> same two rows.

**`F-rado-r4-a5-b3.doc.json`** (computed / search-certificate / NOVEL)
- `status-axes`: epistemic `computed` -> badge `evidence` (3 of 3 checked);
  external `open`. A `disagreement-novel` block is present and its text
  names both values -- this mirrors `validate-facts.py`, which prints
  exactly this fact (and `F:rado-r4-a5-b4`) as NOVEL.
- `trust-base` lists all three footprint entries verbatim, including
  `rado.certificate-not-re-checked-per-commit` -- the fact's own admission
  that its DRAT is not replayed per commit stays visible on the page.
- 3 evidence rows -> 3 certificates; all three `replay.line` byte-equal to
  the ledger `checker_command`; all three artifacts
  (`claim.json`, `witness.txt`, `F_625.cnf`) resolve to files in the tree
  and their `sha256` values in the card were **recomputed from the files
  and match**.

**`F-ml430-nat-fib-coprime-fib-succ-162fc738.doc.json`** (open / external
proved -- a pilot member)
- `status-axes`: `open / open / 0 of 0 evidence row(s) checked` and
  external `proved`. No certificate blocks, no claim block, no green
  anything -- the fail-closed default for a fact with nothing behind it.
- `disagreement-import-backlog` block present; text names both axes.
- `depends_on` `[F:ml430-nat-fib-add-two-b86e0c82]` -> one row, and the
  dependency-neighbourhood figure carries an `href` to that card.
- Neither `statement` nor `formal.statement` appears anywhere in the file
  (this fact's formal statement contains non-ASCII Lean surface syntax;
  the emitted file is pure ASCII regardless, by `ensure_ascii`).

## Findings worth other lanes' attention

1. **Two evidence rows have no `checker_command`** and therefore render
   with no replay route and no certificate block (they still get a record
   table): `F:fp32-doubling-add-equals-mul-two` /
   `fp32-doubling-unsat-drat` and `F:fp8-add-monotone-rne` /
   `fp8-monotone-unsat-drat`. Both are `check_status: checked`
   `unsat-certificate` rows. A checked certificate a reader cannot replay
   is exactly what the reader test for this strand is about; this is a
   ledger gap, not a render gap.
2. **`evidence[].artifact` is used three different ways.** Over 104 rows:
   96 repo-relative file paths, 6 bare `sha256:<64 hex>` content digests
   naming no file, 2 directories
   (`artifacts/instances/dbdesign/negative-controls/`). The producer
   resolves each to a distinct state (`present` / `content-hash-only` /
   `directory`) and only `present` gets an `include` block with a
   recomputed hash. Nothing is silently treated as a hashable file.
3. **`prior_art` entries do not use the schema's own key names.** The
   schema documents `who` / `what` / `where` / `year` / `attribution`;
   the ledger predominantly uses `citation` / `establishes`. Both validate
   (the object is `additionalProperties: true`), so the producer derives
   the prior-art table's columns from the keys actually present per fact.
   Two vocabularies for one field is a small version of the problem
   `proof_route` was introduced to fix.
4. **All 200 evidence rows say `check_status: checked`.** The field has
   zero discriminating power in the current ledger -- the same observation
   `fact.schema.json` records about `checkers`, one level up. The renderer
   cannot distinguish evidence strength from this field, so it shows the
   `checkers` list instead (127 rows name 2+ independent checkers).
5. **Output size.** 6.9 MB for the full ledger (324 cards). If committing
   that as example input is unwelcome, `--pilot <ids>` emits a restricted
   set, or the cards directory can be generated by `render/check.sh`
   instead of committed. Coordinator's call.

## Round-2 handoff

- Resolve fact `FormalRef`s in assembly and honour `BlockStatement.show`
  (items 1 and 5 above) -- without it a card renders as badges and tables
  with no mathematics.
- Decide the run-record question for fact pages (item 2). Until then, fact
  pages legitimately carry no claims.
- Emitter needs: `FigureDepGraph` with `href` and `group` (routes, plus
  `focus` on a card's own node), `include` with `render_hint` in
  `{json, text, code, link, table}`, and `RichText` captions.
- Interface assumption to confirm with CORE: this producer invokes
  `scripts/validate-docir.py <paths...>` for its own output check, and
  retries once with `--kind document` if that spelling is an argparse usage
  error (CORE's diary says the same script validates run records under
  `--kind run-record`). The script is not on disk yet, so this path is
  written but unexercised; until it lands, the output check runs the schema
  directly and passes.
- Regenerate with `python3 render/producers-py/facts_to_docir.py`; it is
  safe to run repeatedly (deterministic, and it refuses to write when the
  ledger is inconsistent).
