# ADR-0540: Doc-IR and the run record as public evidence formats; render/ promotion criteria

Status: proposed
Date: 2026-08-21
Index-summary: Doc-IR + RunRecord become public evidence formats (semantics, replay, checker); `render/` promotes to `axeyum-render` on named triggers, not yet; fail-closed rendering and the no-Node/self-containment rules become repo-level.

## Context

The render strand (`docs/render-2026-08/`) exists because this project produced
documents by hand-transcribing machine-checked numbers into prose and LaTeX --
the drift class the whole stack exists to kill, reintroduced at the last step.
The NoH-p2 paper needed three normalization corrections across documents in one
project because the same number lived in four places and only one of them was
computed.

P0 built the machinery: a Doc-IR (`render/src/ir.rs`), a fail-closed resolver
(`render/src/assemble.rs`), three emitters (Markdown, LaTeX, self-contained
HTML), a JSON Schema (`artifacts/ontology/docir.schema.json`), and an
independent Python validator (`scripts/validate-docir.py`). The P0 exit report
(`docs/render-2026-08/14-p0-exit-report.md`) records eight criteria measured one
by one: seven PASS, one ADJUSTED-PASS, plus one reader test that is the owner's
and not an agent's to run.

Three questions were deliberately left to this ADR by
`docs/render-2026-08/03-architecture.md` ("Crate and ADR plan") and queued as
"ADR #1" in `06-roadmap.md` P1:

1. `render/` is a plain cargo package that is NOT in the workspace members list
   -- a tool, not public surface. ADR-0001 says crates land only after a
   boundary is proven by use. Is the boundary proven?
2. The Doc-IR document and the run record are consumed by producers in two
   languages and validated by a repo-level gate script. Hard Rules require
   semantics, model/proof lifting, and replay/checker routes to be explicit
   *before* something becomes public surface. They are not yet written down as
   a contract anywhere outside the schema's own prose.
3. Two constraints are currently enforced by one strand's `check.sh` and stated
   only in that strand's notes: the owner's no-Node rule, and the fail-closed
   rendering law. Both are repository-level properties wearing strand-level
   clothes.

### Where this sits in the foundational DAG

Checked, as required before adding public surface:
`docs/research/08-planning/foundational-dag.md` has no rendering node, no
rendering layer contract, and no rendering arrow. **That is correct and should
stay correct.** Reader-facing rendering is not a foundation layer: it introduces
no operator, no rewrite class, no encoding, no backend, and no logic fragment,
so five of the six bullets in the Phase 7 standing entry contract do not bind
it. It is a strictly downstream CONSUMER of the DAG's terminal evidence layers
-- "layered SAT/BV evidence artifacts", the fact ledger, and kernel admission --
and it must never become an input to any of them. A renderer that could
influence what is proved would be a second place a green badge could come from.

The sixth bullet does bind, and is why this ADR exists: *proof/evidence format
and checker plan*. Doc-IR documents and run records are evidence artifacts, so
they need declared semantics, a replay route, and a checker route before they
are public.

If this ADR is accepted, its owner should add one terminal arrow and one row to
the DAG (this ADR does not edit that file):

```text
  -> SMT-LIB text front door (`solve_smtlib`: text -> checked answer)
  -> reader-facing rendering (consumes evidence; produces none)
```

| Layer | Depends on | Contract | Required check |
|---|---|---|---|
| Reader-facing rendering | Evidence artifacts, fact ledger, kernel inventory | A rendered document asserts nothing its references do not; every claim resolves to a recorded run, and no rendering result feeds back into any layer above. | Assembly's fail-closed negative tests (delete-one-guard), `scripts/validate-docir.py`, byte-determinism of two builds. |

## Decision

**Doc-IR and the run record become public evidence formats now, under the
semantics/replay/checker contract stated below; the fail-closed rendering law
and the no-Node/self-containment rules become repository-level rules; and
`render/` is promoted to the workspace crate `axeyum-render` at the next natural
point, defined by the named triggers below rather than by a date.**

### (a) Promotion of `render/` to `axeyum-render`

Not yet. Promote when ANY of these three triggers fires:

* **T1 -- an outside producer.** A producer authored by someone other than the
  render lane lands using only the committed docs and schema. This is
  `06-roadmap.md` P1's own gate ("the boundary-proven-by-use test") and it is
  the trigger that actually discharges ADR-0001.
* **T2 -- an in-workspace consumer.** A workspace crate needs the Doc-IR types
  directly -- an `--emit-docir` flag inside a crate rather than a script over
  that crate's output. At that moment the non-member package becomes an
  unsatisfiable dependency, and promotion stops being a preference.
* **T3 -- gate integration.** `render/check.sh` folds into `just check` /
  `scripts/check.sh`, at which point the package is on the repository's critical
  path and must carry the workspace's lint, MSRV, `cargo deny`, `cargo doc` and
  wasm obligations rather than its own.

**Boundary-proven-by-use evidence today** (what is genuinely exercised):

| axis | evidence |
|---|---|
| Producer families | THREE, in two languages and three shapes: a Rust `--emit-run` binary (`render/producers/noh_wt_certificate_emitrun.rs`, CERT); a Python ledger reader over `artifacts/facts/*.json` (`render/producers-py/facts_to_docir.py`, FACTS, 324 cards + atlas); and a Python producer over the output of Rust example binaries (`render/producers-kernel/kernel_to_docir.py`, this ADR's companion work, 3 documents + 5 run records + 2 inventory snapshots). The third exercises `FormalRef::Kernel`, which until now was implemented but not used by any committed document -- item 4 of the P1 queue in `15-integrate-diary.md`. |
| Emitters | THREE (`md`, `tex`, `html`) behind one `Emitter` trait, with a cross-format property test that recovers `(claim label, status)` from the emitted BYTES of each format and requires the three sets to be equal, on the fixture AND on the committed corpus. |
| The P0 gate | `render/check.sh`: 15 passed / 0 failed over 10 steps, 126 tests across nine binaries; eight exit criteria measured individually; a mutation pass in which each fail-closed guard is deleted and the tests that die are counted (`14-p0-exit-report.md`, 2026-08-21). |
| Independent re-derivation | The schema has two implementations (Rust serde model + `scripts/validate-docir.py`), by the same discipline `validate-facts.py` applies to the fact ledger. |

**What is NOT proven, stated so the promotion is not argued from a number
alone:**

* No producer has yet been written by anyone outside the render lane. Three
  producers by three agents of one strand is breadth, not independence: T1 is
  the trigger precisely because this is the gap.
* No crate in the workspace depends on `render/`, so promotion today would
  create a member that nothing imports.
* The workspace-wide obligations have not been run against it as a member: MSRV
  1.88, `cargo deny` (not installed on any measured fleet host), `cargo doc -D
  warnings`, and the wasm32 target build.
* `schema_version: 1` has been evolved additively for one week. The additive-only
  rule below has not yet had to refuse anything.
* The owner's reader test on `render/out/certificate.html` is still outstanding,
  and it is the criterion that decides whether the output is worth a crate.

Until a trigger fires, `render/` stays a non-member package, and the strand's
standing rule stands: additive changes and new files only.

### (b) Doc-IR and the run record as public evidence formats

Public as of this ADR, with the contract Hard Rules require stated explicitly.

**Semantics.** A `Document` is a projection of resolved references, not a
container of assertions. It holds prose plus references; it holds no number,
statement, table cell, badge or figure that a human typed. A `RunRecord` is one
execution's testimony: what ran (`provenance.generator`, `provenance.command`),
over which bytes (`provenance.inputs`, SHA-256 per path), whether it completed
(`provenance.exit_status`), what it FOUND (`outcome`), what it is (`role`:
`production` or `negative-control`), and which claims it establishes (`claims`,
each with its own status). `exit_status` and `outcome` are separate on purpose:
a run that completes and finds a counterexample is not the same event as a run
that crashed.

A third format is public with them: the **kernel inventory snapshot** that
`FormalRef::Kernel` resolves against (`{"declarations": [{name, kind, type,
axiom_footprint}]}`). It exists because this kernel's theorem inventory cannot
be read from source text -- declarations go through a `.theorem(name, ...)`
helper over interned name ids, `grep '.theorem("'` returns zero, and three
counts of this repository's theorems were wrong before anyone built the
environment to look. A snapshot is therefore always the output of an inventory
example, never a search.

**The load-bearing producer rule.** `provenance.exit_status` is the field every
claim's status flows through, so a producer must make its exit status depend on
the FINDING and not on completion. This repository audited 40 of 162 checker
runs exiting 0 on completion alone on 2026-08-15, including the run asserting
its headline claim. Concretely: a census tool that prints a number and exits 0
whatever the number is may supply DATA to a document and may not be the evidence
for a claim. The kernel producer applies this rule in both directions -- it
passes `--expect-count` / `--require-axiom-free` / `--expect-axioms` to the
three tools that have such flags, and it gives the fourth
(`theorem_axiom_footprint`, whose `main` returns `()`) a record with NO claims,
`outcome: inconclusive`, and a note saying why.

**Replay route.** Every run record carries `replay: Command` -- a line, a `cwd`,
an `expected_exit_status`, and a MEASURED `expected_seconds` so an expensive but
honest replay is distinguishable from a hung one. Certificate blocks carry the
same. A document's own replay is: re-run its producer, re-assemble, compare
bytes; determinism makes that a check rather than an inspection (epoch is INPUT
-- a pinned commit or `SOURCE_DATE_EPOCH` -- and no code on this path reads a
clock).

**Checker route**, in four independent layers:

1. `scripts/validate-docir.py` -- structure against the schema plus the semantic
   rules a schema cannot express (unique block ids, at least one evidence
   reference per claim, row width equals column count, unique run-record claim
   keys, `exit_status != 0` may not coexist with `outcome: established`, every
   figure has an `alt`, the file is ASCII). Its exit status depends on the
   finding, and checking zero files is exit 2, not exit 0.
2. Assembly's fail-closed rules, each carried by a test that dies when its guard
   is deleted (the table in `14-p0-exit-report.md`).
3. The canonical-JSON round trip: `axeyum_render::canonical_json` and
   `validate-docir.py --canonicalize` must agree byte for byte, which is what
   keeps the two implementations from drifting.
4. Determinism: two builds byte-identical, including the PDF, with the
   mtime-staleness attack tested explicitly.

**Compatibility.** `schema_version` is an integer, currently 1. Within a version
the schema evolves ADDITIVELY only -- new optional properties, enum members
appended. Anything that would reject a document that validated yesterday is a
version bump. `BlockKind` is a CLOSED set: a new kind lands in every emitter in
the same change or not at all, because an emitter is total and has no error path
to fall back to.

**One known honesty gap, recorded rather than left implicit.**
`assemble.rs` resolves EVERY kernel reference to `epistemic_status: proved` and
`proof_route: kernel-lean` without consulting the snapshot's `kind` column, so
an `axiom` row referenced from a `statement` block would render as proved. Until
assembly reads `kind`, the rule is: a snapshot that a `statement` block resolves
against contains theorem rows only, and the trusted surface lives in a separate
file that no statement block references. The kernel producer implements exactly
that split (`kernel-inventory.json` vs `kernel-assumptions.json`) and says so on
the page.

### (c) No Node, and the self-containment lint, as repository rules

Normative for any HTML this repository publishes, not only for `render/`:

* Implementation languages are Rust and Python. No Node runtime, no Node build
  chain, no `package.json`, no CDN script or stylesheet, no webfont fetch.
  Vendored single-file JS is acceptable only if genuinely self-contained;
  generating SVG and JS from Rust is preferred.
* Every emitted HTML page is ONE file with zero external requests, and that is
  checked by a lint with an allowlist of `#`, `data:` and `mailto:` -- and the
  lint must have a negative control that fails when an external resource is
  introduced. The lint parses attributes by NAME; the first version matched
  `href="` inside `data-href="` and reported 177 violations that were not
  violations, which is why "a second implementation" is only worth something
  when it does not repeat the first one's bug.
* This is a trust property, not a style preference: a page that phones home is
  a page whose content is not the content that was checked.

### (d) The fail-closed rendering law, repo-level

Any renderer, exporter, or report generator in this repository obeys four rules
and one split.

1. A claim block carries at least one evidence reference. No evidence is a build
   error, not a warning.
2. Evidence resolves to a recorded run. A nonzero exit status can only DEMOTE a
   claim; there is no styling path from red evidence to a green claim, and under
   strict mode it is a build error.
3. Statements of record are pulled by checked reference -- fact id or kernel
   name -- never inlined by hand. A dangling reference is a build error.
4. Determinism: identical inputs give byte-identical outputs; no wall clock,
   stable iteration order.

**The split: assembly REFUSES, an emitter REPORTS.** Everything that can fail
fails in one small resolver. An emitter is a pure, total function from a
resolved document to bytes: it never reads an exit status to choose a badge, it
cannot refuse, and a block it cannot draw renders as a loud visible box AND
appears in `Emitter::diagnostics` so a gate can fail the build. Keeping the
trusted logic in one file is what makes the law auditable; a second place that
could decide a status would be a second place a green badge could come from.

**Guard discipline.** Every new guard on this path gets the delete-one-guard
test: remove it and require that EXACTLY ONE test dies. Two guards in the P0
pass killed zero tests (the certificate-artifact digest and the include digest,
both shadowed by a third carrier), and one gate step was fully inert -- found
only because the exercise was run rather than repeated from memory. At N lanes
the ledger is the product, and a checker that cannot fail is worse than no
checker.

## Evidence

Measured 2026-08-21 on this host, first-hand, for this ADR:

* The four kernel inventory tools are DETERMINISTIC: `theorem_axiom_footprint`
  run three times gives byte-identical stdout and stderr
  (`c9f8d7d4...`/`d59b03f1...`); `nat_theorem_inventory` twice likewise. This
  was checked before any of their output was trusted.
* The kernel producer is deterministic: two full runs produce byte-identical
  output across all ten emitted files.
* Its guards fail when they should: pinning the Nat theorem count at 140
  (actual 139) and the Real trusted surface at 29 (actual 30) each make the run
  exit 1 and write nothing -- "refusing to emit: a census whose expectation
  failed is a finding, not a page".
* All three emitted documents assemble through the real fail-closed resolver
  (`axeyum-render validate`), with 139 and 57 declared inputs re-hashed and
  matched; the trusted-base page resolves 8 claims, all `[EVIDENCE]`.
* Rule 3 bites on a kernel reference, not only on a fact reference: renaming one
  theorem to a name the snapshot does not carry gives `BUILD REFUSED: dangling
  kernel reference ... (fail-closed law rule 3)`, exit 1.
* `scripts/validate-docir.py` accepts the 3 documents and 5 run records with 0
  errors and 0 warnings, in both `--kind` modes.

Standing evidence, cited rather than re-run: the P0 exit report
(`14-p0-exit-report.md`) with its eight criteria and its guard-deletion table,
and the integrate diary (`15-integrate-diary.md`) for the two inert-checker
findings that shaped rule (d).

## Alternatives

* **Promote to a workspace crate now.** Rejected: ADR-0001's boundary test is
  "proven by use", and every current user is one strand. Promotion today buys a
  member nothing imports plus five workspace obligations, and it spends the
  crate-split budget on a boundary that T1 would settle honestly within a phase.
* **Never promote; keep it a tool.** Rejected: the Doc-IR schema already lives
  in `artifacts/ontology/` next to `fact.schema.json`, is validated by a script
  in `scripts/`, and is consumed by producers in two languages. That is public
  surface whatever the Cargo manifest says, and leaving it undeclared means the
  Hard Rules contract in (b) never gets written.
* **Keep the Doc-IR internal and version only the run record.** Rejected: the
  Python producers consume the document schema directly; an internal format with
  two out-of-tree implementations is a format with no owner.
* **Inline evidence in the document instead of referencing a record file.**
  Rejected outright: the document must not be able to repair itself. The
  asymmetry -- edit the document, and the re-hash and the exit status are
  unchanged -- is the entire fail-closed guarantee.
* **Allow a Node toolchain for the HTML target.** Rejected by the owner's
  constraint, and independently by the trust argument: self-containment is
  checkable, "we only use the toolchain at build time" is not.
* **Let emitters refuse a block they cannot draw.** Rejected: a second failure
  surface that no test exercises. Report-and-let-the-gate-decide keeps the
  refusing code in one place.

## Consequences

**Easier.** A producer author now has a written contract instead of a reading of
one strand's source: semantics, the exit-status rule, the replay field, and four
checker layers. `FormalRef::Kernel` has a committed corpus, so the kernel route
is exercised rather than merely implemented. The repo-level statement of (c) and
(d) means the next exporter -- a paper build, a Pages atlas, a CI report --
inherits the law rather than reinventing a weaker version of it.

**Harder.** Additive-only evolution of `schema_version: 1` means a mistake in
the block set is expensive; the closed `BlockKind` means a new kind is a
three-emitter change. Producers that would have printed a number and exited 0
now have to earn their claims, and some upstream tools do not yet have the flags
to let them (see the wish list in `19-adr-kernel-diary.md`).

**Revisited when.** T1/T2/T3 fire -- promotion becomes a mechanical change plus
the five workspace obligations, recorded as a short follow-up ADR that
supersedes this section only. Sooner if assembly starts reading the snapshot's
`kind` column, which retires the theorem-rows-only rule in (b). The owner's
reader test may also send the whole output back, which is a design finding, not
a format finding, and does not disturb (b), (c) or (d).
