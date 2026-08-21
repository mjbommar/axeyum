# 10 -- CORE lane diary (render strand, round 1)

Agent: CORE. Opened 2026-08-21. Owns `render/` core (ir, assemble, emit_md,
emit_tex, main, lib, tests, check.sh), `artifacts/ontology/docir.schema.json`,
`scripts/validate-docir.py`.

## Schema landing (the thing three other lanes are blocked on)

- **2026-08-21 12:05Z** -- render/ directory created, work started.
- **2026-08-21 12:10Z** -- `artifacts/ontology/docir.schema.json` LANDED on
  disk, self-validating (`Draft202012Validator.check_schema`) plus a smoke
  document. 30 `$defs`. From here it evolves ADDITIVELY only for the rest of
  the round: new optional properties and appended enum members are fine,
  anything that would reject a document that validated at 12:10Z is a
  `schema_version` bump and a message to every lane.
- One correction after first write, before anyone could have consumed it:
  `Cell` was spelled as a `oneOf` over `string | number | integer | boolean |
  null`. An integer satisfies BOTH `number` and `integer`, so `oneOf` (exactly
  one) rejects every whole number -- i.e. the schema would have rejected
  essentially every real table in this repository. It is a type union now, and
  the reason is written into the schema so it does not come back.

## What the schema decides that 03-architecture.md left open

03 sketches the IR; these are the choices made turning the sketch into data,
recorded because downstream lanes build against them:

1. **`BlockKind` is internally tagged on `type`** (`prose`, `claim`,
   `statement`, `steps`, `table`, `certificate`, `figure`, `include`), each
   variant `additionalProperties: false`. That makes the `oneOf` a real
   discriminated union that a hand-written manifest cannot accidentally satisfy
   two ways.
2. **`RunRecord` lives in the SAME file**, under `$defs/RunRecord`, not in a
   separate schema. 03 says "EvidenceRef -> a run record (JSON file) carrying
   its own Provenance" and leaves the record undefined -- but CERT is writing
   producers against it this round, so it had to exist by 12:10Z too. It shares
   `Provenance`, `Cell`, `ArtifactRef`, `Command`, `FormalRef` and
   `EvidenceStatus` with the document, which is the point: one vocabulary.
   Validate a record with `scripts/validate-docir.py --kind run-record`.
3. **`outcome` on a run record is separate from `provenance.exit_status`.**
   Exit status says whether the run COMPLETED; outcome says what it FOUND.
   Assembly needs both: a nonzero exit demotes a claim, and `outcome` chooses
   between demoting to `refuted` (the run found a counterexample) and `open`
   (the run did not settle it). Collapsing them is precisely the
   "checker that cannot fail" shape -- exit 0 on completion alone -- that the
   audit on 2026-08-15 found in 40 of 162 runs, so they are two fields.
4. **`Epoch` is a struct with a declared `source`**, not a bare integer, so a
   fixture constant (`fixed`) is distinguishable from a commit time
   (`commit`) without diffing two builds. No emitter or assembly path is
   allowed to read a clock.
5. **`RichText` is an object with optional `latex` / `html` overrides**, not a
   bare string. Mechanical CommonMark->LaTeX conversion is right for the common
   case and wrong for the interesting one; the override is typographic only and
   cannot introduce a claim, because claims are not prose. `prose.text` accepts
   the bare-string shorthand since that is the one field humans hand-write.
6. **A claim's declared `status` is a CEILING, not a result.** Assembly
   computes the rendered status and may only lower it. This is written into
   the schema description so a producer author reads it there.
7. **`table.source` is REQUIRED provenance.** A table with no command that
   produced it is a transcription, which is the drift class this strand exists
   to kill.
8. **`statement` blocks have no `text` property at all.** There is no fallback
   to inlined prose; if the reference does not resolve, the build fails. That
   is Isabelle antiquotation semantics and it is enforced by the absence of a
   field, not by a lint.
9. `FormalRef.kernel` carries an `inventory` path. Kernel declarations are not
   readable from source text (the `.theorem(name, ...)` helper over interned
   name ids -- three counts of this repository's theorems were wrong before
   anyone built the environment to look), so a kernel ref resolves against an
   inventory snapshot or it is not a checked reference.

## Dependency justification (`render/Cargo.toml`)

Standalone package, NOT in the root workspace `members` (03 says so; root
`Cargo.toml` untouched). It carries its own lockfile.

- `serde` + `serde_derive` (`features = ["derive"]`) -- the IR must round-trip
  JSON, and the schema is the interchange format with the Python producers.
  Hand-rolling the derive for 30 `$defs` would be the actual risk.
- `serde_json` -- reading manifests, run records and fact-ledger entries, and
  emitting canonical JSON for the round-trip test. Its `preserve_order` feature
  is deliberately NOT enabled: the round-trip test wants the canonical
  (BTreeMap-sorted) form, which is what determinism means here.
- `sha2` -- pure-Rust SHA-256 for input-hash verification. It is the hash the
  schema already commits to and the one `sha256sum` prints, so a reader can
  check by hand. Pure Rust, no C dependency (repo Hard Rule).
- **`pulldown-cmark`: NOT taken.** It would be needed to parse CommonMark into
  an AST, and no emitter here does that. The Markdown emitter passes prose
  through verbatim (it is already CommonMark) and the LaTeX emitter needs only
  a small, auditable escaper over TeX metacharacters with `$...$` math spans
  preserved -- about 60 lines, fully under test, versus a parser whose
  behaviour on the interesting cases we would have to test anyway. If a real
  MD->TeX conversion is ever needed the dependency comes back with a note here.

No other dependencies. Zero C/C++ in the graph.

## Assembly: the fail-closed rules, and the MEASURED mutation results

Delete-one-guard discipline, run for real on 2026-08-21. The mutation script
deleted each guard in `render/src/assemble.rs` in turn and re-ran the whole
suite; the file `render/tests/negative.rs` carries the same table in its header.

| guard deleted | tests that died |
|---|---|
| `evidence.is_empty()` in `resolve_claim` | 1 -- `claim_without_evidence_is_a_build_error` |
| `map_err(|_| DanglingFactRef)` on the ledger read | **0** |
| `fact.id != *id` in `resolve_formal_ref` | 1 -- `a_fact_file_whose_id_disagrees_with_the_reference_is_a_build_error` |
| both dangling-ref guards together | 2 |
| `actual != input.sha256` in `verify_inputs` | 2 -- `input_hash_mismatch_is_a_build_error`, `stale_mtimes_cannot_produce_a_stale_render` |
| `e.exit_status != 0` in `rendered_status` | 2 -- one unit, one integration |
| the `strict` block in `resolve_claim` | 1 -- `nonzero_exit_status_is_an_error_in_strict_mode` |

Three things this exercise actually caught, none of which I would have known
otherwise:

1. **The first run reported three numbers too low.** `cargo test` STOPS after
   the first failing test binary, so a mutation that killed a test in
   `determinism` was reported as killing nothing in `negative`. Every count
   above is from `--no-fail-fast`. A mutation harness without that flag
   systematically under-reports, which is the worst possible direction for this
   particular exercise -- it makes guards look load-bearing when they are not.
2. **A guard that killed zero tests.** The dangling-fact-ref property had two
   guards (file missing; file present but declaring a different id) and only one
   test, aimed at the first. Deleting the first alone changed nothing, because
   removing that refusal means inventing ledger content and any invented content
   fails the second. So rule 3 is carried by the ID COMPARISON, and the
   missing-file arm only improves the error message. Fixed by adding the missing
   test (`a_fact_file_whose_id_disagrees_with_the_reference_is_a_build_error`),
   after which deleting either guard kills exactly one test and deleting both
   kills two. The zero row is left in the published table rather than tidied
   away: it is the finding.
3. **A test that could pass over a dead guard.** The demotion test originally
   used `exit_status: 1` with `outcome: inconclusive`, so deleting the
   exit-status branch still demoted (via the outcome branch) and the test passed.
   It now uses `exit_status: 1` with `outcome: established` -- the shape of a
   checker that reports success because it finished -- which only the
   exit-status guard catches.

The rows that killed two tests are two LEVELS of one property (a unit test and
an integration test), not two properties routed through one shared check. That
distinction is the one CLAUDE.md's "six of seven guards were removable" incident
turns on, and it is why the table lists which tests, not just how many.

## Test inventory (39 assertions, all green)

| file | n | what it holds down |
|---|---|---|
| `src/assemble.rs` (unit) | 5 | status algebra: green evidence never raises; red is absorbing; nonzero exit without a counterexample renders `open` not `refuted`; fact-id to filename; SHA-256 against a known digest |
| `src/emit_md.rs` (unit) | 1 | the clock-free ISO-8601 conversion, against three instants cross-checked with `date -u` |
| `src/emit_tex.rs` (unit) | 4 | the CommonMark-to-TeX scanner: escaping outside math, math passthrough, code/bold macros, and that an unterminated delimiter loses no text |
| `tests/negative.rs` | 12 | the fail-closed law (table above) plus the ceiling property in both directions |
| `tests/golden.rs` | 5 | byte-exact md/tex/sty/wrapper; ASCII; verbosity tiers honoured in md; LaTeX appendix mode |
| `tests/determinism.rs` | 3 | two builds byte-identical; the epoch comes from the manifest, not the machine; the mtime attack |
| `tests/cross_format.rs` | 4 | md and tex report the same (label, status) set, recovered FROM THE BYTES; a demotion moves both together; the recovery parsers are not vacuous |
| `tests/schema.rs` | 5 | Rust->Python round-trip for document and record; the committed fixtures validate; the Python validator can fail; it refuses an empty check |

Two controls worth naming, because they are what stops the suite from being
decorative: `the_recovery_parsers_are_not_vacuous` feeds each cross-format
parser the OTHER format's output and requires zero matches (a parser that
matched everything would make the property trivially true), and
`the_committed_fixture_assembles_and_every_claim_is_checked` fails loudly if the
fixture ever stops assembling -- without it, every negative test would pass for
the wrong reason.

## The fixture is real, and what that costs

Two committed fact-ledger entries: `F:bool-and-comm` (proved,
`imported-kernel-lean`, 3-entry axiom footprint) and `F:excluded-middle`
(proved, `smt-term-level`, 2-entry footprint). Deliberately different routes, so
the document renders the distinction the fact schema exists to protect.

The evidence is `render/tests/fixtures/run-fact-ledger-check.json`, written by
`render/tests/fixtures/make_run_record.py`, which really validates both entries
against `artifacts/ontology/fact.schema.json` and really reads what they record.
Its exit status depends on the FINDINGS, not on completion, and it writes the
record either way -- a failed run produces `exit_status: 1` and
`outcome: refuted` so a consumer sees red evidence rather than a missing file.

**Scope discipline was the hard part of the fixture.** The run checked the
LEDGER'S RECORD of two facts; it did not check the mathematics. So the claims
say exactly that, and the mathematical statements appear as `statement` blocks
carrying the ledger's own status axes -- data pulled by reference, not a claim
the document makes. Letting the document say "Boolean conjunction is commutative
[CHECKED]" on the strength of a JSON validation would have been precisely the
lie this pipeline exists to prevent, in the pipeline's own test fixture.

The cost is real and accepted: the golden files are coupled to two entries of a
ledger that other lanes edit. If either changes, `render/check.sh` step 6 fails
with instructions rather than the goldens silently drifting. That coupling is
the feature.

## One schema change after landing, additive

`BlockTable` gained an optional `from_run` (naming a run record and one of its
`tables`), and `columns`/`rows`/`source` became optional under an `anyOf`.
Motive: the hand-written manifest was about to TRANSCRIBE the run's table into
the document -- reintroducing, in the fixture, the exact drift the strand
exists to kill. With `from_run` the numbers exist in one place and a changed
measurement changes the rendered table. Making required fields optional and
adding a property are both backward-compatible: every document that validated at
12:10Z still validates.

## `render/check.sh`: 9 passed, 0 failed (measured 2026-08-21)

Steps: formatting, clippy `-D warnings`, the full test suite, the Python
validator on the fixtures, a NEGATIVE control proving that validator can fail,
a freshness check that re-runs the fixture producer and diffs, ASCII, and an
optional LaTeX compile. Three deliberate choices:

- **The test count is asserted nonzero** (>= 30). "running 0 tests ... ok" is
  this repository's signature inert gate.
- **The LaTeX step prints `SKIP`, never `PASS`, when there is no `pdflatex`.**
  A step that counts as green on a host that cannot run it is how a gate stops
  meaning anything -- `lean` and `just` existed on one fleet host of five.
- **Formatting is PARTITIONED by ownership rather than scoped.** `rustfmt` on a
  file list follows `mod` declarations out of `lib.rs` into files this lane does
  not own (it reported ten diffs in DESIGN's `emit_html.rs`, and in non-check
  mode it would have REWRITTEN them -- a cross-lane clobber in a gate).
  `--skip-children` is nightly-only. So the whole package is checked and the
  results are split: a diff in an owned file fails, a diff elsewhere is a note.
  Nothing is skipped silently.

Verified the gate can fail, twice: a one-word edit to a golden gives exit 1, and
a tampered digest in the run record fails two independent steps (tests, and the
freshness re-run).

LaTeX: `pdflatex` on the emitted standalone wrapper exits 0 and produces a
174,158-byte PDF, so the `axeyum.sty` macros are not merely plausible.

## For DESIGN: the Emitter contract

Full text is the module documentation in `render/src/lib.rs`. `emit_html.rs`
and `layout.rs` are declared behind an off-by-default `html` cargo feature so
this package builds before they exist; round 2 turns it on.

## Open items handed to round 2

- Wire the `html` feature on by default; add `--all-features` to check.sh
  step 2 and fold DESIGN's files into the formatting partition.
- The HTML emitter joins `tests/cross_format.rs` (contract point 5).
- `FigureSpec::Plot`/`DepGraph`/`Polygon` render as data listings in md and tex
  because no layout engine lives in those emitters -- honest and total, but
  DESIGN's `layout.rs` is what makes them pictures.
- A kernel-inventory snapshot for `FormalRef::Kernel`. The resolver is written
  and refuses a reference with no inventory to check against, but no snapshot
  file exists yet, so that path is unexercised by the fixture.
