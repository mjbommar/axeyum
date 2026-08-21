# 12 -- CERT diary (render strand, round 1)

Agent CERT. 2026-08-21. Charge: `04-prototype-plan.md` P0-A steps 1-2 --
give the NoH-p2 weight certificate a `--emit-run`, produce a real run
record and a real FAILING run record, and write the P0-A assembly manifest.

Owned paths: `render/producers/`, `render/examples-input/cert/`, this file.
Nothing else was written. No git command was run.

---

## 1. What the producer is, and what it actually checks

Producer: `crates/axeyum-cas/examples/noh_wt_certificate.rs`, pinned at axeyum
`75663ef85c2dad4390a3b6d77361919a914642a9` (committer epoch `1787307950`,
`2026-08-21T06:25:50-04:00`). Compile-ready snapshot at
`/data0/axeyum/scratch/snap-claude-noh-p2-6f4e5608c` (throwaway; the shared
checkout's `crates/` was never modified).

Background read at source before writing anything:
`newton-over-hodge-char2/research-log/04-weight-proof.md` (Theorems 1-4,
Lemma A, sec. 3-5) and `20-verify.md` Part Two (the adversarial audit,
P2-1..P2-10).

The audit changes what the run record is allowed to say, and this is the single
most important thing in this diary:

- **`20-verify.md` P2-8: check `[1]`'s "INDEPENDENT route" is not independent.**
  `c_ode` iterates the same product as `c_closed` in a different association
  order, so `[1]` verifies exact rational arithmetic, not the operator `U_2`.
  The certificate's ONLY binding to `U_2` is the block of hard-coded
  ground-truth rows (13 coefficient values, `k in 3..8`, `m <= 2`).
- Consequently the record's claim `c1` carries that caveat in its `note`, the
  record's top-level `notes` repeats it, and the page states it in the
  `detail-what-is-checked` block. The words "four independent routes" appear
  nowhere in anything I wrote.
- The audit's count of "11 coefficients" is one I could not reproduce -- I count
  13 asserted coefficient values plus 2 asserted support-map values -- so the
  record says 13 and 2, which are what the assertions actually contain, and does
  not repeat the 11.

Everything else the record claims was cross-checked against the log:
`d(4..24) = 1,1,1,1,1,2,1,1,2,3,1,2,3,3,2,3,3,4,3,3,4`, `d(100) = 17`,
`d(200) = 33`, `d(400) = 67`, 150 tight Lemma-A pairs all of shape
`k = 2 mod 4, m = 1`, `c_{6,6} = 2`, `v_2(c_{6,6}) = 1`, `j'(6) + 3 = 6`. All
reproduced by the run; all match `04` sec. 4.4 / sec. 5 and `20-verify` P2-3 /
P2-4 / P2-8.

## 2. What `--emit-run` does, and why it does not weaken the certificate

`render/producers/noh_wt_certificate_emitrun.rs` (1144 lines; base is 376).
Added: argument parsing, a pure-std SHA-256 (FIPS 180-4), a deterministic JSON
writer, per-section claim records, and the data blocks. Nothing was removed,
relaxed, or made conditional. The file's header documents all of it.

Design decisions that matter for soundness:

- **A section's recorded status is the DELTA of the certificate's own `fail`
  counter across that section.** It is not a second judgement. A recorded
  `evidence` cannot disagree with the assertions that ran, because it is
  computed from them.
- **`c7` (the census guards) is the exception, deliberately.** Those guards
  (`pairs >= 400`, `vpairs >= 300`, `la >= 40000`, `cols == 397`,
  `kmax == 400`, `min d over 4..24 == 1`) are asserted INSIDE earlier sections,
  so their failures land in those sections' deltas and `c7` would have recorded
  `pass` over a violated guard -- the checker-that-cannot-fail pattern. So
  `c7`'s status is derived from the measured values against the thresholds. The
  two counts overlap rather than partition, and the claim's note says so. The
  M1 record is the proof that this matters: `c7` renders `refuted` there because
  `min d over 4..24` measured 0 against a required 1.
- **`--emit-run` without `--source` is exit 2.** A run record with no hashed
  input is not evidence.
- **A failing run writes the record and THEN exits 1.** `exit_status` is 1,
  `outcome` is `refuted`, and the failing claims are `refuted`.
- **No wall clock.** `epoch` is `SOURCE_DATE_EPOCH` when set (`source`
  `source-date-epoch`) and the pinned commit time otherwise (`source` `commit`,
  with the commit recorded). `command` normalises argv[0] to a fixed program
  name. Verified: two runs in different directories are byte-identical.
- **The `replay.line` is DERIVED from the argv the run actually received**, so
  pasting it reproduces the record byte for byte. Verified below.

Measurements, not claims:

```
$ rustfmt --edition 2024 --check render/producers/noh_wt_certificate_emitrun.rs   # clean
$ cargo clippy -p axeyum-cas --example noh_wt_certificate --all-features -- -D warnings
    Finished `dev` profile ...                                                   # clean
$ cargo run --release -q -p axeyum-cas --example noh_wt_certificate
    ... all assertions passed                                                    # unchanged with no flags
```

Mutation suite re-run against the PATCHED source (all seven mutants from
`newton-over-hodge-char2/replication/certificate/mutants/`, each required to
exit nonzero with its recorded `.expect` catcher):

```
  ok   M1-weight-loses-the-parity-term        (A3) d(5) = 0 < 1
  ok   M2-valuation-formula-off-by-one        v2 mismatch
  ok   M3-jprime-odd-branch                   U_2(t^-3) != t^-3
  ok   M4-xi-doubled-in-product-and-ode       v2 mismatch
  ok   M5-M4-with-ground-truth-deleted        v2 mismatch
  ok   M6-xi-doubled-everywhere               LEMMA A fails: v_2(c_{2,2}) = 1 < 2
  ok   M6b-M6-with-ground-truth-deleted       LEMMA A fails: v_2(c_{2,2}) = 1 < 2
mutants=7 failures=0
```

SHA-256 self-check (the implementation is hand-written, so it was checked
against the system tool rather than trusted):

```
$ sha256sum render/producers/noh_wt_certificate_emitrun.rs
1a11efcbaa49bb4626ade0dc00734ae6ecf9007df8e34a663c7e2946fc1f20e4
$ grep sha256 render/examples-input/cert/run-certificate.json
"sha256": "1a11efcbaa49bb4626ade0dc00734ae6ecf9007df8e34a663c7e2946fc1f20e4"
```

## 3. Exact commands

```sh
# baseline record (exit 0)
rustc --edition 2024 -O -o /tmp/noh_wt_cert render/producers/noh_wt_certificate_emitrun.rs \
  && /tmp/noh_wt_cert --emit-run render/examples-input/cert/run-certificate.json \
       --source render/producers/noh_wt_certificate_emitrun.rs \
       --record-id R:noh-wt-certificate --replay-seconds 1

# the M1 mutant, byte-for-byte from the paper repo's own patch
cp render/producers/noh_wt_certificate_emitrun.rs $W/noh_wt_certificate.rs
(cd $W && patch -s -p0 < $NOH/replication/certificate/mutants/M1-weight-loses-the-parity-term.patch)
# prepend the DELIBERATELY BROKEN header, save as
#   render/producers/mutants/noh_wt_certificate_emitrun_m1.rs
rustc --edition 2024 -O -o /tmp/m1cert render/producers/mutants/noh_wt_certificate_emitrun_m1.rs \
  && /tmp/m1cert --emit-run render/examples-input/cert/run-mutant-M1.json \
       --source render/producers/mutants/noh_wt_certificate_emitrun_m1.rs \
       --record-id R:noh-wt-certificate-mutant-m1 --replay-seconds 1 --notes "..."   # exits 1

# the manifest
python3 render/producers/build-certificate-manifest.py
```

Determinism / replay checks actually performed:

```
$ cmp run-certificate.json (run in a second directory)   -> identical
$ eval "$(jq -r .replay.line run-certificate.json)"      -> exit 0, file identical
$ SOURCE_DATE_EPOCH=1234567890 ...                       -> "epoch": 1234567890,
                                                            "source": "source-date-epoch"
$ /tmp/noh_wt_cert --emit-run x.json                     -> exit 2, usage error
```

## 4. Hashes of everything shipped

```
1a11efcbaa49bb4626ade0dc00734ae6ecf9007df8e34a663c7e2946fc1f20e4  render/producers/noh_wt_certificate_emitrun.rs
8a73324487257ed7a67651c29277f269d20648c4ff83b0b250e0a7f1f2a0685a  render/producers/mutants/noh_wt_certificate_emitrun_m1.rs
3cf1777911339c4575f9c2d21b3b07a09eac7bb0bf614217d8cd0417eb97e8f5  render/producers/build-certificate-manifest.py
6079f71a01225a88c302837e67c78e495df56f441754fc1682735e08ca0c344d  render/examples-input/cert/run-certificate.json
70209534ad58e6fa2f41b17316d5c69a77582c91d0bf96bdddec5e755b8cf194  render/examples-input/cert/run-mutant-M1.json
0863f2c1595513bf405ddf6fd5392159e90c759ac08ddc2c5e7af8dfd5202fe6  render/examples-input/cert/certificate.doc.json
5b4138b21834bebf742a1b681ad524c59396687a445157860a1704c8e12e925a  render/examples-input/cert/certificate-negative-control.doc.json
```

(The `.doc.json` hashes change whenever the generator or a record does; the
generator recomputes them. The two record hashes are the load-bearing ones --
`certificate.doc.json` declares them in its document provenance, which is what
binds the copied table rows to the run that produced them. See sec. 6.)

## 5. Validation against the schema

CORE's `artifacts/ontology/docir.schema.json` landed mid-session; `scripts/
validate-docir.py` and `render/check.sh` had not by the time this was written,
so validation was done with `jsonschema` directly plus CORE's own assembler.

```
$ python3 -c "... jsonschema.Draft202012Validator ..."
run-certificate.json                    errors 0   (#/$defs/RunRecord)
run-mutant-M1.json                      errors 0   (#/$defs/RunRecord)
certificate.doc.json                    errors 0   (Document)
certificate-negative-control.doc.json   errors 0   (Document)
```

Re-validated after the schema changed on disk later in the session: still 0.

End to end through CORE's assembler (built from a COPY of `render/` in scratch,
so as not to touch CORE's tree):

```
$ axeyum-render validate --manifest render/examples-input/cert/certificate.doc.json --repo-root .
document `noh-p2-weight-certificate`: 14 block(s)
4 declared input(s) re-hashed and matched
claims:
  [EVIDENCE] Theorem 3 (the closed-form weight is admissible)
  [EVIDENCE] Theorem 4 (sharpness: the bound at $k = 6$ is universal)
  [REFUTED] Control: KMU's own weight, without the parity indicator, is admissible
exit 0

$ axeyum-render validate --manifest ... --strict
BUILD REFUSED: ... rests on run record `R:noh-wt-certificate-mutant-m1`
               which exited 1 (fail-closed law rule 2)                exit 1

$ axeyum-render render --manifest ... --format md    exit 0, 2 REFUTED badges rendered
$ axeyum-render render --manifest ... --format tex   exit 0, 23425 bytes
$ axeyum-render render --manifest ... --format html  exit 2 (emitter not wired yet; DESIGN)
```

## 6. Guard probes I ran against the pipeline (findings for CORE)

Not part of my charge, but cheap and load-bearing. Each was run against a COPY.

| probe | result |
|---|---|
| corrupt a `sha256` in the document provenance | **REFUSED** -- "the evidence describes bytes that are no longer there (fail-closed law rule 4)" |
| edit a `d(k)` value inside `run-certificate.json` | **REFUSED** -- same rule; the record hash no longer matches what the document declared |
| edit a `d(k)` value in the manifest's own table rows | **NOT CAUGHT** -- renders happily with the wrong number |

The third is the one open hole, and it is structural rather than a bug in
CORE's code. `RunRecord.tables` exists, by its own description, "so a document's
table block can be built from a record rather than transcribed" -- but
`BlockTable` has no field that REFERENCES a record table. It carries `columns`,
`rows` and a `source: Provenance`, so the binding has to be done by a producer
(mine does it, in `build-certificate-manifest.py`) and assembly cannot re-check
it. What saves this document today is that it declares both run records with
their hashes in its `provenance.inputs`, so tampering with a RECORD is caught;
tampering with the MANIFEST is not.

Note this interacts with a P0 exit criterion as written: "mutate one `d(k)`
value in the run record -> the rendered table changes AND the claim flips to
red". With today's shape the mutation is refused before anything renders, which
is arguably better but is not what the criterion says. Whoever runs the
exit-criteria audit should decide which behaviour is wanted.

## 7. Open schema-fit issues for round 2

1. **`BlockTable` cannot reference `RunRecord.tables`** (and `FigurePlot.series`
   cannot reference them either). Proposal: an optional
   `from: { run_record, table, columns? }` on `BlockTable` and
   `from: { run_record, table, x, y }` on a plot series, resolved and copied by
   assembly. That moves the binding from a producer into the fail-closed layer
   and closes the row-tamper hole above. Until then, any table in any manifest
   is a transcription protected only by a document-provenance hash.
2. **`Step` content is `RichText`.** The `k = 6` derivation block necessarily
   contains numbers (`c_{6,6} = 2`, `v_2 = 1`, `j'(6) = 3`), and they are prose
   as far as assembly is concerned. My generator reads each of them out of the
   record's `stats`, so they cannot drift from the run -- but that is my
   discipline, not a checked property. Same remedy as (1): a `value_ref` on a
   step field, or an inline `{{ record.stat }}` interpolation resolved by
   assembly.
3. **A stat-level interpolation for prose/claim statements.** Claim statements
   here embed measured numbers (`397 columns`, `0 violations`). Same situation:
   generated correctly, checkable only by regenerating.
4. **`RunRecord` has no `variant`/`kind` discriminator.** I wanted to mark
   `run-mutant-M1.json` as a deliberate mutant in a machine-readable way and had
   to put it in `notes` and in the `id`. A `role: production | negative-control |
   fixture` would let a checker refuse to cite a negative control as support.
5. **`FigurePlot` was fine.** It needed no escape hatch: `series/points` took the
   `a(k)` and `d(k)` data directly. No `data` blob was needed, contrary to my
   brief's contingency.
6. **`--strict` and pages that legitimately carry a refutation.** A page that
   reports a negative control cannot be strict-rendered. That is correct as a
   rule but means "strict-clean" is not a property of every good document. I
   shipped `certificate-negative-control.doc.json` so the strict-mode test does
   not need the whole page; the coordinator may prefer to drop the control block
   from the production page instead.

## 8. What is NOT claimed

- The run record does not say the certificate proves Theorems 3 or 4. Each claim
  is `evidence` -- "a finite computation, carrying no universal credit" -- and
  each note points at the written proof in `04-weight-proof.md` and its audit.
- The record does not assert `gamma <= 1/6`. The certificate computes two facts
  (`j'(6) + 3 = 6`, `v_2(c_{6,6}) = 1`); the one-line consequence is attributed
  to `04-weight-proof.md` sec. 5 in the claim note.
- `d(k)` is the minimum over the support the certificate COMPUTES (`m <= 250`,
  `4 <= k <= 400`), not over an infinite support. The tail is Lemma A's job, and
  the claim says so.
- Nothing here touches `20-verify.md`'s one substantive gap (P0-12, the Lemma E
  coverage claim). It is outside the certificate and outside this page.
