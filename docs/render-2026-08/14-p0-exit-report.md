# 14 -- P0 exit-criteria report

Agent INTEGRATE, render strand round 2, 2026-08-21. Every row below is a
command that was run and its result, not a judgement about the code. Where a
criterion was ADJUSTED, the adjustment and its reason are stated in the row and
argued in `15-integrate-diary.md`; `04-prototype-plan.md` carries a dated note
pointing here.

Host: the gate-capable one (`pdflatex`, `chromium-browser`, `python3` with
`jsonschema` 4.19.2 all present). `cargo` is nightly-default; the package
builds on the pinned MSRV path unchanged.

## Summary

| # | criterion (04-prototype-plan.md) | result |
|---|---|---|
| 1 | three P0-A outputs from one IR; (claim, status) set identical across formats | **PASS** |
| 2 | LaTeX compiles standalone; HTML passes the self-containment lint | **PASS** |
| 3 | fail-closed (1): claim without evidence is a build error | **PASS** |
| 4 | fail-closed (2): `exit_status: 1` renders REFUTED, and strict mode errors | **PASS** |
| 5 | fail-closed (3): dangling fact reference is a build error | **PASS** |
| 6 | fail-closed (4): input-hash mismatch is a build error | **PASS** |
| 7 | determinism: two builds byte-identical; the mtime attack cannot stale a render | **PASS** |
| 8 | negative control on the pipeline: mutate one `d(k)` -> table changes and the claim flips red | **ADJUSTED (PASS)** |
| -- | reader test: the owner reads `certificate.html` cold | **OUTSTANDING** (not an agent's to run) |

Gate: `./render/check.sh` -> **15 passed, 0 failed** (10 steps; steps 3, 5, 8
and 9 report more than one result each). Suite: **126 tests**, all green,
across nine binaries.

## 1. Three outputs from one IR, identical claim sets

```
$ ./render/build-p0-outputs.sh
build-p0-outputs: wrote render/out           # 10 files, listed in section 9
$ cargo test --manifest-path render/Cargo.toml --all-features --test cross_format
running 6 tests ... test result: ok. 6 passed
```

The property is recovered FROM THE EMITTED BYTES in all three formats
(`**Claim -- L** [BADGE]`, `\axclaim{L}{BADGE}`, `data-claim="L"
data-status="BADGE"`), compared as ordered sets, and cross-checked against
`ResolvedDocument::claims`. Round 1 had the Markdown and LaTeX halves; round 2
added the HTML parser and two more tests:

* `all_three_formats_report_the_same_claims_and_statuses` -- the fixture;
* `the_committed_p0_manifests_agree_across_all_three_formats` -- the REAL
  corpus (certificate, negative control, fact pilot), because a property that
  holds only on the fixture is a property about the fixture.

The anti-vacuity control was extended to the third parser in both directions:
each parser must find NOTHING in the other two formats' bytes.

`render/check.sh` additionally asserts by NAME that these tests ran, because
`#[cfg(feature = "html")]` code compiles to nothing without the feature and the
total count would stay healthy anyway. The `html` feature is now ON BY DEFAULT
(`render/Cargo.toml`).

## 2. LaTeX compiles; HTML is self-contained

```
$ ./render/check.sh    # step 10
      fixture-fact-ledger -> 174158 byte PDF
      noh-p2-weight-certificate -> 265950 byte PDF
PASS  LaTeX compiles (2 standalone documents)
$ ./render/check.sh    # step 9
self-containment: 4 page(s), 4 resource reference(s), 0 finding(s)
PASS  self-containment (grep gate over the emitted HTML)
PASS  the self-containment gate rejects an external resource (negative control)
```

Step 9 is a SECOND implementation of the lint `emit_html.rs` runs in Rust,
written the way 04 specifies it (grep every resource attribute against an
allowlist of `#`, `data:`, `mailto:`), which is the same two-implementation
discipline the Doc-IR schema gets. Its first version repeated the exact bug
DESIGN documented in the Rust lint -- `\bhref="` also matches the tail of
`data-href="` -- and reported 177 violations that were not violations. Fixed by
parsing attributes by NAME; the finding is in the diary.

The deliverable PDF is built with `SOURCE_DATE_EPOCH` + `FORCE_SOURCE_DATE`
from the document's own epoch, so it is byte-reproducible (section 7).

## 3-6. The fail-closed law, by delete-one-guard

The mutation harness deletes one guard from a COPY of the package
(`/data0/axeyum/scratch/render-mutation-integrate`, a faithful miniature repo:
`render/` copied, `artifacts/` and `scripts/` symlinked) and re-runs the whole
suite with `--no-fail-fast`. Measured 2026-08-21, after every round-2 change:

| guard deleted | tests that died |
|---|---|
| `evidence.is_empty()` in `resolve_claim` | 1 -- `claim_without_evidence_is_a_build_error` |
| `map_err(|_| DanglingFactRef)` on the ledger read | **0** -- CORE's published zero row, still zero |
| `fact.id != *id` in `resolve_formal_ref` | 1 -- `a_fact_file_whose_id_disagrees_with_the_reference_is_a_build_error` |
| `actual != input.sha256` in `verify_inputs` | 2 -- `input_hash_mismatch_is_a_build_error`, `stale_mtimes_cannot_produce_a_stale_render` |
| `&actual != want` in `verify_artifact` | 1 -- `a_certificate_artifact_whose_declared_digest_is_stale_is_a_build_error` (**0** before round 2) |
| the `sha256` comparison in the `Include` arm | 1 -- `an_include_block_whose_declared_digest_is_stale_is_a_build_error` (**0** before round 2) |
| ALL THREE rule-4 comparisons together | 3 -- the two above plus `editing_a_measurement_inside_the_run_record_is_refused` |
| `e.exit_status != 0` in `rendered_status` | 2 -- one unit, one integration |
| the `strict` block in `resolve_claim` | 1 -- `nonzero_exit_status_is_an_error_in_strict_mode` |
| `is_control && declared != NegativeControl` (round 2) | 1 -- `a_negative_control_record_cannot_be_cited_as_support` |
| `!is_control && declared == NegativeControl` (round 2) | 1 -- `the_negative_control_role_cannot_be_declared_over_a_production_run` |
| the `<merror>` scan in `emit_with_diagnostics` (round 2) | 1 -- `untranslatable_math_produces_a_diagnostic_as_well_as_a_box` |
| the prime arm in `latex_to_mathml` (round 2) | 1 -- `a_prime_is_an_operator_not_an_unknown_token` |
| `a.fail_on_diagnostics && !diagnostics.is_empty()` in `main.rs` (round 2) | `render/check.sh` step 8 FAILS (no cargo test covers the CLI) |

So criteria 3, 4, 5 and 6 each hold and each is carried by a test that dies
when its guard is removed. Two findings inside this exercise are the reason it
was worth running rather than repeating:

* **Rule 4 turned out to have three carriers, two of them untested.** The
  certificate document pins its run record in three independent places
  (document `provenance.inputs`, the certificate block's `artifact_refs`, and
  the archive `include`'s `sha256`), and any one of them catches a tamper. So
  deleting `verify_artifact`'s comparison, or the include comparison, killed
  ZERO tests -- the shape CLAUDE.md's "six of seven guards were removable"
  incident turns on. Two new tests in `render/tests/negative.rs` now tie one
  test to each carrier, after which every one of the three kills exactly one.
* **The gate step for emitter diagnostics was inert when it was written.** Its
  negative control handed the renderer a figure with no SVG, which ASSEMBLY
  refuses -- so the command exited 1 without the emitter running, and the
  control passed whether or not `--fail-on-diagnostics` did anything. Verified
  by deleting the flag's refusal: the whole step stayed green. The control now
  uses a document that assembles cleanly and is undrawable only to the emitter
  (a formula outside the LaTeX subset), and it runs the same document twice --
  without the flag it must SUCCEED, with the flag it must be REFUSED. Deleting
  the refusal now fails the step.

The independent Python validator carries the same negative-control rules
(two-implementation discipline), and they were exercised, not assumed:

```
$ python3 scripts/validate-docir.py <control cited as `primary`>          exit 1
$ python3 scripts/validate-docir.py <`negative-control` over a real run>  exit 1
$ python3 scripts/validate-docir.py <a control record that exited 0>      exit 1
$ python3 scripts/validate-docir.py <the committed originals>             exit 0
```

## 7. Determinism

```
$ cargo test --manifest-path render/Cargo.toml --all-features --test determinism
running 3 tests ... ok    # two builds byte-identical; epoch from the manifest; the mtime attack
$ ./render/build-p0-outputs.sh && cp -r render/out A && ./render/build-p0-outputs.sh
$ diff -r A render/out
        # no output: all ten deliverables, PDF included, byte-identical
```

The mtime attack is the repository's own cargo trap and it bit this very
report's mutation harness: the first run reported five baseline failures
because `rsync -a` preserved source mtimes older than the copy's `target/`, so
cargo tested a stale library. The harness now touches every `.rs` before each
run, and the numbers in section 3-6 are from after that fix.

## 8. Negative control on the pipeline -- ADJUSTED

**As written the criterion cannot happen on this system, and the reason is that
the system got stronger than the criterion.** It says:

> mutate one `d(k)` value in the run record -> the rendered table changes AND
> the claim whose bound it violates flips to red.

Two things landed between the criterion being written and the pipeline
existing. (a) The document declares the run record's SHA-256 and assembly
re-hashes it every build, so editing a `d(k)` inside the record is REFUSED
before anything renders. (b) The `d(k)` table is now `from_run` -- a reference
into the record rather than a copy of its rows -- so there is no second place
where the number could disagree with itself.

The honest behaviour is two behaviours, and `render/tests/pipeline_negative_control.rs`
tests both against CERT's real records:

* `editing_a_measurement_inside_the_run_record_is_refused` -- one cell of one
  row (`d(5) := 0`) inside a staged copy of `run-certificate.json`; the build
  refuses with `HashMismatch`. Nothing renders, which is strictly stronger than
  rendering it in red.
* `a_record_from_a_mutated_run_changes_the_table_and_flips_the_claim` -- point
  the table and the admissibility claim at `run-mutant-M1.json`, a REAL record
  of a REAL run of the M1 mutant (the paper repository's own
  `M1-weight-loses-the-parity-term.patch`, applied verbatim). The rendered
  `d(5)` becomes `0`, the Theorem 3 claim flips `EVIDENCE -> REFUTED` in all
  formats, and Theorem 4 -- which does not rest on the violated bound -- keeps
  its status. No number is written into the document by the test.

The second half is what the criterion was after: a changed measurement changes
the rendered table and flips the claim, with no edit to the document. The first
half is the guard the criterion did not anticipate.

## 9. The deliverables

`render/out/` is generated by `render/build-p0-outputs.sh` and is not edited by
hand. Sizes and digests as built 2026-08-21:

| file | bytes | sha256 (first 16) |
|---|---:|---|
| `certificate.md` | 30666 | `880cb8df7732f5c3` |
| `certificate.tex` | 31308 | `8200db34c17000d3` |
| `certificate-standalone.tex` | 279 | `5a8c836ba11fcd94` |
| `axeyum.sty` | 2131 | `8ba26fc45b4803d7` |
| `certificate.pdf` | 265939 | `cd7e8599db186ec7` |
| `certificate.html` | 126382 | `89be4a6b25f32b89` |
| `facts-pilot.html` | 49884 | `bcdd2340256ae012` |
| `facts-pilot-arith.html` | 58010 | `ad7c64ed21ff2715` |
| `facts-atlas.html` | 349640 | `a911e01ff5426354` |
| `facts.md` | 177101 | `4c2a352968c2c200` |

1.1 MB total. Every page is a single file with zero external requests.
