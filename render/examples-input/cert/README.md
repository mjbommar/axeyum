# P0-A input set: the NoH-p2 tame-point weight certificate

Owner: render strand agent CERT, round 1 (2026-08-21).
Task: `docs/render-2026-08/04-prototype-plan.md`, P0-A steps 1-2.
Diary, with every command and hash: `docs/render-2026-08/12-cert-diary.md`.

Everything here is REAL: each JSON file was written by a program that ran, and
nothing in it was typed or edited afterwards. That includes the failing one.

## Files

| file | what it is |
|---|---|
| `run-certificate.json` | Run record of the certificate. `exit_status` 0, outcome `established`, 7 claims, 60 stats, 4 tables (the 397-row `d-table`, the weight series, the 150 tight Lemma-A pairs, the ground-truth coefficient rows). Validates against `docir.schema.json#/$defs/RunRecord`. |
| `run-mutant-M1.json` | The deliberately-failing record, for negative tests. Produced by applying `newton-over-hodge-char2/replication/certificate/mutants/M1-weight-loses-the-parity-term.patch` to the producer and RUNNING it -- the exit status 1, the outcome `refuted`, the `refuted` status on claims `c5`/`c7` and the `d = 0` row at `k = 5` are all measured, not written. |
| `certificate.doc.json` | The P0-A assembly manifest: the certificate page as Doc-IR. 14 blocks; prose hand-written, every number resolved from `run-certificate.json`. |
| `certificate-negative-control.doc.json` | The smallest document that exercises fail-closed rule 2: one prose block and the M1 claim. Renders with a REFUTED badge; `--strict` refuses it. |

## Producers

- `render/producers/noh_wt_certificate_emitrun.rs` -- the certificate plus
  `--emit-run`. Base pin axeyum `75663ef8`; see its header for exactly what was
  added and why none of it weakens the checks.
- `render/producers/mutants/noh_wt_certificate_emitrun_m1.rs` -- DELIBERATELY
  BROKEN. Checked in only so that `run-mutant-M1.json` has a hashable input and
  is reproducible; nothing else should build it.
- `render/producers/build-certificate-manifest.py` -- assembles
  `certificate.doc.json` from `run-certificate.json`. Prose lives in this
  script; numbers are read out of the record.

## Reproduce

```sh
# from the repository root
rustc --edition 2024 -O -o /tmp/noh_wt_cert render/producers/noh_wt_certificate_emitrun.rs \
  && /tmp/noh_wt_cert --emit-run render/examples-input/cert/run-certificate.json \
       --source render/producers/noh_wt_certificate_emitrun.rs \
       --record-id R:noh-wt-certificate --replay-seconds 1          # exits 0

rustc --edition 2024 -O -o /tmp/noh_wt_cert_m1 render/producers/mutants/noh_wt_certificate_emitrun_m1.rs \
  && /tmp/noh_wt_cert_m1 --emit-run render/examples-input/cert/run-mutant-M1.json \
       --source render/producers/mutants/noh_wt_certificate_emitrun_m1.rs \
       --record-id R:noh-wt-certificate-mutant-m1 --replay-seconds 1 \
       --notes "<the note recorded in the file>"                     # exits 1

python3 render/producers/build-certificate-manifest.py
```

Each record's own `replay.line` is the first two commands, derived from the
arguments the run actually received; both reproduce their file byte for byte.

## Two things to know before using these

1. **`certificate.doc.json` is refused by `--strict`, on purpose.** It carries
   the M1 negative control, whose evidence is red by construction, and strict
   mode makes red evidence a build error (fail-closed rule 2). Render the page
   without `--strict`, where the control renders as a REFUTED badge, or drop the
   `claim-negative-control-m1` block (it is already `detail`-tier) for a
   strict-clean production page. `certificate-negative-control.doc.json` exists
   so the strict-mode test does not need the whole page.
2. **The certificate's binding to the operator is narrower than its output
   suggests.** Its check `[1]` compares two routes that are NOT independent
   (`20-verify.md` P2-8). The only binding to `U_2` is claim `c2`, the
   hard-coded coefficient rows. This is recorded in the run record's `notes` and
   in claim `c1`'s note, and is stated on the page in the
   `detail-what-is-checked` block. Do not restate the "four independent routes"
   wording anywhere.
