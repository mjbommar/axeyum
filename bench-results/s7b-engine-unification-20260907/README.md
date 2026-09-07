# S7b — the difference-logic route moves onto the native core, 2026-09-07

Backing data for
[`docs/plan/status/s7b-engine-unification.md`](../../docs/plan/status/s7b-engine-unification.md).
Read that file for what the change was and what these numbers do and do not
establish; this one only maps the artifacts and pins the method.

| file | rows | what it is |
|---|---:|---|
| `qf_idl_before_after.tsv` | 50 | `file, declared, before_verdict, before_ms, after_verdict, after_ms` over the population in `../adr-1701-slice-1-20260905/qf_idl_population.tsv` |
| `qf_lra_before_after.tsv` | 33 | the same columns over `../adr-1701-slice-1-20260905/qf_lra_population.tsv` |
| `run-populations.sh` | — | the harness, exactly as run on s5 |
| `summarize.py` | — | the analyser, whose exit status depends on the finding |

## Method

Host **s5**, idle (load average `0.00` immediately before the run; nothing else
on the box for its duration). `taskset -c 0-7`, `--timeout-ms 24000` inside a
`timeout -k 2 30s` external hard-kill backstop. **Arms interleaved per file** —
before, after, next file — so a drift in machine throughput moves both arms
together.

- **BEFORE** = `fcc988900`, the `main` commit this lane branched from, extracted
  with `tar --touch` into a private tree. `sha256=7c5f5329626f8b7f…`
- **AFTER** = this lane at `f429b3b8a`, same extraction.
  `sha256=43060a5e57ecd37c…`

Both binaries `cargo build --release -p axeyum-bench --example smtcomp_cli`
through `scripts/cargo-serialized.sh`; the digests above are the check that they
differ.

The AFTER binary predates two later changes on this branch, neither of which can
move these numbers:

- the merge of local `main` (`7357d0576`), which touched `auto.rs`,
  `evidence.rs` and `nia_linearize.rs`; the merged tree's solver sweep is green
  (1,475 tests);
- a guard in `native_cdclt`'s `propagate_into` that skips a propagation for an
  atom the driver has no variable for, matching what
  `CdclT::theory_propagate` already did. It **cannot fire on this route**:
  `DlTheory` keeps the `take_new_atoms` default of `0`, so the atom↔variable map
  never grows, and it only ever propagates atoms in `0..self.atoms.len()`.

So these are `f429b3b8a`'s numbers, and for the difference-logic route
`f429b3b8a` and the branch head decide identically.

## Two things about the timing column

`ms` is **wall time of the whole process**, measured outside it, so it includes
parse, dispatch and teardown — not the solver's own elapsed figure. It is
comparable between arms (identical harness) and is *not* comparable with the
`axeyum_ms` column of the population TSVs, which the 2026-08-21 diagnosis
measured differently.

`date +%s%3N` is **not honoured on this host** — it yields nine digits, i.e.
nanoseconds. The first attempt at this run recorded 1,213,398,102 "ms" for a
1.2 s solve. The harness reads `%s%N` and divides. Anyone reusing it should
check the same thing rather than assume the format works.

## Reading it

`summarize.py` (here, beside its data) produced the counts in the lane doc, and
its **exit status depends on the finding** — a verdict contradicting the
file's declared `:status`, or a file decided in the BEFORE arm and undecided in
the AFTER arm, is a nonzero exit. It was run against a synthetic two-row file
carrying one of each defect and exited 1, so it is a live check and not a
decoration.
