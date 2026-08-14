# agent-g DIARY — DRAT checking memory

Append-only. Includes what broke.

Lane: `crates/axeyum-cnf/` (owned). Build snapshot: `~/.cache/axeyum-agent-g/snap`
from `git archive HEAD` at `75c5e4544749b7ccc2b99780b969b39a43083b8e`.
Test data: `~/.cache/axeyum-agent-g/data`, decompressed from the committed
ledger certificates. **Not `/tmp`** — it is a 62 GiB tmpfs and this lane's whole
subject is resident memory.

---

## 2026-08-13 22:39 — setup, and the first thing that surprised me

Read the brief, `README.md`, `ACTION-ITEMS.md`, agent-c's `FEEDBACK.md`
(F-C3, F-C7, F-C10).

Snapshot built clean in 5.9 s. `/tmp` was at 63% (39 GiB of 62 GiB tmpfs) when I
started, which is 39 GiB of this machine's 123 GiB of RAM already spent before
anything of mine runs. `free -g` says 72 GiB available; `df -h /tmp` says 24 GiB
"disk" free. Neither number alone is the one that matters, which is the
campaign's own process finding and I hit it in the first five minutes.

## 2026-08-13 22:41 — baseline measured, on four real certificates

Wrote `crates/axeyum-cnf/examples/drat_memory_probe.rs` (scratch, in the
snapshot only) that reads `VmHWM` from `/proc/self/status` around
`parse_drat` + `check_drat_backward`. Decompressed the four largest committed
DRAT certificates.

| certificate | text DRAT | steps | peak RSS | RSS / DRAT | seconds |
|---|---:|---:|---:|---:|---:|
| `rado-r4-a3-b1/F_81` | 8,862,657 | 164,538 | 88,416,256 | **9.98x** | 0.80 |
| `rado-r4-a3-b2/F_103` | 74,818,033 | 1,202,198 | 608,473,088 | **8.13x** | 6.83 |
| `rado-r4-a1-b2/F_171` | 131,197,778 | 2,010,887 | 1,112,662,016 | **8.48x** | 18.64 |
| `rado-r4-a4-b1/F_256` | 166,982,506 | 2,555,413 | 1,335,078,912 | **8.00x** | 23.60 |

So agent-c's 6.6x is not a one-off and it is, if anything, optimistic at these
sizes: the four certificates this repository actually ships cost **8x to 10x**
their own size to re-check. Every certificate in the ledger is currently
checkable only on a host with eight times the proof's size free.

Also counted the proofs exactly (`awk`), which the model needs:

| certificate | adds | add literals | deletes | delete literals |
|---|---:|---:|---:|---:|
| `F_81` | 85,802 | 1,138,646 | 78,736 | 1,055,167 |
| `F_103` | 611,950 | 8,849,656 | 590,248 | 8,559,910 |
| `F_171` | 1,021,888 | 16,317,546 | 988,999 | 15,886,763 |
| `F_256` | 1,297,107 | 19,652,014 | 1,258,306 | 19,122,926 |

## 2026-08-13 22:45 — where the memory actually is

Measured `parse_drat` alone (the probe reports RSS while holding only the step
vector, text dropped):

| certificate | text DRAT | step vector alone | fraction of peak |
|---|---:|---:|---:|
| `F_81` | 8.86 MB | 35.3 MB | 40% |
| `F_103` | 74.8 MB | 255.7 MB | 42% |
| `F_171` | 131.2 MB | 466.9 MB | 42% |
| `F_256` | 167.0 MB | 563.2 MB | 42% |

**Forty-two per cent of the peak is the parsed `Vec<DratStep>`, which the
backward checker does not need after `Plan::build` has run** — and which the
streaming producer of ADR-0381 already proved is not needed to *write* a proof.
That is the asymmetry the brief names, and it is the single biggest term.

Reconstructing the rest of `F_256` from first principles against the observed
770 MB of non-step-vector peak:

| term | bytes | note |
|---|---:|---|
| `Plan::arena` (`Vec<usize>`, 8 B/lit) | 157 MB | only *addition* literals reach it |
| `Plan::records` (48 B each) | 65 MB | 1.36 M records |
| `added_by_step` + `deleted_by_step` | 41 MB | 2 x 2.56 M x 8 B |
| `live: HashMap<Vec<(usize,bool)>, Vec<usize>>` | ~500 MB | **16 B per literal, plus one heap allocation per clause** |

The `live` deletion index — a temporary that exists only during
`Plan::build` — is bigger than everything else in the plan put together. Its key
is `Vec<(usize, bool)>`: 16 bytes to hold one literal that needs 5 bits of sign
and an index.

So the two things to fix, in order of size, are (1) the step vector and (2) the
deletion index's key representation. Neither is the algorithm. That is good
news: it means the fix is representational and the differential test between old
and new can be exact.

## 2026-08-13 22:50 — G1 landed in the snapshot

`crates/axeyum-cnf/src/drat_resource.rs`. Three pieces: `DratProofShape`
(exact / sampled from the head of the file / extrapolated from byte length),
`DratMemoryModel` (per-structural-item costs, with the measurement table above
in the doc comment), `MemoryBudget` (explicit, or 4/5 of `/proc/meminfo`'s
`MemAvailable`).

Two decisions worth recording:

- **`MemAvailable`, not `MemFree` and not `df`.** `MemAvailable` already
  excludes `Shmem`, so it is the one instrument that gets the `/tmp` tmpfs
  right. `df` on that mount reports it as disk.
- **`MemoryBudget::from_system()` returns `Option`, and a `None` is not
  "unlimited".** Defaulting a missing measurement to no limit is precisely the
  behaviour this module exists to replace.

The refusal is `DratResourceDecline`, a distinct type, surfaced through
`BackwardCheckOutcome::{Refuted, NoRefutation, Declined}`. Three outcomes
because two of them used to be the same exit code. `is_refuted()` rather than a
bare `bool` so a decline cannot be read as a refutation by omission.

## 2026-08-13 23:05 — G2 core written

`PlanBuilder` in `drat_backward.rs`: consumes steps one at a time, stops at the
first empty-clause addition, and never sees a `Vec<DratStep>`. The old
`Plan::build(&[DratStep])` now runs through it too, so there is exactly one plan
construction and the two routes cannot drift.

Two representation changes went in with it:

- `ClauseRecord` gains `key_hash: u64`, and the deletion index becomes
  `HashMap<u64, RecordSlot>` where `RecordSlot` is `Empty | One(usize) |
  Many(Vec<usize>)`. **The hash never decides a match** — `pop_matching`
  compares the literal sets themselves, so a 64-bit collision costs a comparison
  and never a wrong deletion. That was the one place where a memory optimisation
  could have become a soundness bug, so it is the one place that got a
  by-construction argument rather than a probability.
- `RecordSlot::One` inline: a `Vec` per key was one heap allocation per clause
  in the proof.

`variable_count()`'s separate pre-pass over the whole proof is gone; the builder
accumulates it as clauses arrive. Deletion literals still never widen it, which
matches the old behaviour exactly (they never reach the arena or the
assignment).

New public surface: `check_drat_backward_reader`,
`check_drat_backward_reader_within`, `check_drat_backward_within`.
`check_drat` (the reference forward checker) is untouched, as required.

## 2026-08-13 23:15 — differential test written before believing any of it

`crates/axeyum-cnf/tests/drat_backward_file_differential.rs`. Both routes get
literally the same bytes (the in-memory route is fed `parse_drat(text)`, not the
original step vector), so a divergence can only come from the checkers.

Deliberate design point: **every randomised test carries a control that fails if
the generator stopped producing the interesting case.** `corrupted_proofs_agree`
asserts at least 10 rejections *and* at least 10 acceptances, because a mutation
that is too gentle or too violent would pass while exercising one path.
`arbitrary_step_sequences_agree` asserts all three of `Ok(true)`, `Ok(false)`,
`Err` were reached. This is agent-a's lesson from today: it tried five instances
and only one flipped.

## 2026-08-13 23:20 — the differential test hung for ten minutes, twice

Not the checker. `random_3cnf` builds clauses of three *distinct* variables with
`while lits.len() < 3`, and `arbitrary_step_sequences_agree` called it with
`variables = 2 + rng.below(4)`, which can be 2. With two variables it can never
find a third, so it spins forever. Two ten-minute timeouts before I stopped
guessing and read the generator.

Worth recording because my first hypothesis was an infinite loop in the streaming
plan builder — the new, suspicious code — and it was in the test's own generator,
the boring code. The guard is now an assertion inside `random_3cnf` with the
reason, so the next person gets a panic instead of a hang.

A second cause found on the way: the pigeonhole case called `check_drat`, the
*reference forward* checker, on PHP(6,5)'s proof. Its cost is superlinear
(the module docs measure 38,015 steps at 200.6 s), so it is now gated to proofs
of at most 2,000 steps, with the reason in the code.

## 2026-08-13 23:25 — G1 + G2 landed: `8e84b2358`

8.00x -> 2.39x on `F_256`. Sixteen differential tests, no disagreement. 370 lib
tests and every integration suite green, clippy clean, `RUSTDOCFLAGS="-D warnings"
cargo doc` clean, `axeyum-solver` and `axeyum-search` still compile. ADR-0426.

Applied to the live tree with `diff` + `patch`, never `cp` over an existing file
— campaign rule 8, after a snapshot copy-back silently reverted another lane's
refactor earlier tonight. The four new files were copied only after checking
they did not already exist.

ADR number: I had written ADR-0383 throughout, having read F-C7's reference to
ADR-0381/0382 and assumed the next free slot was near. It was not — the index is
at 0425, and 0383 is `ground-integer-constant-folding`. Renumbered before
committing. A doc-only error, but it would have made two ADRs claim one number.

## 2026-08-13 23:35 — the calibration test caught the model twice

Both catches were the test doing its job, and both were things I would have
shipped otherwise.

1. **Under-prediction on `PHP(8, 7)`**: predicted 1,083,734, held 1,744,720. My
   per-item constants were fitted against a mental model of the Rado
   certificates, not against a measurement. Instrumented `heap_bytes` to print
   the breakdown and found two terms I had not modelled at all: the `Vec`
   doubling slack (the arena's capacity was 1.82x its length) and the deletion
   index's table. Under-prediction is the direction that ends in an OOM kill, so
   this was the important one.
2. **Calibrating on a proof too small to calibrate on**: `PHP(6, 5)` produces a
   2,875-byte proof, at which the model's 16 MB fixed term is 3,891x the
   structures being measured. The test's own over-prediction bound caught it. Now
   calibrated on `holes = 7..9` (310 KB to 16.6 MB), with the rejected sizes
   recorded in the doc comment so nobody re-picks them.

Also learned that the `FormulaShape` term is not optional: a caller with a large
formula and a short proof would be under-predicted without it.

## 2026-08-13 23:40 — measured the two things other lanes asked about

**agent-b's "large per-call fixed cost"** is not a per-call cost: 0.41 us on a
trivial proof, stable over 100,000 repetitions. It is a per-*formula* cost —
165 ms per call on `F_741`'s 269,664 clauses, because every check rebuilds the
formula's own records and deletion index. For a 6,241-cube cover that is 17.2
minutes of redundant work. Different diagnosis, different fix; written up as G-2.

**agent-a's "7x overhead" on `CnfFormula`** is 2.13x against a flat arena of the
same 8-byte literals. The 2.04 GB measurement is right; the factor is not,
because 109.9 M literals at `size_of::<CnfLit>() == 8` are 879 MB on their own.
Getting past 2.13x needs `CnfLit` packed to 4 bytes as well (3.9x total). Sizing
a fix against 7x would have made a correct fix look like a failure.

## 2026-08-13 23:45 — a 2.5x slowdown that was not there

First measurement of the `u32` follow-on: 61.0 s on `F_256` against 24.8 s for
the previous build. A 2.5x regression, and I nearly reverted.

`uptime` said load average **34** on a 24-core box — other lanes. Built the
previous commit into its own directory and ran the two alternately in one loop:
the `u32` build is *faster* on every pair (23.6-50.5 s vs 57.0-91.6 s). The
memory figures were stable to three digits across all runs while the timings
varied by 4x.

The lesson is not "beware of load". It is that a single timing on a shared box is
not a measurement, and that memory and time needed completely different amounts
of care tonight: RSS was reproducible to 0.1% from one run, time needed
alternating pairs. Thirty seconds of extra work; it was the difference between
landing this and reverting it.

## 2026-08-13 23:51 — G2b landed: `017eebe68`

8.00x -> **1.49x** on `F_256`, a 5.4x reduction overall, and faster. The
in-memory route benefits too without any caller changing a line (1335 MB ->
805 MB), because both routes share the plan.

Two guards needed testing and neither overflow is reachable in a test, which is
the whole reason they needed testing:

- `MAX_STORED_VARIABLE_INDEX` is one *below* the arithmetic maximum, because at
  the arithmetic maximum the negated code is exactly `u32::MAX`, which is the
  `NO_PIVOT` sentinel. I got this wrong on the first pass and the guard test
  caught it — an ordinary literal would have been read as "this clause has no RAT
  pivot", and a lemma that should have been RAT-checked would have been skipped.
  That is a wrong-answer path, in the trusted checker, from a memory
  optimisation.
- `ClauseRecord::start` stays 64-bit. An 18.9 GB proof has ~4.4 G literal
  occurrences; a 32-bit arena offset overflows at 4.29 G. The temptation to
  narrow it was real — it is 8 bytes of every 40-byte record — and it would have
  been wrong on exactly the certificate this lane exists for.

Both routes were also run over each of the four committed certificates in one
process with their verdicts compared directly. They agree on all four.

## 2026-08-13 23:54 — two tools reported clean when they had not looked

Caught in the final verification pass, after the commits.

1. **`cargo clippy` exited 0 over a cached example.** The `differential` mode I
   added to `drat_memory_probe` pushed `main` past `too_many_lines`. I ran clippy
   before adding it and again after committing; the second run reported nothing
   because nothing had been recompiled. `touch crates/axeyum-cnf/src/lib.rs`
   forced the rebuild and the warning appeared. CI runs `-D warnings`, so this
   would have been a red build attributed to whoever pushed next.
2. **My ADR index line was gone.** Another lane appended 0427-0431 to the same
   table between my commit and now, and its version of the file won. Campaign
   rule 9 predicts exactly this. Re-read, re-inserted in numeric order.

Both repaired in `81d29b71a`. Recording them because they are the same failure
mode this repository's own gotchas list is about, and I hit both in one pass
while believing I was done.

## 2026-08-13 23:55 — where I stopped

Both halves of the mandate are landed. G3 (`CnfFormula`'s representation) is
**not** done and is deliberately not started: `.clauses()` has 113 call sites
across four crates, three of them other lanes', and `axeyum-search` is
off-limits tonight. It is measured and specified in `FEEDBACK.md` as G-1, split
into a confined half (pack `CnfLit`, `axeyum-cnf` only, breaks nothing) and a
cross-crate half.
