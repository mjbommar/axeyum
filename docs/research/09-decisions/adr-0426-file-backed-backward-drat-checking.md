# ADR-0426: File-backed backward DRAT checking, and a typed resource decline

Status: accepted

Date: 2026-08-13

Supersedes nothing; extends [ADR-0381](adr-0381-streaming-drat-proofs.md)
(streaming proof *production*) and [ADR-0382](adr-0382-backward-drat-checking.md)
(backward proof *checking*).

## Context

ADR-0381 made proof production streaming: `DratSink` and `TextProofSink` let a
solver write a certificate it never holds, which took one instance from 22.3 GiB
resident to 1.9 GiB. **The consumer half was never done.** `check_drat_backward`
takes `&[DratStep]`, so re-checking a proof requires parsing the whole file into
memory first.

That asymmetry — we can produce proofs we cannot check — was measured this
session and it is worse than the project believed. The prior rule of thumb was
1.5x the proof's size on disk. The measurements:

| certificate | text DRAT | peak RSS | ratio |
|---|---:|---:|---:|
| `rado-r4-a3-b1/F_81` | 8,862,657 | 88,416,256 | **9.98x** |
| `rado-r4-a3-b2/F_103` | 74,818,033 | 608,473,088 | **8.13x** |
| `rado-r4-a1-b2/F_171` | 131,197,778 | 1,112,662,016 | **8.48x** |
| `rado-r4-a4-b1/F_256` | 166,982,506 | 1,335,078,912 | **8.00x** |

and, independently, 1,873,245,421 bytes of DRAT to 12.3 GiB (6.6x) and
8.82 GB to ~56 GiB (6.4x) on a separate lane's instances.

Two consequences, both real:

1. **The ledger records certificates this project cannot re-check anywhere.**
   `rado-r4-a2-b3` stores `proof_bytes: 18921576073`. At the measured ratio that
   is 125-151 GiB resident; the largest host available is 123 GiB. The
   certificate is on disk and no machine here can verify it.
2. **An OOM kill is indistinguishable from a refuted claim.** `SIGKILL` gives
   exit 137 and no output, which reads exactly like a checker that rejected the
   proof. This has cost real work more than once — `recertify_rado` was killed at
   27,742,576 kB on a 27 GiB host — and it caused one lane to run duplicate
   insurance jobs on two hosts for the same instance because it could not
   predict where a check would fit.

The breakdown of where the memory goes, measured rather than assumed:

| term | share of peak | note |
|---|---:|---|
| the parsed `Vec<DratStep>` | **42%** | dropped after `Plan::build`; never needed by the walk |
| `Plan`'s deletion index | ~27% | `HashMap<Vec<(usize, bool)>, Vec<usize>>` — 16 bytes and one allocation per literal |
| `Plan`'s clause arena | ~12% | packed literal codes; irreducible without a narrower code |
| clause records, step maps | ~11% | |

Neither of the top two is the algorithm. Both are representation.

## Decision

### 1. Build the clause plan from a stream

`PlanBuilder` consumes proof steps one at a time and stops at the first
empty-clause addition. `check_drat_backward_reader` feeds it from any
`BufRead` through the existing `DratTextReader`, so no `Vec<DratStep>` is ever
materialised. `check_drat_backward` now runs through the *same* builder, so
there is exactly one plan construction and the two routes cannot drift.

Backward checking is still not a pure stream — the proof prefix up to the empty
clause is walked in reverse and has to be indexable — so the claim made here is
bounded by the *clause plan*, not by the proof text. That is the honest form of
the improvement and it is what the doc comments say.

### 2. Compact the deletion index

`ClauseRecord` gains `key_hash: u64` and the index becomes
`HashMap<u64, RecordSlot>` where `RecordSlot` is `Empty | One(usize) |
Many(Vec<usize>)`.

**The hash never decides a match.** `RecordSlot::pop_matching` compares the
literal sets themselves, recomputing a candidate's sorted key from the arena, so
a 64-bit collision between two different clauses costs one comparison and can
never produce a wrong deletion. This is the one place where a memory
optimisation could have become a soundness bug, and it is settled by
construction rather than by probability.

`RecordSlot::One` is inline because a `Vec` per key was one heap allocation per
clause in the proof.

### 3. Predict, and decline with a type

`drat_resource.rs` adds:

- `DratProofShape` — steps, added clauses, added and total literal occurrences,
  obtained exactly, by sampling the head of a proof file, or extrapolated from
  its byte length alone.
- `DratMemoryModel` — per-structural-item cost constants, each documented with
  the measurement it came from, per route.
- `MemoryBudget` — explicit, or four fifths of `/proc/meminfo`'s `MemAvailable`.
  `from_system()` returns `Option`, and a `None` is a *missing measurement*, not
  "unlimited": defaulting a missing measurement to no limit is the behaviour this
  module exists to replace.
- `BackwardCheckOutcome::{Refuted, NoRefutation, Declined}` — three outcomes,
  because two of them used to be the same exit code. `is_refuted()` rather than a
  bare `bool`, so a decline cannot be read as a refutation by omission. A proof
  that fails to verify is not an outcome here at all; it stays
  `DratError::StepNotVerified`.
- `DratMemoryReport` — the prediction beside `observed_structure_bytes`, which is
  not an estimate but the sum of the allocation capacities the checker actually
  held. A caller that logs it re-measures the cost model on live data.

`MemAvailable` rather than `MemFree` or `df`, deliberately: it is the only one of
the three that excludes `Shmem`, and `/tmp` on these hosts is a 62 GiB tmpfs whose
contents are RAM. `df` on that mount reports disk and is the wrong instrument.

### 4. The reference forward checker is untouched

`check_drat` stays exactly as it was. Its value is that it is small enough to
audit by reading, and nothing here changes it.

## Evidence

**Verdicts.** `tests/drat_backward_file_differential.rs` (16 tests) runs both
backward routes over literally the same bytes — the in-memory route is fed
`parse_drat(text)`, not the original step vector — and asserts they agree verdict
for verdict, error for error, failing step for failing step. It covers fixed
shapes (repeated clauses, repeated literals within a clause, deletions that match
nothing, steps after the empty clause, proofs over variables the formula does not
have), solver-produced pigeonhole proofs, 200 random solver proofs, 400
deliberately corrupted proofs, and 600 arbitrary step sequences.

**No disagreement was found**, on any input, in any category.

Every randomised test carries a control that fails if the generator stopped
producing the interesting case: `corrupted_proofs_agree` requires at least 10
rejections *and* at least 10 acceptances, because a mutation that is too gentle
or too violent would pass while exercising one path;
`arbitrary_step_sequences_agree` requires all three of `Ok(true)`, `Ok(false)` and
`Err` to have been reached.

**Memory.** Measured with `examples/drat_memory_probe`, peak RSS from
`/proc/self/status` `VmHWM`, release build:

| certificate | text DRAT | before | after | reduction |
|---|---:|---:|---:|---:|
| `rado-r4-a3-b1/F_81` | 8.86 MB | 88.4 MB (9.98x) | 27.1 MB (**3.06x**) | 3.26x |
| `rado-r4-a3-b2/F_103` | 74.8 MB | 608.5 MB (8.13x) | 188.0 MB (**2.51x**) | 3.24x |
| `rado-r4-a1-b2/F_171` | 131.2 MB | 1112.7 MB (8.48x) | 321.6 MB (**2.45x**) | 3.46x |
| `rado-r4-a4-b1/F_256` | 167.0 MB | 1335.1 MB (8.00x) | 399.6 MB (**2.39x**) | 3.34x |

Verdicts identical (`true`) on all four; wall time unchanged within noise.

**The model.** `tests/drat_memory_model.rs` (5 tests) re-derives the constants
from live runs on every invocation and asserts the prediction is (a) at least the
observation — under-prediction is the direction that ends in an OOM kill — and
(b) within 6x of it, so a model that over-predicts by a hundredfold and refuses
everything is caught too. Calibration instances were chosen by measurement:
`PHP(6, 5)` was tried first and rejected because its 2,875-byte proof makes the
fixed term 3,891x the structures being measured, at which the calibration says
nothing.

**Sampling bias, measured.** The head of a DRAT proof is not representative. A
0.1% head sample over-estimates the added-literal count by 54-102%; 5% is within
11%; 10% within 3%. The step count is well estimated at any sample size — it is
the mean clause width that drifts, because a proof's early lemmas are wider than
its later ones. The bias is toward over-estimating, which is the safe direction
for a budget. `DratProofShape::recommended_sample_bytes` encodes 5% with a 1 MiB
floor, and the test asserts a deliberately tiny sample is *worse*, so the
recommendation is not vacuous.

### 5. Follow-on: narrow the plan's stored fields to 32 bits

Landed separately, on top of the differential harness rather than beside it.

The clause arena stores `StoredCode = u32` rather than the 8-byte `usize` the
engine computes with; `ClauseRecord`'s `len`, `born`, `died` and `pivot` are
`u32` (40 bytes a record, from 56); and the two step-to-record maps are `Vec<u32>`.

`ClauseRecord::start` **stays 64-bit deliberately**. An 18.9 GB proof — one this
repository ships — has roughly 4.4 G literal occurrences, and a 32-bit arena
offset overflows at 4.29 G. That overflow would appear only at a size no test
here can reach, on exactly the certificates that matter most.

Every other narrowing is guarded at construction and refused as
`DratError::Parse` rather than truncated, because a truncated literal is a
*wrong answer* and not a crash. Two guards need naming:

- `MAX_STORED_VARIABLE_INDEX` is `((u32::MAX - 1) / 2) - 1`, one below the
  arithmetic maximum. At the arithmetic maximum the *negated* code is exactly
  `u32::MAX`, which is the `NO_PIVOT` sentinel — an ordinary literal would become
  indistinguishable from "this clause has no RAT pivot", and a lemma that should
  have been RAT-checked would be skipped.
- Clause widths, step indices and record ids are narrowed through helpers that
  record an overflow for `PlanBuilder::finish` to refuse, rather than panicking
  or truncating in the hot path.

Neither overflow is reachable in a test, which is why both guards are tested
directly, each with a control that fails if the constant moves.

## Consequences

Measured after the follow-on, same four certificates, same instrument:

| certificate | text DRAT | original | file-backed | file-backed + `u32` |
|---|---:|---:|---:|---:|
| `rado-r4-a3-b1/F_81` | 8.86 MB | 88.4 MB (9.98x) | 27.1 MB (3.06x) | 18.9 MB (**2.13x**) |
| `rado-r4-a3-b2/F_103` | 74.8 MB | 608.5 MB (8.13x) | 188.0 MB (2.51x) | 119.4 MB (**1.60x**) |
| `rado-r4-a1-b2/F_171` | 131.2 MB | 1112.7 MB (8.48x) | 321.6 MB (2.45x) | 225.9 MB (**1.72x**) |
| `rado-r4-a4-b1/F_256` | 167.0 MB | 1335.1 MB (8.00x) | 399.6 MB (2.39x) | 248.7 MB (**1.49x**) |

**8.00x to 1.49x, a 5.4x reduction**, verdicts identical throughout. The
in-memory route benefits too, since it shares the plan: `F_256` goes from
1335.1 MB to 805.4 MB.

Both routes were also run in a single process over each of the four
certificates, with their verdicts compared directly, which is the differential
test of `tests/drat_backward_file_differential.rs` applied to real certificates
no unit test can afford to hold. They agree on all four.

The follow-on is also *faster*, measured alternating under identical load on
`F_256`: 57.0-91.6 s before, 23.6-50.5 s after. (An earlier apparent 2.5x
slowdown was machine load — the box was at a load average of 34 on 24 cores from
other lanes — and the alternating re-measurement is the only reason that did not
become a recorded regression.)

The re-checkability of this repository's own certificates changes materially. At
1.5x with a 4/5 headroom fraction:

| host | RAM | largest proof before (8x) | after (1.5x) |
|---|---:|---:|---:|
| s5 / s6 / s7 | 26 GiB | ~2.6 GB | **~14 GB** |
| s1 | 61 GiB | ~6.1 GB | **~32 GB** |
| s0 / s4 | 123 GiB | ~12.3 GB | **~65 GB** |

`rado-r4-a2-b3` (18.9 GB) moves from *uncheckable on every host in the fleet* —
18.9 GB at 6.6-8x is 125-151 GiB against a 123 GiB maximum — to checkable on s0
and s4. `rado-r4-a4-b3` (5.0 GB) moves from s0/s4-only to checkable on any host
here.

What this does **not** do: it does not make the footprint independent of the
proof. A backward walk needs its prefix indexable, so the plan is still
O(proof).

`DratMemoryModel::estimate` takes a `FormulaShape` as well as a proof shape.
Passing `FormulaShape::EMPTY` under-predicts by the formula's own contribution,
which on a search-scale certificate is ~4% but on a large formula with a short
proof is not.

Callers should move from `check_drat_backward` to
`check_drat_backward_reader_within`: it is the form whose budget can still say no
in time. `check_drat_backward_within` guards the in-memory route's plan, but the
step vector is already resident by the time it is called.
