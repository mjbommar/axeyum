# agent-g RESULT — DRAT checking memory, before and after

Lane: `crates/axeyum-cnf/`. Landed as **`8e84b2358`** (`feat(cnf): file-backed
backward DRAT checking, 8.0x -> 2.4x resident`) and **`017eebe68`**
(`perf(cnf): narrow the backward DRAT plan to 32 bits, 2.4x -> 1.5x resident`),
with **ADR-0426**.

All measurements on **s0** (24 cores, 123 GiB), release build, peak RSS from
`/proc/self/status` `VmHWM`, via the committed
`crates/axeyum-cnf/examples/drat_memory_probe.rs`. Subjects are this
repository's own committed certificates, decompressed from
`artifacts/claims/rado/*/F_*.drat.gz`.

---

## 1. The headline

**8.0x-10.0x of the proof's size in resident memory, before. 1.5x-2.1x after.**

| certificate | text DRAT | before | `8e84b2358` | `017eebe68` | total | verdict |
|---|---:|---:|---:|---:|---:|:--:|
| `rado-r4-a3-b1/F_81` | 8,862,657 | 88,416,256 (**9.98x**) | 27,107,328 (3.06x) | 18,857,984 (**2.13x**) | 4.7x | `true` = `true` |
| `rado-r4-a3-b2/F_103` | 74,818,033 | 608,473,088 (**8.13x**) | 187,981,824 (2.51x) | 119,418,880 (**1.60x**) | 5.1x | `true` = `true` |
| `rado-r4-a1-b2/F_171` | 131,197,778 | 1,112,662,016 (**8.48x**) | 321,589,248 (2.45x) | 225,923,072 (**1.72x**) | 4.9x | `true` = `true` |
| `rado-r4-a4-b1/F_256` | 166,982,506 | 1,335,078,912 (**8.00x**) | 399,597,568 (2.39x) | 248,700,928 (**1.49x**) | **5.4x** | `true` = `true` |

The in-memory route shares the plan and benefits too, without any caller
changing a line: `F_256` goes from 1,335,078,912 to 805,380,096 (8.00x -> 4.82x).

Wall time did not regress; it improved. Alternating runs on `F_256` under
identical load: **57.0-91.6 s before, 23.6-50.5 s after**. (See section 5 for
the false regression this nearly became.)

The ratio was believed to be 1.5x (agent-c F-C3) and then measured at 6.6x
(agent-c F-C7). On the certificates this repository actually ships it is **8x**,
so the prior belief was wrong by more than five times, and the corrected belief
was still optimistic at these sizes. The ratio falls with proof size — the fixed
costs amortise — which is why agent-c's larger instance read 6.6x where these
read 8.0x-10.0x. On the after side the same effect runs 2.13x down to 1.49x, so
**1.5x is the number to schedule against for a large proof and 1.4x is a
reasonable extrapolation** to the multi-gigabyte range.

## 2. Which hosts can now check which certificates

Using the shipped default budget — four fifths of `/proc/meminfo`'s
`MemAvailable` — and the measured 1.5x:

| host | RAM | largest checkable proof, before (8x) | after (1.5x) |
|---|---:|---:|---:|
| s5, s6, s7 | 26 GiB | ~2.6 GB | **~14 GB** |
| s1 | 61 GiB | ~6.1 GB | **~32 GB** |
| s0, s4 | 123 GiB | ~12.3 GB | **~65 GB** |

Against the ledger's actual artifacts:

| certificate | `proof_bytes` | before | after |
|---|---:|---|---|
| `rado-r4-a2-b3` | 18,921,576,073 | **no host in this fleet** (needs 125-151 GiB) | s0, s4 (~28 GiB) |
| `rado-r4-a4-b3` | ~5,000,000,000 | s0, s4 only | any host here (~7.5 GiB) |
| agent-c `(5,2,4)` n=625 | 8,820,000,000 | s4 only (measured 56 GiB live) | any host here (~13 GiB) |
| agent-c `(5,1,4)` n=625 | 1,873,245,421 | s0, s1, s4 (12.3 GiB) | any host here (~2.8 GiB) |

The first row is the one that matters most. **`rado-r4-a2-b3` is a certificate
this repository ships and could not re-check on any machine available to this
campaign** — 18.9 GB at the measured 6.6x-8x is 125-151 GiB against a 123 GiB
maximum. It is now within reach on s0 and s4.

The second-order effect is the one agent-c named in F-C10: this converts a hard
resource wall into a scheduling parameter. agent-c had to run duplicate
insurance jobs on two hosts because it could not predict where a check would
fit; the prediction is now a computed value with a typed refusal, so the job can
be placed instead of raced.

## 3. The differential test: no disagreement found

`crates/axeyum-cnf/tests/drat_backward_file_differential.rs`, 16 tests, written
**before** the optimisation it guards. Both backward routes are fed literally the
same bytes (the in-memory route gets `parse_drat(text)`, not the original step
vector), so a divergence can only come from the checkers.

| category | inputs | disagreements |
|---|---:|---:|
| fixed shapes (repeated clauses, repeated literals, unmatched deletions, trailing garbage, proof-only variables, comments) | 12 | **0** |
| solver-produced pigeonhole proofs `PHP(n+1, n)`, n = 2..5 | 4 | **0** |
| random 3-CNF solver proofs | 200 generated, >= 20 unsatisfiable | **0** |
| **corrupted** proofs (step dropped / literal flipped / steps swapped / clause inserted) | 400 generated, >= 10 rejected and >= 10 accepted | **0** |
| arbitrary hand-built step sequences | 600, all three verdict classes reached | **0** |
| **the four committed certificates, both routes in one process** | 4 (164,538 to 2,555,413 steps) | **0** |

The last row is the differential run against real certificates, which no unit
test can afford to hold: `drat_memory_probe <cnf> <drat> differential` runs both
routes over the same file in one process and asserts equality. All four report
`Ok(true)` on both routes.

Agreement is asserted on the *whole* result, not just the boolean: verdict for
verdict, `Err` for `Err`, failing step index for failing step index.

Every randomised category carries a control that fails if the generator stopped
producing the interesting case — `corrupted_proofs_agree` requires both at least
10 rejections and at least 10 acceptances, because a mutation that is too gentle
or too violent would pass while exercising a single path. This is agent-a's
lesson from today applied deliberately: it tried five instances and only one
flipped.

The full `axeyum-cnf` suite is green: **372** lib + 4 + 16 + 5 + 9 + 19 + 4 + 3
integration tests, `cargo clippy --all-targets --all-features` clean, and
`RUSTDOCFLAGS="-D warnings" cargo doc` clean. `axeyum-solver` and
`axeyum-search` still compile against the changed crate.

The two lib tests added by `017eebe68` are the narrowing guards, each with a
control: `a_variable_count_that_would_truncate_a_stored_code_is_refused` (with
the identical shape over a narrow variable refuted, not refused, so the test
cannot pass against a checker that refuses everything) and
`no_real_literal_code_can_be_mistaken_for_the_pivot_sentinel` (which asserts
that one index past the guard lands the negated code exactly on `u32::MAX`, so
it fails if anyone raises the constant).

## 4. Where the memory went, and where it goes now

Measured, not assumed. `parse_drat` alone (proof text dropped):

| certificate | text DRAT | step vector alone | share of the old peak |
|---|---:|---:|---:|
| `F_81` | 8.86 MB | 35.3 MB | 40% |
| `F_103` | 74.8 MB | 255.7 MB | 42% |
| `F_171` | 131.2 MB | 466.9 MB | 42% |
| `F_256` | 167.0 MB | 563.2 MB | 42% |

The remaining 58%, reconstructed for `F_256` against the observed 770 MB:

| term | bytes | note |
|---|---:|---|
| `live: HashMap<Vec<(usize,bool)>, Vec<usize>>` | ~500 MB | 16 bytes and one heap allocation *per literal*, for a temporary |
| `Plan::arena` | 157 MB | 8-byte packed literal codes |
| `Plan::records` | 65 MB | 48 bytes each |
| `added_by_step` + `deleted_by_step` | 41 MB | |

Both of the top two are representation, not algorithm — which is why the change
is verdict-preserving by construction and the differential test can be exact.

After, measured directly on `PHP(8, 7)` from the checker's own allocation
capacities, in the two stages:

| term | after `8e84b2358` | after `017eebe68` |
|---|---:|---:|
| clause arena (62,961 literals) | 917,504 | 458,752 |
| clause records (4,212) | 458,752 | 327,680 |
| step maps (6,153 steps) | 131,072 | 65,536 |
| deletion index | 236,544 | 236,544 |
| **total held** | **1,744,720** | **1,089,360** |

The deletion index is what to attack next at this scale: it is now the largest
single term at 22% of the total, and its 33-byte slot is `u64` key plus a
`RecordSlot` that is 24 bytes because of the rare `Many(Vec<usize>)` arm.

## 5. Three things I did not expect

**Plan construction got 2.1x faster, not slower.** Same 269,664-clause formula
(`F_741`), same one-step proof, parent commit vs mine:

```
before  349.0 ms per check_drat_backward call
after   165.4 ms per check_drat_backward call
```

The old code allocated a `Vec<(usize, bool)>` per clause as a hash key. Removing
that allocation bought more time than the sorting and hashing it replaced cost.

**The per-*call* fixed cost is negligible; the per-*formula* cost is not.**
agent-b's FEEDBACK #2 reports a large fixed cost per backward-checker call. On a
trivial proof against a trivial formula it is **0.41 us**, in-memory and
file-backed alike, stable across 1,000 / 10,000 / 100,000 repetitions — so it is
not a per-call constant. What is large is the part that scales with the
*formula*: **165 ms per call on a 269,664-clause formula**, because every check
rebuilds the formula's own clause records and deletion index from scratch.

For agent-b's 6,241-cube cover of `R_4(5(x-y)=4z)`, that is **17.2 minutes of
pure plan construction** across the cover, down from 36 minutes before this
change — and all of it redundant, because the formula prefix is identical for
every cube. That is the single cheapest remaining win and it is written up as
G-2 in `FEEDBACK.md`.

**A 2.5x slowdown that was not real.** The first measurement of the `u32`
follow-on read 61.0 s against 24.8 s for the previous build on `F_256` — a
2.5x regression that would have justified reverting it. The load average on this
24-core box was **34**, from other lanes. Re-measured alternating between the two
builds in one loop, the `u32` build is *faster* on every pair (23.6-50.5 s vs
57.0-91.6 s), and the memory figures are stable to three digits across runs while
the timings vary by 4x.

The lesson is not "beware of load" — it is that a single measurement of a *timing*
on a shared box is not a measurement. Memory was reproducible to 0.1%; time was
not reproducible to a factor of four. Alternating the two builds within one loop
is what made the comparison mean anything, and it cost thirty seconds.

## 6. `CnfFormula`'s representation, measured

The G3 item, grounded before proposing it. `parse_dimacs` resident size:

| formula | DIMACS | vars | clauses | literals | resident | flat-arena floor | headroom |
|---|---:|---:|---:|---:|---:|---:|---:|
| `F_741` (Rado 741) | 8,591,634 | 2,964 | 269,664 | 1,622,431 | 31,731,712 (2.41x) | 14,058,104 | **1.47x** |
| `F_188` (Schur 3;5,7,7) | 525,542,410 | 564 | 19,807,560 | 109,858,889 | **2,035,638,272** (2.87x) | 958,101,352 | **2.13x** |

A correction to agent-a's FEEDBACK #6, which reads "2.3 GB RSS for 330 MB of
literals — a 7x overhead". The 2.0-2.3 GB is right. The overhead against a flat
arena of the *same* 8-byte literals is **2.13x**, not 7x: 109.9 M literals at
`size_of::<CnfLit>() == 8` are 879 MB on their own, so most of the flat floor is
the literals themselves. Getting past 2.13x needs `CnfLit` narrowed from 8 bytes
to a packed 4-byte code as well, which would put the floor at 519 MB and the
total available win at **3.9x**.

I did not attempt this refactor: `.clauses()` has 113 call sites across four
crates, three of which are other lanes' (`axeyum-solver`, `axeyum-search`,
`axeyum-bench`), and `axeyum-search` is explicitly off-limits tonight. It is
written up as G-1 in `FEEDBACK.md` with the measurement and a migration order.

## 7. What this does not do

The footprint is still **O(proof)**, not bounded. A backward walk needs its
prefix indexable, so "file-backed" here means *the parsed step vector is gone and
the clause plan is built straight from the reader* — not that the proof is
streamed the way `check_drat_streaming` streams the forward check. The doc
comments say exactly this; the phrase "bounded memory" would have been a
comfortable overstatement and is not used.

`ClauseRecord::start` is deliberately still 64-bit. An 18.9 GB proof has roughly
4.4 G literal occurrences and a 32-bit arena offset overflows at 4.29 G — on
exactly the certificate this whole lane exists for. Everything else narrowed is
guarded and refused rather than truncated, because a truncated literal is a wrong
answer and not a crash, and both guards are tested directly since neither
overflow is reachable in a test.

The largest remaining term is the deletion index (22% of what is held), which is
a temporary that exists only during plan construction. G-3 in `FEEDBACK.md` is
now about that rather than about the arena.

## 8. Reproducing

```sh
# From the repository root, at 8e84b2358 or later.
gzip -dc artifacts/claims/rado/rado-r4-a4-b1/F_256.drat.gz > /var/tmp/F_256.drat
cargo run --release -p axeyum-cnf --example drat_memory_probe -- \
    artifacts/claims/rado/rado-r4-a4-b1/F_256.cnf /var/tmp/F_256.drat backward
cargo run --release -p axeyum-cnf --example drat_memory_probe -- \
    artifacts/claims/rado/rado-r4-a4-b1/F_256.cnf /var/tmp/F_256.drat file-backed
cargo test -p axeyum-cnf --release --test drat_backward_file_differential   # expect 16
cargo test -p axeyum-cnf --release --test drat_memory_model                 # expect 5
```

Not `/tmp`: it is a 62 GiB tmpfs on these hosts, and a 167 MB file written there
is 167 MB of the memory being measured.
