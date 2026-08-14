# 05 — Proof consumption: nearly closed, and the remaining wall is Lean's

**Status:** mostly resolved by [ADR-0426](../research/09-decisions/adr-0426-file-backed-backward-drat-checking.md).
This document exists to record what is left, and to stop a stale framing being
repeated.
**Research note:** [`proof-checking-memory-and-io.md`](../research/07-verification/proof-checking-memory-and-io.md)

## Correcting a framing this folder repeated

The README says the proof-checking blow-up was "6.6× since reduced to 1.5×", and
a first draft of this document asserted a live asymmetry — *"we can produce
proofs we cannot check."* Both were stale. The measured history:

| stage | ratio to proof size on disk |
|---|---|
| prior rule of thumb (belief, never measured) | 1.5× |
| actual, measured by ADR-0426 | **8.00×–9.98×** |
| ADR-0426 file-backed plan | 2.39×–3.06× |
| ADR-0426 follow-on, `u32` records | **1.49×–2.13×** |

**8.00× → 1.49×, a 5.4× reduction, verdicts identical on all four certificates —
and the follow-on is also faster**, 57.0–91.6 s to 23.6–50.5 s on `F_256` under
alternating load. Consumption is no longer the broken half. The item that
mattered here is *done*; what remains is smaller than it looks from the outside.

Its own consequence table makes the fleet effect concrete, at 1.5× with a 4/5
headroom fraction:

| host | RAM | largest checkable proof before (8×) | after (1.5×) |
|---|---:|---:|---:|
| s5 / s6 / s7 | 26 GiB | ~2.6 GB | **~14 GB** |
| s1 | 61 GiB | ~6.1 GB | **~32 GB** |
| s0 / s4 | 123 GiB | ~12.3 GB | **~65 GB** |

`rado-r4-a2-b3` (18.9 GB) went from uncheckable *anywhere in the fleet* to
checkable on s0 and s4. The ~30 GB certificate from the in-flight b=3 run is
comfortably inside that budget.

## What is actually left

### 05.1 — Drop written proof pages from page cache (small, unblocked)

Writing a 30 GB write-once certificate pushes 30 GB through page cache and
evicts everything else; three build lanes were competing for cache during the
b=3 run. `posix_fadvise(DONTNEED)` after the sink flushes.

- Touch: the ADR-0381 streaming sink (`DratSink` / `TextProofSink`).
- Dependency check first: the hard rule is no C/C++ in the default build.
  `rustix` on its `linux_raw` backend is pure-Rust syscalls with **safe**
  wrappers, satisfying both that rule and the `unsafe_code` ban — **verify
  before adopting**, do not assume.
- Exit: page-cache footprint during a multi-GB write, measured before and after.
- **Not** `O_DIRECT`: it bypasses cache on reads too, the opposite of what a
  re-scanned proof wants.

### 05.2 — mmap the indexable prefix (medium, ADR-gated, now LOW priority)

ADR-0426 is explicit about its residue: *"the proof prefix up to the empty
clause is walked in reverse and has to be indexable."* "Indexable" and
"resident" are different requirements; an mmap'd prefix is indexable at zero
heap cost.

**But size the prize honestly.** This is 1.49× → sub-1×, not 8× → 1×. For
comparison, `cake_lpr` — the formally verified checker — needs memory "around the
size of the proof file", so ~1× *is* the state of the art and we are already
within 50% of it. Going sub-1× would put us ahead of the field, which is a real
result but not an unblocking one.

- Requires an ADR for an `unsafe_code` exception: `memmap2::Mmap::map` is
  `unsafe` and necessarily so — a concurrent truncation turns a mapped read into
  SIGBUS. The ADR must state the file-stability assumption and how it is
  enforced, not merely note the risk.
- Instrument already exists: `drat_memory_probe`, and ADR-0426's four-certificate
  table is the baseline to beat.
- `DratMemoryModel`'s cost constants would need re-fitting, or the typed
  predictor will decline runs the new route could serve.

### 05.3 — LRAT forward checking (large, strategic)

Hints turn checking from a search into a linear forward pass.
`elaborate_drat_to_lrat` and `elaborate_drat_to_lrat_backward` already exist in
`crates/axeyum-cnf/src/lrat.rs`. Lower urgency than it looked before the numbers
above, but it is the route the field has standardised on and it is the input to
05.4.

### 05.4 — **The actual remaining wall: Lean parity on large proofs**

This is the item worth attention, and it is not about I/O at all.
[LRAT-Catcher](https://arxiv.org/html/2607.00815v1) (July 2026) reports Mathlib's
`lrat_proof` peaking at **96.6 GB on a 628 MB Schur certificate** — it embeds the
formula in the proof term — against **8.9 GB** for native reflection on the same
instance.

The b=3 certificate is ~30 GB, roughly **50× that Schur instance**. So:

- DRAT checking of a 30 GB proof: **fine**, ~45 GB at 1.5×, inside s0/s4's budget.
- Turning that same proof into a Lean proof *term*: **not available at any size
  we care about.**

Any plan asserting "every unsat carries a machine-checkable Lean proof" has to
mean **reflection** for this class of result. That interacts directly with
[ADR-0453](../research/09-decisions/adr-0453-route-dependent-provability.md):
reflection has a different trust base from a kernel-checked proof term — it adds
the compiler, or reduces through the kernel at steep cost — and `proof_route`
exists to record exactly that kind of difference. A `reflection` route value is
the likely follow-up.

## Explicitly rejected

**`io_uring`.** Searched the SAT proof-checking literature through 2026,
including the DFG "Proofs as Big Data" project (Heule, Biere, Tan): no use of it.
The reason is structural — io_uring buys batched async submission and low syscall
overhead, and the bottleneck was a resident index, not I/O latency or queue
depth. Now that the index is 1.49×, there is even less to gain. Revisit only if a
profile shows I/O wait; it does not.

**`O_DIRECT` on the read path.** See 05.1.

## Why any of it matters

**An unchecked certificate is not evidence**, and the ledger now enforces that
literally: `close-fact.py` refuses to flip a status whose checker does not return
0. A proof too expensive to check cannot close a fact. ADR-0426 moved that line
from 12.3 GB to ~65 GB on this host; 05.4 is about where the line sits for the
*Lean* leg, which is currently far lower.
