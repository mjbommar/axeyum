# Proof-checking memory, and what modern Linux I/O can and cannot do about it

Notes, 2026-08-14. Prompted by a live 8-hour Rado run whose certificate was
growing toward ~30 GB, and by the question of whether `mmap`, `O_DIRECT` or
`io_uring` would help. Short answer: one is aimed at a real residue whose prize
is smaller than it looks, one is aimed at a different constraint we genuinely
have, and one is aimed at nothing we have. The larger correction is that the
problem prompting the question was already solved and the folder was still
quoting the pre-fix number.

## Where we actually stand

Proof **production** is solved. [ADR-0381](../09-decisions/adr-0381-streaming-drat-proofs.md)
made it streaming: a solver writes a certificate it never holds, taking one
instance from 22.3 GiB resident to 1.9 GiB.

Proof **consumption** was the open half, and is now largely closed.
[ADR-0426](../09-decisions/adr-0426-file-backed-backward-drat-checking.md) first
measured the asymmetry, and it was far worse than the project's rule of thumb of
1.5× — that figure was a belief, never a measurement:

| certificate | text DRAT | peak RSS | ratio |
|---|---:|---:|---:|
| `rado-r4-a3-b1/F_81` | 8.9 MB | 88 MB | 9.98× |
| `rado-r4-a3-b2/F_103` | 74.8 MB | 608 MB | 8.13× |
| `rado-r4-a1-b2/F_171` | 131.2 MB | 1.11 GB | 8.48× |
| `rado-r4-a4-b1/F_256` | 167.0 MB | 1.34 GB | 8.00× |

ADR-0426 then **fixed it**, and this note nearly failed to say so. Its own
consequence table, same four certificates and same instrument:

| certificate | original | file-backed | file-backed + `u32` |
|---|---:|---:|---:|
| `rado-r4-a3-b1/F_81` | 9.98× | 3.06× | **2.13×** |
| `rado-r4-a3-b2/F_103` | 8.13× | 2.51× | **1.60×** |
| `rado-r4-a1-b2/F_171` | 8.48× | 2.45× | **1.72×** |
| `rado-r4-a4-b1/F_256` | 8.00× | 2.39× | **1.49×** |

**8.00× → 1.49×, verdicts identical, and faster** (57.0–91.6 s → 23.6–50.5 s on
`F_256` under alternating load). The 18.9 GB `rado-r4-a2-b3` certificate went
from uncheckable on every host in the fleet to checkable on s0 and s4.

So "we can produce proofs we cannot check" was true when ADR-0426 was written
and is not true now. Anyone reasoning from the 8× figure — including the first
draft of this note, and the `docs/refactor-2026-08/README.md` line about "6.6×
since reduced to 1.5×" — is reasoning from a superseded measurement.

What remains is the residue ADR-0426 names:

> Backward checking is still not a pure stream — the proof prefix up to the
> empty clause is walked in reverse and has to be **indexable**.

Separately, measured live on the in-flight b=3 *solve*: resident memory grows
about **1.14 bytes per byte of proof**. That is the solver, not the checker —
expected for CDCL, since every learned clause lives in both the clause database
and the proof file — and it is why a 30 GB certificate implies a ~30 GB process
while searching. The two numbers are about different processes and must not be
added carelessly.

## The three techniques, judged against that

### `mmap` — aimed at the residue, and the prize is smaller than it looks

"Has to be indexable" and "has to be resident" are different requirements, and
only the first is real. A memory-mapped file is indexable at zero resident cost:
the kernel pages it in on fault and evicts under pressure, so a reverse walk over
a 30 GB prefix costs page cache rather than heap. `MADV_SEQUENTIAL` for the
forward parse and `MADV_WILLNEED` ahead of the reverse scan make the access
pattern explicit rather than leaving it to readahead heuristics.

**Size the prize honestly.** This is 1.49× → sub-1×, not 8× → 1×. `cake_lpr`,
the formally verified checker, needs memory "around the size of the proof file",
so ~1× is the state of the art and we are already within 50% of it. Going
sub-1× would be ahead of the field — a real result, not an unblocking one.

**Constraint that makes this an ADR, not a dependency bump:** `unsafe_code` is
denied workspace-wide, and `memmap2::Mmap::map` is `unsafe` — necessarily, since
another process truncating the file turns a mapped read into SIGBUS. Any
adoption needs an ADR that states the file-stability assumption and how it is
enforced (the checker owns the file, or it is opened O_RDONLY on a path nothing
else writes).

### `posix_fadvise(DONTNEED)` — aimed at a different constraint we have

Writing 30 GB of write-once certificate pushes 30 GB through page cache and
evicts everything else on the box. That is not theoretical here: three build
lanes were competing for cache during the run. Dropping written pages after the
sink flushes them is a two-line change with no alignment requirements.

`O_DIRECT` is the heavier version of the same idea and is the **wrong** tool for
the read side: it bypasses page cache, which is exactly what you want to keep for
a proof you re-scan. Reach for `fadvise` on the write path, not `O_DIRECT`
anywhere.

### `io_uring` — aimed at nothing we have

Searched the SAT proof-checking literature through 2026, including the new DFG
"Proofs as Big Data" project (Heule, Biere, Tan). No use of it, and the reason is
structural rather than conservatism: io_uring buys batched asynchronous
submission and low syscall overhead, and our bottleneck is a resident index, not
I/O latency or queue depth. A checker that faults on mapped pages is already
doing the right amount of I/O; making those faults asynchronous does not shrink
the index. **Recommend against** until a profile shows I/O wait, which today it
does not.

## The bigger lever is the format, not the plumbing

The field's answer to checking cost is not I/O engineering, it is LRAT: hints in
the proof turn checking from a search into a linear forward pass. We already have
`elaborate_drat_to_lrat` and `elaborate_drat_to_lrat_backward` in
`crates/axeyum-cnf/src/lrat.rs`.

Two external calibration points worth having:

- **`cake_lpr`, the formally verified checker, needs memory "around the size of
  the proof file."** ~1× is the state of the art, not a floor we are failing to
  reach — and at 1.49× we are already close to it.
- **The Lean proof-term route caps out well below our proof sizes.**
  [LRAT-Catcher](https://arxiv.org/html/2607.00815v1) (July 2026) reports
  Mathlib's `lrat_proof` peaking at **96.6 GB on a 628 MB Schur certificate**,
  because it embeds the formula in the proof term, against **8.9 GB** for native
  reflection on the same instance. Our in-flight certificate is ~30 GB, roughly
  50× that Schur instance. **This is a strategic input, not a footnote:** the
  Lean-parity story for large combinatorial results has to run through
  reflection, not through explicit proof terms, and no amount of I/O work changes
  that.

## What this does not change

The running solve is unaffected. If the in-process check exhausts memory at the
end, `akb2_frontier check` exists precisely so "a proof can be moved to a host
that can afford to check it rather than being re-derived there" — the DRAT on
disk survives, so the failure costs the convenience and not the search.

## Sources

- [DRAT-trim: Efficient Checking and Trimming Using Expressive Clausal Proofs](https://www.cs.utexas.edu/~marijn/publications/drat-trim.pdf)
- [cake_lpr: Verified Propagation Redundancy Checking in CakeML](https://cakeml.org/tacas21.pdf)
- [Verified LRAT and LPR Proof Checking with cake_lpr (SAT Competition 2025)](https://satcompetition.github.io/2025/downloads/checkers/cakelpr.pdf)
- [Faster LRAT Checking Than Solving with CaDiCaL (SAT 2023)](https://drops.dagstuhl.de/storage/00lipics/lipics-vol271-sat2023/LIPIcs.SAT.2023.21/LIPIcs.SAT.2023.21.pdf)
- [LRAT-Catcher: Importing SAT Solver Certificates into Lean 4 by Reflection](https://arxiv.org/html/2607.00815v1)
- [Proofs as Big Data (DFG project)](https://satres.kikit.kit.edu/news/2025-11-11-dfg-proofs)
