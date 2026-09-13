# Addendum to the pre-registration — after merging `main`, still before measuring

Lane `QBUDGET`, 2026-09-13. `PREREGISTRATION.md` is unedited; this is what
changed and what it does to the sizing. Written **before this lane's first
solver run**, and committed before the sweep launched.

## What changed

The pre-registration was written at branch point `c73eb8adf`, which was **17
commits behind** `main`. The merge is `7276aaa7a`; `git merge-base main HEAD` is
now `e542fdc3d`, which **is** `main`'s HEAD, so the base arm measures the tree
that ships. (`origin/main` is `76f4f22c6`; local `main` is one commit ahead of it
with `e542fdc3d`, a bench-results document.)

Three merged changes touch the ladder the pre-registration describes.

### 1. A reserve now sits ABOVE the ladder (ADR-1975, `727c6dac5` + `55b1e5443`)

Valid-universal elimination — which runs before rung 1 of the pre-registration's
table — took the whole remaining clock and now **ships a `share = 4` reserve**
(`quant_valid_universal_budget`, `auto.rs:5053`). So the "remaining" every rung
below slices is already a reserved remainder. Concretely: where the
pre-registration's table says rung 5 and rung 6 slice *what is left of the root
deadline*, that is now *what is left of three quarters of it*, on any file where
valid-universal elimination is reached and spends its slice.

This **does not change the direction or the one-way property** of this lane's
lever: `qinst_egraph_retry_slice` still divides whatever its caller has left, and
`share = 1` still takes all of it, which is still strictly more than any policy
on that rung can grant. It does mean the **absolute** grant in the sizing table
may be smaller than the census walls implied, which is failure mode (b) already
named in `PREREGISTRATION.md` §5. The re-derived census below says by how much.

### 2. The relationship between this lever and ADR-1975's, stated

ADR-1975's generalisable finding is the one this lane must honour:

> a one-way ceiling answers "is anything reachable?", never "what should the
> constant be" — ADR-1970 shipped OFF because its ceiling was worth nothing, and
> a lane whose ceiling IS worth something must still run the shipped value
> against the control.

ADR-1975's own numbers are the proof: its ceiling arm (`=1`) gained 19 on
`UFDTNIRA` **and lost 2 on the `UF` control, reproducibly**; `=4` gained the
identical 19 and lost 0.

The three levers are **not the same mechanism**, and the differences decide what
each can be worth:

| lever | direction | what it moves clock FROM | ...TO | ships |
|---|---|---|---|---|
| `AXEYUM_QUANT_VALID_UNIVERSAL_RESERVE` (ADR-1975) | reserve | valid-universal elimination | everything below it | **ON, share 4** |
| `AXEYUM_QUANT_EGRAPH_RESERVE` (ADR-1970) | reserve | `q:egraph` | `q:mbqi`, `q:uf-fmf-full` | OFF |
| `AXEYUM_QINST_EGRAPH_RETRY_SHARE` (this lane) | **grant** | `q:uf-fmf-full`'s unspent reserve | the retry **inside** `q:mbqi` | OFF |

The first two take clock off a rung. This one is the only one that **gives** a
rung more, and it is the only one whose donor is a rung measured not to spend
what it is given on these divisions. That is why ADR-1970's null does not settle
it: ADR-1970's ceiling moved clock onto `q:mbqi`, and `q:mbqi` hands half of
whatever it gets straight back to this same loop.

**The consequence for the ship decision, fixed now.** My lever has no moderate
value in the same direction — the shares are integers and the ceiling is `1`,
the neighbour is the shipped `2`. So if the ceiling pays on `UFNIA`/`UFLIA` **and
the `UF` control does not lose**, the ceiling IS the shipping value. If the
ceiling pays **and `UF` loses**, the correct ship is not a different share but a
**conditional**: take the whole remainder only when the reserved consumer cannot
use it (the query is not pure UF), which is exactly the asymmetry the control is
there to detect. I am recording that branch before seeing the number so the
choice cannot be made to fit the result.

### 3. The datatype rung's refusal is now a decline (ADR-1980, `76f4f22c6`)

`UFLIA`/`UFNIA` carry no datatypes, so I do not expect this to move them — and
"I do not expect" is not a measurement, which is why the census is re-derived on
the merged tree rather than inherited. The `AUFLIA` and `UF` controls are
likewise re-measured rather than quoted from ADR-1970.

## The committed census is now a hypothesis, not a baseline

`bench-results/ufnia-uflia-census-20260913/` was taken at `c281a4b22`, before all
of the above. Its give-up *distribution* is treated here as **the hypothesis to
re-derive**, and the sizing in `PREREGISTRATION.md` §5 rests on it. The base arm
of this lane's sweep carries the `bound_by` and give-up columns for exactly this
reason, so the re-derivation and the A/B come from one set of runs on one tree.

**The pre-registered numbers stand unchanged.** Point estimate **+2** net over
400 files (`UFNIA` +2, `UFLIA` +0), 80 % bracket **[0, +5]**, negative-result
threshold **net ≤ +1** after the 3×-per-arm re-check. If the re-derived census
shows the family has shrunk or moved, that is a **miss of my sizing**, reported
as one — not a reason to restate the bracket.

## Compute taken

**s5 and s6, four core pairs each (`1,9` `3,11` `5,13` `6,14`) — 8 shards.**
`s7` is left free. One division at a time, because `launch-ab.sh` restarts shard
numbering per division and two divisions launched together would put two of this
lane's own shards on one physical core.
