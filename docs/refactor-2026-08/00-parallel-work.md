# 00 — Parallel work: who owns what, and what that changes

Both strands were written as if one party would execute them. That is not the
situation. This document records the measured ownership picture and the
re-ordering it forces, and **both strands defer to it**:
[engineering](README.md) · [mathematics](../mathematics-2026-08/README.md).

## The other lane, measured

A second session — driven by the codex CLI, and **not reachable from this one**
— has been working continuously in this checkout. Measured 2026-08-14 over its
`feat(lean)` / `docs(plan)` commits:

| its territory | touches in 24h |
|---|---:|
| `PLAN.md` | 67 |
| `docs/research/09-decisions/README.md` (the ADR index) | 60 |
| `crates/axeyum-lean-kernel/src/nat_prelude.rs` + its tests | 49 each |
| `docs/plan/lean-kernel-requirements-2026-08-13.md` | 12 |
| `crates/axeyum-lean-kernel/tests/rado_sharp_factorization.rs` | 9 |
| `crates/axeyum-lean-kernel/src/{prelude,lib,tc,env,lean_pp,int_prelude,arith_prelude,string_prelude,lean_export}.rs` | 1–5 each |
| new ADRs `adr-0387` … `adr-0452` | ~65, roughly one per theorem |

**69 commits in 24 hours.** It effectively owns all of
`crates/axeyum-lean-kernel/`, and reaches occasionally into `axeyum-solver`'s
reconstruction files.

## The partition

### Uncontested — no touch by that lane, safe to work now

| area | strand item |
|---|---|
| `axeyum-cas/` and `axeyum-solver/src/nra_real_root.rs` | eng `02` W2 (one real-algebra engine); math `01` (widen the certifying path) |
| `axeyum-search/src/colouring.rs`, `axeyum-cnf/src/colouring.rs` | eng `02` W3 (one encoder, and the parity gate its comment promises) |
| `axeyum-scenarios/` | eng `01` K2 (UNSAT evidence route for `Int`/`Real`) |
| `axeyum-solver/src/nra.rs` and the rewrite passes | eng `01` K3 (integer bound strictness, product abstraction) |
| `axeyum-solver/src/capabilities.rs` | math `01` (generate the capability table instead of hand-maintaining it) |
| `docs/curriculum/` | eng `01` K5, math `04` (re-derive `covered` from evidence) |
| `docs/internals/architecture.md` | eng `04` T3 (11 of 23 crates documented) |
| `scripts/` | eng `04` G2 (clippy exiting 0 over a cached warning) |

### Contested — do not start

**All of `crates/axeyum-lean-kernel/`.** This includes the item both strands
named as the keystone: **constructing ℤ from proved ℕ**. `int_prelude.rs`
cannot be built without `nat_prelude.rs`, which that lane rewrites every few
minutes.

**That is the right outcome, not a compromise.** Its recent commits are
extended-Euclidean and Bézout certificates, gcd's universal property, and
divisibility bridged through executable remainder. **It is already building
toward ℤ.** Contesting the file would slow the very thing the strands identify
as the keystone.

Also contested for the same reason: the two `nat_prelude.rs` hazards recorded in
math `02` — the `:8090` `.expect(...)` panic and the O(n³) bubble sort in
`prove_left_sum_permutation`. Both are real; neither is ours to fix.

### Shared append points — FIXED 2026-08-14 (lane `append-points`)

`PLAN.md` and `docs/research/09-decisions/README.md` were clobbered by
concurrent lanes **four times on 2026-08-14**. Pathspec discipline does not
help: it stops you sweeping files you did not touch, not two lanes legitimately
touching the same one. The session protocol *instructed* every lane to edit
`PLAN.md`, so the instruction was the defect.

Both are now **generated views over per-lane sources**, so there is nothing left
to clobber:

- `PLAN.md` ← `docs/plan/status/<lane>.md` (one file per lane; lane blocks and
  landed-changes rows merged deterministically) + `docs/plan/global/*.md` (the
  project-wide sections, still hand-authored and deliberately so).
  `python3 scripts/gen-plan.py`, gated by `--check`.
- the ADR index ← each `adr-*.md`'s own front matter (`Index-summary:` /
  `Index-status:` carry the curated row text that previously existed only in
  the index) + `README-preamble.md`. `python3 scripts/gen-adr-index.py`, gated
  by `--check`.

Both gates run in `scripts/check.sh` and `just check` (`generated-trackers`).
Writing an ADR or a lane status update while another lane is live is now safe.

- **tag every commit with an `Agent:` trailer.** Every commit in this checkout
  carries the same git author, so `git log` attribution is otherwise
  unrecoverable — two lanes and this session all misattributed commits on the
  same day. Identity is `export AXEYUM_AGENT=<lane>` in your environment,
  per-process: the first version of the hook read a repo-local git config key,
  which was a third shared append point of exactly the same shape (one lane set
  it and the next lane's commits were stamped with the wrong name).

Note the slope that made this urgent: the ADR index was growing at **~65 per
day** against a 455 baseline. A generated index does not care.

## What this changes in the ordering

Both strands said "the keystone first". **We cannot do the keystone.** So the
work re-orders into *what the keystone will need the moment it lands*:

1. **`axeyum-scenarios` Int/Real evidence route** (eng `01` K2). The single
   highest-value uncontested item. When ℤ lands, results about it still cannot
   carry a negative control until this exists — today the crate
   `unreachable!()`s on `Sort::Int` and `Sort::Real`. Build the receiver while
   the other lane builds the thing.
2. **Integer bound strictness + product abstraction** (eng `01` K3). Measured
   as `unknown`-at-20s → 0 ms on both bounding steps of the `k=3` critical leaf.
   Independent of the library.
3. **Gates: G2 and the architecture doc** (eng `04`). Cheap, uncontested, and a
   precondition for anything that moves files.
4. **One real-algebra engine, one colouring encoder** (eng `02` W2/W3). Pure
   duplication removal in files nobody else is in.
5. **Curriculum `covered` flags re-derived from evidence** (math `04`, eng `01`
   K5). Cheap, and it stops the routing table asserting coverage of sorts that
   cannot carry evidence.

**Deferred while that lane is live**, beyond the contested crate:

- **eng `02` W1 (kernel reuse).** It touches `axeyum-lean-kernel/src/{env,lib}.rs`
  *and* six `axeyum-solver` reconstruction call sites the lane also edits. The
  measurement stands (26 ms vs 6.6 µs, ~4,000×, on a library that grew 2.6× in
  one session) and it gets *more* valuable as the library grows — but it is the
  worst possible file set to contest.
- **eng `03` (solver decomposition).** Already sequenced last; this is a second
  reason. Moving files that another lane edits occasionally is how a merge goes
  wrong quietly.

## Re-check before starting

This picture is a snapshot. Before taking any item:

```
git status --short                       # who is holding what right now
git log --since="2 hours ago" --name-only --format=""  | sort | uniq -c | sort -rn
```

If the other lane has gone quiet, the contested set collapses and the keystone
becomes available — at which point the ordering above reverts to the one in each
strand's README.

## Using the other hosts — a verified recipe, because three lanes got this wrong

`s0 s1 s4 s5 s6 s7` are reachable over ssh and all mount `/nas3/data/axeyum`
(NFS, ~15 TB). `s0` is this box. Verify before concluding otherwise:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=8 s5 'hostname; nproc; free -g | awk "NR==2{print \$7\" GB free\"}"'
```

Long work belongs in a **memory-bounded transient unit**, not `nohup`:

```sh
ssh s5 "systemd-run --user --unit=<name> \
  -p MemoryHigh=18G -p MemoryMax=22G \
  -p StandardOutput=append:/nas3/data/axeyum/<dir>/<log> \
  -p StandardError=append:/nas3/data/axeyum/<dir>/<log> \
  -p WorkingDirectory=/tmp <binary> <args>"
ssh s5 'systemctl --user is-active <name>'
```

`loginctl enable-linger` is set on s4 and s5, so such a unit survives ssh
disconnect **and** the death of whatever started it. That matters: `systemd-oomd`
killed this box's entire session cgroup on 2026-08-14 (68.36% pressure for >20 s,
27 processes, 83.6 GB peak), taking a 2¼-hour solve and two watchers with it.
It kills by **cgroup**, so `nohup` does not help and bystanders die with the
cause. A binary staged to `/nas3/data/axeyum/bin/` runs on any of them.

**Three lanes in one day concluded a resource was unavailable without checking:**
one ran `which lean`, got nothing, and reported no toolchain — Lean 4.30.0 was
installed under `~/.elan/toolchains/`, merely off `PATH`, and seven test suites
had been printing `ok` while checking nothing. One reported `/data0` as the
scratch disk without noticing it is root-owned and unwritable. One reported
`server0` as "the only machine available" while `ssh s5` worked. The shape is
always the same: a plausible probe returned empty, and empty was read as a fact
about the world. Confirm the probe covered the subject before believing its
zero.
