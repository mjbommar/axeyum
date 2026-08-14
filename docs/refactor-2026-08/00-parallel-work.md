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

### Shared append points — protocol, not avoidance

`PLAN.md` and `docs/research/09-decisions/README.md` were clobbered by
concurrent lanes **four times on 2026-08-14**. Pathspec discipline does not
help: it stops you sweeping files you did not touch, not two lanes legitimately
touching the same one. The session protocol *instructs* every lane to edit
`PLAN.md`, so the instruction is the defect.

Until that is fixed:

- **write no ADR while that lane is live** — the index is touched 60 times a
  day and every ADR appends to it. Record decisions in this folder and link
  inward; convert to ADRs when the lane goes quiet.
- **make no `PLAN.md` edit** for the same reason.
- **tag every commit with an `Agent:` trailer.** Every commit in this checkout
  carries the same git author, so `git log` attribution is otherwise
  unrecoverable — two lanes and this session all misattributed commits on the
  same day.

Note the slope: the ADR index is growing at **~65 per day** against a 455
baseline. Engineering `04`'s governance point is not static.

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
