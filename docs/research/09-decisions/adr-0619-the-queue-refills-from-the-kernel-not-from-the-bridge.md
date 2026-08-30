# ADR-0619: The queue refills from the kernel, not from the bridge

Status: accepted
Date: 2026-08-30
Index-summary: The refill pool grows by DECLARING constants, not by widening the statable screen; the bridge is capped at +9 constants by a fixed 202-row catalog, and `instSubNat` alone gates 292 rows it can never admit

Related: ADR-0542 (held-out isolation), ADR-0615 (evaluation envelope),
ADR-0616 (the ceiling counts attestation), ADR-0601 (three producers, one
trust anchor)

## Context

The flywheel's input queue is the set of `ml430` mirrors that are open, not
held-out, not a mutation control, and not blocked by a construction-level
divergence. It has been hand-refilled four times. On 2026-08-30 it stood at
**3 dispatchable rows**, all three needing the same missing keystone (totient
multiplicativity), so its effective depth was one.

Two things were true and neither was written down.

**A "draw" is a source edit, not an operation.** `gen-autogenesis-nursery-
refill.py` emits `PER_FAMILY * len(FAMILY_MODULES)` rows from two module-level
dicts. Re-running it unchanged is a byte-level no-op that prints
`AUTOGENESIS_NURSERY_REFILL_OK` and adds nothing. Draws 2, 3 and 4 were all
authored by hand on one day; nothing has run since. So "refill the queue" was
never a command anyone could issue, and nothing computed whether a refill was
even possible.

**The queue drains far faster than draws are authored.** Draw 4 put 110
non-held-out rows into the population; 107 were settled within a day. The
partition rule takes `ceil(n/3)` of each draw's new families for held-out — a
restart per draw, not a running cycle — so the committed manifest is 45%
held-out, not 33%. A draw therefore buys roughly one day of throughput.

## The measurement

The pinned pool is `mathlib-v4.30.0-nat-int-statement-inventory-v2.ndjson`,
9,729 records. Screened through the divergence registry, the hygiene filter,
the statable-here vocabulary, the glyph screen, and the already-drawn set:

| | |
| --- | --- |
| not statable here | 5,399 |
| hygienic or generated | 1,699 |
| already drawn | 200 |
| blocked by the divergence registry | 136 |
| **survivors** | **2,295** across 94 modules |
| **ready families** (>= 10 survivors, module not already owned) | **19** |

So the queue *can* be refilled, comfortably, without going near a held-out row.
A draw of all 19 ready families would add 120 dispatchable rows.

The question this ADR settles is what happens after that.

## The finding: two growth routes, wildly asymmetric

A rejected candidate names at least one Lean constant outside
`admissible = env | bridge`, where `env` is 2,207 declarations read from
`kernel.environment()` and `bridge` is 70 constants **derived** from settled
mirrors. **1,314 rejected rows are blocked by exactly one missing constant**,
across 166 distinct sole-blockers. Those unlock by one of two routes.

**Route 1 — grow the bridge. Capped, and the cap is small.** S2 requires every
bridge constant to be witnessed by a SETTLED mirror, and the witnesses come from
`mathlib-nat-int-fact-catalog-v1.json`: **202 rows, 162 settled, sharing zero
source names with either nursery manifest.** Settling all 40 remaining catalog
rows would take the bridge from 70 to 79 constants and the unused-statable pool
from 2,354 to 2,526 — **+9 constants, +172 candidates, and then nothing.** The
catalog is a fixed population and is not growing.

**Route 2 — declare the constant.** Refreshing the environment snapshot
(`--snapshot-from shape_search`) admits everything the kernel has learned to
name. The largest sole-blockers of this kind are the Int division family —
`Int.lcm` (79 rows), `Int.bmod` (73), `Int.fmod` (60), `Int.fdiv` (58),
`Int.tdiv` (54), `Int.sign` (37), `Int.tmod` (34) — plus `Nat.nth`, `Nat.dist`,
`Nat.centralBinom`, `Nat.bodd`. These are real mathematical content this kernel
has genuinely not built. Building one is ordinary proof work and it pays for
itself in population.

**So: the queue refills from the kernel, not from the bridge.** That is the
decision, and it inverts the instinct the numbers first suggest — the bridge
looks like the cheap lever because it is a JSON file, and it is the one with a
hard ceiling.

## The exception, and it needs a decision rather than a screen change

`instSubNat` is the sole blocker of **292 rows** — more than the entire draw-4
population — and it is pure **elaboration**, not content:

- `Nat.sub` is already in the environment.
- `instAddNat`, `instMulNat`, `HSub.hSub` and `instHSub` are already bridged.
- So the `Sub Nat` instance is the missing sibling of four constants the bridge
  already has.
- **No catalog row mentions it**, so S2 can never admit it.

The same shape holds for `GT.gt` (17 rows), `GE.ge` (13) and `NatCast.natCast`
(14) — notation abbreviations with no kernel counterpart and no witness.

These are not unstatable propositions. They are propositions the screen **cannot
see are statable**. That is a false negative in a screen whose false positives
this repository has been careful about and whose false negatives nobody had
measured.

## Decision

1. **The statable screen stays as it is.** It is not a hand-written word list
   and must not be loosened into one: `env` is read from the kernel and the
   bridge is derived, never asserted. Every rejection names a constant this
   kernel does not declare. Widening it by hand would reintroduce exactly the
   "population nobody can close" failure the screen was built to stop.
2. **Pool growth is a KERNEL activity.** When the pool tightens, the response is
   to declare a blocking construction and refresh the environment snapshot — not
   to touch the vocabulary. `propose-nursery-refill.py` publishes
   `top_sole_blockers` so the highest-yield target is visible without anyone
   re-deriving it.
3. **A pure-elaboration sole-blocker is a recorded exception, not a silent
   bridge entry.** Admitting `instSubNat` requires a decision that says why it
   is elaboration rather than content, with the witness recorded — because "it
   looks like an instance" is exactly the reasoning that would let anything in.
   This ADR does not admit it; it records the 292 rows it costs so the trade is
   visible when someone chooses.
4. **The frontier gate fails at a floor, not at zero** (`FLOOR = 10`, G7), and
   `--floor` is a one-way ratchet. A gate that fires when the queue is empty has
   told you after every lane is already blocked, and a refill needs lead time
   because it is a hand edit.
5. **`propose-nursery-refill.py` is the standing answer to "can it be
   refilled".** Its R3 fails when the ready families cannot yield enough rows to
   clear the floor. That is the terminal condition for the whole flywheel and
   nothing computed it before.

## Consequences

- The gate is RED on the tree that adopts this, at 3 dispatchable against a
  floor of 10. That is the true state. It goes green when someone authors a
  draw, which `propose-nursery-refill.py` now reduces to picking two names off a
  printed list.
- The pool is finite and its size is now published and re-derived on every gate
  run rather than re-measured by hand.
- A held-out row is never the answer to a low queue. R3's failure text says so,
  because a starved queue is exactly the pressure under which spending one
  starts to look reasonable.

## What would change this decision

Measured evidence that a bridge entry can be witnessed without a settled mirror
in a way that cannot be abused — or a catalog that grows, which would lift
route 1's ceiling. Neither exists today.
