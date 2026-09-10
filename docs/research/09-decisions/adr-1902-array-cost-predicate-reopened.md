# ADR-1902: ADR-1814's falsifier 1 has fired — build the array cost predicate, at `abv.rs:739` and *before* the admission rewrite, but pin the threshold behind two measurements, one of which is new

Status: accepted (supersedes ADR-1814 commitment 2 only; its commitments 1, 3 and 4 stand)
Index-summary: Roadmap 3.8's public-corpus measurement is exactly the falsifier ADR-1814 named, so the cost-based staged eager/lazy rule is now a BUILD — but not for the reason roadmap 4.2 gives (the `MAX_ARRAY_EQ_INDEX_BITS = 8` cap is a route selector, re-confirmed, and deep store chains never reach it). Two constraints neither 4.2 nor 3.8 states: the predicate must run BEFORE the `abstract_arrays_counted` call at `abv.rs:739`, because that call IS the read-over-write expansion rather than a cheap probe; and `abstract_arrays` and `eliminate_arrays` share that rewrite verbatim, differing only by the appended Ackermann set, so how much of the measured 2.5 M-node blow-up a reroute actually avoids is UNMEASURED and is a second prerequisite.
Index-status: accepted — supersedes ADR-1814 commitment 2
Date: 2026-09-10

## Context

[ADR-0010](adr-0010-arrays-via-eager-elimination.md) chose eager array
elimination. Roadmap item 4.2 proposed keeping it but adopting STP's staged
cost rule.
[ADR-1814](adr-1814-staged-eager-lazy-arrays.md) (2026-09-09) declined **for
now**, on two findings that were correct then and are correct now: the
`MAX_ARRAY_EQ_INDEX_BITS = 8` cap is a *route selector*, not a refusal, on the
main QF_ABV route; and the certificate a cost rule would trade away is not on
the shipping evidence path, so the trade could not be priced. It named five
things that would say it chose wrong. The first reads:

> **A public QF_ABV corpus measurement (roadmap 3.8) showing eagerly-admitted
> deep store chains cost us decided instances at a realistic budget.**

That measurement landed the next day:
[`docs/research/03-measurements/array-store-chain-gap-2026-09-10.md`](../03-measurements/array-store-chain-gap-2026-09-10.md).
Its finding is the falsifier verbatim — on the `brummayerbiere/wchains*` family
(104 files in SMT-LIB-2024 `QF_ABV`), the default solve path returns `unknown`
from depth ~240–320 and reaches **23.4 GB RSS at depth 800**, while
`eliminate_arrays` itself succeeds in 1.5 s. Its §6 recommendation is **BUILD,
scoped to a cost predicate**.

So the question is not whether to reopen — ADR-1814 pre-committed to that. It
is what, precisely, to build, and what has to be true before a threshold is
chosen.

## Decision

**ADR-1814 commitment 2 ("no cost predicate is added now") is superseded: build
the cost-based admission test. It goes at `crates/axeyum-solver/src/abv.rs:739`,
*ahead of* the `abstract_arrays_counted` call, and its threshold is not chosen
until two measurements exist — 3.8's own named follow-up, and a second one this
ADR adds. ADR-1814's commitments 1 (ADR-0010 stands), 3 (wire
`certify_array_elim_unsat` through `evidence.rs`) and 4 (the cap is a separate
question) are unchanged, as is its stated bound: a cost rule may route a query
to an uncertified arm only if the certified share of QF_ABV unsat verdicts is
measured before and after, and the drop reported rather than discovered.**

Five commitments.

### 1. The motivation in roadmap 4.2 is wrong and is not adopted

Roadmap 4.2 says the point of the staged rule is "to remove the
`MAX_ARRAY_EQ_INDEX_BITS = 8` refusal". It is not, and building toward that
sentence would build the wrong thing.

Re-verified at `60fe8bdf2`: `const MAX_ARRAY_EQ_INDEX_BITS: u32 = 8;` is still
at `crates/axeyum-rewrite/src/arrays.rs:31`, still raises
`ArrayElimError::Unsupported` at `:461-466`, and that error is still consumed as
the **lazy trigger** at `crates/axeyum-solver/src/abv.rs:739-744`, comment and
all. 3.8 §3.1 confirmed the consequence independently: of 267 committed QF_ABV
files, calling `eliminate_arrays` directly fails on 22, of which 13 cross the
cap — and **all 22 are decided** (12 sat / 10 unsat, no timeout) by the shipped
route. The cap costs zero verdicts.

**Deep store chains never reach that arm at all.** 3.8 §6 states it plainly:
`eliminate_arrays` never returns `Unsupported` for a deep chain — it succeeds,
slowly, at whatever size the chain demands. The cap and the blow-up are disjoint
problems, and the cost predicate addresses only the second.

### 2. The predicate goes at `abv.rs:739`, and it must run BEFORE the call there

This is the constraint that decides whether the build works, and no input
document states it.

`abv.rs:739` reads:

```rust
match abstract_arrays_counted(arena, assertions) {
    Ok(_) => return check_qf_abv_lazy(backend, arena, assertions, config),
    Err(ArrayElimError::Ir(inner)) => return Err(SolverError::Backend(inner.to_string())),
    // The refused case: engage the lazy-ROW path below.
    Err(ArrayElimError::Unsupported(_)) => {}
}
```

It is natural to read that `match` as a cheap capability probe and to add a cost
test to its `Ok` arm. **That would be a no-op on cost.**
`abstract_arrays` (`arrays.rs:221-249`) runs `Eliminator::rewrite` over every
assertion, building the whole post-read-over-write expansion into the arena
before it returns `Ok`. By the time the `Ok` arm is entered, the multi-million
node formula 3.8 measured **already exists**.

The predicate must therefore be a **syntactic scan of the original assertions**
— store-chain length along the array edge, and select count per chain — run
before line 739, in the shape of 3.8's own throwaway probe (a memoized DAG walk,
O(n) on a `let`-shared chain). Where it fires, control goes straight to the
lazy-ROW path below the `match`, which — verified — performs no
`abstract_arrays` / `eliminate_arrays` call of its own after the fallthrough.

### 3. A second prerequisite this ADR adds: the eager/lazy delta is unmeasured

3.8 §8 already names the prerequisite it could not run: **force the lazy-ROW
path directly on `wchains060`–`wchains200` and confirm it decides them fast.**
That stands, and no threshold should be chosen without it.

There is a second, and it is sharper. `abstract_arrays` and `eliminate_arrays`
are the *same rewrite*:

- `arrays.rs:236-241` (`abstract_arrays`) and `:274-278`
  (`eliminate_arrays`) both build a fresh `Eliminator` and call
  `ctx.rewrite(arena, assertion)` over the identical loop.
- `eliminate_arrays` then does one extra thing:
  `rewritten.extend(ctx.ackermann_constraints(arena)?)` (`:281`).
- `abstract_arrays_counted`'s own doc comment (`abv.rs:560-566`) says as much:
  "the two forms accept and refuse exactly the same queries", and the Ackermann
  set is "pure waste" on the lazy path — 1,233,416 constraints built twice and
  discarded on one KLEE file.

So the read-over-write ITE expansion — one `ite` per store link per read, the
thing that is quadratic in reads × depth and the thing STP's comment describes
— is in the **shared** half. 3.8 measured `dag_out = 2,563,409` at depth 800
through `eliminate_arrays`, and did **not** decompose it into
read-over-write versus Ackermann.

That decomposition is load-bearing. If the expansion is overwhelmingly
read-over-write, then the arm a cost predicate routes *away from* and the arm it
routes *to* differ by much less than the numbers suggest — and the fix is a
different one (Boolector-style lambda/memset recognition, or a lazy read-over-
write, both of which 3.8 explicitly declined to reach for). If it is
substantially Ackermann, the reroute is close to free. **Measure the split
before choosing a threshold.** It is one probe run twice, on the same wchains
ladder 3.8 already built.

### 4. The threshold, when it is chosen, is reads × depth — and STP's constants are second-hand

3.8's driver finding is that **depth alone does not predict cost**: a 595-file
KLEE family at depth 256 solves in 18.3 s using 68 MB, two orders of magnitude
cheaper than `wchains060se` at depth 240. The distinguishing quantity is
reads-per-chain-position. A depth-only cap would refuse the KLEE family for
nothing.

On STP's own numbers, this ADR inherits ADR-1814's correction and adds nothing:
`arrayReadLimit = 10` (50 under `--ackermannisation`) and
`arrayEagerCostPerRead = 20`, with the threshold the *product*; "expansion
< 200" is a derived default, not a source constant. **This remains a
second-hand citation.** Re-checked at `60fe8bdf2`: `references/` contains one
file, `README.md`, and `scripts/fetch-references.sh` lists 20+ repositories
(cadical, kissat, bitwuzla, carcara, ethos, …) but **not STP** — positive
control: the same grep finds `cadical`. Treat 10 and 20 as a starting point to
calibrate against our own curve, never as constants to transplant.

### 5. Sequencing against commitment 3 stays as ADR-1814 set it

`certify_array_elim_unsat` still has **zero** occurrences in
`crates/axeyum-solver/src/evidence.rs` — re-verified, `grep -c` → `0`; its only
non-test callers remain `crates/axeyum-machine-evidence/src/symbolic_memory.rs:344`
and `:409`. ADR-1814's sequencing argument for doing the wiring first is
untouched by 3.8 and is not superseded: doing both at once makes the resulting
certified-share number uninterpretable. What 3.8 changes is the *priority* of
the cost predicate, not the *order* relative to the wiring — and 3.8 §3.2 makes
the same point from the other side ("the certificate isn't shipping either
way").

## Evidence

Re-verified in this worktree at `60fe8bdf2`; each is a single command or a
single file read.

- `crates/axeyum-rewrite/src/arrays.rs:31` — `const MAX_ARRAY_EQ_INDEX_BITS: u32 = 8;`, unchanged.
- `crates/axeyum-solver/src/abv.rs:739-744` — the `Unsupported`-as-lazy-trigger
  match, unchanged, with its comment.
- `crates/axeyum-rewrite/src/arrays.rs:221-249` vs `:261-289` — the two
  functions, identical rewrite loop, differing only at `:281`.
- `crates/axeyum-solver/src/abv.rs:560-566` — the doc comment stating both
  forms accept and refuse the same queries.
- `grep -c certify_array_elim_unsat crates/axeyum-solver/src/evidence.rs` → **0**.
- `awk 'NR>=729 && NR<=1100' crates/axeyum-solver/src/abv.rs | grep -n 'abstract_arrays\|eliminate_arrays'`
  → only the admission match itself; the ROW path below it calls neither.
- No array cost predicate exists anywhere: a search for
  `array_read_limit|arrayReadLimit|eager_cost|expansion_cost|eager_admission`
  over `crates/` returns only `retained_warm_array_read_count` /
  `retained_warm_structural_read_count` (`incremental.rs:1005`, `:1012`),
  which are warm-solver telemetry, not admission. The nearest analogue in the
  tree is still for UF: `refuse_oversized_ackermann` (`euf.rs:119`, called from
  `combined.rs:86` and `auto.rs:3672`).
- `ls -a references/` → `README.md` only; `grep -i stp scripts/fetch-references.sh`
  → nothing, with `grep -ic cadical` → 1 as the positive control.
- The corpus numbers, the depth distributions, the cost curve and the 23.4 GB
  boundary are 3.8's, cited not re-run — this lane does no heavy compute. They
  are the input, and they are the thing a referee should re-run first.

## Alternatives

- **Keep ADR-1814 as it stands (no cost predicate).** Rejected: ADR-1814
  pre-committed to reversing on exactly this observation, and refusing to
  reverse when a pre-registered falsifier fires is how a decision record becomes
  decoration.
- **Adopt roadmap 4.2 as written — the staged rule, motivated by the cap.**
  Rejected: the motivation is false (commitment 1), and building to it would
  produce a predicate aimed at a route selector that costs no verdicts, while
  leaving the wchains tail exactly where it is.
- **Choose STP's 10 × 20 now and ship it.** Rejected: transplanting a constant
  from a solver whose source is not in this tree, onto a cost curve we have
  measured only through the eager arm, is the shape that put
  `TickEffort::bootstrap_reference` 1.69× below its own useful window (roadmap
  3.2). Calibrate against our own numbers.
- **Add the cost test in the `Ok` arm at `abv.rs:740`.** Rejected on the
  measurement in commitment 2: the expansion is already built by then. Recorded
  as an alternative rather than omitted because it is the reading the code
  invites.
- **Build Boolector-style lambda / memset recognition instead.** Deferred, as
  3.8 recommends — a bigger encoding-level change (symbolic ranges) that no
  measurement yet motivates. But note it becomes the *live* option, not the
  deferred one, if commitment 3's decomposition says the blow-up is
  read-over-write rather than Ackermann, because then rerouting between arms
  cannot help and only a better encoding can.
- **Declare 4.2 blocked pending the two measurements.** Rejected: the direction
  is decided by 3.8 and the two constraints above are decisions in their own
  right — where the predicate goes, and what has to be measured before a
  number is written down. Only the *threshold* is deferred, and it is deferred
  to two named, runnable measurements.

## Consequences

**What this buys.** The `wchains`-shaped tail gets an owner, and the
implementation starts from the right line of code rather than the inviting one.
The roadmap's motivation for 4.2 stops propagating: anyone who builds this to
"remove the cap" builds the wrong predicate, and that sentence is now
contradicted in writing.

**What is LOST by deciding this way.**

- **It is still not built, and now it has two prerequisites instead of one.**
  ADR-1814 deferred on a wiring prerequisite; this ADR keeps that and adds a
  measurement. Every wchains-shaped instance stays `unknown` in the meantime.
  If the decomposition in commitment 3 comes back "mostly Ackermann", that delay
  bought nothing and the predicate could have shipped a cycle earlier.
- **The certified share will fall when this lands, by construction**, and
  ADR-1814's bound requires it be measured before and after. Nobody has measured
  the "before" — it is 0 today only because `certify_array_elim_unsat` is
  unwired, so the "before" number is a moving target that depends on commitment
  3 landing first. If the predicate ships before the wiring, the drop is
  unmeasurable and ADR-1814's bound has been violated silently rather than
  waived openly.
- **We inherit an unverified provenance.** STP's rule is still second-hand and
  `references/stp` is still absent. If a lane later fetches STP and the rule or
  the "48x" comment reads differently, the design being calibrated against is
  not the design STP ships.

## What would falsify this decision

1. **The decomposition (commitment 3) shows the blow-up is overwhelmingly
   read-over-write.** Then eager and lazy differ by a small constant on this
   shape, a cost predicate reroutes between two equally bad arms, and the item
   should be re-decided as an *encoding* problem (lazy read-over-write, or
   lambda recognition) rather than an admission one.
2. **The forced lazy-ROW run on `wchains060`–`wchains200` (3.8 §8) is also
   slow.** 3.8 says this in as many words: "if the lazy path is *also* slow on
   this shape, a cost predicate alone doesn't fix the underlying problem."
3. **A reads × depth predicate calibrated on `wchains` misroutes the KLEE
   family.** 595 organic files at depth 256 currently solve in seconds on the
   eager arm; a predicate that moves them is a regression on real-world input
   traded for a synthetic torture family, and the threshold is wrong.
4. **The 42 excluded `QF_ABV` files >5 MB (up to 1.17 GB), or the unsampled
   `QF_AUFBV` set, turn out to hold a shape neither arm handles.** 3.8 excluded
   them explicitly; they are the largest unmeasured region and could change what
   the predicate should be measuring.
5. **`references/stp` is fetched and the quoted rule reads differently.**
   Inherited unchanged from ADR-1814 falsifier 5.
