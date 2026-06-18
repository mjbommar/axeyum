# Lazy bit-blasting (P2.1) — measured findings and the wiring plan

Status: **measurement-grounded design note (2026-06-17).** Records what the
existing-but-unwired lazy bit-blasting lever actually does, so the next
performance step (wiring + broad measurement) is executed cleanly, coordinated,
and gated on `DISAGREE=0`. This is destination-2 (Z3-class measured speed), the
biggest open gap: axeyum decides **~2–3 of 113** real public QF_BV problems Z3
sweeps in ~1 s each, because the **default path eagerly bit-blasts everything** to
a ~1M-clause "switch-mountain" the SAT solver drowns in.

## The key fact: the lever exists, and it's NOT wired in

`solve_lazy_bv_abstraction` (`axeyum-solver/src/lazy_bv.rs`, ADR-0019) already
implements abstraction-refinement (CEGAR) bit-blasting: it abstracts every heavy
gadget (`bvmul`/`bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/`bvsmod`) by a fresh
unconstrained variable (a sound over-approximation), solves the much smaller
abstraction with the eager path, and — on a spurious `sat` — refines only the ops
whose abstraction value disagrees with their real result (bit-blasting *just
those*), re-solving to a fixpoint. Sound, complete, terminating; every `sat`
replays; `unsat` is sound by over-approximation.

**But `grep` of `auto.rs`/`backend.rs` finds no call to it — it is built but never
invoked by the default `solve()`/`check_auto` or the bench.** So the "2–3/113"
number is the eager mountain-builder; the lever that sidesteps the mountain sits
unused.

## What it actually does (measured — `tests/lazy_bv_curated_measure.rs`)

| cohort | instance | result | heavy ops blasted |
|---|---|---|---|
| **incidental** | `x=1 ∧ x=2 ∧ r=p·q` (64-bit `bvmul`) | lazy **unsat ~0 ms** (eager 17 ms) | **0 refined** — multiplier never materialized |
| **essential** | curated `mulhs08`/`stp_samples` (multiplier IS the crux) | lazy refines all → still unknown | no shortcut (= eager) |
| **selective** | curated `calypto_9` | lazy **sat in 923 ms** | only **2** of its ops refined |
| **no-op safety** | 2 small public files (no heavy ops) | lazy = eager (5 vs 8 ms; 86 vs 90 ms) | `ops=0` — zero overhead |

Reading: lazy is a decisive win when the heavy op is **incidental** (the
contradiction/model lives in non-multiplier constraints) — it decides *without
building the mountain*; it is a safe no-op when there are no heavy ops; it offers
no shortcut on pure multiplier-*equivalence* (those genuinely need the multiplier
— that's the CDCL(XOR)/algebraic frontier). The broad public QF_BV families here
(Composition/MobileDevice/StringMatching/TCP/VideoConf — software/protocol
verification) are exactly the incidental-heavy-op regime where this should move
the scoreboard, and where Z3's word-level reasoning wins today.

## The wiring plan (the high-ROL next step — likely a real jump, no new algorithm)

**Status update (2026-06-17): step 3's opt-in dispatch landed** in commit
`10a412e`. `SolverConfig::lazy_bv` (off by default) + `with_lazy_bv` route the
quantifier-free path through `solve_lazy_bv_abstraction`; the hook is
recursion-safe (inner abstraction solves run with the flag cleared) and a safe
no-op when no heavy ops are present. Verified by `tests/lazy_bv_dispatch.rs`
(routes-and-decides incidental UNSAT with 0 ops materialized; flag-off unchanged;
lazy agrees with eager on a sat model needing the heavy op). The remaining work is
the *measurement* path (steps 1–2) and the default-on decision (the tail of 3).

1. **Make it measurable (bench backend) — blocked on an arena-mutability
   impedance.** `solve_lazy_bv_abstraction` takes `arena: &mut TermArena` (it adds
   fresh abstraction symbols to the arena), but `SolverBackend::check` exposes only
   `&TermArena` and the whole bench pipeline (`solve_planned`, oracle compare,
   preprocessing) is built around the immutable-arena trait. So a drop-in
   `BackendKind::LazyBv` that just calls `solve_lazy_bv_abstraction` does **not**
   typecheck. Two clean resolutions, to be chosen in its own turn (not hacked into
   the shared `axeyum-bench/src/main.rs` mid-flight):
   - **(a) read-only entry point.** Add `check_lazy_bv_abstraction_ro(arena:
     &TermArena, …)` that copies the queried terms into a scratch `TermArena`, runs
     the existing mutable strategy there, and lifts the model back over the original
     symbols. Self-contained in `lazy_bv.rs` (not shared); the bench backend then
     fits the trait unchanged. Cost: a cross-arena term/model copy with its own
     replay test.
   - **(b) mutable-arena bench branch.** Special-case the lazy kind in `run_one`
     (which owns `mut script.arena`) to call `solve_lazy_bv_abstraction` directly,
     bypassing the `&TermArena` trait path. Smaller code, but forks the bench's
     solve/replay/oracle plumbing for one backend — more shared-file churn.
   Prefer (a): it keeps the bench's single solve path and the trait honest. Either
   way: additive edits only, commit promptly, no crate-wide fmt / destructive git
   (see the clobber post-mortem).
2. **Measure the public 113** (the big files need the bench's parallelism + memory
   caps; standalone harness only handles the 2 small ones). Headline metric: lazy
   decided-count vs the eager 2–3, with `DISAGREE=0` / 0 replay-failures the hard
   invariant. Record the per-family delta + `ops_refined` distribution.
3. **Wire into the product as a strategy.** `SolverConfig::lazy_bv` (opt-in first
   — **done**, `10a412e`), routed in dispatch when QF_BV carries heavy ops; next, a
   portfolio/strategy (try lazy when heavy ops present, eager otherwise). Default-on
   only after the public measurement (step 2) shows net benefit (an ADR, like
   ADR-0034 for word-level preprocessing default).
4. **Then deepen P2.1:** abstract *any* expensive subterm (not just mul/div),
   smarter refinement (refine the fewest ops), word-level slicing/sharing (P1.2)
   to shrink before abstracting, and P1.3 (competitive CDCL) for the bits that do
   get blasted.

## Bottom line

The single highest-leverage performance move is **not a new algorithm** — it is
wiring + measuring an already-built CEGAR bit-blaster that provably sidesteps the
multiplier mountain on the incidental-heavy-op problems that dominate real
corpora. Measured here to work and to be safe (zero overhead when nothing to
abstract); the wiring is the next focused, coordinated build.
