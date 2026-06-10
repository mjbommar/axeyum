# SAT Core State

Status: draft
Last updated: 2026-06-10

## Purpose

Document the central state and invariants of a CDCL SAT solver.

## Scope

In scope:

- Clause storage, assignments, trail, watch lists, activities, and learned clauses.

Out of scope:

- A complete CDCL implementation spec.

## Core Claims

- SAT performance depends heavily on compact memory layout and propagation speed.
- Two-watched-literal propagation is the core hot path.
- Learned clause management and restart policy are as important as the base algorithm.
- A custom SAT core should start after Axeyum has real generated CNF benchmarks.

## Core State

```text
assigns: Vec<LBool>
trail: Vec<Lit>
trail_lim: Vec<usize>
reason: Vec<Option<ClauseId>>
level: Vec<u32>

watches: Vec<Vec<Watcher>>
clauses: ClauseArena
learnts: ClauseArena or tagged clauses
activity: Vec<Activity>
decision_heap: Heap<Var>
```

## Clause Arena

Clauses should be compact and iteration-friendly:

```text
ClauseHeader {
  len
  lbd
  activity
  flags
}
ClauseBody = [Lit; len]
```

## Design Implications

- Avoid per-clause heap allocation where possible.
- Separate stable `ClauseId` from memory addresses.
- Keep assumption literals and proof logging in the design from the start.
- Add instrumentation counters early: propagations, conflicts, decisions, restarts,
  learned clauses, deleted clauses.

## Risks

- A safe Rust design can still be slow if it scatters memory.
- Borrow checker friction can push toward awkward layouts; design arenas explicitly.

## Open Questions

- [ ] Should the first SAT layer be trait-only with adapters to RustSAT/varisat/splr?
- [ ] Should a custom CDCL core target proof logging from day one?
- [ ] Which clause deletion policy is simplest while still useful?

## Source Pointers

- CaDiCaL: https://github.com/arminbiere/cadical
- Kissat: https://github.com/arminbiere/kissat
- splr: https://github.com/shnarazk/splr
- RustSAT: https://github.com/chrjabs/rustsat

