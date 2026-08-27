# ADR-0590: Recursive cube checking parallelizes one bounded split

Status: accepted
Date: 2026-08-26

## Context

ADR-0589 made adaptive Boolean-product proof trees checkable but retained a sequential depth-first
replay. The two completed `PRIMATEs^-1` MC=7 trees contain roughly 62 and 87 GB of DRAT data.
After about one hour, the live sequential checkers had read only 11--13 GB apiece while using one
core each. Sibling children of a checked split are logically independent, and this host had spare
cores, but launching unrelated checker processes would duplicate root reconstruction and lose one
deterministic composite verdict.

## Decision

`axeyum-cnf` provides `check_cube_refutation_reader_tree_parallel` on native targets. A caller
supplies an explicit positive worker count. The checker reconstructs every root child formula in
artifact order, schedules those owned `(formula, proof-tree)` jobs through a bounded standard-library
worker pool, runs the unchanged recursive backward-DRAT checker inside each job, sorts results by
root child index, and checks the root covering proof only after every child succeeds.

Only the root split runs concurrently. Nested trees remain sequential. This bounds simultaneous
formula copies and backward-checker memory by the explicit worker count, makes `workers=1` exactly
the old route, and avoids recursive thread multiplication. A worker panic is resumed; it can never
be converted into a successful or partial verdict. The command-line front door exposes the bound
as `--workers=N` and prints it in the receipt.

## Evidence

Two focused controls pass: the parallel checker accepts the same valid two-level composition as
the sequential checker, and two concurrently incomplete leaves deterministically report the lowest
path `[0]`. The existing sequential valid-tree and missing-child controls remain green, as does
the complete 18-test cube module, warning-denied Clippy for all `axeyum-cnf` targets, warning-denied
Rustdoc, and both the library and sequential example under `wasm32-unknown-unknown`.

On a retained 1,281,549,482-byte / 32-leaf S-box subtree, the four-worker release checker returned
`unsat-checked` in 67.53 wall seconds at 351% CPU and 713,172 KiB peak RSS. A historical sequential
run of the byte-identical artifact took 13:51.34 at 197,944 KiB, but cache state and host contention
were not controlled, so that comparison is operational context rather than a speedup claim.

## Alternatives

- Launch one process per leaf: rejected because process count, root binding, aggregate verdict, and
  error ordering would move outside the checker.
- Recursively parallelize every split: rejected because nested fan-out makes the worker and memory
  bounds misleading.
- Trust prior subtree receipts: rejected because an unsigned receipt is not a proof and would enlarge
  the trusted base.

## Consequences

Large independent proof branches can use a deliberate share of a host without changing certificate
semantics or accepting partial completion. Peak memory grows with the chosen worker count; callers
must choose it under host-level CPU and memory budgets. WASM retains the sequential API because this
route depends on native scoped threads.
