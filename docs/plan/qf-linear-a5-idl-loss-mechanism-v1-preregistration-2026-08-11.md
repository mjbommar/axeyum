# QF linear A5 IDL loss-mechanism v1 preregistration — 2026-08-11

**Closed.** B1 failed its 3/3 target and was removed; G1 found a nearby
unchanged-route boundary without authorizing production changes. See the
[result](qf-linear-a5-idl-loss-mechanism-v1-result-2026-08-11.md).

## Evidence boundary

The [isolated replay result](qf-linear-a5-idl-monotonicity-v1-result-2026-08-11.md)
establishes two deterministic but distinct losses. BubbleSort spends 43 seconds
across the DL and LIA chains, then times out during Boolean abstraction after
4,705 atoms. Inspection shows that abstraction currently invokes a complete
single-constraint simplex solve merely to validate each atom's linear fragment.
GraphPartitioning spends its 18-second DL probe slice, then safely declines at
the unchanged pre-SAT boundary. The following discriminators remain separate;
success on one cannot excuse failure on the other.

## B1 — linearization-only atom admission

In an isolated candidate worktree, change only the arithmetic-atom admission
check and its focused tests:

1. expose crate-private, search-free validators in `lra.rs` that run the same
   exact Int/Real linearizers (including opaque-Int application policy and
   overflow handling) without simplex feasibility search;
2. make `ArithAbstractor::ensure_supported_atom` use those validators; and
3. add equivalence controls for supported integer/real atoms, opaque integer
   applications, nonlinear products, `div`/`mod`, wrong sorts, and overflow.

No Boolean simplification, atom identity/order, theory route, timeout, cap,
model/proof path, public API, or verdict policy may change. A validator error
must occur before an unsupported atom enters the Boolean skeleton, preserving
the current contract and its regression test.

Build one fresh release candidate and run three isolated 24,000 ms / 8 GiB
observations each of BubbleSort, GraphPartitioning, the maze gain, and
`lpsat-goal-18`, starting the group at load at most 12. Acceptance requires
BubbleSort UNSAT in 3/3, maze and lpsat UNSAT in 3/3, GraphPartitioning no wrong
verdict or process failure, byte-stable supported/unsupported unit outcomes,
zero stderr, and all focused/deep-input/online-arithmetic tests green. If
BubbleSort does not recover 3/3, remove the candidate and close B1 negatively.

## G1 — unchanged-route timeout ladder

Using the unchanged exact `d0e0d6cea` binary and GraphPartitioning file only,
run one isolated observation at 32,000 ms. If it returns replay-checked SAT,
repeat twice at 32,000 ms. If it remains `unknown`, run one at 48,000 ms and,
only if SAT, repeat twice there. Keep the 8 GiB limit, zero-stderr rule, fresh
workers, and start-load ceiling. Stop on `unknown` at 48 seconds, any wrong
verdict, malformed output, stderr, or process failure.

This diagnostic may show whether the existing DL route has a nearby decision
boundary. It cannot justify changing the shipped 24-second protocol, bypassing
the pre-SAT boundary, or admitting the generic DPLL path. Any production
optimization needs a later preregistration with the original allocation-abort
controls and the full retained IDL/RDL decision set.

## Retention gate

B1 code may be retained only if its target and controls pass, focused tests and
strict all-feature solver gates are green, and a separate result records exact
source/binary identity. G1 retains no code. Even joint success authorizes no
200-row run: both historical losses must have a sound bounded production path,
then the combined candidate must be committed, pushed, pass one uninterrupted
external-frontier `just check`, and restart V2 from QF_LRA row 1. QF_RDL remains
forbidden until fresh LRA and IDL strict joins both pass.
