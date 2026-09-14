# Lane: distinct-linear — the front-door `distinct` refusal, sized and measured

<!-- plan-section: lane-status -->

**Lane distinct-linear (`DONE`, distinct-linear, 2026-09-13).** Branched from
`main` at `2611e14b0` — `git merge-base main <branch>` = `2611e14b0`, which was
main's HEAD at branch time. Decision: [ADR-2000], the lever **ships OFF**.

**The sizing is 356 files, not 5.** [ADR-1995]'s handoff sized the `distinct`
pair-expansion refusal from one division's pinned 200. Scanning the corpus —
438,631 files, 28,415 containing `distinct` — **356 carry an application of
arity ≥ 363**, the first arity the `n(n-1)/2` cap refuses: `UFNIA` 309,
`QF_NIA` 35, `QF_LIA` 12, **265 declaring `unsat`**, largest application
**65,677 arguments**.

**Two of the handoff's three structural claims are false, and each would have
shipped a rewrite that fires on nothing.**

- *"the `distinct` is the whole body of an `(assert …)`"* — **zero of 356**. The
  chains are `assert > and` (257), `assert > let > not > or > not` (52), and a
  `let` BINDING (47); all positive polarity. The shipped site test is a polarity
  walk keyed on argument-slice address, covering **309 of 356**.
- *"nullary constants of an uninterpreted sort"* — true of the 257 `lahiri`
  files, false of the other 99, which are `Int`: Boogie's UFNIA encoding uses
  `Int` as a universal carrier and those files carry no `declare-sort` at all.
- And the safety net: the front door's model replay runs over the **rewritten**
  assertions (`smtlib.rs:4426`), so it is no check on this rewrite at all. The
  `sat` direction is safe because the encoding is strictly stronger — proved, not
  checked.

**Measured**, one binary, two env values, back to back per file on six pinned
core pairs, 24 s / 8 GiB: treatment (all 356) **0 → 1 decided**, control
(`UFLIA` pinned 200) 68 → 69, **0 losses and 0 sat↔unsat flips in 712 solves**,
mean 267 ms → 21,175 ms. Both `+1`s were re-run: the control's is the **machine**
(that division's largest arity is 256, inside the cap, so the arm cannot change
one parsed byte; STABLE-SAME, `unsat` 3/3 in both arms; noise floor 72/72/74,
band 2), and the treatment's is real but costs 61 % of the budget — UNSTABLE at
1/3 under the sweep's own load, **12/15 at a mean of 14,727 ms** alone on a core.
6 of 6 authority comparisons agree, 0 disagreements.

**The finding: the front-door refusal was never the binding constraint.** Two
files, one per family, at a **600 s** budget — 25× the envelope — both hit the
watchdog and returned `unknown`. z3 refutes one of them in 508 ms. What stops
these queries is the quantified ladder, at any budget.

**A checker that failed, reported as failed:** the mutation control's
STRENGTHENING mutant produced **0 decided contradictions** over 200 files and
still 0 when given its 12 best-case files at 6× budget (12/12 changed to
`unknown`, 0/12 contradicted). It is never decisive at corpus scale, so the
zero-disagreement result is evidence for the weakening direction only; that
mutant's decided kill exists at unit scale.

Landed: `1e8aa69ae` (encoding + lever, OFF), `b7f761f70` (20 tests, both mutants
flip), `b439597e9` (the polarity walk), `1688f46b6` (pre-registered sizing +
harness), `d8649123c` (analysis scripts), `c78566d1d` (A/B, mutation, re-check,
long probes), `d03a9ffd2` (noise floor).

Full record: [`bench-results/distinct-linear-20260913/AB.md`](../../../bench-results/distinct-linear-20260913/AB.md)
and its `README.md`.
