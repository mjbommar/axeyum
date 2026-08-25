# Lane: coordinator — working the curriculum DAG toward the autogenesis frontier

<!-- plan-section: lane-status -->

**Curriculum-directed kernel development (`WIP`, coordinator, 2026-08-25).**
**1,106 distinct theorems, every one axiom-free**; trusted base unmoved at 30
declared-and-unreached `axreal` assumptions, and no `Opaque` or `Quotient`
declaration exists anywhere, so `Axiom`-only and the trusted surface coincide. Fact ledger **362 → 587**, `missing_edges=0`.

**The loop is code-complete.** Frontier selects → operation re-derives → receipt
survives a re-signed cross-target forgery → transaction verifies. Reproduced
end to end; the fact stays `open` on purpose, because whether to WRITE is not a
decision a gate should make.

**Why it is not yet automatic has a measured answer, not a direction.** Three
producers cover 7, 4 and 1 facts; the third is single-target **by
construction** (`const TARGET`, `const STREAM_SHA256`). Both routes past the
wall were tested: premise composition dies on WHNF opacity — reconfirmed
through a code path that never touches the induction producer — and on a
`fibAux`-vs-`Nat.iterate` representation mismatch; iterate re-derivation dies
because `LE.le` desugars to a four-argument spine and is rejected before any
combinator runs. The next capability is named: an order-relation combinator
vocabulary. Full chain in doc 262's fourth, fifth and sixth amendments.

**Next.** (1) That vocabulary, narrowly scoped — the previously-reverted broad
version exhausted a shared budget for zero admits. (2) Coverage is 210+/1134;
`Complex` and `CPoint` are thinnest. (3) `sumRange_cauchy_of_dominated` is three
named steps from closing.

**Three findings outrank the counts.** The binding constraint on the mathematics
is a **missing type** — no `List`, no `Finset`, no product — found every time by
a lane trying to prove something, never by planning. **Three targets I named
were false or unsatisfiable**, and lanes refuted them with counterexamples
rather than failing to prove them. And **reading a producer gave a plausible,
partly wrong picture three times running**; every correction came from running
it.

<!-- plan-section: landed-changes -->

| 2026-08-25 | `beb27f1ba` | **The trusted-core ceiling, raised the way the gate demanded.** Guard C failed at 5,508 past 5,500 with "say why before raising it." The baseline was RE-DERIVED by `git archive` rather than trusted, giving a per-file table summing to exactly +379 (`tc.rs` +347, `inductive.rs` +30, `env.rs` +2). Verdict: real and necessary — a universe-parameter closure fixing declarations **official Lean 4.30.0 refuses but this kernel wrongly admitted**, and `whnf_core` memoisation (138× cost, 1,857 s → 13.4 s) inside `def_eq`. Ceiling 5,900 with headroom matching the original's character; guard C re-verified to fire by injecting 500 lines in a scratch copy. The file's own comment said "5,110" where the real baseline was 5,129 — wrong from day one. |
