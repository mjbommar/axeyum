# Notes: agent-string-recon

Detail moved out of [`../status/agent-string-recon.md`](../status/agent-string-recon.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Measured over the 217 committed `QF_S`/`QF_SLIA`/`QF_SEQ` files: 3 certificates,
**2 reconstructed** — `r0_QF_SLIA_str004.smt2` and `r0_QF_S_str005.smt2`, taking
different engines (strict / non-strict), both accepted by real Lean 4 with
`#print axioms` reporting nothing but the query's own facts and the abstraction
variables. `r1_QF_SLIA_str-code-unsat-2.smt2` declines twice over: it is a
two-arm case split (refuting one arm proves nothing, and its first arm closes on
its own, so the guard is load-bearing), and its second arm needs `10^28 −
0x2FFFF` unary `one`s.

The finding worth carrying forward is about the size guard, not the route. It
was written at `4_096` and mutating it away did not fail a test — it **aborted
the process** with a stack overflow, because the fold builds a left-nested `add`
chain the kernel walks recursively. Measured: cost 514 renders a 13.2 MB module,
cost 1026 SIGABRTs. So the guard was calibrated to admit exactly the failure it
existed to prevent, and no test could have said so, because the test only ever
exercised the decline side. **A budget needs pinning from both ends: at the
budget it must still work.**

Next: the case-split arm needs `Or.elim` in the kernel — the machinery exists
(`reconstruct_disjunctive_lra_proof`) — but it buys nothing measurable while the
only case-split corpus file also needs a `10^28` numeral. A binary numeral
development for the ordered-ring engine is the change that would move that file,
and it would also lift every other route's constant ceiling off `k` copies of
`one`.
