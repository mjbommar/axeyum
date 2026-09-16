# Lane: quant-session-arith — the session hosts arithmetic, and the verdict does not move (ADR-2130)

<!-- plan-section: lane-status -->

**Lane QUANT-SESSION-ARITH (`DONE`, quant-session-arith, 2026-09-16).**
[ADR-2124]'s named next increment: the quantifier-instance session hosts the
arithmetic theory beside its `EUF` e-graph instead of abstracting the arithmetic
away, so its `unsat` can be a Farkas conflict rather than only a congruence one.

**What it is.** `EufLiaSessionTheory` (`qinst_session_theory.rs`) runs `EUF` and
`LIA` side by side over **one shared atom index space**. No index mapping is
needed because both sub-theories were already written to tolerate an atom they
cannot represent, so composite atom `i` is `EUF` atom `i` and `LIA` atom `i` and
a conflict core from either half is already in composite indices. Behind
ground-session level 2, shipped **OFF**.

**The sizing, before any code.** 77 of ADR-2124's 101 ground-check rows are
arithmetic-bearing — AUFDTLIRA 18/18, AUFLIRA 6/6, UFLIA 28/28, UFNIA 24/44,
UFDTLIRA 1/1, UF 0/4. **53 of them carry a comparison in a GROUND position** and
24 acquire one only through an instance, which is why the original assertions
needed their own collection pass and not just the instance route. `dt-only` is
**0 of 108**, so the typed datatype decline the brief asked for excludes nothing.

**The lever engages, measured before any A/B.** On ADR-2113's 53 UFLIA cores,
level 1 abstracts **366 atoms across 20 cores** and level 2 abstracts **0** — at
least 365 of them `IntLt`/`IntLe`/`IntGt`/`IntGe` becoming real constraints.
`filespace.ZipTree` goes `atoms=45 abstracted=7` to `atoms=52 abstracted=0`.

**And the verdict does not move.** Paired probe, 24 s, interleaved per file on
one pinned idle s6 core: OFF 15 decided, ON 17, 2 raw gains, 0 losses, **0
flips**. The 3× re-check makes that **1 STABLE-GAIN and 1 ambient**, and the
stable one is `TypeDeclElemPragma.373` — the same single file ADR-2124's
abstraction moved. **Hosting arithmetic adds zero net movers over abstracting
it** on this population, so the divisions were not run and the lever ships OFF.
Twelve of these cores still die naming the interleaved ground check *with the
arithmetic hosted*, which is where the next lane should look.

**Three corrections to the brief, each verified in-tree.**
`TheorySolver::take_new_atoms` is **not** the hook for this route and using it
would have been a wrong-answer defect — it is polled inside a solve, so it
cannot hand an index back to a caller still building the clause; the warm route
registers driver-side and this theory's `take_new_atoms` returns `0` with a
fixture pinning it. **[ADR-2125] built no bound trail to reuse**: its subject is
the offline cube loop and its lever ships `off`; the trail it was confused with
is ADR-1701/ADR-2122's and lives on `LraTheory`, not `LiaTheory`. There is also
nothing to build — `IntSimplexEngine::sync` re-derives the imposed bounds from
the live set on every check, so the forwarded `LiaTheory::pop` **is** the
retraction, and the mutation suite aims at exactly that. And `LiaTheory` lives
in `lia_online.rs`.

**A fourth correction, to ADR-2124 itself.** Its premise is that one integer
comparison anywhere in the ground set refuses the session, so UFLIA takes the
cold branch for its entire run. Measured directly: the **shipped** arm reached
the session-construction site on 45 of 53 cores and **built a session on 26** of
them. Round 0's ground set is the quantifier-free subset, and on most
Boogie/Simplify-family files that subset is EUF-only — their arithmetic is
encoded through uninterpreted functions over `Int`.

**What is left.** `simplex::Incremental` exposes no row- or column-append
method, so a growth event **rebuilds** the arithmetic tableau; the Boolean
search, clause database, learned clauses and e-graph stay warm across it, but a
real `add_row` is the next increment and cvc5's shape (keep the column, replay
the registration) is the model. No interface equalities are propagated between
the two sub-theories — an incompleteness, free here because the session's `Sat`
is never a verdict. The new differential seed class (incrementally assembled
`QF_UFLIA` sets compared against z3 on the whole set) was **not built**, and it
is the most valuable thing left undone.

[ADR-2113]: ../../research/09-decisions/adr-2113-uflia-the-instance-we-never-produce.md
[ADR-2124]: ../../research/09-decisions/adr-2124-incremental-ground-closure-for-quantifier-instances.md
[ADR-2125]: ../../research/09-decisions/adr-2125-a-warm-simplex-basis-across-sat-decisions.md
