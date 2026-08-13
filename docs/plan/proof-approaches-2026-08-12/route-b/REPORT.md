# Route B — what axeyum actually proved

*Transcribed by the orchestrator from the agent's final report; the agent's
`Write` was blocked for report files. `LOG.md` (706 lines, append-only) and
the `.out` files are the primary evidence.*

**Axeyum proved three genuinely universally quantified theorems.** No
soundness bug was found and no wrong verdict occurred in ~100 queries. Every
failure was `unknown`, never a wrong `sat`/`unsat`.

| suite | file | matched | mismatched |
|---|---|---:|---:|
| B1 audit | `b1_audit.out` | 20 | 0 |
| B2 family | `b2_family2.out` | 21 | 3 (retained bad encodings) |
| B3 k=2 monolithic | `b3_k2.out` | 3 | 9 (all `unknown`) |
| B3 k=2 chain (full hyps) | `b3_k2_chain.out` | 4 | 8 (all `unknown`) |
| B3 k=2 minimal lemmas | `b3_k2_min.out` | 11 | 2 |
| B3 k=2 micro-lemmas | `b3_k2_micro.out` | **16** | **0** |
| B3 colour-1 (all k) | `b3_colour1.out` | 9 | 1 |

Machine: 4 cores shared by three agents — **all wall times are upper bounds.**

## B1 — the precedent is real, and NOT bit-vector-bounded

The solution-form lemma's unbounded `unsat` **stands**; no correction needed.
Source: `multilayer/src/bin/layer2_lia.rs:150`. With `bounded == false` it
pushes **no** range constraints; `x,y,z` are plain `Sort::Int`. Reproduced in
23 ms. The deciding route is **`lia-dpll`** — DPLL(T) over exact-rational
simplices. Its search budget is bounded; the *domain* is not. No bit-blasting
and no BV route appears in any trace of the lemma.

Two defects **as evidence** were found and fixed:

1. **No unbounded false-variant control** — the headline `unsat` rested on a
   gate never shown able to return `sat` unbounded. Controls now fire
   unbounded (`ctrlA` → `sat`, `x=6 y=0 z=4`: `2·6 = 12 = 3·4`, `3 ∤ 4`), and
   anti-bounding controls return witnesses at ±3·10^18 and at genuinely
   negative solutions.
2. **No provenance** — `check_auto` returns a verdict, not a route. Re-posed
   with `check_auto_explained`, which prints the route.

## B2 — an infinite counterexample family, proved symbolically in `a`

> **Theorem.** For every `a >= 2`, with `b = a+1`, `k = 3`,
> `N = 2ab + a^2 b` and `(x,y,z) = (a b^2 + 1, 1, a^2 b)`:
> (i) `a(x-y) = bz`; (ii) `1 <= x,y,z <= N`; (iii) `chi(x)=chi(y)=chi(z)=2`.

The structural reason, found by enumeration then proved symbolically:
`N - ab + 1 = a^3 + 2a^2 + a + 1 = x` exactly — **`x` is the left endpoint of
the right-hand shell.** (This is why the family coincides with route A's
*moving* witness `X = N - ab + 1` at `k = 3`, and only there.)

All 13 claims `unsat`, mostly via `int-real-relax` in 0.00 s; the entire
arithmetic half as a single query in 0.14 s. Six false-variant controls all
returned `sat`.

## B3 — proved at k = 2 for symbolic `a` and `b`

> **Theorem.** For all `a >= 2`, `b >= 1` with `gcd(a,b) = 1`, the `k=2`
> shell colouring of `[1, ab]` admits **no** monochromatic solution of
> `a(x-y) = bz`.

**`b < a` is not assumed** — the proof does not need it, and enumeration
confirms the stronger statement. This independently reproduces route A's
Proposition (`k = 2` is solution-free for every `b`) by a completely
different method.

Two design choices made it tractable, both worth reporting:

- **gcd as Bezout**: `exists u,v. au + bv = 1`. The theorem is a refutation,
  hence existential, so an existential hypothesis is just two more free
  variables. **Route B contains no quantifier alternation anywhere.**
- **Negated divisibility by remainder witness**:
  `a does not divide j  <=>  exists s,r. j = a s + r and 1 <= r <= a-1`.

Ten lemmas with minimal hypotheses, each `unsat`, **each paired with a
control that returned `sat`** (16/16 micro-queries in 57 ms).

Independent cross-check (`verify_k2_wide.py`, a full scan that does not even
assume the solution form): **973 coprime pairs, zero counterexamples; 53/53
non-coprime pairs defective** — the `gcd` hypothesis is exactly sharp.

**Bonus:** the colour-1 lemma is proved for **every `k >= 2`** (colour 1 is
`{v_a(j) = 1}` independent of `N`, the shells, and `k`).

**k = 3 is incomplete:** 1 of 3 cases proved, 2 not encoded. Cases 2 and 3
genuinely need `b < a` and degree-3/4 inequalities in three variables — the
shape that defeated every monolithic attempt. The agent stopped rather than
encode ten leaf cases at session end and risk an unchecked composition error.

## What axeyum could NOT do (the reusable finding)

1. **Refuting divisibility with a variable divisor.** `exists a,p. a>=2 and
   a p = 1` → `unknown(Timeout)` after 60 s via `int-blast-ladder`: *"no model
   within the bounded integer width 32"*. This caused every B2 failure. Fix:
   pose non-divisibility in the **witness direction** — same facts, `unsat` in
   0.00 s.
2. **Any monolithic query carrying the full hypothesis set.** All 8 attempts
   returned `unknown`. Split into 3–4-hypothesis lemmas → 0.00 s.
   **Minimal hypotheses beat a bigger budget.**
3. **Generalising a lemma made it harder.** `M8` with an opaque `M` timed out
   at 45 s; the same fact at `M := a^2` was `unsat` in 0.01 s.
4. Routes that worked: `int-real-relax`, `lia-dpll`, `lia-simplex`,
   `nia-linearize`, `term-identity-refuter`, `dl-online`.

## Soundness

No concerns found. Where controls did **not** fire (`cT1`, `cT2`, `cC2.1`)
the corresponding `unsat` was **discarded rather than banked**; the cause was
an own-goal — those hypothesis sets were contradictory by construction, so
they could never return `sat`. Logged at the moment of discovery.
`explain_corpus` was never used (it is documented as capable of printing a
wrong verdict).

## Attribution caveat — read before writing any of this up

These theorems are machine-**checked**, not machine-**discovered**. The case
analysis, dropping the `a^2 does not divide` conjuncts, the Bezout witness,
and the ten-lemma decomposition were the agent's; axeyum verified each step
over unbounded `Z` and returned `unknown` for what it could not. The 57 ms is
not the cost of the theorem — four attempts and roughly 32 minutes of solver
time went into finding a decomposition the tool could accept.

**Do not write this up as "axeyum proved the construction correct".**
