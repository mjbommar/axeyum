# agent-k — roadmap feedback for axeyum

Cited by file and line. Ordered by what I would fix first.

---

## F1. `nra.rs:107` `MAX_CROSS_PRODUCTS = 2` is the whole B4 phenomenon

`crates/axeyum-solver/src/nra.rs:107`

```rust
const MAX_CROSS_PRODUCTS: usize = 2;
```

checked at `nra.rs:334`. Measured today: it is what turns "minimal hypotheses"
into a 1500x difference. `a>=2, b>=1, w>=1, t=a*w |- b*t >= a*b` is `unsat` in
1 ms; add the Bezout conjunct `a*u + b*v = 1` and the identical query is
`unknown` at **1 s, 10 s, 60 s, 300 s and 1800 s** (`logs/k1-real-probe.log`,
`logs/ladder-*.log`). The decline arrives in **40 ms at every budget** with the
words

> "nonlinear abstraction: 4 cross-products exceed the deterministic admission
> bound of 2 (the multi-variable nonlinear case can OOM the relaxation; this
> needs a nlsat/CAD engine)"

The constant's own doc comment says `2` is "the documented boundary between the
working 2-variable SOS frontier and the blowing-up 3-variable case", i.e. it is
an **OOM guard**, not a completeness statement. Two things follow:

1. **The guard should be a configurable budget, not a hard-coded literal.** A
   caller who has memory to spend cannot buy reach today. `SolverConfig`
   (`backend.rs:129`) already carries `memory_limit_mb` and `node_budget`; this
   is the same kind of knob and it is the one that matters most for the
   symbolic-parameter route.
2. **The decline should say `4 > 2` in the route trace even when it is reached
   through `int-real-relax`.** Right now it does not: `auto.rs:3865` records
   `int-real-relax` only on *success* (`record_decided`), so a decline is
   invisible. I spent a measurement round on the wrong hypothesis because of it
   — the trace showed `nia-linearize` burning the clock and `int-real-relax`
   absent, which reads as "the route was never reached". It was reached, every
   time, and declined silently. **Every route that runs should record its
   decline**, exactly as `record_nia_decline` (`auto.rs:3760`) already does for
   the three NIA routes, and for the same reason its doc comment gives.

## F2. `auto::unsat_core` cannot minimise the queries that need minimising

`crates/axeyum-solver/src/auto.rs:658-695`, line 664:

```rust
if !matches!(solve(arena, assertions, config)?, CheckResult::Unsat) {
    return Ok(None);
}
```

Deletion-based minimisation is guided by a monotone predicate. Logically
`unsat` *is* monotone; operationally the solver's `unsat` is not, and that
non-monotonicity is the entire B4 phenomenon. So `unsat_core` returns `None` on
precisely the inputs a user wants minimised. The new
`hypothesis_min::minimize_hypotheses` grows from below instead; `unsat_core`'s
doc should point at it, so the next person does not conclude the capability is
already there.

## F3. An integer goal's verdict depends on which side the constant is written

Measured (`logs/k4-rounding.log`), same hypotheses, same arena, same budget:

```
P>=1, P*s >= P+1  |=  s > 1     unsat   0.000 s
P>=1, P*s >= P+1  |=  s >= 2    unknown 1.5 s
```

`s > 1` and `s >= 2` are **the same statement over the integers**. Likewise on
the other side:

```
P>=2, P*s <= a*P+2*P-1  |=  s < a+2     unsat   0.001 s
P>=2, P*s <= a*P+2*P-1  |=  s <= a+1    unknown 20 s
```

This is B5 ("generalising made it harder",
`next-actions-from-the-rado-paper-2026-08-12.md:238`) in its smallest
reproduction, and the fix looks cheap: **normalise integer bound atoms to a
canonical strictness and try the other form on `unknown`.** The rewrite is
`x >= k  <->  x > k-1` over `Sort::Int`, denotation-preserving, and it is the
difference between `unknown` and 0 ms on the step that currently stops the
`k = 3` Rado refutation. This is the single highest value-per-line item I found.

## F4. Naming a repeated product re-introduces the cross-products it removes

```
P>=2, a>=2, P*s >= a*P+1              |= s > a    unsat   0.001 s
Q=a*b, Q>=2, a>=2, Q*s >= a*Q+1       |= s > a    unknown 20 s
```

Adding the *definition* is what kills it. So a caller cannot get the benefit of
abstraction by writing it down; they have to drop the definition, which is a
weakening step no route performs. A **product-abstraction preprocessing pass** —
replace a maximal repeated nonlinear monomial by a fresh symbol, carry only its
sign/magnitude consequences, and accept `unsat` (sound: a weaker hypothesis set
refuting is a stronger result) — would take the `k = 3` step from `unknown` to
1 ms. Together with F3 it is the whole remaining gap on that step.

## F5. Two documents number a finding "B4" and the roadmap cites the wrong one

`NEXT-MATH-STACK.md` item 4 says "the 2026-08-12 findings register, item B4".
The register's B4 (`docs/plan/findings-register-2026-08-12.md:35`) is

> `climb.py` hard-coded `k = 4` | Rejected a valid 5-colour seed

The measurement is in a *different* file's B-list:
`docs/plan/next-actions-from-the-rado-paper-2026-08-12.md:222-234`. Anyone
tracing the provenance lands on a Python colour-range bug. One of the two lists
should be renamed, or the citation should carry the filename.

## F6. `REPORT.md` disagrees with itself on the 8-of-8 count

`docs/plan/proof-approaches-2026-08-12/route-b/REPORT.md:98` says "All 8
attempts returned `unknown`"; the table at `REPORT.md:15` says the monolithic
run was `3 matched / 9 mismatched`. The 8 is the *chain* run (`REPORT.md:19`);
the monolithic run had **9**. The phenomenon is real and reproduces; the number
in the headline is the wrong run's.

## F7. The route-B primary evidence is not in the repository

`docs/plan/proof-approaches-2026-08-12/route-b/` contains exactly `LOG.md` and
`REPORT.md`. The `.out` files that `LOG.md:697-705` calls "the complete primary
evidence", and the `route-b/*.rs` binaries that produced them, are gone. I had
to re-encode every lemma from the notebook transcript. The transcript is good
enough that this worked — every lemma statement is quoted verbatim — but a
result whose evidence cannot be re-run is a result that decays. The same applies
to `verify_k2_wide.py`, cited as the independent cross-check of a claimed
theorem.

## F8. The `k = 3` case analysis is 1 leaf, not 10 — and nobody had enumerated it

`route-b/LOG.md:671-673` budgets "roughly 10 leaf cases". `k3_ground_truth.py`
(in this directory) enumerates the shell colouring directly and finds that
**every** monochromatic solution, in every defective `(a,b)` pair with
`2 <= a <= 7`, `b <= 9`, sits in one leaf: colour 2, `x` in the right shell, `y`
in the left shell, `v(z) = 2`. Colour 1 and colour 3 are solution-free at every
tested pair on both sides of `b = a`. Whoever takes `k = 3` next should encode
that leaf first and treat the other twelve as k=2-style arguments that do not
need `b < a`. Ten minutes of enumeration would have saved the session's
"stopped rather than encode ten leaf cases" decision.

## F9. `MinimizeConfig::max_subset_size = 4` is the wrong shape for real chains

Mine, and I am flagging it against myself. The route-B lemmas need 3-4
hypotheses, so 4 was the measured default — but the `k = 3` leaf's chain steps
need **5-7**, and `C(24, <=4)` already exceeds the 4000-probe cap. Exhaustive
enumeration by cardinality is the wrong search for hypothesis sets past ~15.
The K1 finding hands the replacement over: greedily **delete** the hypothesis
whose removal most reduces `normalized_cross_product_count`
(`nra_real_root.rs:6017`) until the set is admissible, probing at every step —
`O(n^2)` syntactic evaluations and `O(n)` solver probes, no cardinality cap.
That is the next slice and it is bounded.

## F10. `Agent:` is not a trailer when a blank line separates it from `Co-Authored-By:`

Campaign rule 10 asks for an `Agent: <lane>` trailer. Written as

```
Agent: agent-k

Co-Authored-By: Claude Opus 5 (1M context) <noreply@anthropic.com>
```

git parses only the LAST paragraph as trailers, so
`git log --format='%(trailers:key=Agent)'` prints **nothing** for every such
commit. `git log --grep='Agent: <lane>'` still works, so attribution is
recoverable — but a lane-attribution tool built on `%(trailers:)` would report
every commit as unattributed and look correct doing it. Put `Agent:` in the same
paragraph as `Co-Authored-By:`.
