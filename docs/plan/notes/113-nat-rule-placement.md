# Notes: 113-nat-rule-placement

Detail moved out of [`../status/113-nat-rule-placement.md`](../status/113-nat-rule-placement.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The placement alone buys nothing — the guard is the whole prize, and that
distinction is the finding.** Three interleaved rounds, release,
`AXEYUM_PRELUDE_CACHE=0`, `taskset -c 0-7`, median `creal` seconds: before
**12.99**, Lean's placement unguarded **12.12**, Lean's placement + guard
**6.79**. 12.99 → 12.12 is inside this workload's run-to-run spread on a shared
box. The rule fires 1.19 M times per `build_creal_prelude` and produces a literal
575 times, and 99.98% of the probes are on a term that mentions a free variable —
so the O(1) structural guard removes essentially all of the cost, and moving the
call site removes essentially none of it. For scale, 8.71 s was the time *before*
the acceleration was ever switched on.

**Identification is unmoved, measured rather than argued.** `axeyum-lean-kernel`
lib **399 passed / 0 failed**; the full kernel crate (lib + all 46 integration
suites) **609 passed / 1 failed**, the one being
`real_lean_wellfounded_elaborator_divergence`, which fails **byte-identically on
an unmodified `HEAD`** in a snapshot tree and is a *Lean elaborator* rejection,
not ours — a live separate finding, flagged for whoever owns ADR-0517;
`axeyum-solver --features full --lib reconstruct::` **312 passed / 0 failed**;
clippy 618/618 targets, 0 diagnostics; `check-prelude-reuse-equivalence.sh`
`compared=8 failures=0` with live counters;
`gen-lean-axiom-ledger.py --check` exit 0 with
`total=30 axreal=30` and every other prelude 0. No declaration stopped admitting.
That is a measurement over this repository's corpora, not a proof: the class the
guard gives up is nonempty and a fixture constructs one — `Nat.mod ((fun _ => 7)
x) 0`, whose operands reduce to literals while `has_fvars` is structurally true.
Our corpus simply does not reach it.

Four mutations, each alone: dropping either `has_fvars` guard kills exactly one
test, dropping the `whnf_core` call site kills exactly one, and dropping the
lazy-delta call site kills five — one of them by **overflowing the stack** on
`2^64`-scale literals, which is ADR-0459's unbounded-successor-chain hazard
reproducing on demand. That is which of the two sites carries the rule's reason
for existing.

Next on this axis: `reduce_nat_succ` is still in the δ-free step, a residual
divergence from Lean's `reduce_nat`. It is one interned-name comparison per
constant-headed reduction step, so it is not a cost today — revisit only if a
profile says otherwise, since moving it would change identification for no
measured gain.
