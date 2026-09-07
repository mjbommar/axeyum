# certificate-chain lane diary, 2026-09-07

The lane's subject is the one axis no competitor contests: SMT-COMP has had no
proof track since 2024, the fastest checker for the main SMT proof format is
documented as not formally verified, and a kernel-checked pipeline pays a median
6.9% for *checking* while *production* is the real cost. Measured here
yesterday, DRAT recording at the SAT level costs under 1%. So the expensive half
is nearly free for us.

## Where the chain was broken when the lane opened

`with_artifact_recording` had exactly one call site, `evidence.rs:2609`, inside
`dl_decided_report`. Six of the seven one-shot theory routes still built
`crate::cdclt::CdclT`, which emits no proof at all, so their `unsat` reached the
front door as `Evidence::Unsat(None)` with `trusted_steps` EMPTY — the theory
reasoning trusted and *uncounted*.

## Step 1 — three routes onto the native core

`euf_egraph::check_qf_uf_online_cdclt`, `lra_theory::check_qf_lra_online_cdclt`
and `lia_theory::check_qf_lia_online_cdclt` now call
`native_cdclt::solve_native` instead of `CdclT::new(..).solve(..)`. The diff is
the one `dl_online` took in S7b: the outcome enum changes, and the Boolean-leaf
injector takes `&NativeModel` instead of `&CdclT` (both expose
`value(var) -> Option<bool>` with the same "never assigned" contract).

The inline `mod tests` in `lra_theory.rs` and `lia_theory.rs` keep their own
`CdclT` import: those tests pin the *adapter contract* against the driver they
were written for, and they are still worth running.

### The swap moved a give-up reason, and the existing suite caught it

`cdclt_lia_online::default_lia_wrapper_leads_with_generic_cdclt` went red on the
first build. Measured, not guessed — a scratch test printed the probe's actual
return:

```
before: Unknown { kind: Timeout,    detail: "timeout in the online CDCL(T) LIA driver" }
after:  Unknown { kind: Incomplete, detail: "online CDCL(T) LIA model did not replay
                                             (arithmetic outside the incremental engine)" }
```

Cause: `CdclT::solve_inner` tests `timed_out()` at the TOP of its main loop, so
an exhausted budget returns `Outcome::Unknown` having propagated nothing. The
native core checks less eagerly. At a zero budget it propagated both units of
`x > 0 ∧ x < 1`, reached `final_check`, got `Sat` from a theory with no budget
to say otherwise, and returned `Sat`; `lia_theory` then could not build an
integer model and reported `Incomplete`.

No verdict moved — the replay gate turned the vacuous `Sat` into `Unknown`, as
it is there to. But the *kind* moved, and
`dpll_lia::check_with_arith_dpll` branches on it: `budget_unknown_kind(Timeout)`
routes to the legacy loop with the remaining budget, `Incomplete` falls through
to a different arm. A route that silently changes which fallback runs is not a
swap.

Fix is at the engine boundary, in `solve_native`, so every route that moves
inherits it (`dl_online` included): an exhausted deadline returns `Unknown`
before the formula is even built. The test in `native_cdclt/tests.rs` is
discriminating rather than vacuous — its fixture is Boolean-satisfiable and
theory-refuted, so *without* the check the same call returns `Unsat`, and it
carries a no-deadline control proving that.

This is the S7b finding restated in a second currency: that lane found a model
change costing a verdict (MBQI), this one found a deadline-check granularity
change costing a give-up reason. Both are the same shape — the engines differ in
places that are not the Boolean search.
