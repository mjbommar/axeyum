# Quantified-UFLIA unknown adjudication

Status: complete; ADR-0359 accepted
Date: 2026-07-22
Owner: solver/engine lane in `agent/smtcomp/full-library-resume`

## Result

The direct-Z3 quantified-UFLIA model-finder smoke harness now retains the exact
Axeyum Unknown/Error class, Z3 adjudication, and deterministic example seeds.
On 256 generated one-binder almost-uninterpreted instances:

| Axeyum outcome | Z3 SAT | Z3 UNSAT | Z3 Unknown | Total |
|---|---:|---:|---:|---:|
| Incomplete: satisfiable instantiation | 96 | 1 | 3 | 100 |
| ResourceLimit: MBQI budget | 9 | 9 | 2 | 20 |
| Incomplete: 16 rounds | 0 | 1 | 0 | 1 |
| Axeyum Error | 0 | 0 | 0 | 0 |

The same run produced 111 checked SAT results and 24 UNSAT results. All 131
jointly decided cases agreed with Z3, all 111 SAT models passed canonical source
replay, and there were zero disagreements. Timing-sensitive routing can move a
small number of cases between decided and resource-limited outcomes, so the
reason-by-oracle partition is the durable diagnostic, not a performance claim.

## Diagnostic evidence

The retained diagnostic entry point reproduces arbitrary seeds through the
same generator and both solvers. The first stable ordinary-incomplete examples
include:

- seed 0: two unconstrained functions whose total defaults must jointly satisfy
  `forall x. g(x) >= -8 - 2*f(x)`;
- seed 1: ground constraints fix selected `f`/`g` points while the universal
  requires `f`'s total default to remain above a `g` value;
- seed 2: `f` must avoid one value at every unobserved argument while preserving
  a separate ground inequality; and
- seeds 6, 12, and 16: coupled default inequalities with nested ground UF
  applications.

These are model-completion problems, not evidence gaps: ADR-0357/0358 already
checks the exact finite table/default profiles. The next bounded increment is
[ADR-0359](../research/09-decisions/adr-0359-preregister-checked-quantified-uf-default-repair.md):
search only default results, preserve explicit entries, and accept only after
the existing source checker and canonical model replay both pass.

## ADR-0359 implementation result

Topic commit `79a8dd21` adds that bounded search without widening the trusted
checker. It discovers at most eight relevant `Int`/`Real`-result functions,
preserves all scalar assignments and explicit table entries, and enumerates
stable same-sort default pools under the preregistered 32-value and 256-complete-
candidate caps. Missing interpretations become constant total functions with
the declared signature. Zero and checked `-1`/`+1` neighbors supplement values
already present in the candidate model. Unsupported result sorts, malformed
function storage, cap excess, and arithmetic overflow decline.

Every leaf is untrusted until the ADR-0357/0358 finite-profile checker accepts
all exact source universals and canonical `check_model` accepts the original
assertion sequence. Focused tests cover two missing functions, preservation of
an explicit integer point while repairing a strict default, a strict real
successor, unsupported results, all three caps, and overflow-safe neighbor
generation.

On the same 256 generated instances, the implemented repair produces:

| Axeyum outcome | Z3 SAT | Z3 UNSAT | Z3 Unknown | Total |
|---|---:|---:|---:|---:|
| Incomplete: satisfiable instantiation | 39 | 1 | 3 | 43 |
| ResourceLimit: MBQI budget | 0 | 9 | 1 | 10 |
| Incomplete: 16 rounds | 0 | 1 | 0 | 1 |
| Axeyum Error | 0 | 0 | 0 | 0 |

Axeyum now returns 178 checked SAT and 24 UNSAT results. All 197 jointly
decided cases agree with Z3 and all 178 SAT models pass canonical source replay.
Compared with the frozen baseline, this is 67 additional checked SAT results;
the ordinary Z3-SAT incomplete bucket falls from 96 to 39 and the resource-
limited Z3-SAT bucket from nine to zero. Seeds 1, 2, 6, 12, and 16 move from
Unknown to checked SAT. Seeds 0, 11, and 14 remain honest Unknowns and expose
separate free-scalar or larger-search boundaries; they are not silently folded
into ADR-0359.

## Reproduction

```sh
CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  quantified_uflia_model_finder_differential_fuzz_disagree_zero \
  -j2 -- --nocapture

AXEYUM_QUANT_UFLIA_DIAGNOSTIC_SEEDS=0,1,2,6,11,12,14,16 \
  CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  diagnose_quantified_uflia_model_finder_seeds \
  -j2 -- --ignored --nocapture
```
