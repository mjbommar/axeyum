# Quantified-UFLIA profile-guided model-completion measurement

Status: measured; production boundary preregistered
Date: 2026-07-23
Owner: solver/engine lane in `agent/smtcomp/full-library-resume`

## Population

ADR-0363 leaves exactly three ordinary Z3-SAT Unknowns in the frozen 256-case
quantified-UFLIA differential:

```text
122, 175, 182
```

The complete Axeyum baseline is 215 SAT, 24 UNSAT, and 17 Unknown, with all 215
SAT models replayed. The remaining fourteen Unknowns are independently timed-out
Z3 cases and are retained in the measurement rather than silently discarded.

## Exact residuals

The three ordinary Z3-SAT formulas require table structure, not another scalar
or fixed default value:

- seed 122 has `forall x. f(x) = C` plus the binder-independent guard
  `11 <= g(-y0 - 2)`. Its ground model has no UF entries. Even uncapped search
  over ADR-0363's fixed 17-value default pool finds no model; Z3 uses distinct
  `g(-2)` and default values.
- seed 175 has `forall x. f(x) = -3`, while the ground candidate retains
  `f(2) = 6`. Default-only repair cannot change that explicit entry, although
  the source itself requires the total constant function.
- seed 182 requires a nonconstant nested model for
  `forall x. f(g(x)) < f(f(-1))`; two fixed defaults necessarily make the
  strict comparison reflexive.

An additional baseline Unknown, seed 226, has the independently checkable model
shape `f(default)=0`, `f(0)=f(1)=1` for
`forall x. f(x) >= 0 and f(f(x)) > f(-1)`. Z3 times out at the registered two
seconds, so this case receives no oracle-derived credit; Axeyum's independent
finite-profile certificate and exact source replay establish its SAT result.

## Measured mechanism

The retained diagnostic runs only after the existing MBQI, E-matching, and
ADR-0361 routes decline. It uses the time remaining under the original
three-second MBQI deadline and performs a SAT-only finite-profile CEGIS loop:

1. Solve the original quantifier-free ground assertions plus accumulated exact
   source instances.
2. Complete only absent source-relevant `Int` functions with zero defaults so
   the candidate can be evaluated.
3. As an untrusted search hint, recognize top-level conjunctive equalities of
   exact shape `f(binder) = ground_term` (or the symmetric form), require unary
   `Int -> Int` `f` and a binder-independent other side, evaluate that side in
   the candidate, and propose the corresponding total constant function.
4. Ask the existing independent finite-profile checker and canonical full
   source replay to accept the candidate.
5. On failure, derive the first falsifying binder representative from the same
   exact function-table positions and alternating fresh-Int policy used by the
   checker, instantiate the untouched source body at that value, and repeat.

The diagnostic caps the loop at 32 rounds/instances. Every inner QF timeout,
Unknown, error, duplicate instance, unsupported shape, missing falsifier, or
shared-deadline expiry declines. Inner UNSAT is not transferred; only a fully
certified and replayed SAT model can change the outer result.

Two repeated full-population runs under the original shared deadline produce
the identical result:

| Seed | Z3 at 2 s | Completion rounds | Added instances | Result |
|---:|---|---:|---:|---|
| 122 | SAT | 1 | 1 | checked SAT |
| 175 | SAT | 0 | 0 | checked SAT |
| 182 | SAT | 1 | 1 | checked SAT |
| 226 | Unknown | 2 | 2 | checked SAT |

The projected production totals are therefore exactly 219 SAT, 24 UNSAT, and
13 Unknown, with 219/219 SAT replay and no remaining ordinary Z3-SAT Unknown.
The direct-Z3 gate should reach at least 235 jointly decided agreements; higher
counts are permitted only for the already observed independent oracle-timeout
variance.

## Rejected measured alternative

A blind batch of sixteen canonical integer instances is not the production
mechanism. It solves seed 122 in 19 ms, but overfits explicit tables: seed 175
does not converge within the 32-round diagnostic cap, and seed 182 reaches an
inner timeout after 33 seconds. Exact definitional completion plus one-at-a-time
profile counterexamples closes all four cases together in 0.08 seconds when run
directly and preserves the original shared-deadline placement in both complete
population measurements.

## Production boundary

Proposed
[ADR-0364](../research/09-decisions/adr-0364-preregister-profile-guided-quantified-uf-model-completion.md)
freezes the measured mechanism. It does not widen the accepted quantified
source fragment, trusted checker, evidence format, UNSAT route, scalar/default
candidate pools, or any earlier search cap. The constant-function recognizer and
profile representatives are search hints only; final authority remains the
independent finite-profile checker plus canonical exact-source replay.

## Reproduction

```sh
AXEYUM_QUANT_UFLIA_PROFILE_CEGIS_SEEDS='122,175,182,226' \
  CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  diagnose_finite_profile_cegis_for_quantified_uflia_residuals \
  -j2 -- --ignored --exact --nocapture

CARGO_TARGET_DIR=target-codex CARGO_BUILD_JOBS=2 \
  cargo test -p axeyum-solver --all-features \
  --test quantified_uflia_model_finder_differential_fuzz \
  diagnose_finite_profile_cegis_smoke_population \
  -j2 -- --ignored --exact --nocapture
```
