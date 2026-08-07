# QF_NIA A3 relevance-activated bound ladders v1 result — 2026-08-07

## Verdict

The preregistered relevance-activated bound-ladder experiment is **rejected**.
It added no theory-oracle calls and emitted only sound adjacent two-literal
implications for expressions that had produced a checked simple-bound conflict,
but neither target became SAT in any of three observations. The 2-of-3 target
gate failed, so routing controls, retained decisions, the 200-row list, and the
full aggregate gate were not authorized.

All temporary solver code, diagnostic counters, and tests were removed. The
preregistration, exact input lists, and this negative result are the only
retained artifacts.

## Bound implementation and focused evidence

The implementation preserved the existing complete implication behavior below
the 512-atom admission boundary. Above it, a deterministic latent index grouped
adjacent implications by stable expression term ID and bound side. A checked
dynamic `Bound` conflict activated its expression once; unrelated expressions
remained latent. The existing 4,096 implication ceiling remained unchanged,
and model/original-assertion replay remained mandatory.

The temporary release `explain_corpus` binary had SHA-256
`30f7eb00c2235b36507137259ce0cd36c4ecd9bdac51559f4ddb59b1ceda3832`.
Before measurement:

- `CARGO_BUILD_JOBS=2 cargo check -p axeyum-solver --all-features` passed;
- the exact relevance-activation unit passed 1/1 with 1,078 library tests
  filtered; it proved one-shot activation, unrelated-ladder non-activation,
  deterministic ceiling behavior, and independent UNSAT checking for every
  emitted implication;
- the existing upfront bound-implication focused filter passed;
- file-local Rustfmt and `git diff --check` passed.

## Direct target observations

All observations used the preregistered 8 GiB process ceiling, 24,000 ms query
budget, serialized execution, and CPU 4 affinity. Every verdict was `unknown`.

| Target | Run | Lazy rounds | Activated / latent expressions | Emitted / latent implications | Terminal shape |
|---|---:|---:|---:|---:|---|
| `p4943` | 1 | 86 | 79 / 997 | 470 / 1,898 | query deadline |
| `p4943` | 2 | 113 | 80 / 997 | 472 / 1,898 | query deadline |
| `p4943` | 3 | 113 | 80 / 997 | 472 / 1,898 | query deadline |
| `p32598` | 1 | 18 | 158 / 2,213 | 484 / 3,486 | query deadline |
| `p32598` | 2 | 23 | 158 / 2,213 | 484 / 3,486 | terminal 4,679-literal core, then deadline |
| `p32598` | 3 | 23 | 158 / 2,213 | 484 / 3,486 | query deadline |

The 4,096 ceiling was never reached. `p4943` sometimes completed more rounds
than its 82-round direct baseline but never reached reconstruction or SAT.
`p32598` remained near its 22-round baseline and reproduced the previously
observed load-sensitive single huge terminal core in one run. In all six runs,
support was available, every completed round found a conflict, model attempts
and replay failures stayed zero, and the full-assignment fallback stayed zero.

## Causal conclusion

The experiment proves that missing adjacent propagation is real but not the
owning completeness defect for this pair. Hundreds of relevant checked clauses
can be added at negligible theory-oracle cost without reaching a theory-
consistent Boolean candidate. The residual bottleneck is the scale and search
structure of the support-guided Boolean/arithmetic abstraction itself, not
merely rediscovery of adjacent scalar-bound implications.

Together with the rejected broad-core group deletion, this closes the five-row
DPLL/core-search partition against the two measured explanation-quality
mechanisms:

- repeated full-theory calls to shrink broad cores are too expensive;
- relevance-triggered cheap adjacent implications change search shape but do
  not decide the small-core pair;
- `p1784` remains load-sensitive between the search and reconstruction
  boundaries;
- the `SAT14` pair and single-terminal-large-core behavior remain negative
  controls, not authorization for a cap or deadline change.

The next A3 slice should return to the 52-row budget population and partition
it by its already-retained downstream reason (pre-lowering clause estimate,
width-ladder timeout, exact-width/model-overflow, and other typed budget
declines). It must not revive probe-model reuse, reconstruction reservation,
group deletion, or relevance-activated bound ladders without new causal
evidence and a new preregistration.
