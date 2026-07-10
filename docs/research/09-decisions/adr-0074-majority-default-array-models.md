# ADR-0074: Deterministic Majority-Default Array Models

Status: accepted
Date: 2026-07-09

## Context

ADR-0073 put bounded extensionality on canonical ABV/AUFBV, but projected array
models still used the well-founded zero/default value as every array's else
branch and stored every non-default observation. Z3's array model construction
instead selects a frequently observed range value as the function
interpretation's else branch, reducing explicit entries and producing models
that better reflect the solved select classes.

P2.2.4 calls for `func_interp`-style array models with majority-vote else values.
The projection helper is shared by canonical ROW/extensionality and the one-shot
fallbacks, so the policy must be deterministic, preserve every observed read,
and remain guarded by original-query replay.

## Decision

Select the most frequent element value over distinct observed indices as each
projected array symbol's else value, with a stable smallest-value tie-break, and
store only observations that differ from that else value.

- `array_value_from_entries` first normalizes duplicate observations by index in
  deterministic discovery order; majority counts are over distinct indices, not
  repeated read sites.
- Compact BV arrays count values in a `BTreeMap<u128, usize>`. Maximum frequency
  wins; equal frequencies choose the smaller masked BV value.
- Generic arrays use full `Value` equality and the stable `sort:value` rendering
  key for ties. An array with no observations retains the IR's well-founded
  default.
- `ArrayValue::store` and `GenericArrayValue::store` remove entries equal to the
  chosen default, so the resulting representation is normalized and
  deterministic.
- The policy lives in the shared projection helper. Canonical online, lazy ROW,
  and one-shot lazy-extensionality paths therefore cannot drift.
- No solving constraint or verdict rule changes. Every projected SAT model still
  replays every original assertion; a poor else choice can only cause a
  conservative Unknown, never a wrong SAT.

## Soundness Argument

For each distinct observed index, projection stores its candidate element value
unless that value equals the selected default, in which case the total array's
else branch already returns it. Therefore every observed select has exactly the
same value before and after majority selection. Unobserved indices are
unconstrained by the scalar abstraction except through original array terms;
the mandatory original-query replay checks those terms extensionally.

Normalizing duplicate indices before voting prevents repeated syntactic reads
from changing the model policy. Deterministic tie-breaking removes hash or site
order from output. Sort checks and existing projection errors remain unchanged.

## Evidence

- Focused compact-BV model test: observed values `7,7,7,3,4` choose default `7`,
  retain exactly two overrides, and preserve all five reads.
- A tie test chooses value `3` over `9` and retains one override.
- A generic `(Array Int Int)` test chooses `7` for observations `7,7,3`, retains
  one override, and preserves selected values.
- An end-to-end canonical model with 16 concrete reads (12 value `7`, four
  minority values) returns replayed SAT with default `7`, four overrides, one
  solve round, and zero refinement requirements.
- The equality-bearing 768-comparison direct/eager, front-door/eager, and
  direct/Z3 AUFBV matrix remains clean.
- Single-run public measurements at a 1 s cap preserve all decisions and replay:

| corpus | ADR-0073 decisions | majority-default decisions | disagreements | replay failures | PAR-2 mean |
|---|---:|---:|---:|---:|---:|
| QF_ABV (193) | 187 | 187 | 0 | 0 | 84 ms (unchanged) |
| QF_AUFBV (53) | 49 | 49 | 0 | 0 | 206 ms (was 221 ms) |

The AUFBV timing movement is one noisy portfolio sample and is not treated as a
performance claim. The separate fallback deadline-overrun row remains.

## Alternatives

- **Keep zero/well-founded defaults everywhere.** Sound but stores avoidable
  entries and does not implement the planned majority-default model policy.
- **Count every read site.** Rejected because syntactic duplication would bias
  the model and make output sensitive to abstraction shape.
- **Choose the first maximum as Z3's local loop does.** Rejected because Axeyum's
  public determinism promise benefits from an explicit order-independent tie.
- **Choose defaults per e-graph array class.** Deferred until the array theory has
  merge-triggered class ownership. The current projection is per original array
  symbol; equality/replay remains the correctness gate.
- **Use majority selection to accept SAT without replay.** Rejected. Model
  construction is an untrusted hint and never replaces checking.

## Consequences

- Projected arrays are smaller when many observed cells share a value, including
  common zero-fill and repeated-constant memory shapes.
- Canonical and fallback array routes share one deterministic model policy.
- T2.2.4 is complete only for original-symbol finite-map projection. Full
  e-graph-class `func_interp` ownership, explicit class defaults, nested/extended
  arrays, warm model reuse, and proof/evidence integration remain.
