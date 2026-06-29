# axeyum-verify

A bounded Rust verifier built on Axeyum: a `#[axeyum::verify]` proc-macro that
symbolically checks a function for panics — integer overflow, `÷0`/`%0`,
index-out-of-bounds, `assert!`/`assert_eq!` violations, `panic!`/`unreachable!`,
and `unwrap`-on-`None` — and emits either a runnable failing `#[test]` or a
re-checked, bounded-verified certificate (Lean-checkable when in fragment).

The macro parses a *restricted Rust surface* (`syn`, not MIR): integer/bool
params and locals, arithmetic/bitwise/comparison, `if`/`match`-on-int, fixed
arrays + indexing, compound assignment, and `#[unwind(K)]`-bounded `while`/`for`.
Common integer methods are modeled exactly: `wrapping_{add,sub,mul}` (modular, no
overflow class), `saturating_{add,sub,mul}` (clamp to the type bound via `ite`
over the overflow predicate, signed and unsigned), `min`/`max` (a
signedness-correct select), `abs` (with its `iN::MIN` overflow panic), `pow(N)`
for a constant exponent (folded to checked `Mul`s), `rotate_left`/`rotate_right`
by a constant, and the `checked_{add,sub,mul}`
Option idiom (`.unwrap()`/`.expect()`, `.unwrap_or(d)`, and `match … { Some(v) =>
.., None => .. }`). It lowers each panic class to an explicit *bad-state* boolean
term and asks the solver whether any is reachable — a model is a concrete bug
witness; `unsat` is a bounded safety proof.

## Soundness — `DISAGREE = 0`

Counterexamples are self-validated: the original function is re-run on the lifted
inputs under `catch_unwind` and must actually panic before a counterexample is
reported. An adversarial differential fuzz (`tests/differential_fuzz.rs`) uses a
trivially-correct concrete evaluator as the oracle over the arithmetic fragment
(unsigned + signed, plus the `iN::MIN / -1` and `÷0` edges) and the array/index
fragment: a reachable panic must **never** yield `Verified`. The fuzz found and
we fixed a real wrong-safe (signed `iN::MIN / -1` division overflow was
undetected). It also value-checks the modeled methods against std oracles
(`wrapping_*` modular result, `saturating_*` clamp over both signednesses,
`min`/`max` selection) and the `match`-on-int dispatch desugar (per-branch panic
folding): an always-false assertion over each computed value must stay reachable,
so a wrong value would surface as a wrong-safe.

## Loops — warm BMC

`while` bodies in the scalar fragment lower to a `ScalarLoopSystem`
(`loop_system::loop_from_program`) decided by the solver's warm
`bounded_model_check` — re-lowering each step against the pre-state via the real
expression lowering (no duplicated semantics), folding nested `if` into guarded
`ite` updates and update-overflow into the bad predicate. `verify_program_warm`
routes a loop program's decision through this path (measured ~40× faster on safe
deep loops than unrolling — see the scoreboard), deferring to the unroll route
for the concrete witness, the certificate, and out-of-fragment programs. Both
routes are cross-checked to agree.

## Measured

A construction-known scoreboard
([`docs/consumer-track/verify/SCOREBOARD.md`](../../docs/consumer-track/verify/SCOREBOARD.md),
`cargo run -p axeyum-verify --example measure_verify`) reports
bug-found/verified/unknown per class with `DISAGREE = 0`, the **Lean-cert
coverage** of verified results (the trusted-checking moat metric), and a
warm-BMC-vs-unroll depth-scaling sweep.

## Honest limits

- The fragment is restricted (no heap/traits/closures/floats — same scoping
  discipline as Verus/Flux); out-of-fragment constructs are `Unknown`, never a
  wrong verdict.
- Loops are **bounded** (`#[unwind(K)]`); `Verified` is a bounded guarantee.
- Lean-cert coverage is partial (it inherits the upstream reconstructor's
  fragment, `UPSTREAM-FEEDBACK.md` U1/U4); the warm loop route currently returns
  the decision without a packaged certificate.
- vs-Kani is the named SOTA competitor; that scoreboard is install-gated.
