# Interpolation strength and shape — is there a consumer yet? (roadmap 3.7)

**Lane M3-7, 2026-09-10. Base `b424f4a9f`.**
Item **3.7** of [`docs/solver-comparison-2026-09/11-roadmap-and-plan.md`](../../solver-comparison-2026-09/11-roadmap-and-plan.md):

> **Interpolation strength and shape** — no strength parameter, no tree/sequence
> interpolants, decline on AB-mixed literals (`euf_interpolant.rs:503`). OpenSMT
> has six systems; SMTInterpol checks every leaf.
> *Measurement gate:* "Only when a consumer (IMC/PDR) needs it; those routes are
> themselves unwired (2.7)."

Item 2.7 landed on 2026-09-09/10 (`3724b4c1a`) and gave `pdr_lia.rs` /
`imc_lia.rs` a caller. This lane asks whether the gate is now open.

## Recommendation

**DO NOT BUILD.** The gate is still shut, and 2.7 did not open it.

Three numbers, each measured below:

1. **0 of 1,179 committed `.smt2` files, and 0 of the 84 SMT-LIB 2024 divisions
   on the NAS, can reach an interpolant at all.** Every interpolant consumer in
   the tree sits behind `solve_horn`, and `solve_horn` has no caller in `src/`.
   `(set-logic HORN)` is accepted and routed through the ordinary quantified
   ladder — item 2.7's record is **confirmed** (§2.2).
2. **Of the 7 `Int` transition systems committed to the repository, exactly 1
   reaches the interpolant, and today's interpolant proves it `Safe`.**
   `horn.rs::dispatch` runs PDR first; PDR decides 6 of 7. The interpolant is
   the binding constraint on **0 of 7** (§2.3).
3. On the one fragment 2.7 newly wired — **integers** — the reference solver
   that motivates this item **deleted its own strength knob**:
   `PTRef getFlexibleInterpolant(Real) = delete;  // not implemented for integers`
   (`LIAInterpolator.h:26-27`). And its default propositional system is
   McMillan, which is exactly the one we implement (§4.1).

What would settle it is named in §6: this is CANNOT-DETERMINE-shaped on the
*algorithm* question and DO-NOT-BUILD-shaped on the *sequencing* question. The
prerequisite is not a better interpolant. It is **an SMT-LIB CHC front door**
(recognising `(declare-fun P (…) Bool)` + universally quantified implications as
a `HornSystem`) plus a vendored CHC-COMP corpus. Until those exist there is no
population on which "stronger" or "differently shaped" can be scored.

## 1. The question, as a number

On how many committed or public benchmarks does the strength or shape of a Craig
interpolant cost us a verdict we would otherwise get?

**Answer: 0.** The denominator is empty in two independent senses — no benchmark
file reaches an interpolant (§2.1–2.2), and of the seven hand-written systems
that *can* reach one through the Rust API, six are decided before the
interpolant is consulted and the seventh is decided by it (§2.3).

## 2. The measurement

### 2.1 Who consumes an interpolant, statically

Every interpolator and its consumers. Commands and full output in §7.1.

| Interpolator | Consumed by | That consumer's caller in `src/` |
|---|---|---|
| `bv_interpolant::qf_bv_interpolant` | `imc.rs:65` (`prove_safety_imc`) | `horn.rs` `StateClass::Finite` |
| `lra_interpolant`, `lra_interpolant_cnf` | `imc_lra.rs:340`, `:347` | `horn.rs` `StateClass::Real` |
| `lia_interpolant`, `lia_interpolant_cnf` | `imc_lia.rs:376`, `:383` | `horn.rs` `StateClass::Int` **(new, 2.7)** |
| `euf_interpolant` (`qf_uf_interpolant`) | **nothing** | — |
| `uflra_interpolant`, `uflia_interpolant` | **nothing** | — |
| `axeyum_cnf::propositional_interpolant` | `bv_interpolant.rs:173` | (as row 1) |
| the 8-rung ladder `dispatch_interpolant` | `Solver::interpolant*` | **nothing** |

Two facts fall out of that table and they are the whole finding.

**(a) PDR consumes no interpolant.** `pdr.rs`, `pdr_lra.rs` and `pdr_lia.rs`
contain the substring `interpolant` **zero** times; `pdr_lia.rs` generalises with
`mbp_lia` (model-based projection). The roadmap row says "a consumer (IMC/PDR)";
only IMC is one. And `horn.rs::dispatch` tries **PDR first in all three
families** — the interpolating engine is the *fallback*, entered only on
`PdrLiaOutcome::Unknown` (`horn.rs:769-778`).

**(b) The chain terminates at the public Rust API, not at the front door.**
`solve_horn` has no caller in `src/`, by design and by its own module doc
(`horn.rs:164-172`, "No in-crate caller by design"). `Solver::interpolant`,
`interpolant_certified` and `interpolant_explained` have **no non-test caller**
anywhere in `crates/`. So the only interpolant consumers in this tree are
reachable exclusively by a Rust program that calls `axeyum_solver::solve_horn`
or `Solver::interpolant` itself.

**This is not what 2.7 changed.** `StateClass::Real` → `imc_lra` and
`StateClass::Finite` → `imc` *already* routed this way before `3724b4c1a`; that
commit's diff adds the third of three families. If mere reachability satisfied
item 3.7's gate, the gate was open before today. It was not, and it is not.

### 2.2 What `(set-logic HORN)` does — item 2.7's record, re-run

Item 2.7 recorded HORN as "accepted and routes nothing … worse than absent,
because it looks like support". **Confirmed.**

`smtlib.rs:3400` — `if name == "ALL" || name == "HORN" { return true; }` inside
`is_smtlib_logic_name`, whose only use is to decide between a `success` ack and
an `Unsupported` response (`smtlib.rs:3552-3563`). The logic name is never read
again. `auto.rs` (the front door) contains the substrings `horn`/`chc`
**0** times, against a positive control of 3 for `dispatch_pure_qf_abv`.

Run through the shipping front door (`solve_smtlib`), on the two CHC systems
`tests/horn_lia.rs` drives through `solve_horn`, restated in standard SMT-LIB
CHC syntax:

```
SAFE_CHC     (a CHC solver says sat) -> Ok(SmtLibOutcome { result: Unknown(UnknownReason { kind: Incomplete, detail: "instantiation is satisfiable; the universal may still be violated outside the instantiated terms" }), logic: Some("HORN"), expected_status: None })
UNSAFE_CHC   (a CHC solver says unsat) -> Ok(SmtLibOutcome { result: Unknown(UnknownReason { kind: Incomplete, detail: "instantiation is satisfiable; the universal may still be violated outside the instantiated terms" }), logic: Some("HORN"), expected_status: None })
CONTROL_QF_LIA (must be sat) -> Ok(SmtLibOutcome { result: Sat(Model { entries: [(SymbolId(0), Int(3))], functions: [], real_div_zero: [], uninterpreted_cardinalities: [], quantified: None }), logic: Some("QF_LIA"), expected_status: None })
```

The positive control fires (`QF_LIA` → `Sat` with a model). Both CHCs — the
safe one, whose invariant `x ≥ 0` `solve_horn` finds in milliseconds, and the
unsafe one, whose counterexample is three `+1` steps — come back `Unknown` from
the quantified instantiation ladder. `logic: Some("HORN")` shows the name was
parsed and kept; nothing acted on it.

**One correction to the framing.** "Worse than absent" is about the *advertised*
support, not about soundness: both verdicts are a sound `unknown` with an honest
reason, not a wrong answer. The cost is a benchmark silently scoring 0 instead of
being routed to an engine that would decide it.

### 2.3 The PDR × IMC decision matrix — does interpolant quality bind?

The load-bearing measurement. `horn.rs` reaches `prove_safety_imc_lia` only when
`prove_safety_pdr_lia` returns `Unknown`, so I ran **both** engines over **every
`Int`-sorted `TransitionSystem` committed to the repository** — the four in
`tests/imc_lia.rs` and the five in `tests/pdr_lia.rs`, seven distinct systems
after de-duplication (`IntAccumulator` and `ReachesThree` appear in both files;
`IntAccumulator`'s two definitions are byte-identical apart from the doc comment
and one blank line, verified by `diff`).

```sh
cargo test -p axeyum-solver --features full \
    --test pdr_imc_lia_reachability_probe -- --ignored --nocapture
```

```
running 1 test
--- M3-7 PDR x IMC matrix over every committed Int transition system ---
MonotoneLowerBound       pdr=SAFE       imc=SAFE       imc_reached_in_horn=no
IntAccumulator           pdr=SAFE       imc=SAFE       imc_reached_in_horn=no
DisjunctiveTwoRegion     pdr=SAFE       imc=SAFE       imc_reached_in_horn=no
TwinCounters             pdr=SAFE       imc=SAFE       imc_reached_in_horn=no
EvenStepperOddTarget     pdr=unknown    imc=SAFE       imc_reached_in_horn=YES
ReachesThree             pdr=REACHABLE  imc=REACHABLE  imc_reached_in_horn=no
UnboundedReachesFive     pdr=REACHABLE  imc=REACHABLE  imc_reached_in_horn=no
--- systems=7 reach_imc=1 imc_rescues=1 ---
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 5.20s
```

Reproduced identically on two runs (2m30s cold build, 5.2s warm).

Read it:

- **`reach_imc = 1 of 7`.** PDR decides six systems — four `Safe`, two
  `Reachable` — before the interpolant is consulted. Only
  `EvenStepperOddTarget` (`init : x = 0`, `trans : x' = x + 2`, `bad : x = 1`;
  the parity system whose real relaxation is unsafe) falls through.
- **`imc_rescues = 1 of 1`.** On that one system today's `lia_interpolant_cnf` /
  `lia_interpolant` pair produces an interpolant good enough to close the
  fixpoint, and the invariant passes the three independent `check_auto` gates.
- **So the interpolant is the binding constraint on 0 of 7.** There is no
  committed `Int` shape where IMC is entered and fails.

A stronger or differently shaped interpolant would move zero of these rows.

**Side finding (not fixed here).** `tests/imc_lia.rs:74-80` and `:381-387` still
say `IntAccumulator` "declines to `Unknown`" because "no disjunctive integer
fallback exists yet". The matrix says `imc=SAFE`: the disjunctive route landed
and closed it. The test passes either way (it accepts `Safe` with a re-check), so
nothing is red — but the comment now states the opposite of the behaviour. Worth
a one-line fix by whoever owns that file.

## 3. Coverage and controls

The trap named in the shared brief is an empty result from a probe that never
reached its subject. What each probe examined, and what fired:

| Probe | Examined | Positive control |
|---|---|---|
| Interpolator consumer map (§2.1) | all 8 `*_interpolant` modules + `propositional_interpolant`, grepped over `crates/` | `.interpolant(` finds 5+1+1 hits in `tests/` while finding 0 in `src/` — the grep form works |
| `auto.rs` CHC recognition (§2.2) | `auto.rs`, 0 hits for `horn|chc` | `dispatch_pure_qf_abv` → 3 hits in the same file |
| HORN front door (§2.2) | 3 scripts through `solve_smtlib` | `CONTROL_QF_LIA` → `Sat` with a model |
| PDR × IMC matrix (§2.3) | **7 of 7** committed `Int` systems; the probe asserts `total == 7` so a dropped row fails the test | `ReachesThree`/`UnboundedReachesFive` return `REACHABLE`, `MonotoneLowerBound` returns `SAFE` — the harness distinguishes all three outcomes |
| Committed corpus (§2.1) | 1,179 `.smt2` under `corpus/`, 0 containing `set-logic HORN` | — |
| NAS (§2.1) | 84 division directories under `/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/`, and 84 `.tar.zst` under `_archives/` | the directory listing contains `QF_LIA`, `LIA`, `QF_SLIA` etc.; `*HORN*` matches nothing in either |

On the NAS: **SMT-LIB has no HORN division.** CHC benchmarks are distributed by
CHC-COMP, not by SMT-LIB, so no amount of sweeping the mounted corpus will
produce one. That is a fact about the corpus, not about the mount.

## 4. What we would be building, and in what order

The item names three candidates. With the consumer map in §2.1 they rank
themselves, and the ranking is not the one the item's evidence column suggests.

### 4.1 Strength parameterisation — LAST, and partly already done

OpenSMT's "six propositional interpolation systems" are six *labelled
interpolation systems over the resolution proof*, selected by
`:interpolation-bool-algorithm`. Its **default is `itp_alg_mcmillan` (0)**
(`SMTConfig.h:467`). Our propositional interpolant
(`axeyum-cnf/src/interpolant.rs`) is McMillan 2003 read off the elaborated LRAT
proof — the same system, and it is what `qf_bv_interpolant` uses
(`bv_interpolant.rs:173`). So "six vs one" compares their menu to our default,
not their default to ours.

The continuous knob is LRA-only, and OpenSMT **explicitly deletes it for
integers**: `PTRef getFlexibleInterpolant(Real) = delete;` with the comment
`// not implemented for integers` (`LIAInterpolator.h:26-27`). The one fragment
2.7 newly wired is exactly the integer one. Building a strength knob for `imc_lia`
would put us ahead of the field on an axis the field found not worth having, on a
route that today has one live shape and closes it.

### 4.2 Tree / sequence interpolants — FIRST, if anything

This is the only candidate whose shape matches the consumer we have.
`imc_lia.rs::interpolation_fixpoint` re-derives **one** interpolant per inner
iteration from a k-unrolling partitioned at position 1, and on a too-coarse `R`
it **resets `R := init` and deepens `k`** (`imc_lia.rs:345-425`). A sequence
interpolant `I₁ … I_k` from a single refutation is exactly what removes that
reset — it is the Vizel–Grumberg interpolation-sequence variant of McMillan IMC.
The gap analysis already sized this ("Medium … our IMC/PDR consumers would use
sequence interpolants directly",
[`05-yices-opensmt-smtinterpol.md:354`](../../solver-comparison-2026-09/05-yices-opensmt-smtinterpol.md)),
and it would apply to all three IMC engines at once, not just the integer one.

It is still not worth starting: the reset it removes fires on **0 of 7**
committed shapes (§2.3).

### 4.3 AB-mixed literal handling — no consumer at all

`euf_interpolant.rs:503` is `Color::Empty | Color::Mixed => return None` inside
`summarize`, a decline on a mixed-color congruence-explanation edge.
`qf_uf_interpolant` has **no consumer in `src/`** (§2.1): no IMC engine calls it,
and the only route into it is `dispatch_interpolant`, which itself has no
non-test caller. SMTInterpol's purification (`InterpolantPurifier`, the internal
`@EQ` predicate) fixes a decline nothing in this tree can currently trigger.

If a CHC front door lands, this stays last: CHC predicate vocabularies are
`Int`/`Real`/`BitVec`, so they route to the LIA/LRA/BV interpolators, not the
EUF one.

## 5. What this does NOT say

- It does not say our interpolators are strong. It says nothing consumes them,
  which is a different claim and a weaker one.
- It does not contradict item 2.8. `dispatch_interpolant_certified` routes six of
  seven rungs through their certified variants and all eight interpolators
  enforce Craig symbol containment; both remain true. §2.1 adds only that the
  *ladder* has no non-test caller — 2.8 wired `certify_*` into `dispatch`, and
  `dispatch` into nothing.
- It does not contradict 2.8b. `certify_qf_bv` being shadowed by the ground-EUF
  rung and `certify_uflia` being unreached are properties **inside** the ladder;
  this note is about the ladder's own reachability.
- It does not say 2.7 was not worth doing. 2.7 turned a 1,771-line dead branch
  into a live one and the matrix in §2.3 exists because of it.

## 6. What would settle it

Not a better interpolant. In order:

1. **An SMT-LIB CHC front door.** Recognise `(declare-fun P (…) Bool)` plus
   universally quantified implication assertions as a `HornSystem` and route to
   `solve_horn`. `horn.rs:164-172` already names this as the missing work and
   places it "in the front door, not in this module". Exit criterion: the two
   scripts in §2.2 return `sat` and `unsat`, not `unknown`.
2. **Vendor a CHC-COMP slice** (there is no HORN division in SMT-LIB, §3), with
   `:status`, into `corpus/regression/`.
3. **Re-run the §2.3 matrix over that corpus**, not over seven hand-written
   systems. The number to watch is `reach_imc` — how many benchmarks PDR fails
   and IMC is asked about — and then, within those, how many IMC also fails.
4. **Re-open item 3.7 only if that second number is nonzero**, and let the
   *reason* IMC failed choose between §4.1, §4.2 and §4.3 rather than choosing
   in advance. Today the reason would have to be invented.

A cheap intermediate signal, if someone wants one before step 1: the `Real` and
`Finite` families of `horn.rs` have their own committed systems
(`tests/imc_lra.rs`, `tests/imc.rs`, `tests/pdr_lra.rs`, `tests/pdr.rs`). The
same matrix over those would say whether `reach_imc = 1 of 7` is an integer-only
artefact of PDR's strength or holds across all three engine families. I did not
run it (§8).

## 7. Reproduction

### 7.1 The static consumer map

```sh
# Callers of each interpolator, excluding the module itself and `lib.rs` re-exports.
for f in euf_interpolant bv_interpolant lia_interpolant lia_interpolant_cnf lra_interpolant_cnf; do
  echo "=== $f"
  grep -rn "\b$f\b" --include=*.rs crates/axeyum-solver/src/ \
    | grep -v "^crates/axeyum-solver/src/$f.rs" | grep -v '//'
done

# PDR uses no interpolant at all.
grep -c "interpolant" crates/axeyum-solver/src/pdr_lia.rs \
                      crates/axeyum-solver/src/pdr_lra.rs \
                      crates/axeyum-solver/src/pdr.rs
# -> crates/axeyum-solver/src/pdr_lia.rs:0
#    crates/axeyum-solver/src/pdr.rs:0
#    crates/axeyum-solver/src/pdr_lra.rs:0

# `solve_horn` has no caller in src/.
grep -rn "solve_horn" --include=*.rs . | grep -v "/tests/"
# -> only capabilities.rs prose, horn.rs's own definition, and two lib.rs re-exports.

# The 8-rung ladder has no non-test caller.
grep -rn "\.interpolant(\|\.interpolant_certified(\|\.interpolant_explained(" \
    --include=*.rs crates/ | grep -v "/tests/"
# -> (empty).  Positive control: the same pattern finds 5 / 1 / 1 hits in
#    tests/dispatch_interpolant_certified.rs, tests/euf_interpolant.rs, tests/interpolant.rs.

# auto.rs never mentions Horn or CHC.
grep -c -iE "horn|chc" crates/axeyum-solver/src/auto.rs      # -> 0
grep -c "dispatch_pure_qf_abv" crates/axeyum-solver/src/auto.rs  # -> 3 (control)
```

### 7.2 The corpus counts

```sh
find corpus -name '*.smt2' | wc -l                    # -> 1179
grep -rl "set-logic *HORN" corpus/ | wc -l            # -> 0
ls /nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/ | wc -l   # -> 84
ls -d /nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/*HORN*
# -> ls: cannot access ...: No such file or directory
ls /nas3/data/axeyum/corpus/smtlib-2024/_archives/ | wc -l                          # -> 84
ls /nas3/data/axeyum/corpus/smtlib-2024/_archives*/ | grep -i horn                  # -> (no match, exit 1)
```

### 7.3 The two probes

The PDR × IMC matrix (§2.3) is kept, `#[ignore]`d, at
`crates/axeyum-solver/tests/pdr_imc_lia_reachability_probe.rs`. It gates nothing;
its module doc records the measured triple and says what would move it. Re-run:

```sh
cargo test -p axeyum-solver --features full \
    --test pdr_imc_lia_reachability_probe -- --ignored --nocapture
```

The HORN front-door probe (§2.2) was thrown away — it is three `solve_smtlib`
calls and is reproduced in full here:

```rust
#![cfg(feature = "full")]
use axeyum_solver::{SolverConfig, solve_smtlib};

const SAFE_CHC: &str = "(set-logic HORN)\n\
(declare-fun Inv (Int) Bool)\n\
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n\
(assert (forall ((x Int) (y Int)) (=> (and (Inv x) (= y (+ x 1))) (Inv y))))\n\
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))\n\
(check-sat)\n";
// UNSAFE_CHC replaces the last assertion's `(< x 0)` with `(= x 3)`.
// CONTROL_QF_LIA is `(set-logic QF_LIA)` + `(assert (and (> x 2) (< x 4)))`.

#[test]
fn horn_front_door_probe() {
    for (name, script) in [/* the three above */] {
        println!("{name} -> {:?}", solve_smtlib(script, &SolverConfig::default()));
    }
}
```

## 8. What I did not measure

- **The `Real` and `Finite` engine families.** The §2.3 matrix covers `Int`
  only. Whether `reach_imc = 1 of 7` generalises is open, and §6 says how to
  find out. It does not change the recommendation, because §2.1–2.2 already
  make the denominator empty for all three families.
- **Anything on a public corpus.** There is nothing to run: no HORN division
  exists in SMT-LIB (§3) and no CHC corpus is vendored.
- **Whether a weaker interpolant would help `EvenStepperOddTarget`.** It does not
  need help; today's interpolant proves it `Safe`.
- **Timings.** Every verdict here is a decision class, not a runtime. The matrix
  runs in 5.2 s warm on a loaded box; I made no performance claim from it.
- **The `IntAccumulator` divergence question in the abstract.** Classic McMillan
  IMC is known to diverge on unbounded counters; on ours it does not, because the
  disjunctive `lia_interpolant_cnf` route closes it. I measured the behaviour, not
  the theory.
- **Whether `check_auto`'s quantified ladder could be made to decide a CHC
  directly**, without a Horn front door. §2.2 shows it returns `unknown` today
  with an `Incomplete` reason; I did not investigate whether MBQI or a different
  instantiation strategy could close it, and that question belongs to item 3.5.
