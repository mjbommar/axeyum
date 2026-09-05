# The independent-replay census, over every carrier the kernel builds

Measured 2026-09-05 at commit `3328d2a80` (lane `lean-replay-census-all`),
host: shared dev box, uptime 23 days, **not idle** (load average 22.97 /
26.85 / 26.57 immediately before the run — the `seconds` column below is
therefore an upper bound and not a benchmark).

Decision: [ADR-1661](../../docs/research/09-decisions/adr-1661-the-replay-census-covers-every-carrier-and-type-valued-theorems-are-a-named-class.md).
Predecessor: [ADR-0760](../../docs/research/09-decisions/adr-0760-independent-replay-is-graded-per-declaration-by-name.md),
which built the same census over the constructed reals alone.

## The question

`docs/math-department/14-lean-lang.md`, Next Ten item 2: *replay every proved
theorem in pinned Lean, or name the reason.* Before this run, the answer
existed for one carrier out of sixteen, so the chair's headline — *N
axiom-free results* — could not be paired with *and pinned Lean's kernel
accepts M of them*.

Reviewer 02 (constructive analysis) asked the same thing from the other end:
`creal` replays into Lean, "but as a census artifact, not a library; 48
theorems are `Type`-valued and Lean's kernel refuses them as theorems." That
class had a count and no names.

## Which Lean

The **cross-check pin** ([ADR-1660](../../docs/research/09-decisions/adr-1660-there-are-two-lean-pins-and-every-claim-names-which-one-it-means.md)
disambiguates the two pins): `lean-toolchain` = `leanprover/lean4:v4.34.0-rc1`,
resolved to
`~/.elan/toolchains/leanprover--lean4---v4.34.0-rc1/bin/lean`, reported as
`Lean (version 4.34.0-rc1, x86_64-unknown-linux-gnu, commit
3447a668783dbce1a8fdb97101dd067687b2b418, Release)`, `matches_pin=true` on
every one of the eighteen `AXEYUM-LEAN-TOOLCHAIN` lines the two suites
printed. Nothing here touches the Mathlib **corpus** pin (Lean 4.30.0,
mathlib4 `c5ea0035`), which is a different pin and does not move with this
one.

The `lean_version` label inside the export header still reads `4.30.0`. That
is a statement about the **wire format** the stream targets, not about the
binary that replayed it; `Lean4ExportMetadata::axeyum` sets `lean_githash` to
`axeyum-lean-kernel` precisely because nothing in the stream came from a Lean
binary.

## Method

Per carrier, on a fresh `Kernel`:

1. **Build** the carrier through the ordinary trusted gate
   (`Kernel::add_declaration`); the census reads `kernel.environment()`
   afterwards, so the population is the whole carrier and never a sample.
2. **Classify** every declaration into one of three typed classes.
   `Prop`-ness is read from the kernel by inference
   (`infer` → `whnf` → `Sort 0`), never from a name or a doc comment:
   - `representable` — the wire format carries it and Lean's kernel will
     accept its kind;
   - `theorem_type_not_prop` — a `Declaration::Theorem` whose type is not a
     proposition. `Lean.Environment.addDeclCore` refuses a `theorem` whose
     type does not live in `Prop`;
   - `blocked_by_dependency` — its dependency closure reaches one of those,
     with the blocker named.
3. **Export** the representable slice as `lean4export` NDJSON
   (`render_lean4export_ndjson_roots`).
4. **Replay** it through the pinned `lean` binary with
   `scripts/lean/replay-lean4export.lean --emit-names`, which dumps
   `env.constants` — **Lean's own environment**, not our stream.
5. **Grade** each declaration by membership of *its own name* in that set.
   `grade` consults no family, no module, no prefix and no sibling.
6. **Assert** `missing == 0`, `extra == 0`, and a per-carrier monotone floor.

Shared harness: `crates/axeyum-lean-kernel/tests/support/replay_census.rs`,
included by `#[path]` into both suites so they cannot drift.

### Reproduce

```sh
scripts/cargo-serialized.sh test --release -p axeyum-lean-kernel \
  --test real_lean_replay_census_all --no-run
# then run the built binary directly -- the cargo wrapper takes a host-wide
# flock, so timing it measures the queue rather than the work:
AXEYUM_REQUIRE_LEAN=1 ./target/release/deps/real_lean_replay_census_all-* \
  --test-threads=1 --nocapture
AXEYUM_REQUIRE_LEAN=1 ./target/release/deps/real_lean_replay_census-* \
  --test-threads=1 --nocapture          # the `creal` row
```

`--test-threads=1` is belt-and-braces here: the suite holds a
`static ONE_CARRIER_AT_A_TIME: Mutex<()>` across each carrier's build and
census, because `scripts/check-lean-gate.sh` runs registered suites with the
default thread count and seven of these carriers hold a full `CReal` kernel.
A rule written only in a module header is enforced only on whoever read it.

## The result

`ok. 20 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in
738.79s` for `real_lean_replay_census_all` (17 carriers × 1 Lean invocation,
plus 3 tests that need no Lean), and `ok. 5 passed; 0 failed … finished in
104.18s` for `real_lean_replay_census` (the `creal` row, 6 Lean invocations).
**No carrier was skipped and none was left unrun.**

| carrier | population | representable | replayed | `Type`-valued | blocked | missing | seconds |
|---|---:|---:|---:|---:|---:|---:|---:|
| `logic` | 99 | 99 | 99 | 0 | 0 | 0 | 5.2 |
| `axreal` | 129 | 129 | 129 | 0 | 0 | 0 | 3.8 |
| `nat` | 1,990 | 1,990 | 1,990 | 0 | 0 | 0 | 7.0 |
| `ipc_eval` | 2,003 | 2,003 | 2,003 | 0 | 0 | 0 | 6.2 |
| `list` | 2,021 | 2,021 | 2,021 | 0 | 0 | 0 | 7.0 |
| `ipc` | 2,040 | 2,040 | 2,040 | 0 | 0 | 0 | 6.0 |
| `string` | 2,086 | 2,086 | 2,086 | 0 | 0 | 0 | 6.0 |
| `int` | 2,391 | 2,391 | 2,391 | 0 | 0 | 0 | 6.3 |
| `characterization` | 2,427 | 2,427 | 2,427 | 0 | 0 | 0 | 6.5 |
| `rat` | 2,997 | 2,997 | 2,997 | 0 | 0 | 0 | 8.6 |
| `creal` | 3,617 | 3,542 | 3,542 | 49 | 26 | 0 | 104.2 (whole suite) |
| `arith_models` | 3,713 | 3,638 | 3,638 | 49 | 26 | 0 | 21.7 |
| `cpoint` | 3,766 | 3,691 | 3,691 | 49 | 26 | 0 | 34.5 |
| `complex` | 3,767 | 3,692 | 3,692 | 49 | 26 | 0 | 17.5 |
| `metric` | 3,863 | 3,788 | 3,788 | 49 | 26 | 0 | 39.6 |
| `rn` | 3,921 | 3,846 | 3,846 | 49 | 26 | 0 | 25.9 |
| `intspace` | 3,961 | 3,877 | 3,877 | 50 | 34 | 0 | 36.5 |
| **`everything`** | **4,478** | **4,394** | **4,394** | **50** | **34** | **0** | **25.1** |

**These rows nest and must not be added up.** `rn` ⊇ `metric` ⊇ `cpoint` ⊇
`creal` ⊇ `rat` ⊇ `int` ⊇ `nat` ⊇ `logic`; `ipc` ⊇ `ipc_eval`'s content
(`build_ipc_soundness_prelude` calls `ipc_eval::declare_eval` itself);
`characterization` ⊇ `int`; `list`, `string` ⊇ `nat`; `arith_models` ⊇
`axreal` and `creal`. Summing them counts most declarations six or seven
times. The `everything` row exists for exactly this reason: it builds every
carrier into **one** kernel, so it is a union, and it is the only row a
headline may be read from.

### The headline

> Of **4,478** declarations this kernel proved, pinned Lean's kernel accepts
> **4,394**; **50** are `Type`-valued theorems it refuses as theorems, and
> **34** are blocked behind one of those.

`seconds` covers classification, export and the Lean run — not the prelude
build, which dominates and is not what is being measured. The whole
`real_lean_replay_census_all` binary, all 20 tests, was 738.79 s.

## The two non-representable classes, named

### `theorem_type_not_prop` — 50 declarations

Every one is a `Declaration::Theorem` this kernel admitted whose **type is
not in `Prop`**. Lean's `Environment.addDeclCore` refuses such a thing as a
`theorem`; in Lean it would have to be a `def`. This is deliberate on our
side and the reason is written down in `creal/uniform_convergence.rs`:
`CReal.UniformConvergesOn` is `Type`-valued because `Exists.rec` cannot
eliminate into `Type`, so the convergence *rate* has to be data rather than
an existential. The same argument makes `CReal.UniformlyContinuousOn` and
`CReal.HasDerivativeAt` carry their moduli as data.

It is **not a demonstrated soundness hole** — nothing here shows a wrong
statement — but it is a real gap in *independent checkability*: for these 50,
no other kernel has been asked to confirm what we admitted, and the census
says so rather than absorbing them into a percentage.

That Lean really does refuse them for this reason is **earned, not
asserted**: `lean_really_does_refuse_a_theorem_whose_type_is_not_a_proposition`
hands pinned Lean `CReal.weierstrassMTest` on its own and requires the
rejection to say `REAL LEAN KERNEL REJECTED`, to say `is not a proposition`,
and to name that declaration.

- `CReal.cosFnPartialHasDerivative`
- `CReal.cosFnTermHasDerivative`
- `CReal.cosFnUniformConverges`
- `CReal.cosFnWideHasDerivative`
- `CReal.cosFnWideUniformConverges`
- `CReal.cosFnWideUniformlyContinuous`
- `CReal.evtLinear_uniformly_continuous`
- `CReal.expFnUniformConverges`
- `CReal.hasDerivativeOn_restrict`
- `CReal.hasDerivative_add`
- `CReal.hasDerivative_antiderivative`
- `CReal.hasDerivative_antiderivative_of_uc`
- `CReal.hasDerivative_chain`
- `CReal.hasDerivative_chain_id_sq`
- `CReal.hasDerivative_congr`
- `CReal.hasDerivative_const`
- `CReal.hasDerivative_cube`
- `CReal.hasDerivative_id`
- `CReal.hasDerivative_integral_const`
- `CReal.hasDerivative_mul`
- `CReal.hasDerivative_neg`
- `CReal.hasDerivative_pow`
- `CReal.hasDerivative_pow_two`
- `CReal.hasDerivative_smul`
- `CReal.hasDerivative_sq`
- `CReal.hasDerivative_sub`
- `CReal.hasDerivative_uniform_limit`
- `CReal.ivtPlateau_uniformly_continuous`
- `CReal.powerSeriesUniformConvergesOn`
- `CReal.sinFnUniformConverges`
- `CReal.sinFnUniformlyContinuous`
- `CReal.uniformConvergesNeg`
- `CReal.uniformConvergesShift`
- `CReal.uniform_converges_add`
- `CReal.uniform_converges_geom_half`
- `CReal.uniform_converges_id`
- `CReal.uniform_limit_uniformly_continuous`
- `CReal.uniformlyContinuousOn_restrict`
- `CReal.uniformly_continuous_add`
- `CReal.uniformly_continuous_const`
- `CReal.uniformly_continuous_id`
- `CReal.uniformly_continuous_max`
- `CReal.uniformly_continuous_min`
- `CReal.uniformly_continuous_mul`
- `CReal.uniformly_continuous_neg`
- `CReal.uniformly_continuous_poly_example`
- `CReal.uniformly_continuous_sq`
- `CReal.uniformly_continuous_sub`
- `CReal.weierstrassMTest`
- `IntSpace.CReal.uniformly_continuous_abs`

Forty-nine of the fifty are in `CReal`; the fiftieth,
`IntSpace.CReal.uniformly_continuous_abs`, is in the integration space and
appears only in the `intspace` and `everything` rows.

### `blocked_by_dependency` — 34 declarations

These are ordinary `Prop`-valued theorems whose dependency closure reaches
one of the 50, so the stream cannot carry them either. The blocker is named
because "why can this not go" and "what is it waiting on" are different
findings — and the shape of the table is the actionable part: **26 of the 34
are blocked by only five declarations** (`hasDerivative_add`,
`hasDerivative_neg`, `uniformlyContinuousOn_restrict`,
`uniformly_continuous_const`, `uniformly_continuous_add`).

| declaration | blocked by |
|---|---|
| `CReal.abs_diff_le_of_deriv_bound` | `CReal.hasDerivative_add` |
| `CReal.abs_diff_sub_le_of_deriv_bound` | `CReal.hasDerivative_add` |
| `CReal.antiderivative` | `CReal.uniformlyContinuousOn_restrict` |
| `CReal.antiderivative_abs_le` | `CReal.uniformlyContinuousOn_restrict` |
| `CReal.antitone_of_nonpos_deriv` | `CReal.hasDerivative_neg` |
| `CReal.constant_of_zero_deriv` | `CReal.hasDerivative_neg` |
| `CReal.cosFnWide_one_equiv_cosOne` | `CReal.cosFnWideUniformConverges` |
| `CReal.cosFnWide_one_nonneg` | `CReal.cosFnWideUniformConverges` |
| `CReal.cosFn_one_equiv_cosOne` | `CReal.cosFnUniformConverges` |
| `CReal.cosWideNonpositive` | `CReal.cosFnWideUniformConverges` |
| `CReal.cosWideSeriesConverges` | `CReal.cosFnWideUniformConverges` |
| `CReal.expFn_one_equiv_e` | `CReal.expFnUniformConverges` |
| `CReal.integralSplitAnywhere` | `CReal.uniformlyContinuousOn_restrict` |
| `CReal.integralSplitArbitrary` | `CReal.uniformlyContinuousOn_restrict` |
| `CReal.integral_abs_le` | `CReal.uniformly_continuous_const` |
| `CReal.integral_abs_le_of_bound` | `CReal.uniformly_continuous_const` |
| `CReal.integral_by_parts` | `CReal.hasDerivative_add` |
| `CReal.integral_eq_antideriv_diff` | `CReal.hasDerivative_add` |
| `CReal.integral_eq_antideriv_diff_of_uc` | `CReal.hasDerivative_add` |
| `CReal.integral_sub_linear_le` | `CReal.uniformly_continuous_add` |
| `CReal.ivt_exact_root_at` | `CReal.hasDerivative_add` |
| `CReal.lipschitz_of_deriv_bound` | `CReal.hasDerivative_add` |
| `CReal.mvt_interiorExtremum` | `CReal.hasDerivative_add` |
| `CReal.rolle_interiorExtremum` | `CReal.hasDerivative_neg` |
| `CReal.sinFnLowerBoundOneToR` | `CReal.sinFnUniformConverges` |
| `CReal.strict_antitone_of_neg_deriv` | `CReal.hasDerivative_neg` |
| `IntSpace.CReal.integral_congr` | `CReal.uniformly_continuous_const` |
| `IntSpace.CReal.integral_nonneg` | `CReal.uniformly_continuous_const` |
| `IntSpace.CReal.integral_witness_independent` | `CReal.uniformly_continuous_const` |
| `IntSpace.crealInterval` | `CReal.uniformly_continuous_const` |
| `IntSpace.crealIntervalL1` | `CReal.uniformly_continuous_add` |
| `IntSpace.crealIntervalL1_dist` | `CReal.uniformly_continuous_add` |
| `IntSpace.crealInterval_integral` | `CReal.uniformly_continuous_const` |
| `IntSpace.crealInterval_total` | `CReal.uniformly_continuous_const` |

Two of these are flagship results that the `creal` suite grades explicitly:
`CReal.rolle_interiorExtremum` and `CReal.mvt_interiorExtremum` are
*accepted by Axeyum* and *not representable to Lean*, and the census prints
both grades separately rather than collapsing them.

## What was checked about the checker

**The floors are live.** Three of them fired during this lane's own
development, before being set to their measured values: `logic` at
`99 < 100`, `int` at `2371 < 2400`, and (after the merge that added
`int_prelude/two_squares.rs`) every `int`-derived carrier moved by exactly
20 declarations. A floor that no run has ever tripped is a floor nobody has
tested.

**`missing == 0` is live, and one mutant showed how.** Two mutants were run
against the `logic` carrier in an isolated worktree, both reverted before
committing:

| mutant | outcome |
|---|---|
| drop the **first** export root (`roots.remove(0)`) | **SURVIVED** — `missing=0`, test passed |
| drop the **last** export root (`roots.pop()`) | **KILLED** — `missing=1`, naming `Subtype.mk_eta`; the test failed |

The survivor is not a hole, and the reason is worth writing down:
`render_lean4export_ndjson_roots` emits the dependency **closure** of its
roots, so removing a root that some other root depends on changes nothing
about what Lean ends up holding — and the census's claim is exactly "Lean's
environment holds a constant of this name", which remains true. Removing a
*leaf* root removes a name, and the guard catches it and names it. So the
guard is sensitive to the only loss that matters, which is what a mutation
pass is for.

**The population is derived, not recalled.**
`every_public_prelude_builder_is_accounted_for` reads `src/lib.rs`'s `pub use`
re-export block — the authority for what this crate offers to build —
extracts every `build_*` name, and requires each to appear in the census's
`BUILDERS` table as a carrier, as covered by one, or as explicitly not a
carrier with a stated reason. It reported `carriers=17 builders=26` on this
run. It carries its own positive control: if the `pub use` scan does not find
`build_nat_prelude` and `build_creal_prelude`, it fails as a broken parse
rather than passing as "the crate exports no builders".

**The classifier discriminates.** `is_a_proposition` is checked in both
directions on a carrier cheap enough to build in seconds: `True : Prop` must
classify as a proposition and `Nat : Type` must not. Without both halves, a
classifier that had started saying "no" to everything would export an empty
slice and every `missing == 0` would pass over nothing.

## What this does NOT measure

- **It is not a Lean library.** A declaration replaying by name means Lean's
  kernel admitted the exported term. It does not mean anyone can `import` it:
  there is no Lake package and no `.lean` source (Next Ten item 3).
- **It says nothing about the 50.** They are named, not graded. Whether any
  of them can be restated in a `Prop`-valued form Lean would accept — and at
  what cost to the constructive content — is open work, and the five blockers
  above are where it would pay most.
- **It is not a statement about Mathlib.** Nothing here imports or compares
  against Mathlib; that is a different pin and a different question.
- **The `seconds` column is not a benchmark.** The host was carrying more
  than twenty concurrent jobs.
