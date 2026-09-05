# Lane: lean-tactic — `by axeyum` as a Lean tactic (Next Ten item 6)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE` for the ℕ fragment, `lean-tactic`, 2026-09-05).**
`docs/math-department/14-lean-lang.md` Next Ten item 6 is landed for ℕ:
`lean/axeyum-tactic` is a Lake package with no Mathlib dependency, exposing
`by axeyum` ([ADR-1666](../../research/09-decisions/adr-1666-by-axeyum-is-a-lean-tactic-and-lean-checks-the-term.md)).
The tactic serializes the already-elaborated goal as JSON, calls a Rust sidecar
(`crates/axeyum-lean-import/examples/axeyum_sidecar.rs`), and hands the proof
**term** that comes back to Lean's own parser, elaborator and kernel. There is
no `sorry` path, no `admit` path, and no axiom added anywhere in the package.

**Measured on the pinned toolchain** `leanprover/lean4:v4.34.0-rc1` (commit
`3447a668783dbce1a8fdb97101dd067687b2b418`), binary
`~/.elan/toolchains/leanprover--lean4---v4.34.0-rc1/bin/lean`:

| | |
|---|---|
| goals accepted | **11 of 11** (`Tests/NatLinear.lean`) |
| mutations rejected | **11 of 11** (`Tests/Mutations.lean`), 1 positive control |
| shim rows proved from Lean core | **13**, of which **10 depend on no axiom** and 3 reach `propext` |
| goals axiom-free end to end | 5 (the ring goals); the 6 order goals carry `propext` via `natLeOfAddLeAddRight` |

The goals are stated the way a Lean user states them — `+`, `*`, `≤`,
numerals, through `HAdd.hAdd` / `instLENat` / `OfNat.ofNat` — not with
`Nat.add` spelled by hand.

**The name-correspondence finding, which is the real result.** A rename is not
enough. The producers emit terms over `AxNat` in which every lemma is applied
with **all arguments explicit, in axeyum's own order**; Lean core takes most of
them implicitly and, in five cases, in a different order. Measured with
`crates/axeyum-lean-import/examples/axeyum_tactic_probe.rs` over an
eleven-goal battery: 20 constants, of which 9 are structural (map to Lean core
by name), 6 are `exact` (same explicit order) and 5 are `reordered`
(`AxNat.le.refl`, `le_trans`, `add_le_add_left`, `add_le_add_right`,
`le_of_add_le_add_right`). Zero needed a `derived` proof. Those 11 lemmas
route through `Axeyum.Shim` — one Lean theorem each, stated with axeyum's
signature and **proved from Lean core**, so the shim is the correspondence
table *and* its own check. The shim carries 13 rows: the 11 the battery
reached plus `natMulAssoc` and `natRightDistrib`, which `ring/nat.rs`'s
emitted-term table names but no goal in this battery exercised.

**Bounded, and stated as such.** ℕ only; quantifier-free; the goal must be a
`Eq`/`≤`/`<` over `+`, `*`, `succ`, `zero` and numerals ≤ 64, with ℕ's own
instances (a foreign `+` instance at ℕ is refused, not translated). Hypotheses
from the local context are used. The environment-identity check is a
**staleness** check and not a soundness one — a plain string comparison an
honest sidecar simply echoes, the same limit ADR-0935 recorded for C3.

**Did not build, with reasons measured rather than guessed:**

- **ℤ.** Blocked before any correspondence question: `linarith::int::prove`
  and `ring::int::prove` are `pub(crate)` in `axeyum-lean-kernel`, so no
  downstream crate can call them. Sized in ADR-1666 §"Fragment 3", including a
  name collision the ℕ side does not have — the ℤ carrier is interned as
  `Int`, not `AxInt` (`int_prelude.rs`, `let z = kernel.name_str(anon, "Int")`), so the name map has to become
  carrier-scoped.
- **The LRAT route for `Bool`/BV goals via `Std.Tactic.BVDecide`.** Not
  started. Needs a DRAT→LRAT conversion (our core emits DRAT, ADR-0012;
  `BVDecide` consumes LRAT), a `BitVec`/`Bool` goal fragment in the
  translator, and a second `accepted` shape carrying a certificate file rather
  than a term. Its own lane and its own ADR.

**Two defects real Lean found that no Rust-side test could have**, both on the
first run against Lean, both recorded in ADR-1666: `@` binds to the
*application node* rather than the head (so binary-application printing put
every `Eq.rec` argument one slot late), and the mutation battery was
**vacuous** because the tactic read `stx[1]` — the optional syntax node —
instead of `stx[1][0]`, so every stub silently fell back to the real sidecar
and "passed" by closing the goal it was meant to fail. The second was caught
only because `#guard_msgs` reported an *empty* message where an error was
expected.

**Gate:** `scripts/check-lean-tactic.sh`, registered in `scripts/check.sh` and
as `just lean-tactic` (on the `check:` dependency line beside `lean-adapter`).
It resolves the pin through `scripts/check-lean-gate.sh --print-toolchain`,
asserts the package's `lean-toolchain` equals the repository pin (the two-pin
distinction is ADR-1660; this package follows the **cross-check** pin), builds
the sidecar rather than assuming it, **deletes the `Tests` build products
first** so the counts are this run's and not a cache's, and enforces four
floors. Three negative controls run 2026-09-05, each failing differently:
removing one goal drops `goals-accepted` to 10 (floor 11); making a mutation
stop being a mutation fails the `lake build`; removing a shim row drops
`shim-rows` to 12 *and* fails the build with `Unknown constant`.

**Red found and not fixed:** none new. `14-lean-lang.md`'s three red gates were
being repaired in parallel by lane `lean-pin-gates`
([ADR-1660](../../research/09-decisions/adr-1660-there-are-two-lean-pins-and-every-claim-names-which-one-it-means.md),
merged into this lane's branch); this lane did not touch them.

**Next, in the order that serves the most chairs:** the ℤ fragment (one
visibility change plus a carrier-scoped name map), then `Tests/` goals drawn
from a real population rather than authored here, then the LRAT route.

<!-- plan-section: landed-changes -->

| 2026-09-05 | lean-tactic | ADR-1666 + `lean/axeyum-tactic` (Lake package: `Axeyum.Shim` 13 proved rows, `Axeyum.Protocol`, `Axeyum.Tactic` = `by axeyum`; `Tests/NatLinear` 11 goals accepted, `Tests/Mutations` 11 rejections + 1 control, `Tests/ShimCorrespondence` axiom census + reverse re-derivation) + `axeyum_lean_import::tactic_bridge` (goal decode, ℕ translator, name map, Lean printer, 11 unit tests) + `examples/axeyum_sidecar.rs` + `examples/axeyum_tactic_probe.rs` + `scripts/check-lean-tactic.sh` (4 floors, 3 negative controls) registered in `scripts/check.sh` and `just lean-tactic` |
