# Lane: collision-gap — wiring `build_characterization` into the cross-prelude collision gate

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, collision-gap, 2026-08-27).**
[144-denominator](144-denominator.md) fixed `prelude_theorem_inventory.rs`'s
`build_groups` (it never called `build_characterization`, so 32 genuine,
axiom-free theorems were invisible to the theorem-count denominator) and
**found, but deliberately left alone**, the identical gap one layer over in
`crates/axeyum-lean-kernel/src/cross_prelude_collision_tests.rs`. This lane
verified that claim independently, then closed it.

**Confirmed the gap was real by reading the file, not by trusting the prior
report.** `cross_prelude_collision_tests.rs`'s `build_groups` built `logic`,
`nat`, `axreal`, `integer`, `rat`, `string`, `creal`, `complex`, `cpoint` —
nine groups — and never called `build_characterization`, despite its own
module doc claiming the function "mirrors `examples/prelude_theorem_
inventory.rs`'s `build_groups`: same prelude list, same dependency order".
That comment was wrong for as long as the gap existed. Consequence: the 32
`Nat.Peano.*`/`Int.Characterization.*` declarations had never been checked
by [`cross_prelude_collisions`] for a name clash against any other prelude —
a DIFFERENT question from the theorem-count gap 144-denominator fixed, since
collision-checking spans every `Declaration` kind (definitions included),
not only theorems.

**Fix: added a `characterization` group**, built the same way
`prelude_theorem_inventory.rs` and `kernel_declaration_projection.rs` build
it (`build_characterization(&mut kernel)`, which builds `Int` — and
therefore `Nat`/`logic` — internally before admitting its own theorems), at
the same dependency-order position both other tools use (after `integer`,
before `rat`). Added a matching `DEPENDS_ON` entry,
`("characterization", Some("integer"))`, so `own_declarations` credits only
what `build_characterization` adds beyond `integer`, not `integer`'s own
declarations a second time.

**Result: no collision found.** `cross_prelude_declaration_names_are_disjoint`
passes with `characterization` now built and diffed against every other
prelude — stated plainly, not as a non-event: nobody had ever run this check
over those 32 declarations before, and now it has been run and the answer is
clean. `cargo test -p axeyum-lean-kernel --lib cross_prelude`: **2 passed**
(unchanged count — both pre-existing tests, `cross_prelude_declaration_names_
are_disjoint` and the negative control), same as before the fix; the new
group changes what the first test covers, not how many tests exist. ~84s
(debug; the constructed carriers force `on_a_deep_stack`).

**Mechanism added so a fourth prelude group cannot be silently forgotten by
any of the three `build_groups` implementations again.** Extended
`scripts/check-theorem-inventory-completeness.py` (already comparing
`kernel_declaration_projection`'s and `prelude_theorem_inventory`'s distinct
theorem-name sets) with a second, independent comparison: the set of
prelude-group LABELS each of the three tools' `build_groups` actually
covers — `kdp_prelude_labels`/`pti_prelude_labels` read the label column
from each tool's real TSV output; `collision_group_labels` reads
`cross_prelude_collision_tests.rs`'s own source text for its
`Group { label: "...", ... }` literals, since a `#[test]` has no runnable
TSV output to compare. `check_group_labels` fails, naming the exact label
and which of the three implementations is missing it, on any label present
in one and absent from another — checked pairwise across all three, not
just the two `check()` already covered. Run for real against the fixed
tree: **10 prelude-group labels agree across all three `build_groups`
implementations** (`logic`, `nat`, `axreal`, `integer`, `characterization`,
`rat`, `string`, `creal`, `complex`, `cpoint`).

**Unit tests:** `scripts/tests/test_theorem_inventory_completeness.py` grew
from 11 to 20 cases (9 new, in a new `GroupLabelAgreementTests` class) —
agreement, each of the three pairwise "one tool is missing a group"
directions (reproducing the actual `characterization` gap in the
`cross_prelude_collision_tests`-only direction), a control confirming the
`negative_control` submodule's synthetic labels (a subset of `build_groups`'
real ones) cannot mask a real gap by "supplying" a missing label, and the
empty/malformed-input guards for the three new extraction functions.

**Every new guard mutation-verified, in a scratch copy under `/tmp`, never
the shared checkout.** First automated sweep produced a FALSE result — two
mutations (`kdp_prelude_labels`'s and `pti_prelude_labels`'s empty-result
guards) each reported killing the SAME two `collision_group_labels` tests,
which is impossible by inspection. Cause: the documented "hand-rolled
mutation loop over a Python file reports the previous mutant's result" trap
— equal-size mutations applied back-to-back within one second hit Python's
`(mtime-in-whole-seconds, size)` bytecode cache key. Fixed by clearing
`__pycache__` before every run rather than once; re-run, all six guards
killed cleanly with no overlap:

| guard | mutation | killed |
|---|---|---:|
| `check_group_labels`'s `if missing:` | forced `False` | 4 (all three "one tool short" tests + the negative-label-masking control) |
| `collision_group_labels` empty-result guard | forced `False` | 2 |
| `kdp_prelude_labels` empty-result guard | forced `False` | 1 |
| `pti_prelude_labels` empty-result guard | forced `False` | 1 |
| `kdp_prelude_labels` malformed-row guard | forced `False` | 1 |
| `pti_prelude_labels` malformed-row guard | forced `False` | 1 |

No survivors. Two of the six anchors (the malformed-row guards) initially
matched **two** locations each — `kdp_theorem_names`/`kdp_prelude_labels`
and `pti_theorem_names`/`pti_prelude_labels` share identical guard text —
and had to be re-anchored on each function's distinguishing docstring text
before the mutation tool would apply cleanly to the intended one; the
anchor-count check (borrowed from `scripts/tests/mutation_controls.py`'s
"NOT APPLIED" outcome) is what caught that rather than silently mutating the
wrong copy. Not wired into `scripts/tests/mutation_controls.py` itself this
round, matching 144-denominator's own note: that registry is a large,
actively-appended shared file, and this script's manual mutation evidence
already satisfies the "guard nothing kills is decoration" bar.

**Verified:** `python3 scripts/check-theorem-inventory-completeness.py`
(real cargo run, no substitution flags) — `1450 distinct theorem names
agree` and `10 prelude-group labels agree across all three build_groups
implementations`, exit 0. `python3 scripts/validate-facts.py` — **1,383
facts, 0 errors**, unchanged by this lane (no fact files touched, as
scoped). `python3 -m unittest scripts.tests.test_theorem_inventory_
completeness` — 20 passed.

<!-- plan-section: landed-changes -->

| 2026-08-27 | collision-gap | Wired `build_characterization` into `cross_prelude_collision_tests.rs`'s `build_groups` at the same dependency-order position the other two theorem/declaration inventory tools use; confirmed no cross-prelude name collision exists for the 32 `Nat.Peano.*`/`Int.Characterization.*` declarations. Extended `scripts/check-theorem-inventory-completeness.py` with a three-way prelude-group-label agreement check (`kdp_prelude_labels`/`pti_prelude_labels`/`collision_group_labels`/`check_group_labels`) so a fourth prelude group omitted from any of the three `build_groups` implementations fails loudly instead of silently; 9 new unit tests (20 total), all 6 new guards mutation-verified with no survivors after fixing a stale-`__pycache__` false-kill in the mutation sweep itself. |
