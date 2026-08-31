# Lane: draw11-theorems-c — proving theorems from the refilled dispatch queue (ADR-0925 draw 11), continued

<!-- plan-section: lane-status -->

**Done (`DONE`, draw11-theorems-c, 2026-08-31).** Measured 31 dispatchable at
session start (`python3 scripts/check-dispatchable-frontier.py`), minus the
targets flagged already-taken by sibling lanes that day. Closed **9**
`ml430` mirrors, all axiom-free on the Nat prelude's trusted surface
(`nat_axiom_inventory --require-axiom-free nat` exits 0 throughout):

- `Nat.bit_false_zero`, `Nat.bit_le`, `Nat.bit_ne_zero`, `Nat.bit_lt_bit`,
  `Nat.bit_add_left`, `Nat.bit_add_right` (six facts, one new module
  `nat_prelude/bit_extra.rs`). Two real bugs found and fixed by running the
  `nat_prelude::` sweep before flipping anything: (1) `declare_bit_extra_all`
  was first wired in right after `declare_bit_all`, but `bit_ne_zero`
  references `Nat.mul_lt_mul_left`, which is not declared until
  `declare_mul_lt_mul_iff` runs much later — `UnknownConst`, fixed by moving
  the call site; (2) `bit_lt_bit` passed `lt_succ_self(mul2m)` where
  `lt_succ_self(succ_mul2m)` was needed — a `TypeMismatch` from a genuinely
  wrong lemma instantiation, not a wiring problem. Both are recorded in the
  commit messages, not just fixed silently.
- `Nat.size_one` (free by construction — `Eq.refl`, `size 1` already reduces
  to `1` by delta+iota, confirmed by an existing test) and `Nat.size_eq_zero`
  (routes through the already-proved `lt_pow_size`). New module
  `nat_prelude/size_extra.rs`.
- `Nat.add_choose_mul_factorial_mul_factorial` — `(i+j).choose j * i! * j! =
  (i+j)!`. The falling-factorial/`choose` bridge already in
  `desc_factorial.rs` gave `descFactorial(i+j,j) = j! * choose(i+j,j)` for
  any `n,k`, but nothing tied `descFactorial` back to plain `factorial` by
  the complementary `i!`. New module `nat_prelude/choose_factorial_add.rs`
  supplies exactly that missing piece — `descFactorial(i+j,j) * i! =
  (i+j)!` — by induction on `j` with `i` fixed, routed through the existing
  "front-peel" identity `desc_factorial_succ_eq_succ_mul` rather than
  `desc_factorial`'s own bottom-peeling recursion (which would need
  `Nat.sub` reasoning at a moving index — `i + succ j` is `refl`-`succ(i+j)`,
  so the front-peel form needs no rewrite to line up). Admitted on the first
  kernel attempt.

Every new declaration has a concrete-instance test (new files
`bit_extra_tests.rs`, `size_extra_tests.rs`,
`choose_factorial_add_tests.rs` — kept separate from the dense
`nat_prelude_tests.rs` per this session's own merge-hazard note) with a
genuinely-discriminating negative control each. One control was caught and
fixed as vacuous before landing: `bit_add_left`'s and `bit_add_right`'s
5-splits both total 11 (`4+7=11`, `5+6=11`), so comparing them against each
other proved nothing — replaced with a split totaling a different value
(12). All nine facts flipped to `proved` with kernel-term + axiom-footprint
evidence, `depends_on` derived via `check-fact-depends-derived.py --fix`
(one, `Nat.bit_false_zero`, correctly gets none — its proof is a bare
`Eq.refl`), and statements pinned via
`check-settled-fact-statements.py --write`.

**Full `nat_prelude::` sweep after every change: 248 passed, 0 failed**
(240 baseline for the six bit facts alone, +5/+2/+1 for the new test files,
no regressions at any step). Clippy clean on `cargo clippy -p
axeyum-lean-kernel --lib -- -D warnings` (note: `--tests` fails to compile
for reasons unrelated to this lane — two PRE-EXISTING integration test files,
`tests/real_lean_replay_census.rs` and
`tests/real_lean_creal_carrier_kernel_replay.rs`, fail `clippy::doc_markdown`
and `clippy::too_many_lines`/`clippy::similar_names`; confirmed by reading
those files, neither was touched this session).

Holdout isolation: `python3 scripts/check-autogenesis-holdout-isolation.py`
→ `PASS`, `held_out=146`, measured before this lane's first fact edit and
again after the last — unchanged both times. `artifacts/autogenesis/` was
never touched (confirmed via `git status`/`git diff`: zero files under that
path across this lane's eight commits).

**24 declined without attempting** (reported precisely, not silently
skipped): `Nat.minFac`/`Nat.testBit`/`Nat.multichoose`/`Nat.fastFib`
structurally-blocked divergences (11, unchanged from session start — these
are pinned in the divergence registry, not this lane's to reopen);
`F:ml430-nat-fermat-primefactors-one-lt-58343c6f` was already sized and
declined in detail by a sibling lane the same day
(`docs/plan/status/395-draw11-theorems.md` — needs multiplicative-order
theory plus a quadratic-reciprocity supplementary law, neither of which
exists in this prelude; re-verified the blocker is still real before
leaving it alone, per this file's own standing rule about stale blockers).
The remaining ~22 (int `gcd`/`Coprime`/`lcm` family, `Nat.squarefree`,
`Nat.ascFactorial`/`descFactorial` div/order facts, more `factorial`
monotonicity mirrors) were left for time reasons, not because they were
sized and found hard — the next lane should treat them as an open queue,
not a picked-over one.

**Hardest thing this session:** not any single proof step, but that the
`ml430`-mirror facts a lane touches most (`Nat.bit`, `Nat.size`) have very
few EXISTING lemmas already in the prelude to lean on compared to, say, the
`choose`/`factorial` family — most of `bit_extra.rs`'s six proofs had to be
built from raw order/algebra primitives (`mul_le_mul_left`,
`add_le_add_right`, `lt_of_lt_of_le`, …) rather than composing one or two
existing higher-level lemmas, which is exactly the shape that produces
wrong-argument bugs like the `lt_succ_self` one above. Running the full
`nat_prelude::` sweep — not just a targeted single-test check — before
flipping any fact status is what caught both bugs; a narrower check would
have missed the second one entirely (`bit_lt_bit`'s own concrete test,
written afterward, would have caught it too, but the sweep came first).

<!-- plan-section: landed-changes -->

| 2026-08-31 | `0a19a8faa` | wip: `nat_prelude/bit_extra.rs` (untested, compiles) |
| 2026-08-31 | `e0dbe1481` | fix: bit_extra build-order + `lt_succ_self` argument bugs; 240 nat_prelude:: tests pass |
| 2026-08-31 | `9455a7be2` | test: concrete-instance coverage for bit_extra's six theorems (245 pass) |
| 2026-08-31 | `e5dbb235b` | facts: flip six `Nat.bit` `ml430` mirrors to proved |
| 2026-08-31 | `03256ae48` | feat: `Nat.size_one` (refl) + `Nat.size_eq_zero`, with tests (247 pass) |
| 2026-08-31 | `ea4c884ae` | facts: flip `Nat.size_one`/`Nat.size_eq_zero` to proved |
| 2026-08-31 | `5018725f7` | feat: `Nat.add_choose_mul_factorial_mul_factorial`, with test (248 pass) |
| 2026-08-31 | `8f914f7ca` | facts: flip `Nat.add_choose_mul_factorial_mul_factorial` to proved |
