# Lane: fermat-easy — five `fermatNumber` mirrors (three closed reductions, oddness, strict monotonicity)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this dispatch`, fermat-easy, 2026-08-30).**
All five dispatched facts closed, axiom-free, in one new dispatcher
(`declare_fermat_number_easy_all`) appended to
`crates/axeyum-lean-kernel/src/nat_prelude/fermat_number_mirrors.rs`:

- `F:ml430-nat-fermatnumber-zero-ca7aac67` — `Nat.fermatNumber 0 = 3`
- `F:ml430-nat-fermatnumber-one-b1b0798f` — `Nat.fermatNumber 1 = 5`
- `F:ml430-nat-fermatnumber-two-3aa3bfc4` — `Nat.fermatNumber 2 = 17`
- `F:ml430-nat-odd-fermatnumber-251041a5` — `∀ n, Odd n.fermatNumber`
- `F:ml430-nat-fermatnumber-strictmono-acbcb8c6` — `StrictMono Nat.fermatNumber`

As ADR-0695 predicted, the three closed equations were pure `refl` once
stated — `fermat_number_evaluates_correctly` already asserted them by
`def_eq`, so declaring them as their own `Theorem`s (rather than test
assertions) was the entire task. **Largest formed numeral anywhere in this
lane: 17** (`fermatNumber 2 = 17`, the ceiling the brief set — `n = 3` would
form 257). The two general theorems (`odd_fermatNumber`,
`fermatNumber_strictMono`) are fully symbolic; their largest formed numeral
is the base `2`.

**`odd_fermatNumber`** reused the file's own private
`odd_fermat_number_local`/`even_pow_two_of_pos` helpers verbatim (already
built for `coprime_fermatNumber_fermatNumber`'s proof) — no new proof
machinery, just a new `d.theorem` wrapper stating it as its own declaration.

**`fermatNumber_strictMono`** did NOT go through `fermatNumber_mono` plus a
strict step (the brief's suggested route) — building directly with
`pow_lt_pow_of_lt` climbed twice turned out to be no harder than the
`Monotone` proof's `Le`-branch, since the `Lt` hypothesis needs no
`lt_or_eq_of_le` case split at all. The one new piece is
`add_lt_add_right_local` (`Lt a b → Lt (add a c) (add b c)`, via `add_comm` +
`add_lt_add_left`, since only the `Le`-strength `add_le_add_right` exists
directly in this prelude) — ~15 lines, transport-based, reusable by any
future `Lt`-shaped `+c` step.

**No blockers.** All five closed on the first construction attempt; no
handoff needed for a next lane.

**Two negative controls added for `fermatNumber_strictMono`** (per the
brief's "controls must discriminate" requirement, and a prior lane's caught
vacuous control on this same family): the argument-swapped conclusion
(`Lt (fermatNumber y) (fermatNumber x)`) is checked NOT `def_eq` to what's
proven, and a reflexive `Le` witness supplied at `m = n` is checked to be
REJECTED by `Kernel::infer` (`is_err()`) — the theorem's hypothesis slot is
strict `Lt`, not `Le`, and does not hold vacuously at equal arguments. A
third control on `odd_fermatNumber` confirms `Odd 5` is not `def_eq` to
`Even 5`.

Verification run: `scripts/cargo-serialized.sh test -p axeyum-lean-kernel
--lib nat_prelude::` — 222 passed, 0 failed (was 220 passed before this
lane's first commit, +1 failing on the coverage-inventory assertion until
the five new names were added to `theorem_names`; +2 total for the fixed
inventory test plus one new dedicated test). Confirmed the new test runs by
NAME (`nat_prelude::nat_prelude_tests::fermat_number_easy_mirrors_apply_at_
free_and_concrete_instances_with_two_negative_controls ... ok`, 1 passed).
`cargo fmt --all --check` clean. `cargo clippy -p axeyum-lean-kernel
--all-targets --all-features -- -D warnings` clean.

`python3 scripts/validate-facts.py` — 2270 facts, 0 errors (ran
`check-fact-depends-derived.py --fix` once mid-lane to add three edges the
proof terms used but `depends_on` hadn't named:
`F:ml430-nat-add-comm-56a2d614` for `strictmono`, `F:nat-le-succ-succ` and
`F:nat-zero-le` for `odd-fermatnumber`).
`python3 scripts/check-mirror-statement-fidelity.py` — violations=0 (no
`formal.statement` was touched; only `formal.kernel_theorem`/
`kernel_statement`, `evidence`, `notes`, `epistemic_status`, `depends_on`,
`proof_route`, `axiom_footprint` were added).
`python3 scripts/check-autogenesis-holdout-isolation.py` — settled=0,
references=0, verdict=PASS (all five facts are `partition: development` in
`artifacts/autogenesis/nursery-v2-extension.json`'s `fermat-numbers`
family, confirmed by direct lookup — never held-out).

Each `checker_command` verified BOTH directions against a fresh
`nat_theorem_inventory` dump: 1 match for the true (name, type) pair, 0 for
a fabricated name, 0 for the true name paired with a wrong type.

<!-- plan-section: landed-changes -->

| 2026-08-30 | fermat-easy | 5 axiom-free Nat kernel theorems: the three closed `fermatNumber` reductions (0/1/2 = 3/5/17), `Nat.odd_fermatNumber`, and `Nat.fermatNumber_strictMono`; all fully symbolic except the three closed equalities (largest formed numeral 17) |
