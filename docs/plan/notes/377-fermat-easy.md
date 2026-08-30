# Notes: 377-fermat-easy

Detail moved out of [`../status/377-fermat-easy.md`](../status/377-fermat-easy.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
