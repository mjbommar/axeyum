# Lane: nat-div-mod-family — the `ml430` `Nat` add/div/mod shift mirrors

<!-- plan-section: lane-status -->

**Lane block (`DONE for this dispatch`, nat-div-mod-family, 2026-08-29).**

**The task.** Nine freshly-preregistered `ml430` `Nat` division/modulo
mirrors were dispatchable (`python3 scripts/check-dispatchable-frontier.py`
confirmed these are exactly the `nat-`-family entries in the 50-item
dispatchable set, no others among the "div"/"mod" hits — the rest of that
grep is `nat-lcm-div`, which is a different family, and the `int-` ediv/emod
entries, out of scope for this lane):

```
F:ml430-nat-add-div-left-1b15b2b2          F:ml430-nat-add-div-right-4b60b393
F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0
F:ml430-nat-add-mod-left-6b337077          F:ml430-nat-add-mod-right-c047c67a
F:ml430-nat-add-mul-div-left-e20827dd      F:ml430-nat-add-mul-div-right-44a689e4
F:ml430-nat-add-mul-mod-self-left-108b5fe0 F:ml430-nat-add-mul-mod-self-right-ac5b3624
```

**Closed, 8 of 9.** All landed as fresh local constructions (Step 0's
absence check confirmed none of these were already proved under a different
name — no existing declaration matched any of the eight shapes) —

- `Nat.add_mul_div_left`, `Nat.add_mul_div_right`
- `Nat.add_mul_mod_self_left`, `Nat.add_mul_mod_self_right`
- `Nat.add_mod_left`, `Nat.add_mod_right`
- `Nat.add_div_left`, `Nat.add_div_right`

New file `crates/axeyum-lean-kernel/src/nat_prelude/div_mod_lemmas.rs`. All
eight reduce to one reusable fact, `div_mod_shift(d, p, dd, pos_dd, n, k)`:
for a positive divisor `dd` and any `n, k`, `(n+dd*k)/dd = n/dd+k` and
`(n+dd*k)%dd = n%dd`. That is built from `division.rs`'s
`div_mod_exec`/`div_mod_unique`/`div_mod_add_multiple` via a local
`div_mod_reconstructed` (a copy of `group.rs`'s private helper of the same
shape — established per-file pattern in this prelude, not a new one). The
four with no positivity hypothesis in the Mathlib statement
(`add_mod_left`/`_right`, `add_mul_mod_self_left`/`_right`) case-split their
divisor via `cases_zero_succ`; the zero branch collapses via
`zero_mul`/`mul_zero` plus `add_zero`, never touching division. `add_div_left`/
`add_div_right` are the `k := 1` instance of the `add_mul_div_*` shape after
an `add_comm`/`mul_one` bridge.

**Two real bugs found and fixed while landing this** (both in the commit
history, not left for the next lane):

Detail moved to [`../notes/283-nat-div-mod-family.md`](../notes/283-nat-div-mod-family.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-div-mod-family | `Nat.add_mul_div_left`/`_right`, `Nat.add_mul_mod_self_left`/`_right`, `Nat.add_mod_left`/`_right`, `Nat.add_div_left`/`_right` — 8 of 9 dispatched `ml430` add/div/mod mirrors, axiom-free, via a new reusable `div_mod_shift` helper (`nat_prelude/div_mod_lemmas.rs`). `add_div_of_dvd_add_add_one` left open (needs a different argument). |
