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

1. Dispatch-order `UnknownConst`: the new `declare_add_div_mod_shift_family`
   call used `succ_pred_of_pos` (via `div_mod_reconstructed`) before
   `declare_succ_pred_of_pos` ran in `build_nat_prelude_uncached`. Fixed by
   moving the call to right after `declare_succ_pred_of_pos` instead of
   right after `declare_divisibility` (which supplies `div_mod_exec`, the
   other dependency — both needed, and `succ_pred_of_pos` is declared later
   than `div_mod_exec` in this prelude's build order).
2. A swapped `symm(a, b, h)` argument order in `div_mod_shift`: `and_left`/
   `and_right` project `q_eq : Eq shift_q fq` / `r_eq : Eq nr fr`, and the
   code called `symm(fq, shift_q, q_eq)` (wrong anchor) instead of
   `symm(shift_q, fq, q_eq)`. `symm`'s own construction doesn't verify `h`'s
   actual type — it just anchors an `Eq.rec` motive at whichever `a` it's
   given — so the swapped call built a term that quietly inferred to the
   UNREVERSED type instead of failing at construction time; it only
   surfaced as an opaque top-level `TypeMismatch` at `add_declaration`.
   Found by bisecting declarations down to one theorem, then a throwaway
   `#[test]` dumping `Kernel::render_lean` of both `TypeMismatch` sides
   (CLAUDE.md's standard move for this shape of error) — the "got" side was
   visibly the un-reversed equation.

**Open, 1 of 9 — `F:ml430-nat-add-div-of-dvd-add-add-one-f17dffc0`.**
`∀ {c a b : ℕ}, c ∣ a+b+1 → (a+b)/c = a/c+b/c`. This needs a genuinely
different argument from the shift family: the divisibility hypothesis pins
`(a+b) % c` at exactly `c-1` (since `a+b+1 ≡ 0 (mod c)` and `a+b < a+b+1`),
and the identity holds because that forces the fractional remainders of
`a/c` and `b/c` to sum to exactly `1`. `div_mod_shift`/`div_mod_reconstructed`
don't reach this — they relate a dividend to `dividend + divisor*k`, not two
independent dividends whose remainders are constrained to sum to the
divisor. Left open for a follow-up lane; not attempted.

**Verification.** `env -u RUST_MIN_STACK scripts/cargo-serialized.sh test -p
axeyum-lean-kernel --lib nat_prelude::` — **159 passed, 0 failed** (158
baseline + the new `add_div_mod_shift_family_applies_at_concrete_discriminating_instances`
test, concrete numerals `x=7,y=2,z=3` and `x=7,z=4` chosen to discriminate a
swapped argument or a wrong `symm` direction via `def_eq`, not merely a
type-check pass — this is exactly the test that would have caught bug 2
above on its own). `cargo fmt --all --check` and
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` both
clean. `python3 scripts/check-test-attribute-integrity.py` clean (9101
`#[test]` attributes, 0 findings). `python3 scripts/validate-facts.py`: 0
errors. `nat_axiom_inventory --require-axiom-free nat`: `axiom=0 opaque=0
quotient=0`, exit 0.

All eight facts flipped to `epistemic_status: proved`, each with a
kernel-term evidence row (`nat_theorem_inventory -- <name>`, rendered type
compared verbatim against `formal.statement`) and an exhaustive-enumeration
axiom-freedom row (`nat_axiom_inventory --require-axiom-free nat`).
`proof_route: kernel-lean`, `axiom_footprint: []` on all eight.

**Commits** (not pushed): `699572d97` (the 8 declarations),
`c4f1095ac` (the two bug fixes, coverage-list registration, determinism pin
recount 93+516 -> 93+524, and the concrete-instance test). The fact-ledger
JSON edits and this status file are uncommitted as of writing this — commit
them together with the pathspec-discipline rules in `CLAUDE.md` before
ending the session.

**For the next lane on this family:** `add_div_of_dvd_add_add_one` is the
one piece left. Route sketch: derive `(a+b) % c = c - 1` from the
divisibility hypothesis (via `div_mod_exec`/`div_mod_unique` at dividend
`a+b+1`, comparing against the `a+b` decomposition shifted by one), then
case-split on whether `a % c + b % c` overflows `c` — this is the step that
actually needs new machinery beyond `div_mod_shift`, and is why it was left
open rather than attempted under time pressure.

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-div-mod-family | `Nat.add_mul_div_left`/`_right`, `Nat.add_mul_mod_self_left`/`_right`, `Nat.add_mod_left`/`_right`, `Nat.add_div_left`/`_right` — 8 of 9 dispatched `ml430` add/div/mod mirrors, axiom-free, via a new reusable `div_mod_shift` helper (`nat_prelude/div_mod_lemmas.rs`). `add_div_of_dvd_add_add_one` left open (needs a different argument). |
