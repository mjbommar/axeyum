# Notes: 338-int-gcd-mul-transport

Detail moved out of [`../status/338-int-gcd-mul-transport.md`](../status/338-int-gcd-mul-transport.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

`Nat.dvd_add_iff_left` (new file `nat_prelude/dvd_add_iff_left.rs`) turned out
to be genuinely cheap, not merely "looks cheap": the existing
`dvd_add_iff_right(k,m,n,h : dvd k m) : Iff (dvd k n) (dvd k (m+n))`
instantiated with the summands swapped, `(k,n,m,h)`, gives
`Iff (dvd k m) (dvd k (n+m))` directly, and one `add_comm` transport turns
`n+m` into `m+n`. No new case split.

**Step 0 checks, before writing any code:** grepped for `dvd_add_iff_left`
across `nat_prelude/` (absent) and confirmed via `nat_theorem_inventory`
(exit 1, "no Nat theorem matches") before building it. The `int_prelude/gcd.rs`
module doc explicitly rules out its own `Int.gcd_mul_right` as a shortcut
(unrelated coprimality-descent proposition sharing the Mathlib name) — did not
reach for it.

**Verification, per the standing non-negotiable (concrete AND free-variable):**
every declaration here is proved directly over the `int_theorem`/`theorem`
combinators' genuinely free `k, n, m` (or `k, m, n`) fvars — there is no
concrete-instantiation shortcut in these proofs, so the kernel's acceptance
*is* the symbolic check. `int_theorem_inventory`/`nat_theorem_inventory`'s
rendered types were diffed character-for-character against each fact's
`formal.statement` (recorded per-fact in the evidence notes). Each
`checker_command` verified both directions: the anchored `grep -c` (`-ge 1`,
never piped through `grep -q`) requires the exact name followed by whitespace,
checked not to also match the closest substring-overlapping sibling
(`dvd_gcd_mul_iff_dvd_mul` vs `dvd_gcd_mul_gcd_iff_dvd_mul`,
`dvd_add_iff_left` vs the pre-existing `dvd_add_iff_right`), and a fabricated
name for each (`*_bogus_xyz`) makes the inventory tool exit 1, "no
Int/Nat declaration matches".

All four are axiom-free: `prelude_axiom_inventory --require-axiom-free
integer` -> `integer axiom=0`; `nat_axiom_inventory --require-axiom-free nat`
-> `nat axiom=0 opaque=0 quotient=0`. `int_prelude::` sweep: 49 passed, 0
failed (unchanged count — no new `#[test]`, only coverage-list entries).
`nat_prelude::` sweep: 183 passed, 0 failed (also unchanged). `derived_laws`
pin (`int_prelude_tests.rs`) 208 -> 211, a Rust array-length literal the
compiler itself enforces against the added entries (not hand-counted).
`the_build_is_deterministic` pin (`nat_prelude_tests.rs`) 93+602 -> 93+603,
recounted by running the test after adding one entry to `theorem_names`, not
by hand-incrementing.

`python3 scripts/check-fact-depends-derived.py --fix` regenerated
`depends_on` from each proof term (`F:int-dvd-of-nat-abs-dvd`,
`F:int-nat-abs-dvd-nat-abs-of-dvd`, `F:int-nat-abs-mul`,
`F:ml430-nat-dvd-gcd-mul-iff-dvd-mul-0afe640a`, `F:int-mul-comm` for the three
ℤ facts; `F:ml430-nat-add-comm-56a2d614`, `F:ml430-nat-dvd-add-iff-right-bf79c0cd`
for the ℕ fact). `python3 scripts/validate-facts.py`: 2220 facts checked, 0
errors, `missing_edges=0`.

Partition check before touching any fact: all four are `development` in
`artifacts/autogenesis/nursery-v2-extension.json` — none held-out.

`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean.
`rustfmt --edition 2024 --check` on every touched/new file: clean.

**Nothing left open from this lane's scope.** The four dispatched targets are
all closed.

`bash scripts/check-merge-hygiene.sh`: see commit history for the exact line.
