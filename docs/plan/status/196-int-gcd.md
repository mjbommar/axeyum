# Lane: int-gcd — closing three of the seven `Int.gcd` import-backlog facts

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for the three landed; one fact deliberately
deferred with a sized reason`, int-gcd, 2026-08-28).** Closed
`F:ml430-int-ne-zero-of-gcd-f71f00df`,
`F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82`, and
`F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222`, each via a
genuine new kernel declaration in `int_prelude/gcd.rs`
(`declare_ne_zero_of_gcd`, `declare_gcd_eq_one_of_gcd_mul_right_eq_one`).
Left `F:ml430-int-gcd-div-5e01872f`, `F:ml430-int-gcd-div-gcd-div-gcd-2db608dc`,
and `F:ml430-int-gcd-greatest-5b31c5fe` untouched (not attempted — see
below); did not close `F:ml430-int-gcd-eq-gcd-ab-63005aef` (the brief's
"interesting one" — my characterization of it was correct, see below).

**The brief's characterization of `Int.gcd_eq_gcd_ab` was RIGHT, and the
closing work is LARGER than "small but real".** The kernel's existing
`Int.gcd_eq_gcd_ab` proves `∀ a b, ∃ u v, ofNat (gcd a b) = a*u + b*v` —
confirmed by reading `declare_gcd_eq_gcd_ab` in `gcd.rs` line-by-line: the
`stmt` it builds is an `Exists`/`Exists` nest (`exists_name` applied twice),
never a named witness. Mathlib's `Int.gcd_eq_gcd_ab` is
`∀ x y, ↑(x.gcd y) = x * x.gcdA y + y * x.gcdB y` — computable projections,
not an existential. These are different propositions.

**But the witnesses are NOT extractable**, and I was wrong to assume they
might be without checking. `declare_gcd_eq_gcd_ab`'s `u`/`v` come from two
sources that are each individually non-computable in this kernel: (1) the
magnitude coefficients `u0`/`v0` (`factor_out`, built from `mp,mn,np,nn`)
come from `Nat.gcd_bezout`, which is a `Declaration::Theorem` — its
existential witnesses live inside a `Prop` (`bezout m n g := ∃ mp mn np nn,
…`) and cannot be projected out without choice; (2) the sign flip
(`match_sign`, using `sign_cases`) is built as a `Prop`-typed `Or`-elimination
over a proof of `Or (Eq a big_a) (Eq a (neg big_a))`, not a computable
`Int.rec` branch selection. Defining genuine computable `Int.gcdA`/`Int.gcdB`
needs a FRESH computable extended-Euclidean `Definition` (built by
`WellFounded.fix` mirroring `bezout.rs`'s own recursion, but returning actual
`Nat`/`Int` VALUES instead of an existential proof), plus re-deriving the
Bézout equation for it by induction (reusing much of
`prove_bezout_euclidean_update`'s shape, but over data). That is a genuinely
new multi-hundred-line construction, not an extraction — deferred as a
separate, sizeable task rather than attempted this session.

**`F:ml430-int-gcd-div-5e01872f` is untouched, and the brief's warning about
it is confirmed**: `scripts/check-autogenesis-semantic-contract-target-census.py`
line 31 names this exact fact id as a fixture entry (`"fact_id":
"F:ml430-int-gcd-div-5e01872f"`), so it may be a negative control elsewhere in
that script. Read but did not edit it, and left the fact `open`.

**What the kernel REJECTED and why.** Nothing on the version committed. The
only non-proof failures were two `E0499` borrow-checker errors (`d.imul(d.of_nat(m),
d.of_nat(n))` double-borrows `d` — flattened into two lets) and one
initially-missing test-coverage failure
(`every_int_declaration_is_checked_and_axiom_free` correctly named all three
new declarations as unlisted in `derived_laws` before I added them there).

**`int_prelude::` count.** 33 passed / 1 failed before adding the three new
names to `derived_laws` (pin 138 → 141, recounted by grepping `^        p\.`
lines in the array body, not hand-incremented); 34 passed / 0 failed after.

Verified foreground: `scripts/cargo-serialized.sh test -p axeyum-lean-kernel
--lib int_prelude::` — 34 passed, 0 failed. Each new fact's
`checker_command` run individually against the prebuilt
`target/release/examples/int_theorem_inventory` binary (built once,
`--release`), all three `-ge 1`. `python3 scripts/validate-facts.py`: 0
errors (1867 facts checked).

Did not run: `just check` / `./scripts/check.sh` (out of scope for a
single-crate change and multi-lane host contention; the coordinator's merge
gate re-verifies).

<!-- plan-section: landed-changes -->

| 2026-08-28 | int-gcd | `Int.ne_zero_of_gcd` + `Int.gcd_eq_one_of_gcd_mul_right_eq_one_left`/`_right` landed as new kernel declarations in `int_prelude/gcd.rs`; three ml430 facts flipped `open`→`proved`, axiom-free; `Int.gcd_eq_gcd_ab` (existential Bézout) confirmed NOT the same fact as Mathlib's computable `gcd_eq_gcd_ab` and left open with a sized reason; `gcd_div`/`gcd_div_gcd_div_gcd`/`gcd_greatest` not attempted |
