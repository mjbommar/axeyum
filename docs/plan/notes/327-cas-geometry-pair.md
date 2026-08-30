# Notes: 327-cas-geometry-pair

Detail moved out of [`../status/327-cas-geometry-pair.md`](../status/327-cas-geometry-pair.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**A second, self-inflicted correction during this lane's own first draft:**
the module doc initially claimed "both certificates' generators carry `±1/2`
coefficients". Running the numeric checks (before trusting the kernel
reconstruction) falsified this for `parallelogram-diagonals-bisect`: its two
parallelism generators are INTEGER; the fractional coefficients and the
non-constant cofactor live in the COFACTORS and the CONCLUSION instead.
`centroid-divides-medians` is the opposite (fractional generators, integer
cofactors/conclusion). Both numeric tests now check all three locations
(generators, cofactors, conclusion) rather than assuming one.

A third bug caught the same way: the centroid numeric test's first negative
control (cross-wiring centroid-x's cofactors against centroid-y's
conclusion) used the certificate's own generic witness point, which happens
to BE the triangle's centroid — at that point both generators are zero, so
both cofactor sums are zero regardless of which set is used, and the control
was vacuous (`0 != 0` failed). Replaced with a generic, non-centroid point,
discriminating verified in a throwaway (uncommitted) Python script before
editing Rust.

## What landed

`crates/axeyum-lean-kernel/src/rat_prelude/cas_geometry_pair_bridge_tests.rs`
(new, 7 tests): 2 numeric-only translator checks (one per certificate,
covering both conclusions and, for centroid, a cross-wired negative
control), 4 kernel-checked reconstructions (`Check.geometry_centroid_cofactor
_identity_{x,y}`, `Check.geometry_parallelogram_cofactor_identity_{x,y}`),
and 1 declaration-kind probe. `prove_poly_combination_rat` widened
`pub(super)` in `cas_partial_fractions_bridge_tests.rs` (only change to that
file).

Two sibling facts registered per ADR-0601 §2, mirroring the rhombus/
orthocentre/medians-concurrent/partial-fractions convention (a new fact, the
parent left unmodified, non-reconstructed scope disclosed in
`axiom_footprint`):

- `F:geometry-centroid-divides-medians-kernel-checked`
- `F:geometry-parallelogram-diagonals-bisect-kernel-checked`

    cas-certificate: 41 total -- kernel-reconstructed 13, cas-internal 28
    (up from 11/28 before this lane)

## What is NOT established (see each fact's `axiom_footprint` for the full list)

Same six-item disclosure shape as the rhombus/centroid/parallelogram-sized
siblings: does not prove the geometry itself; does not establish the
geometric conditional (`(∀i. gᵢ=0) → concl=0`); `Zinv0` is an uninterpreted
`Rat` variable, not known to witness a nonzero determinant's inverse; over
`Rat`, not `CReal`; the translator (`rat_poly`) is checked by evaluation
only, never by the trusted gate; and — the item specific to this lane — the
two conclusions per certificate are proved as TWO SEPARATE kernel theorems,
never as one joint statement.

## Cost, measured

Debug, this host, through `scripts/cargo-serialized.sh`, uncontended:

| run | wall clock |
| --- | --- |
| `centroid_certificate_identity_holds_at_integer_points` | well under 1s |
| `parallelogram_certificate_identity_holds_at_integer_points` | well under 1s |
| `geometry_centroid_cofactor_identity_x_kernel_checked` alone | 11.33s |
| `geometry_centroid_cofactor_identity_y_kernel_checked` alone | 18.55s |
| `geometry_parallelogram_cofactor_identity_x_kernel_checked` alone | 12.27s |
| `geometry_parallelogram_cofactor_identity_y_kernel_checked` alone | 11.83s |
| `centroid_x_is_declared_as_a_theorem` alone | 11.30s |
| this module's 7-test sweep (cargo's own parallel scheduling) | 11.2s-20.1s across two runs |
| full `rat_prelude::cas_` sweep (28 tests, all bridge modules) | 144.64s |

Cheaper per-theorem than `rhombus-diagonals-perpendicular`'s single
152.79s-test: this session's four reconstructions total roughly the same
wall-clock as rhombus ALONE, because each certificate's maximum cofactor is
only 4 terms against rhombus's 12, even though (unlike rhombus) both need
the fractional cast. No numeral magnitude larger than the certificates' own
small denominators (1 or 2) is ever formed.

## Both checker_command directions verified

Verified standalone with `/usr/bin/grep -cE` explicitly (not the interactive
`ugrep`), all four evidence rows across the two facts:

- `kernel-reconstructed-centroid-divides-medians-cofactor-identities`: real
  filter (matches both `_x_kernel_checked`/`_y_kernel_checked`, `test
  result: ok. 2 passed`) -> count 1, exit 0; fabricated test-name suffix ->
  count 0, exit 1.
- `translator-checked-against-numbers-centroid`: real test name -> count 1,
  exit 0; fabricated name -> count 0, exit 1.
- `kernel-reconstructed-parallelogram-diagonals-bisect-cofactor-identities`:
  same shape as centroid's, real -> 1/exit 0, fabricated -> 0/exit 1.
- `translator-checked-against-numbers-parallelogram`: real -> 1/exit 0,
  fabricated -> 0/exit 1.

## Next cheapest `cas-internal` target

Measured directly from `artifacts/geometry-certificates/`, not from a stale
table: `thales-right-angle-in-semicircle` (1 generator, 1 conclusion, 8-term
conclusion polynomial, a SINGLE-TERM constant cofactor) and
`varignon-midpoint-parallelogram` (0 coordinates, 0 generators, both
conclusions are the EMPTY polynomial with no cofactors at all -- literally
`0 = 0`) are both cheaper than anything landed this session or its
predecessors: neither needs the fractional cast (both are already
integer-coefficient) or `prove_mul` (thales's cofactor is a single constant
term; varignon's identity is vacuous). These should be reachable with the
ORIGINAL `cas_geometry_bridge_tests.rs` machinery (`prove_const_combination`,
constant-cofactor-only, already landed for `orthocentre-altitudes-concurrent`)
with no new proof-emitting code at all -- possibly the cheapest reconstruction
in the whole geometry family. `varignon-midpoint-parallelogram` in particular
may need special-casing for the zero-coordinate/zero-generator degenerate
shape (verify the certificate's own semantics for an empty conclusion before
assuming `add_declaration` accepts an empty `Σ` the same way as a non-empty
one).

After those: `pappus-hexagon` (145 terms, 10-term max cofactor, `prove_mul`
only, no cast) is the next tier; `simson-line` (2010 terms, 324-term max
cofactor) and `euler-line` (337 terms, 272 non-integer, 74-term max cofactor,
needs both cast and `prove_mul`) are the expensive remainder and should not
be attempted without measuring a smaller slice first, per the standing
numeral-magnitude and prelude-build-cost cautions in `CLAUDE.md`.

## Gates run (all foreground)

- `cargo check -p axeyum-lean-kernel --lib --tests` -- clean
- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib
  cas_geometry_pair_bridge_tests` -- **7 passed, 0 failed** (nonzero count
  confirmed), and again as part of the 28-test `rat_prelude::cas_` sweep
  across every bridge module -- **28 passed, 0 failed** (144.64s)
- All four `checker_command`s re-run standalone through `/usr/bin/grep -cE`
  explicitly, BOTH directions (see above)
- `rustfmt --edition 2024 --check` on the new file (after one `rustfmt`
  auto-format pass, no functional change), plus `cargo fmt --all --check`
  (workspace-wide, read-only) -- clean
- `scripts/cargo-serialized.sh clippy -p axeyum-lean-kernel --all-targets --
  -D warnings` -- clean
- `python3 scripts/validate-facts.py` -- **2159 facts, 0 errors**;
  `cas-certificate: 41 total -- kernel-reconstructed 13, cas-internal 28`

Not run: the aggregate gate (`just check`/`check.sh`), per the brief.

## Did NOT touch

`crates/axeyum-lean-kernel/src/nat_prelude/`, `int_prelude/`, `creal/`, and
`axeyum-cas` itself (read-only -- the translator only reads existing public
certificate fields via `axeyum_cas::geometry_certify`/`geometry_corpus` and
`axeyum_ir`, both already-public APIs). `F:geometry-centroid-divides-medians`
and `F:geometry-parallelogram-diagonals-bisect` themselves are unmodified,
per the sibling-fact convention. Nothing pushed.
