# Lane: cas-thales-varignon — thales kernel-reconstructed and disclosed as refl-shaped; varignon deliberately left cas-internal

<!-- plan-section: lane-status -->

**Your lane's block (`DONE (kernel-reconstructed 13 -> 14; thales
kernel-reconstructed with a full disclosure that its cofactor identity is
refl-shaped, not a genuine combination; varignon deliberately NOT
reconstructed -- its certificate has zero coordinates, zero generators, and
an already-empty conclusion polynomial, so reconstructing it would produce
Rat.zero = Rat.zero with no geometric content at all; next cheapest
cas-internal target is pappus-hexagon)`, cas-thales-varignon, 2026-08-30).**

## Step 0: verified the sizing rather than trusting it

`docs/plan/status/327-cas-geometry-pair.md` named both targets "reachable
with the ORIGINAL constant-cofactor-only machinery
(`cas_geometry_bridge_tests.rs`'s `prove_const_combination`)... possibly the
cheapest reconstruction in the whole geometry family." That much is TRUE for
thales and held with zero new proof-emitting code. But the same handoff, and
— it turns out — the orthocentre sibling fact's own `notes` field (written
2026-08-29, before this lane started) already contained the finding that
matters more than the sizing:

> "thales' single cofactor is the constant 1 against a conclusion
> byte-identical to its generator, so the kernel obligation there is refl."

This lane verified that claim directly against the CAS's own certificate
(`artifacts/geometry-certificates/thales-right-angle-in-semicircle.json`):
`cert.generators[0]` and `cert.conclusions[0].poly` are BYTE-IDENTICAL as
`IntPoly` (same 8 terms, same coefficients), and the cofactor is the constant
`1`. Since `poly_expr` is a deterministic function of its `IntPoly` input,
the kernel statement this bridge builds is literally `poly_expr(X) =
Rat.ofInt 1 * poly_expr(X)` for one specific `X` — a `mul_one`-shaped ring
fact true of ANY polynomial whatsoever, not one that discriminates Thales'
theorem from any other. The genuinely geometric coincidence — that "C lies
on the circle with diameter AB" and "CA ⟂ CB" expand to the IDENTICAL
polynomial — is checked only by a plain Rust `assert_eq!` in the translator
test, never by `Kernel::add_declaration`.

Detail moved to [`../notes/332-cas-thales-varignon.md`](../notes/332-cas-thales-varignon.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `e91e718a0` | draft: `cas_geometry_bridge_tests.rs` thales addition + varignon exclusion doc -- not yet compiled (committed within first 10 tool calls per lane protocol) |
| 2026-08-30 | `28a77b5c9` | feat: kernel-reconstruct thales cofactor identity, full disclosure of its refl-shaped obligation; register `F:geometry-thales-cofactor-identity-kernel-checked`; `cas-certificate` kernel-reconstructed 13 -> 14 |
