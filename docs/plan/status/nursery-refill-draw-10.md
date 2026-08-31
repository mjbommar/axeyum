# nursery-refill-draw-10

Status: in progress (screening).

## Repair landed first

`artifacts/autogenesis/nursery-v2-extension.json`'s own `extension_sha256` did
not match its body. Commit `5f2664b5a` (a sibling lane, "extend nursery
component-split gate to nursery-v2-extension") added a new top-level key,
`cross_population_component_split_exemptions`, directly to the committed JSON
without recomputing the digest through `gen-autogenesis-nursery-refill.py`'s
own `build_extension()`/`digest()`. Confirmed: `digest(body without the new
key)` reproduces the recorded hash exactly; `digest(body with it)` does not.

This blocks `gen-autogenesis-nursery-refill.py` entirely (`frozen_partitions()`
raises on load, before `--check` or a real run reaches `select()`/`guard()`),
which blocks this draw. Fixed by recomputing `extension_sha256` against the
current body (including the new key) -- a 1-line diff, no other content
touched. `check-autogenesis-nursery.py` (one of this draw's four required
gates) does not read `extension_sha256` at all, so it was unaffected either
way and passes before and after.

**Residual, NOT fixed here, logged instead (ADR-0830 precedent for an
unrelated red gate):** `gen-autogenesis-nursery-refill.py`'s own
`build_extension()` does not know about `cross_population_component_split_exemptions`,
so a REAL (non-`--check`) run of the generator overwrites the file with a body
lacking that key -- reproducing check-autogenesis-nursery.py's 3-component
cross-population leak (none held-out, but the gate would go red without the
exemption records). This draw's regeneration step restores the field by hand
afterward and recomputes a self-consistent `extension_sha256` over the
augmented body, which keeps `check-autogenesis-nursery.py` green. It does NOT
make `gen-autogenesis-nursery-refill.py --check` green: that comparison is
against `build_extension()`'s own in-memory reconstruction, which still omits
the key, so `--check` reports the file "stale" for a reason unrelated to this
draw's content. This is not one of this draw's four required gates. The real
fix is to teach `build_extension()` to round-trip
`cross_population_component_split_exemptions`, and it belongs to whoever
extends that schema next, not to this draw.
