# Lane: py-prelude-fields-fix — fix the path-qualified-field silent skip in `scripts/gen-py-prelude-fields.py`

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, py-prelude-fields-fix, 2026-09-05).** Fixed
ADR-1613's "unrelated live gap": `scripts/gen-py-prelude-fields.py`'s field
regex excluded `:`, so a path-qualified registry field (`pub poly:
poly::PolyNames` on `ComplexPrelude`) never matched the field pattern at all
-- silently absent before classification ever ran, and `--check` printed a
plausible count and exited 0. Measured on main before the fix: `complex=129`,
zero `"poly.` entries in the generated file, `--check` green.

Fix: the field regex now allows `:`, and a qualified registry type is
resolved by walking the real `mod`/`use` declarations starting from the file
that declares the field (`resolve_qualified_type` / `resolve_module_path` /
`resolve_struct_in_file` in the generator), never by a bare-name global
search -- that search is exactly what's ambiguous when a field is written
qualified (`PolyNames` is defined in both `complex/poly.rs` and
`nat_prelude/polynomial_setoid.rs`). An unresolvable module or type is a hard
error naming the field, never a skip.

Regenerated `crates/axeyum-py/src/kernel/prelude_fields.rs`: `complex`
129 -> 150 names (the 21 `poly.*` fields), diff is exactly those 21 lines
plus the doc-count comment.

New control suite `scripts/tests/test_gen_py_prelude_fields.py` (15 tests):
real-repo tests against the actual `ComplexPrelude.poly` two-files case, plus
synthetic fixtures for guards the current source doesn't exercise (`crate::`
absolute path + `use` re-export, `super`, an unresolvable module, an
unresolvable type, a `use` cycle, the bare-name ambiguity regression). A
`MirrorCompletenessTests` check uses an independent, looser regex (not
`collect()`'s own) to assert every top-level field of every walked struct has
some trace in the generated file -- would have caught the original bug
without sharing its blind spot. Mutation-verified on a scratch copy (not
`mutation_controls.py` -- this suite wasn't registered there): all 7 guards
killed, none survived, none failed to build, file restored byte-identical.
Registered in `scripts/check.sh` (`py-prelude-fields-tests`, before
`py-prelude-fields`) and `justfile`.

Also fixed a latent crash in `struct_file`'s ambiguity-error path
(`p.relative_to(ROOT)` raised `ValueError` for any `KERNEL_SRC` outside
`ROOT`, e.g. a test fixture) -- added `display_path()`, falls back to the
full path.

Did not touch `mutation_controls.py` (suite not previously registered
there, task allowed a scratch copy instead). Did not touch any `*Prelude`
struct or kernel source. ADR-1628 was reserved but not used -- no decision
was needed; the fix and its rationale are in the generator's own module
docstring.

<!-- plan-section: landed-changes -->

| 2026-09-05 | py-prelude-fields-fix | fixed the path-qualified-field silent skip in gen-py-prelude-fields.py; regenerated prelude_fields.rs (+21 poly.* fields); added scripts/tests/test_gen_py_prelude_fields.py, registered in check.sh + justfile |
