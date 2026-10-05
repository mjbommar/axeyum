# Lane: ax-bindings — Python bindings, SMT-LIB overflow predicates, CLI docs (improvement list 2026-09-16 items 1, 2, 3, 4, 13)

<!-- plan-section: lane-status -->

**Done (`ax-bindings`, 2026-09-16).** All five assigned items landed as five
separate commits, each verified before the next:

- **Item 1.** `python/examples/cindergraph_defects/check.py` calls
  `axeyum.smt.solve` (the built native bindings) by default instead of
  shelling out to `axeyum_cli`; `--cli` is the explicit subprocess fallback.
  A small `Backend` abstraction (`NativeBackend`/`CliBackend`) keeps both
  routes sharing the bounded-witness-search logic. Verified the two routes
  decide identically (byte-identical finding/line/kind columns) over the full
  sample set. README's quickstart now builds the extension first
  (`uv sync --dev`, `maturin develop --release`, the `TMPDIR` RAM-tmpfs note)
  and installs `cindergraph` into the same venv.
- **Item 2.** `lift.py`'s double-width signed-overflow encoding
  (`sign_extend`/`bvadd`/compare) replaced with the SMT-LIB 2.6 overflow
  predicates the parser already accepts (`bvsaddo`/`bvssubo`/`bvsmulo` for
  binary `+`/`-`/`*`, `bvnego` for unary negation). Confirmed all seven
  predicates (`bvuaddo`/`bvsaddo`/`bvusubo`/`bvssubo`/`bvumulo`/`bvsmulo`/
  `bvnego`) parse and decide correctly through both `axeyum_cli` and
  `axeyum.smt.solve` with two-line scripts before relying on them. Documented
  in `docs/reference/smtlib-support.md`.
- **Item 3.** `axeyum-bench` gained a `full` feature forwarding to
  `axeyum-solver/full` (previously a hard dependency-level requirement, but
  with no same-named feature `--features full` was refused by Cargo naming
  the wrong package). Swapped every doc line building `axeyum_cli`/
  `smtcomp_cli` with the old `--features axeyum-solver/full` spelling to the
  new `--features full` form.
- **Item 4.** `docs/user-guide/first-smtlib-query.md` gained a "From the
  command line" section pointing a stranger at `axeyum_cli` (models, push/
  pop) ahead of the corpus-harness section, with `smtcomp_cli` named as the
  narrower single-verdict tool a harness reaches for, not a human.
- **Item 13.** `docs/reference/examples.md` gained a "Python examples"
  section (`gallery.py`: learning; `cindergraph_defects/check.py`: artifact
  generator; `lift.py`/`test_lift.py`: support modules), using the page's own
  three-way classification. Confirmed this does not touch the Cargo example
  population or its generated count (`_tracked_examples()` derives from
  `git ls-files crates/*/examples/*.rs` alone).

**Found but explicitly NOT fixed (out of scope for items 1/2/3/4/13):**
`scripts/check-parity-docs.py` and `scripts/gen-example-inventory.py --check`
are both pre-existing RED on this branch, independent of this lane's changes:
the tracked Cargo example count has drifted to 259 against the 203 pinned in
`docs/documentation-plan.md`/`PLAN.md` (last regenerated 2026-08-30, per
`git log`), and `docs/reference/examples.md` is missing 56 Cargo example
rows this lane did not add. Confirmed via `git diff` that this lane touched
neither marker file nor any Cargo example source — the drift predates this
lane's work. A future lane should run `scripts/gen-example-inventory.py`
and backfill the 56 missing Cargo rows.

`docs/plan/improvement-list-2026-09-16.md`'s README table for
`cindergraph_defects` ("Thirteen witnesses... seven fixed variants") does
not match its own table (12 finding rows, 8 `_fixed` clean rows) — a
pre-existing prose/table mismatch, not introduced here and not one of this
lane's five items; left as-is (frozen measurement snapshot).

**Next.** Items 5–12, 14+ of the same improvement list are unclaimed.

<!-- plan-section: landed-changes -->

| 2026-09-16 | `5bd0e77c4` | `axeyum-bench` gains a `full` feature forwarding to `axeyum-solver/full`; doc lines updated to the new flag spelling. |
| 2026-09-16 | `a306a017b` | `cindergraph_defects/lift.py` uses SMT-LIB 2.6 overflow predicates instead of a double-width shadow computation; documented in `smtlib-support.md`. |
| 2026-09-16 | `68f8887c9` | `cindergraph_defects/check.py` calls `axeyum.smt.solve` by default; `axeyum_cli` subprocess kept as an explicit `--cli` fallback. |
| 2026-09-16 | `0a839ec4e` | `first-smtlib-query.md` gets a "From the command line" section naming `axeyum_cli` before `smtcomp_cli`. |
| 2026-09-16 | `f767e463e` | `docs/reference/examples.md` gets a "Python examples" section. |
