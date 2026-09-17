# Lane: ax-gate — the cindergraph C-defect example as a gate (improvement-list item 16)

<!-- plan-section: lane-status -->

**Lane ax-gate (`DONE`, ax-gate, 2026-09-17).** Item 16 of
[improvement-list-2026-09-16](../improvement-list-2026-09-16.md) is closed:
`check.py` is a gate, not an example with an exit status.

- **Pinned.** `cindergraph` is in `pyproject.toml`'s dev group at
  `8bd20512158d19d4cf632caba4bbed629271a3e5` (`uv.lock` relocked; `uv sync
  --dev` builds it from git — first sync needs a Rust toolchain and network).
  Installed `__version__` is `0.1.0`; `check.py`'s first line prints
  `cindergraph|version=0.1.0|commit=8bd20512…|pinned=8bd20512…|match=yes`,
  read from the distribution's PEP 610 `direct_url.json` and from
  `pyproject.toml`, so a run says what it ran against.
- **The gate.** `scripts/check-cindergraph-defects.sh` (a step of `just
  py-check` and of `scripts/check.sh`'s Python block) refuses (exit 2)
  without an importable `axeyum._native` or `cindergraph`, SKIPS loudly and
  never passes without `clang` (`AXEYUM_REQUIRE_CINDERGRAPH_DEFECTS=1` makes
  that a failure), runs the sweep once, and has
  `scripts/check-cindergraph-defects.py` re-derive the verdict from
  `results.tsv` and the samples' `// expect:` lines under five failure
  classes (expectation, replay, control, provenance, inconsistent). Measured:
  `CINDERGRAPH_DEFECTS|rows=33|replayed=18|dead=2|clean=13|bounded=0|no_oracle=0|failures=0|PASS`,
  ~15 s. The driver itself now judges its first replayed harness at the line
  AFTER its finding and must see it refused — the check on the replay check.
- **Controls.** `scripts/tests/test_check_cindergraph_defects.py` (21 tests:
  15 reader guards on synthetic rows + 6 live) and
  `mutation_controls.py cindergraph-defects`: a sample's bounds check
  deleted → `killed 1: test_every_expectation_in_the_samples_is_met`; the
  `int`-against-`size_t` usual-arithmetic rule broken → `killed 1:
  test_every_witness_replayed_at_its_own_line` (a bogus signed-overflow
  witness in `pack_bug` that `DID NOT REPLAY`); `replay()` accepting every
  report → `killed 1: test_the_replay_check_refuses_a_wrong_line`.
- **cindergraph attributes the lifter now reads** (each with a synthetic-node
  unit test in `test_lift.py`, 35 tests; the old reading kept as fallback):
  `line` on every node (counted newlines otherwise; identical on all 1,100
  sample nodes), `facts` on `param_decl` / `func_def` for capacity, strlen
  and unroll (the comment regexes otherwise), and `loop_kind` for the loop
  form (the statement tag otherwise) with `bound_kind` / `induction` /
  `step` / `bound_value` carried as `LoopInfo` on `Lifted.loops`. Honest
  note: the lifter has no loop classification beyond for/while/do, so the
  bound metadata deletes nothing; it is carried for a `bounded` verdict to
  cite. All 356 queries and 18 harnesses are byte-identical to the
  pre-change sweep at the pin; only ASLR addresses in ASan reports move.
- **Not done, deliberately.** cindergraph's `type` attribute is `unknown` for
  `size_t`/`uint32_t` (typedefs it never saw), so parameter types are still
  parsed from the declaration text; and its `unroll` fact is function-scoped
  where the file comment is file-wide, so the second function in sample 09
  keeps the file's bound through the fallback.

Next for whoever picks this up: the `bounded` row could cite `LoopInfo`
(`constant bound 8: raise unroll to 9`) once a sample pins a `bounded`
verdict; and a fleet probe for `clang` on s2/s5–s7 would turn the SKIPPED
path from a documented possibility into a measured one.

<!-- plan-section: landed-changes -->

| 2026-09-17 | `8ac48b6fa` | ax-gate: cindergraph pinned at `8bd20512`; `check.py` gated by `scripts/check-cindergraph-defects.sh` in `py-check` and `check.sh`; three subject mutations each kill one test; lifter reads `line`, `facts`, `loop_kind` with fallbacks (item 16 done). |
