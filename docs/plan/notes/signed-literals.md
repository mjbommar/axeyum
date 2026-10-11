# CON-6 signed integer literal implementation evidence

Worktree: `/home/mjbommar/projects/personal/axeyum-signed-literals`. Branch:
`fix/signed-literals-20261010`. Source commit `224118bce`; not integrated to main.
ADR-2400 specifies signed integer convenience syntax and quoted symbol identity.

Fresh `scripts/cargo-serialized.sh test -p axeyum-smtlib` on this source passed
380 tests: 96 unit, 16 distinct scope, 5 numeral coercion, 5 packed sorts, 5 new
signed integer regressions, 252 parser/writer integration, 1 doctest. Log:
`/var/tmp/axeyum-signed-parser-tests.log`; exit 0, all populations nonzero.
An earlier writer control inspected a folded constant equality; replaced with
a symbolic assertion to keep the negative literal visible, then reran.

Python/CLI builds run via handle 79707, logs
`/var/tmp/axeyum-signed-python-build.log` and `...-cli-build.log`. Fresh Rust solver
front-door test runs via handle 77339 and is waiting on this build directory.
Target: `/home/mjbommar/projects/personal/axeyum/target/signed-literals`.
Neither public-route run is credited before terminal results. The Python tests
need an isolated copy of the package using the newly built `_native` library,
not the stale extension in main's installed environment.

Remaining: fresh Python/CLI semantic and malformed controls, required full
solver/workspace/front-door gates, docs/link gates, and integration. No signed
decimal extension is claimed. The unidentified `notes/80` remains unresolved.

## Fresh Python public-route result

Built `axeyum-py` with `pyo3/extension-module` from this worktree, then copied
the Python package to `/var/tmp/axeyum-signed-python-girtq_zw/axeyum` and loaded
only the fresh `_native.abi3.so` there. SHA-256:
`7fa689eee156b249f88a5638bc3f43c5cebb7e79b8ad1786ee2783ed766dac0b`.
Import inspection confirmed that exact extension path. Run handle 17311 ended
exit 0: `pytest python/tests/test_smt.py -k signed_integer -q`: 12 passed,
61 deselected (73 collected), in 0.26 s. SAT controls all call `replay()` and
require True. Malformed and unbound quoted-symbol controls require the parse
exception. Python build is terminal successful; CLI build and solver test
remain live with handles 79707 and 77339 respectively.

## Solver and CLI completion

Handle 77339 ended exit 0: signed_integer_front_door ran 1/1 test, checking six
public dispatch cases, in 0.05 s. Handle 79707 ended exit 0: both fresh Python
and CLI builds completed. With AXEYUM_SMTCOMP_CLI explicitly pointing to
`target/signed-literals/debug/examples/smtcomp_cli`, a combined selected
Python run passed 18 tests (12 binding + 6 CLI), 61 deselected, 79 collected,
0 skipped, exit 0, in 0.25 s. Package loaded from the isolated fresh-extension
directory recorded above. Public Rust, Python and CLI syntax coverage is now
verified; workspace/full-solver and five mandatory front-door gates for this
parser branch remain required before integration.
