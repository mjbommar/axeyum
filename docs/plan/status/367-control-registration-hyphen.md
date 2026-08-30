# Lane 367 — control-registration-hyphen

<!-- plan-section: lane-status -->

## Status

**LANDED.** `scripts/check-control-registration.sh`'s G2 rejected four
hyphenated `.py` scripts under `scripts/tests/` on the stated reason that a
hyphenated name "is not an importable module so `python3 -m unittest
scripts.tests.<name>` cannot run it either." **That half of the reasoning is
false, measured directly**, and the fix replaces the blanket rejection with a
reachability check.

### The real mechanism (measured, not inherited)

    python3 -m unittest scripts.tests.check-totient-prime-power-numerics
    -> exit 0, prints all 37 checks, but NO "Ran N tests" line anywhere

    python3 -m unittest scripts.tests.definitely_not_a_module_zzz
    -> exit 1, ModuleNotFoundError (the loader's own __import__ call)

    python3 -c "importlib.import_module('scripts.tests.check-totient-prime-power-numerics')"
    -> exit 0, identical output, NO unittest involved at all

`__import__`/`importlib.import_module` resolve a dotted path by matching file
names on disk; the identifier restriction that forbids a hyphen belongs to the
`import` *statement*'s parser, not to programmatic import. So the hyphenated
file genuinely **does** import under `python3 -m unittest scripts.tests.<name>`
— the guard's premise was wrong. What actually happens is stranger than "runs
as a test": none of the four scripts is a `unittest.TestCase`; each is a
standalone script that calls `sys.exit(0)`/`sys.exit(1)` at module level, so
the *import itself* terminates the whole process before unittest's loader ever
builds or runs a `TestSuite`. The absence of any "Ran N tests" line is what
proves it — this invocation form is not "unittest discovered and ran a test,"
it is "importing the file executes it as a script and its exit code escapes
before unittest does anything." Full writeup is now in
`check-control-registration.sh`'s own G2 header comment so the next reader
doesn't have to re-derive it.

### What actually makes 3 of the 4 files reachable

`scripts/check-fact-evidence-replay.sh` — registered in `scripts/check.sh`
(step `facts-replay`) and the justfile — executes every
`proved`/`computed`/`refuted`/`axiom` fact's `checker_command` string
verbatim. **7 `proved` facts** cite three of the four scripts directly by
path (`python3 scripts/tests/check-<name>.py`):

Detail moved to [`../notes/367-control-registration-hyphen.md`](../notes/367-control-registration-hyphen.md).

