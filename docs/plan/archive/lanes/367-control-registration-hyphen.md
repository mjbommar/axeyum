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

| script | cited by (facts, epistemic_status=proved) |
| --- | --- |
| `check-totient-prime-power-numerics.py` | F-nat-totient-mul-of-dvd, F-nat-totient-dvd-totient-mul-prime, F-nat-totient-prime-pow |
| `check-totient-dvd-chain-numerics.py` | F-ml430-nat-eq-or-eq-of-totient-eq-totient-d4d154c7, F-ml430-nat-totient-dvd-of-dvd-9622e44a |
| `check-totient-mul-coprime-numerics.py` | F-nat-totient-mul-of-coprime, F-nat-crt-self-map-injective-on |
| `check-countrange-bijection-numerics.py` | **none** — 0 facts, 0 gates |

So my earlier framing ("None of the four is invoked from `check.sh` or the
`justfile` … they run in no gate today") was wrong for 3 of the 4 — checked by
grepping `check.sh`/`justfile` for the *filename* directly, which misses a
generic sweep that executes fact `checker_command` strings dynamically.
`check-countrange-bijection-numerics.py` genuinely was an orphan: cited by
zero facts and zero CALLERS.

### What I decided these files are

Standalone numeric-check scripts invoked by path — the same shape as a `.sh`
control, which G2 has always exempted precisely because it is "invoked by
path" rather than discovered. The fix generalizes that exemption from
"`.sh` only" to "invoked by path from CALLERS **or** a fact's
`checker_command`," which is a property, not a filename pattern:

- `scripts/check-control-registration.sh` G2: a hyphenated `.py` is rejected
  **iff** it is invoked by nothing (checked against `callers_text`, unchanged,
  **plus** a new `facts_text` built from `artifacts/facts/*.json`). The old
  false claim about `python3 -m unittest` is removed from both the header
  comment and the per-file error message.
- `scripts/check.sh` and the `justfile`: registered
  `check-countrange-bijection-numerics.py` directly as a step (the one file
  that had no real caller at all), closing the actual gap — "nothing runs
  it" — rather than exempting it by pattern.

### Proof the exemption still catches a real orphan

`scripts/tests/test-hyphen-probe.py` (a hyphenated `.py` cited by nothing) is
still rejected — case `hyphenated-py`, unchanged expectation except for the
updated message text ("invoked by NOTHING" instead of "unreachable TWICE").
Two new cases prove the fact-reachability path is real and not vacuous:

- `hyphen-py-reachable-via-fact` — a hyphenated `.py` cited **only** by a
  fabricated `artifacts/facts/*.json` in the test skeleton (not by any
  CALLERS entry) must pass.
- `hyphen-py-fact-reference-removed` — deleting that one fact reference makes
  the same file fail again (mutation-style regression test, not just a
  positive control).

`scripts/tests/test-check-control-registration.sh`: 17 cases (was 15; 2 new),
threshold raised 14 → 17, all green.

### Mutation kill sets, as measured (in-worktree, reverted after each)

| mutant | description | killed | survived |
| --- | --- | --- | --- |
| M1 | drop the `facts_text` lookup from `by_path` (only `callers_text` counted) | `healthy`, `hyphen-py-reachable-via-fact` (2) | 15 |
| M2 | neuter the orphan test (`[ "${by_path:-0}" -eq -1 ]`, never true) | `hyphenated-py`, `hyphen-py-fact-reference-removed` (2) | 15 |

Both mutants restored; `diff` against a pre-edit copy of the gate script
confirmed byte-identical before re-verifying the full suite green.

### Verified both directions (non-negotiable item)

    python3 scripts/tests/check-totient-prime-power-numerics.py   -> exit 0
    python3 scripts/tests/check-countrange-bijection-numerics.py  -> exit 0
    python3 scripts/tests/check-totient-dvd-chain-numerics.py     -> exit 0
    python3 scripts/tests/check-totient-mul-coprime-numerics.py   -> exit 0
    python3 scripts/tests/check-does-not-exist-numerics.py        -> exit 2 (no such file)

`python3 scripts/validate-facts.py`: 2265 facts checked, 0 errors (no fact
touched — only `checker_command` paths were ever a candidate, and none needed
changing since all 7 already used the correct path).

`scripts/check-control-registration.sh`: exit 0,
`controls=32|orphans=0|py_controls=302|py_orphans=0`.

`scripts/check-aggregate-scope.sh`: exit 0, still 64 recorded divergences (the
new step was added to both `check.sh` and the justfile, so the divergence
count did not move).

### Not touched

`nat_prelude/`, `artifacts/autogenesis/` (sibling lanes), and no fact's
`epistemic_status` / `proof_route` / `formal.statement`.

## Landed changes

- `scripts/check-control-registration.sh` — G2 rewritten: reachability check
  (CALLERS ∪ facts' `checker_command`) replaces blanket hyphen rejection;
  header comment corrected with the measured import mechanism.
- `scripts/check.sh`, `justfile` — registered
  `check-countrange-bijection-numerics.py` as a direct step (the one file with
  no real caller).
- `scripts/tests/test-check-control-registration.sh` — `build()` now includes
  a hyphenated `.py` reachable only via a fabricated fact; 2 new cases; case 4's
  expected message updated; case-count floor 14 → 17.
