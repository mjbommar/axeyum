#!/usr/bin/env bash
# Controls for `scripts/check-aggregate-scope.sh`'s step NORMALIZER.
#
# Why this suite exists. The gate compares the step list of `just check`
# against `./scripts/check.sh` and reports what only one side runs. Its
# normalizer used to strip a `./` path prefix only at LINE START
# (`re.sub(r"^\./", ...)`), but `check.sh` writes its steps as
# `python3 ./scripts/x.py` while the justfile writes `python3 scripts/x.py`.
# Those normalize to different strings, so ONE script was reported as TWO
# divergences -- once as `check.sh-only`, once as `just-only`.
#
# Measured 2026-08-30: 13 reported divergences, 4 of them this artifact
# (`check-autogenesis-already-proved` and `check-test-attribute-integrity`,
# both of which had ALREADY been correctly added to the justfile). Fixing the
# normalizer took the real count to 9. A gate that manufactures divergences
# is a gate whose output nobody can act on, which is how it came to sit red.
#
# These controls test the SHIPPED normalizer, not a copy: the python block is
# extracted from `check-aggregate-scope.sh` itself and exec'd. If that
# extraction ever fails, the suite errors rather than passing vacuously.
set -u
cd "$(dirname "$0")/../.." || exit 2

python3 - <<'PY'
import re, sys, pathlib

src = pathlib.Path("scripts/check-aggregate-scope.sh").read_text()

# Pull the normalizer's python body out of the shell function verbatim.
m = re.search(r"normalize\(\)\s*\{\s*\n\s*python3 -c '(.*?)'\n", src, re.S)
if not m:
    print("FAIL extraction: could not find normalize()'s python body in "
          "scripts/check-aggregate-scope.sh -- the suite cannot test what it "
          "cannot find, and a suite that silently tests nothing is worse than "
          "no suite.")
    sys.exit(1)

ns = {}
try:
    exec(m.group(1), ns)                      # noqa: S102 - the subject under test
except Exception as e:                        # pragma: no cover - extraction guard
    print(f"FAIL extraction: normalizer body did not exec: {e!r}")
    sys.exit(1)

if "strip_wrappers" not in ns:
    print("FAIL extraction: no strip_wrappers() in the extracted body.")
    sys.exit(1)

norm = ns["strip_wrappers"]
fails = []


def case(name, why, got, want):
    if got != want:
        fails.append(f"  {name}: {why}\n      got  {got!r}\n      want {want!r}")


# --- Guard 1: a mid-line `./` path prefix is stripped. -----------------------
# THE regression this suite exists for. Deleting the `(^|\s)\./` substitution
# kills exactly this case.
case(
    "midline-dot-slash",
    "`python3 ./scripts/x.py` and `python3 scripts/x.py` are the same step",
    norm("python3 ./scripts/check-test-attribute-integrity.py"),
    norm("python3 scripts/check-test-attribute-integrity.py"),
)

# --- Guard 2: a leading `./` is still stripped. ------------------------------
# The original anchored behaviour, kept. A fix that replaced the anchored
# substitution instead of generalizing it would kill this case.
case(
    "leading-dot-slash",
    "`./scripts/x.sh` and `scripts/x.sh` are the same step",
    norm("./scripts/tests/test-creal-prelude-build-ratio.sh"),
    norm("scripts/tests/test-creal-prelude-build-ratio.sh"),
)

# --- Guard 3: an env-var wrapper is stripped. -------------------------------
case(
    "env-wrapper",
    "`FOO=1 cmd` and `cmd` are the same step",
    norm('AXEYUM_CHECK_LIST=1 python3 scripts/x.py'),
    norm("python3 scripts/x.py"),
)

# --- Guard 4: the `mem-run.sh` memory-cap wrapper is stripped. ---------------
# A memory cap is not a step; one side wrapping a command in it is not a scope
# difference. Uncovered until 2026-08-30 -- deleting the substitution left the
# whole suite green.
case(
    "mem-run-wrapper",
    "`scripts/mem-run.sh cmd` and `cmd` are the same step",
    norm("scripts/mem-run.sh cargo test --workspace"),
    norm("cargo test --workspace"),
)

# --- Guard 5: whitespace runs collapse. -------------------------------------
case(
    "whitespace-collapse",
    "internal whitespace runs are not a scope difference",
    norm("python3   scripts/x.py    --flag"),
    "python3 scripts/x.py --flag",
)

# --- NEGATIVE control: the normalizer must still SEPARATE real differences. --
# Without this, every guard above is satisfiable by `return ""`, and the gate
# would report zero divergences forever -- the checker-that-cannot-fail defect
# this repository cares most about, arriving through the door marked "fix".
distinct = [
    "python3 scripts/check-facts.py",
    "python3 scripts/check-facts.py --strict",
    "python3 scripts/check-other.py",
    "uv run --no-sync ruff check python/ tools/",
]
normed = [norm(x) for x in distinct]
if len(set(normed)) != len(distinct):
    fails.append(
        "  negative-control: the normalizer COLLAPSED genuinely different "
        f"steps -- {len(distinct)} inputs became {len(set(normed))} outputs: "
        f"{normed!r}. A normalizer that erases real differences makes the "
        "gate incapable of reporting one."
    )

# `../` must survive: it is a real path component, not a `./` prefix.
if "../" not in norm("bash ../outside/x.sh"):
    fails.append("  negative-control: `../` was mangled by the `./` strip.")

if fails:
    print(f"FAIL: {len(fails)} normalizer control(s) failed")
    print("\n".join(fails))
    sys.exit(1)

print("AGGREGATE_SCOPE_CONTROLS|guards=5|negative_controls=2|PASS")
PY
