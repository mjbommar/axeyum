#!/usr/bin/env bash
# Clippy over the whole workspace, reporting WHAT IT LINTED.
#
# WHY THIS EXISTS. `cargo clippy --workspace --all-targets --all-features --
# -D warnings` exits 0 in two situations that look identical from outside:
#
#   (a) it linted every target and found nothing;
#   (b) it linted NOTHING, because cargo decided the cached artifacts were
#       fresh — and cargo decides freshness by MTIME.
#
# (b) is not theoretical. On 2026-08-13 a lane added a `differential` mode to
# `crates/axeyum-cnf/examples/drat_memory_probe.rs` that pushed `main` past
# `clippy::too_many_lines`; clippy run after the edit reported nothing, and
# `touch crates/axeyum-cnf/src/lib.rs` made the warning appear
# (`agent-g-drat-memory/DIARY.md:267`). CI runs `-D warnings`, so the red build
# would have landed on whoever pushed next.
#
# Reproduced from scratch on 2026-08-14 (cargo 1.97.0-nightly, clippy 0.1.97):
#
#     touch -d '2020-01-01' examples/warny.rs   # file carries `needless_return`
#     cargo clippy --all-targets -- -D warnings -> exit 0, "Finished in 0.00s"
#
# and `git archive HEAD | tar -x` — the snapshot build every lane is told to use
# — stamps every file with the COMMIT time, which is exactly how a source file
# ends up older than the artifact built from its predecessor.
#
# WHAT THIS SCRIPT ADDS over the bare cargo invocation:
#
#   1. `scripts/check-source-freshness.sh` touches every build input whose
#      CONTENT changed since the last recorded clean run, so cargo cannot
#      consider changed content fresh.
#   2. It counts the targets clippy actually processed, split into "compiled by
#      this run" and "replayed from cargo's cache", and prints both.
#   3. It compares that against the workspace's target list from `cargo
#      metadata` and NAMES any target that was never linted.
#   4. It names, every run, the things it does NOT cover: dependencies, doc
#      tests, and other `--target` triples (wasm32 is a supported target,
#      ADR-0017).
#
# A gate that cannot say what it examined is not a gate. The model is
# `check-fmt-complete.sh` ("checked 881 files") and the claims checker
# ("103 claims re-checked, 0 errors, 24 row(s) not re-checked here").
#
# Usage: scripts/check-clippy-complete.sh [--toolchain stable] [-- extra cargo args]
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2
root="$PWD"

toolchain=""
extra=()
while [ $# -gt 0 ]; do
  case "$1" in
    --toolchain) toolchain="+${2:-}"; shift 2 ;;
    --) shift; extra=("$@"); break ;;
    *) echo "check-clippy-complete: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

# ---------------------------------------------------------------------------
# 1. Defeat mtime freshness for content that changed.
# ---------------------------------------------------------------------------
"$root/scripts/check-source-freshness.sh" --gate clippy --touch || exit 2

# ---------------------------------------------------------------------------
# 2/3. Lint, and account for every workspace target.
# ---------------------------------------------------------------------------
# `AXEYUM_CLIPPY_JSON_LOG` keeps the raw cargo JSON stream for inspection; it is
# a debugging aid, so it is the one file this script does not delete.
log="${AXEYUM_CLIPPY_JSON_LOG:-}"
scratch=()
if [ -z "$log" ]; then
  log="$(mktemp)" || exit 2
  scratch+=("$log")
fi
cleanup() { [ ${#scratch[@]} -gt 0 ] && rm -f "${scratch[@]}"; }
trap cleanup EXIT

cargo_args=(clippy --workspace --all-targets --all-features --message-format=json)
[ -n "$toolchain" ] && cargo_args=("$toolchain" "${cargo_args[@]}")

# `--message-format=json` suppresses cargo's human rendering, so the parser
# below re-prints `message.rendered` verbatim: no diagnostic is swallowed.
cargo "${cargo_args[@]}" -- -D warnings "${extra[@]+"${extra[@]}"}" > "$log" 2>>"$log"
cargo_status=$?

# Via a FILE, not an environment variable: `cargo metadata` for this workspace is
# ~1 MB and the env route dies with "Argument list too long" (measured).
meta_file="$(mktemp)" || exit 2
scratch+=("$meta_file")
cargo metadata --no-deps --all-features --format-version 1 > "$meta_file" 2>/dev/null

CLIPPY_LOG="$log" CLIPPY_META_FILE="$meta_file" python3 - <<'PY'
import json, os, sys

log = os.environ["CLIPPY_LOG"]
try:
    with open(os.environ["CLIPPY_META_FILE"], "r", errors="replace") as handle:
        meta = json.load(handle)
except (OSError, json.JSONDecodeError):
    meta = None

# Workspace membership is decided by `manifest_path`, not by parsing
# `package_id`: the package-id spec omits the crate name for path dependencies
# whose directory matches ("path+file:///.../axeyum-aig#0.1.0"), and a first
# version of this script mis-parsed it and reported all 24 crates unlinted while
# also reporting 678 targets linted. `manifest_path` is present on both sides
# and is exact.
workspace = {}          # manifest_path -> package name
expected = set()        # (manifest_path, target name, kinds)
if meta:
    for pkg in meta.get("packages", []):
        manifest = pkg.get("manifest_path")
        workspace[manifest] = pkg.get("name")
        for target in pkg.get("targets", []):
            kinds = tuple(target.get("kind", []))
            if "custom-build" in kinds:
                continue  # build scripts are compiled, never linted as targets
            expected.add((manifest, target.get("name"), kinds))

ws_artifacts = {}       # (manifest, name, kinds) -> fresh
dep_artifacts = set()
warn_by_lint = {}
errors = 0
non_json = []

with open(log, "r", errors="replace") as handle:
    for line in handle:
        line = line.strip()
        if not line.startswith("{"):
            if line:
                non_json.append(line)
            continue
        try:
            msg = json.loads(line)
        except json.JSONDecodeError:
            non_json.append(line)
            continue
        reason = msg.get("reason")
        if reason == "compiler-artifact":
            target = msg.get("target", {})
            manifest = msg.get("manifest_path")
            key = (manifest, target.get("name", ""), tuple(target.get("kind", [])))
            if manifest in workspace:
                # A unit can be emitted twice (lib, then lib-as-test); `fresh` is
                # per emission, so "any emission not fresh" means it was compiled.
                ws_artifacts[key] = ws_artifacts.get(key, True) and msg.get("fresh", False)
            else:
                dep_artifacts.add(key)
        elif reason == "compiler-message":
            diag = msg.get("message", {})
            rendered = diag.get("rendered")
            if rendered:
                sys.stderr.write(rendered)
            level = diag.get("level")
            code = (diag.get("code") or {}).get("code") or "(no lint code)"
            if level in ("error", "warning"):
                if level == "error":
                    errors += 1
                warn_by_lint[code] = warn_by_lint.get(code, 0) + 1

compiled = sum(1 for fresh in ws_artifacts.values() if not fresh)
replayed = sum(1 for fresh in ws_artifacts.values() if fresh)
packages = len({key[0] for key in ws_artifacts})

seen = {(key[0], key[1]) for key in ws_artifacts}
missing = sorted(
    f"{workspace.get(manifest, manifest)}:{name} ({'+'.join(kinds)})"
    for manifest, name, kinds in expected
    if (manifest, name) not in seen
)

print(f"check-clippy-complete: linted {len(ws_artifacts)} of {len(expected)} workspace "
      f"targets across {packages} of {len(workspace)} crates "
      f"({compiled} compiled by this run, {replayed} replayed from cargo's cache and "
      f"certified by the freshness manifest); {len(dep_artifacts)} dependency targets "
      f"were built but not linted (cap-lints)")
total_diags = sum(warn_by_lint.values())
if total_diags:
    print(f"check-clippy-complete: {total_diags} diagnostic(s), {errors} at error level:")
    for code, n in sorted(warn_by_lint.items(), key=lambda kv: (-kv[1], kv[0])):
        print(f"    {n:>4}  {code}")
else:
    print("check-clippy-complete: 0 diagnostics")

if missing:
    print(f"check-clippy-complete: {len(missing)} workspace target(s) NOT linted:")
    for entry in missing:
        print(f"    {entry}")

print("check-clippy-complete: not checked here — dependency crates (cap-lints), "
      "doc tests (clippy does not lint them), and every --target triple other than "
      "the host (wasm32 is supported, ADR-0017: run "
      "`cargo clippy --target wasm32-unknown-unknown -p axeyum-solver`)")

if not meta:
    print("check-clippy-complete: `cargo metadata` produced nothing, so the target "
          "list could not be checked for completeness.", file=sys.stderr)
    sys.exit(1)
if not ws_artifacts:
    print("check-clippy-complete: clippy processed ZERO workspace targets — the gate "
          "examined nothing. This is the failure mode the script exists to catch.",
          file=sys.stderr)
    sys.exit(1)
if missing:
    print("check-clippy-complete: a workspace target was never linted (listed above). "
          "Usual causes: `required-features` not enabled, or an excluded package.",
          file=sys.stderr)
    sys.exit(1)
sys.exit(0)
PY
scope_status=$?

if [ "$cargo_status" -ne 0 ]; then
  echo "check-clippy-complete: clippy FAILED (cargo exit $cargo_status)" >&2
  # Anything cargo wrote that was not JSON (linker errors, panics) would be
  # invisible otherwise.
  grep -v '^{' "$log" | tail -20 >&2
  exit "$cargo_status"
fi
[ "$scope_status" -ne 0 ] && exit "$scope_status"

# Only a clean, complete run certifies this content as examined.
"$root/scripts/check-source-freshness.sh" --gate clippy --record
