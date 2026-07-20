#!/usr/bin/env bash
set -euo pipefail

python3 - <<'PY'
from pathlib import Path
import tomllib


def manifest(path: str) -> dict:
    with Path(path).open("rb") as handle:
        return tomllib.load(handle)


solver = manifest("crates/axeyum-solver/Cargo.toml")
if solver["features"].get("default") != ["qfbv"]:
    raise SystemExit("axeyum-solver default feature must be exactly qfbv")

wasm = manifest("crates/axeyum-wasm/Cargo.toml")
workspace = manifest("Cargo.toml")
if "crates/axeyum-wasm" not in workspace["workspace"]["members"]:
    raise SystemExit("axeyum-wasm must remain under the workspace build gate")
wasm_solver = wasm["dependencies"]["axeyum-solver"]
if wasm_solver.get("default-features") is not False or wasm_solver.get("features") != [
    "qfbv"
]:
    raise SystemExit("axeyum-wasm must explicitly consume the qfbv-only profile")

for path in (
    "crates/axeyum-bench/Cargo.toml",
    "crates/axeyum-evm/Cargo.toml",
    "crates/axeyum-property/Cargo.toml",
    "crates/axeyum-verify/Cargo.toml",
):
    dependency = manifest(path)["dependencies"]["axeyum-solver"]
    if dependency.get("default-features") is not False or dependency.get("features") != [
        "full"
    ]:
        raise SystemExit(f"{path} must explicitly opt into the full solver surface")
PY

cargo clippy -p axeyum-solver --no-default-features --features qfbv --lib --jobs 1 -- -D warnings
# The package-default command must not attempt to compile full-only integration
# targets after qfbv became the default.
cargo test -p axeyum-solver --no-run --quiet --jobs 1
cargo test -p axeyum-solver --no-default-features --features qfbv \
  --test qfbv_profile --jobs 1

tree="$(cargo tree -p axeyum-solver --no-default-features --features qfbv \
  -e normal --prefix none)"
unexpected="$(printf '%s\n' "$tree" | rg '^axeyum-' | \
  rg -v '^axeyum-(solver|aig|bv|cnf|ir|query|rewrite) ' || true)"
if [[ -n "$unexpected" ]]; then
  printf '%s\n' 'QF_BV profile pulled an unexpected Axeyum crate:' >&2
  printf '%s\n' "$unexpected" >&2
  exit 1
fi

default_tree="$(cargo tree -p axeyum-solver -e normal --prefix none)"
default_unexpected="$(printf '%s\n' "$default_tree" | rg '^axeyum-' | \
  rg -v '^axeyum-(solver|aig|bv|cnf|ir|query|rewrite) ' || true)"
if [[ -n "$default_unexpected" ]]; then
  printf '%s\n' 'Default axeyum-solver profile pulled an unexpected Axeyum crate:' >&2
  printf '%s\n' "$default_unexpected" >&2
  exit 1
fi
