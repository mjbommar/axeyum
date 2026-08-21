#!/usr/bin/env bash
#
# The render strand's gate. Run from anywhere:  ./render/check.sh
#
# EXIT STATUS DEPENDS ON FINDINGS, and it depends on them in a way that cannot
# be satisfied by completing. Two habits from this repository's history are
# built in on purpose:
#
#   * every step that runs tests asserts a NONZERO TEST COUNT. A suite that
#     compiles to an empty binary prints "running 0 tests ... ok" and exits 0;
#     one of this repository's gates was inert for 15 days that way.
#   * the Python validator refuses to report success when it checked no files,
#     and this script checks that its stdout names the file count it saw.
#
# Steps, in order, with what each one can catch:
#   1  cargo fmt --check          formatting drift
#   2  cargo clippy -D warnings   lints, over ALL targets including tests
#   3  cargo test                 the whole suite; count asserted nonzero
#   4  validate-docir.py          the schema, independently of the Rust model
#   5  validate-docir.py (neg)    proof that step 4 can fail
#   6  fixture freshness          the run record still describes the ledger
#   7  ASCII                      repository-wide rule, over everything owned
#   8  LaTeX compile             optional; SKIPPED loudly when no TeX is present
set -uo pipefail

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
root="$(cd "$here/.." && pwd)"
cd "$root" || exit 2

pass=0
fail=0
step() { printf '\n=== %s\n' "$1"; }
ok() { printf 'PASS  %s\n' "$1"; pass=$((pass + 1)); }
bad() { printf 'FAIL  %s\n' "$1"; fail=$((fail + 1)); }

cargo_flags="--manifest-path $here/Cargo.toml"
# Prefer the offline path: this package's dependency set is small and pinned by
# its own lockfile, and a gate that reaches the network is a gate that fails for
# reasons unrelated to the code.
if cargo metadata $cargo_flags --offline --format-version 1 >/dev/null 2>&1; then
  offline="--offline"
else
  offline=""
  printf 'note: dependencies are not fully vendored; running without --offline\n'
fi

step "1/8 formatting"
# `cargo fmt --check` covers the WHOLE package, including files other lanes own
# (render/src/emit_html.rs, render/src/layout.rs). Restricting rustfmt to a file
# list does not work -- it follows `mod` declarations out of lib.rs -- and
# --skip-children is nightly-only. So the whole package is checked and the
# result is PARTITIONED: a diff in a file this lane owns fails the gate, a diff
# elsewhere is reported as a note. Nothing is skipped silently, and this gate
# never fails because of another lane's in-progress work.
core_files=(
  render/src/ir.rs render/src/assemble.rs render/src/emit_md.rs
  render/src/emit_tex.rs render/src/lib.rs render/src/main.rs
  render/tests/common/mod.rs render/tests/negative.rs render/tests/golden.rs
  render/tests/determinism.rs render/tests/cross_format.rs render/tests/schema.rs
)
fmt_log="$(mktemp)"
cargo fmt $cargo_flags --check >"$fmt_log" 2>&1
dirty="$(grep -oE '^Diff in [^:]+' "$fmt_log" | sed 's/^Diff in //' | sort -u)"
rm -f "$fmt_log"
mine=""
theirs=""
for f in $dirty; do
  rel="${f#"$root"/}"
  if printf '%s\n' "${core_files[@]}" | grep -qxF "$rel"; then
    mine="$mine $rel"
  else
    theirs="$theirs $rel"
  fi
done
if [ -n "$mine" ]; then
  printf 'unformatted (this lane):%s\n' "$mine"
  bad "formatting"
else
  ok "formatting (${#core_files[@]} owned files clean)"
fi
[ -z "$theirs" ] || printf 'note: unformatted, owned by another lane:%s\n' "$theirs"

step "2/8 cargo clippy --all-targets -D warnings"
# Default features: DESIGN's modules are behind the off-by-default `html`
# feature in round 1, so this lints what is wired. Round 2 adds --all-features.
if cargo clippy $cargo_flags $offline --all-targets -- -D warnings; then
  ok "clippy"
else
  bad "clippy"
fi

step "3/8 cargo test (count asserted nonzero)"
test_log="$(mktemp)"
if cargo test $cargo_flags $offline --no-fail-fast 2>&1 | tee "$test_log"; then
  test_status=0
else
  test_status=1
fi
# Sum every "N passed" the run reported. Zero means the suite compiled to
# nothing, which is a green-looking gate that checks nothing.
passed="$(grep -oE '[0-9]+ passed' "$test_log" | grep -oE '^[0-9]+' | paste -sd+ - | bc 2>/dev/null)"
passed="${passed:-0}"
if [ "$test_status" -ne 0 ]; then
  bad "tests (some failed)"
elif [ "$passed" -lt 30 ]; then
  bad "tests ran only $passed assertion(s) -- expected the full suite; a shrinking count means a suite stopped compiling"
else
  ok "tests ($passed passed)"
fi
rm -f "$test_log"

step "4/8 scripts/validate-docir.py on the fixtures"
docir_log="$(mktemp)"
if python3 scripts/validate-docir.py \
  render/tests/fixtures/fixture-doc.json \
  render/tests/fixtures/run-fact-ledger-check.json >"$docir_log" 2>&1; then
  cat "$docir_log"
  if grep -q '2 file(s)' "$docir_log"; then
    ok "docir validation (2 files)"
  else
    bad "docir validation exited 0 but did not report checking 2 files"
  fi
else
  cat "$docir_log"
  bad "docir validation"
fi
rm -f "$docir_log"

step "5/8 the validator can fail (negative control)"
neg_dir="$(mktemp -d)"
python3 - "$neg_dir" <<'PY'
import json, sys
d = sys.argv[1]
doc = json.load(open("render/tests/fixtures/fixture-doc.json"))
for b in doc["blocks"]:
    if b["kind"]["type"] == "claim":
        b["kind"]["evidence"] = []
        break
json.dump(doc, open(d + "/no-evidence.json", "w"), indent=2)
PY
if python3 scripts/validate-docir.py "$neg_dir/no-evidence.json" >/dev/null 2>&1; then
  bad "the validator accepted a claim with no evidence -- it is a checker that cannot fail"
else
  ok "the validator rejects a claim with no evidence"
fi
if python3 scripts/validate-docir.py >/dev/null 2>&1; then
  bad "the validator reported success over zero files"
else
  ok "the validator refuses an empty check"
fi
rm -rf "$neg_dir"

step "6/8 the fixture run record still describes the ledger"
# Re-run the producer into a temp file and compare everything except the epoch
# (which pins whatever commit was HEAD when the record was written). A drift
# here means the ledger moved and the goldens need regenerating -- deliberately,
# by a human who reads the diff.
fresh="$(mktemp -d)"
if python3 render/tests/fixtures/make_run_record.py --out "$fresh/record.json" 2>/dev/null; then
  if python3 - "$fresh/record.json" <<'PY'
import json, sys
new = json.load(open(sys.argv[1]))
old = json.load(open("render/tests/fixtures/run-fact-ledger-check.json"))
for r in (new, old):
    r["provenance"].pop("epoch", None)
    for a in r.get("artifacts", []):
        a.pop("bytes", None)
sys.exit(0 if new == old else 1)
PY
  then
    ok "run record matches a fresh run"
  else
    bad "run record no longer matches a fresh run: the ledger moved. Re-run render/tests/fixtures/make_run_record.py, then UPDATE_GOLDEN=1 cargo test --test golden, and READ THE DIFF"
  fi
else
  bad "the fixture producer itself failed (its exit status depends on its findings)"
fi
rm -rf "$fresh"

step "7/8 ASCII over everything this lane owns"
non_ascii="$(LC_ALL=C grep -lP '[^\x00-\x7F]' \
  "${core_files[@]}" render/check.sh render/Cargo.toml \
  render/tests/fixtures/*.json render/tests/fixtures/*.py render/tests/fixtures/*.svg \
  render/tests/golden/* \
  artifacts/ontology/docir.schema.json scripts/validate-docir.py 2>/dev/null || true)"
if [ -z "$non_ascii" ]; then
  ok "ASCII"
else
  printf '%s\n' "$non_ascii"
  bad "non-ASCII bytes in the files above"
fi

step "8/8 LaTeX compiles standalone (only if a TeX toolchain is here)"
# Reported as SKIPPED, never as a pass. A step that silently counts as green on
# a host that cannot run it is how a gate stops meaning anything -- measured
# 2026-08-16, `lean` and `just` existed on one fleet host of five.
if command -v pdflatex >/dev/null 2>&1; then
  tex_dir="$(mktemp -d)"
  if cargo run $cargo_flags $offline -q -- render \
       --manifest render/tests/fixtures/fixture-doc.json --repo-root . \
       --format tex --out "$tex_dir" >/dev/null 2>&1 \
     && (cd "$tex_dir" && pdflatex -interaction=nonstopmode -halt-on-error \
           fixture-fact-ledger-standalone.tex >latex.log 2>&1) \
     && [ -s "$tex_dir/fixture-fact-ledger-standalone.pdf" ]; then
    ok "LaTeX compiles ($(stat -c %s "$tex_dir/fixture-fact-ledger-standalone.pdf") byte PDF)"
  else
    [ -f "$tex_dir/latex.log" ] && grep -E '^!' "$tex_dir/latex.log" | head -10
    bad "LaTeX does not compile"
  fi
  rm -rf "$tex_dir"
else
  printf 'SKIP  LaTeX compile: no pdflatex on this host (this is NOT a pass)\n'
fi

printf '\n=== render/check.sh: %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ] || exit 1
[ "$pass" -ge 8 ] || { printf 'refusing to report success after only %d checks\n' "$pass"; exit 2; }
exit 0
