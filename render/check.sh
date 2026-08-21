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
#   2  cargo clippy -D warnings   lints, over ALL targets and ALL features
#   3  cargo test                 the whole suite; count asserted nonzero, and
#                                 three named tests asserted to have RUN
#   4  validate-docir.py          the schema, independently of the Rust model,
#                                 over the fixtures AND the whole P0 corpus
#   5  validate-docir.py (neg)    proof that step 4 can fail
#   6  fixture freshness          the run record still describes the ledger
#   7  ASCII                      repository-wide rule, over everything owned
#   8  render the corpus          every manifest x every format, and a NON-EMPTY
#                                 EMITTER DIAGNOSTIC LIST FAILS (round 2)
#   9  self-containment           an independent grep gate over the emitted HTML,
#                                 with a negative control proving it can fail
#  10  LaTeX compile             optional; SKIPPED loudly when no TeX is present
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

step "1/10 formatting"
# `cargo fmt --check` covers the WHOLE package, including files other lanes own
# (render/src/emit_html.rs, render/src/layout.rs). Restricting rustfmt to a file
# list does not work -- it follows `mod` declarations out of lib.rs -- and
# --skip-children is nightly-only. So the whole package is checked and the
# result is PARTITIONED: a diff in a file this lane owns fails the gate, a diff
# elsewhere is reported as a note. Nothing is skipped silently, and this gate
# never fails because of another lane's in-progress work.
# Round 2: the partition is now the WHOLE package. Round 1 split it because
# `emit_html.rs` and `layout.rs` belonged to another lane working in the same
# checkout and `cargo fmt` would have rewritten their in-progress work. Those
# files are integrated now, so an unformatted file anywhere in this package
# fails the gate. The partition machinery stays, because the situation it
# handles (a second lane inside this package) will recur.
core_files=(
  render/src/ir.rs render/src/assemble.rs render/src/emit_md.rs
  render/src/emit_tex.rs render/src/emit_html.rs render/src/layout.rs
  render/src/lib.rs render/src/main.rs
  render/tests/common/mod.rs render/tests/negative.rs render/tests/golden.rs
  render/tests/determinism.rs render/tests/cross_format.rs render/tests/schema.rs
  render/tests/pipeline_negative_control.rs
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

step "2/10 cargo clippy --all-targets --all-features -D warnings"
# --all-features, so the HTML emitter and the layout engine are linted too.
# Without it this step compiled neither, and they are the two largest modules
# in the package.
if cargo clippy $cargo_flags $offline --all-targets --all-features -- -D warnings; then
  ok "clippy"
else
  bad "clippy"
fi

step "3/10 cargo test --all-features (count asserted nonzero; named tests asserted to run)"
test_log="$(mktemp)"
if cargo test $cargo_flags $offline --all-features --no-fail-fast 2>&1 | tee "$test_log"; then
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
elif [ "$passed" -lt 100 ]; then
  bad "tests ran only $passed assertion(s) -- expected the full suite; a shrinking count means a suite stopped compiling"
else
  ok "tests ($passed passed)"
fi
# A COUNT IS NOT ENOUGH for a feature-gated test. `#[cfg(feature = "html")]`
# code compiles to nothing without the feature, and the total would still look
# healthy because 100+ other tests ran. So the three tests that only exist
# under `html` are asserted BY NAME to have appeared in the output.
for named in \
  all_three_formats_report_the_same_claims_and_statuses \
  the_committed_p0_manifests_agree_across_all_three_formats \
  preview_page_matches_its_source; do
  if grep -q "^test .*$named ... ok" "$test_log"; then
    ok "ran $named"
  else
    bad "$named did not run: a feature-gated test that compiles to nothing is an inert gate"
  fi
done
rm -f "$test_log"

step "4/10 scripts/validate-docir.py on the fixtures AND the P0 corpus"
# Round 2 widened this from the two fixtures to every committed manifest and
# run record: the schema is only a gate over what it is pointed at, and an
# empty result from a tool nobody aimed at your subject is indistinguishable
# from a strong negative result. The 324 fact cards are validated by their own
# producer on every run (facts_to_docir.py refuses to write otherwise); the
# nine files here are the ones a human edits or a Rust test consumes.
docir_log="$(mktemp)"
if python3 scripts/validate-docir.py \
  render/tests/fixtures/fixture-doc.json \
  render/tests/fixtures/run-fact-ledger-check.json \
  render/examples-input/cert/certificate.doc.json \
  render/examples-input/cert/certificate-negative-control.doc.json \
  render/examples-input/cert/run-certificate.json \
  render/examples-input/cert/run-mutant-M1.json \
  render/examples-input/facts/facts-atlas.doc.json \
  render/examples-input/facts/facts-pilot.doc.json \
  render/examples-input/facts/facts-pilot-arith.doc.json >"$docir_log" 2>&1; then
  cat "$docir_log"
  if grep -q '9 file(s)' "$docir_log"; then
    ok "docir validation (9 files)"
  else
    bad "docir validation exited 0 but did not report checking 2 files"
  fi
else
  cat "$docir_log"
  bad "docir validation"
fi
rm -f "$docir_log"

step "5/10 the validator can fail (negative control)"
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

step "6/10 the fixture run record still describes the ledger"
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

step "7/10 ASCII over everything this package owns"
non_ascii="$(LC_ALL=C grep -lP '[^\x00-\x7F]' \
  "${core_files[@]}" render/check.sh render/Cargo.toml \
  render/tests/fixtures/*.json render/tests/fixtures/*.py render/tests/fixtures/*.svg \
  render/tests/golden/* \
  render/assets/style.css render/assets/app.js render/assets/preview/*.py \
  render/producers/*.py render/producers/*.rs render/producers/mutants/*.rs \
  render/producers-py/*.py \
  render/examples-input/cert/*.json render/examples-input/facts/*.json \
  artifacts/ontology/docir.schema.json scripts/validate-docir.py 2>/dev/null || true)"
if [ -z "$non_ascii" ]; then
  ok "ASCII"
else
  printf '%s\n' "$non_ascii"
  bad "non-ASCII bytes in the files above"
fi

step "8/10 render the whole P0 corpus in every format; ANY emitter diagnostic fails"
# THE EMITTER REPORTS WHAT IT COULD NOT DRAW, and until round 2 nobody read the
# report. That is how every figure in every assembled document rendered as a
# loud "unknown figure kind" box for a day without a gate noticing: the page
# said so, the diagnostics said so, and no exit status depended on either.
#
# `--fail-on-diagnostics` turns the report into an exit status. It is run over
# the real corpus, not a fixture, because the shapes that break normalization
# are the ones real producers emit.
render_out="$(mktemp -d)"
render_fail=0
render_n=0
for manifest in \
  render/examples-input/cert/certificate.doc.json \
  render/examples-input/facts/facts-pilot.doc.json \
  render/examples-input/facts/facts-pilot-arith.doc.json \
  render/examples-input/facts/facts-atlas.doc.json; do
  for format in md tex html; do
    render_n=$((render_n + 1))
    if ! cargo run $cargo_flags $offline --all-features -q -- render \
         --manifest "$manifest" --repo-root . --format "$format" \
         --out "$render_out" --fail-on-diagnostics >/dev/null 2>"$render_out/err.txt"; then
      sed 's/^/    /' "$render_out/err.txt" | head -5
      printf '    ^ %s as %s\n' "$manifest" "$format"
      render_fail=$((render_fail + 1))
    fi
  done
done
# THE NEGATIVE CONTROL, and the first version of it was INERT. It handed the
# renderer a figure with no SVG, which ASSEMBLY refuses ("declares neither
# `svg` nor `src`") -- so the command exited 1 without the emitter ever
# running, and the control passed whether or not `--fail-on-diagnostics` did
# anything. Deleting the flag's refusal in `main.rs` left this whole step
# green; the delete-one-guard pass on 2026-08-21 is what found it.
#
# The control now uses a document that ASSEMBLES CLEANLY and is undrawable
# only to the emitter: a formula outside the LaTeX subset. Assembly does not
# read math, the HTML emitter renders a visible error box and reports one
# diagnostic, and the ONLY thing that can turn that into a nonzero exit is the
# flag under test.
python3 - "$render_out" <<'PY'
import json, sys
d = sys.argv[1]
doc = json.load(open("render/examples-input/facts/facts-pilot.doc.json"))
for b in doc["blocks"]:
    if b["kind"]["type"] == "prose":
        t = b["kind"]["text"]
        b["kind"]["text"] = (t if isinstance(t, str) else t["text"]) + \
            "\n\nA formula outside the subset: $x \\notacommand y$."
        break
else:
    raise SystemExit("the pilot document has no prose block to mutate")
json.dump(doc, open(d + "/undrawable.doc.json", "w"), indent=2)
PY
# Two runs, because the control has to show the flag is what makes the
# difference: WITHOUT the flag the same document must render successfully
# (contract point 2: the emitter reports, it does not refuse), and WITH it the
# build must be refused.
control_ok=1
cargo run $cargo_flags $offline --all-features -q -- render \
  --manifest "$render_out/undrawable.doc.json" --repo-root . --format html \
  --out "$render_out/neg-control" >/dev/null 2>&1 || control_ok=0
if [ "$control_ok" -eq 0 ]; then
  bad "the diagnostics control does not assemble: it is testing assembly, not --fail-on-diagnostics"
elif cargo run $cargo_flags $offline --all-features -q -- render \
     --manifest "$render_out/undrawable.doc.json" --repo-root . --format html \
     --out "$render_out/neg-control" --fail-on-diagnostics >/dev/null 2>&1; then
  bad "a document the emitter cannot draw rendered without failing: --fail-on-diagnostics is inert"
else
  if [ "$render_fail" -eq 0 ] && [ "$render_n" -eq 12 ]; then
    ok "rendered $render_n (manifest, format) pairs with zero emitter diagnostics"
  else
    bad "$render_fail of $render_n renders produced emitter diagnostics or failed"
  fi
fi

step "9/10 self-containment of the emitted HTML (independent grep gate)"
# A SECOND IMPLEMENTATION of the lint that `emit_html.rs` runs in Rust, written
# the way 04-prototype-plan.md specifies it: grep every resource attribute in
# the emitted bytes against an allowlist of `#`, `data:` and `mailto:`. Two
# implementations of one rule is the same discipline the Doc-IR schema gets
# (serde model + Python validator), and it is the only way a bug in the lint
# itself shows up.
python3 - "$render_out" <<'PY' && ok "self-containment (grep gate over the emitted HTML)" || bad "self-containment"
import re, sys, pathlib

ALLOWED = ("#", "data:", "mailto:")
ATTRS = frozenset(
    ("src", "srcset", "href", "action", "poster", "formaction", "data-src", "xlink:href")
)
pages = sorted(pathlib.Path(sys.argv[1]).glob("*.html"))
if not pages:
    print("no HTML pages to check -- refusing to report success", file=sys.stderr)
    raise SystemExit(1)

bad = 0
checked = 0
for page in pages:
    text = page.read_text()
    # Only look inside real tags: escaped prose may legitimately contain the
    # characters of a URL, and only an attribute in a tag can fetch anything.
    for tag in re.findall(r"<[^<>]+>", text):
        external = 'data-external="1"' in tag
        # Attributes are parsed by NAME, not by substring. Round 2 wrote this
        # as `\bhref="` first, which matches the tail of `data-href="` -- the
        # dep-graph's in-page scroll target -- and reported 177 violations that
        # were not violations. DESIGN's Rust lint documents the same trap; a
        # second implementation that repeats the first one's bug is worth
        # nothing, and this one repeated it on the first try.
        for m in re.finditer(r'([-\w:]+)\s*=\s*"([^"]*)"', tag):
            attr, value = m.group(1).lower(), m.group(2).strip()
            if attr not in ATTRS:
                continue
            checked += 1
            if value == "" or value.startswith(ALLOWED):
                continue
            if attr == "href" and external:
                continue
            print(f"{page.name}: {attr}=\"{value[:60]}\" is not self-contained", file=sys.stderr)
            bad += 1
    for m in re.finditer(r"url\(([^)]*)\)", text):
        checked += 1
        v = m.group(1).strip("\"' ")
        if v and not v.startswith("data:"):
            print(f"{page.name}: CSS url({v[:60]}) is not self-contained", file=sys.stderr)
            bad += 1
    for token in ("http://", "https://", "//cdn", "xmlhttprequest", "fetch(", "websocket"):
        for m in re.finditer(re.escape(token), text, re.IGNORECASE):
            # An absolute URL is allowed only as the text of an element marked
            # external, or inside a tag that carries that marker.
            start = text.rfind("<", 0, m.start())
            end = text.find(">", m.start())
            inside_tag = start != -1 and end != -1 and text.find(">", start) >= m.start()
            if inside_tag and 'data-external="1"' not in text[start : end + 1]:
                print(f"{page.name}: `{token}` inside a tag that is not marked external", file=sys.stderr)
                bad += 1
            checked += 1

if checked == 0:
    print("checked zero attributes -- refusing to report success", file=sys.stderr)
    raise SystemExit(1)
print(f"self-containment: {len(pages)} page(s), {checked} resource reference(s), {bad} finding(s)")
raise SystemExit(1 if bad else 0)
PY
# And the gate must be able to fail: inject one violation into a copy.
sed 's|<main|<main data-x="1"><img src="https://evil.example/x.png"|' \
  "$render_out/fact-pilot.html" > "$render_out/violating.html.tmp" 2>/dev/null
mkdir -p "$render_out/neg" && mv "$render_out/violating.html.tmp" "$render_out/neg/violating.html"
if python3 - "$render_out/neg" <<'PY' >/dev/null 2>&1
import re, sys, pathlib
ALLOWED = ("#", "data:", "mailto:")
bad = 0
for page in pathlib.Path(sys.argv[1]).glob("*.html"):
    for tag in re.findall(r"<[^<>]+>", page.read_text()):
        for m in re.finditer(r'([-\w:]+)\s*=\s*"([^"]*)"', tag):
            if m.group(1).lower() == "src" and m.group(2) and not m.group(2).startswith(ALLOWED):
                bad += 1
raise SystemExit(1 if bad else 0)
PY
then
  bad "the self-containment gate accepted a page with an external image: it is inert"
else
  ok "the self-containment gate rejects an external resource (negative control)"
fi
rm -rf "$render_out"

step "10/10 LaTeX compiles standalone (only if a TeX toolchain is here)"
# Reported as SKIPPED, never as a pass. A step that silently counts as green on
# a host that cannot run it is how a gate stops meaning anything -- measured
# 2026-08-16, `lean` and `just` existed on one fleet host of five.
if command -v pdflatex >/dev/null 2>&1; then
  tex_dir="$(mktemp -d)"
  tex_fail=0
  # Both the fixture and the P0-A deliverable. The fixture is small and
  # exercises the macros; the certificate is the document a reader is handed,
  # and it is the one with a 397-row appendix table, so it is the one that
  # finds a LaTeX problem the fixture cannot.
  for pair in "render/tests/fixtures/fixture-doc.json fixture-fact-ledger" \
              "render/examples-input/cert/certificate.doc.json noh-p2-weight-certificate"; do
    set -- $pair
    if cargo run $cargo_flags $offline --all-features -q -- render \
         --manifest "$1" --repo-root . --format tex --out "$tex_dir" >/dev/null 2>&1 \
       && (cd "$tex_dir" && pdflatex -interaction=nonstopmode -halt-on-error \
             "$2-standalone.tex" >"latex-$2.log" 2>&1) \
       && [ -s "$tex_dir/$2-standalone.pdf" ]; then
      printf '      %s -> %s byte PDF\n' "$2" "$(stat -c %s "$tex_dir/$2-standalone.pdf")"
    else
      [ -f "$tex_dir/latex-$2.log" ] && grep -E '^!' "$tex_dir/latex-$2.log" | head -10
      tex_fail=$((tex_fail + 1))
    fi
  done
  if [ "$tex_fail" -eq 0 ]; then
    ok "LaTeX compiles (2 standalone documents)"
  else
    bad "LaTeX does not compile ($tex_fail of 2)"
  fi
  rm -rf "$tex_dir"
else
  printf 'SKIP  LaTeX compile: no pdflatex on this host (this is NOT a pass)\n'
fi

printf '\n=== render/check.sh: %d passed, %d failed\n' "$pass" "$fail"
[ "$fail" -eq 0 ] || exit 1
# The floor rises with the step count: 10 steps, of which step 3 reports four
# results (the count plus three named tests) and steps 5, 8 and 9 report two.
# 14 is the number when every step runs and pdflatex is present; 13 without it.
[ "$pass" -ge 13 ] || { printf 'refusing to report success after only %d checks\n' "$pass"; exit 2; }
exit 0
