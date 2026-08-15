#!/usr/bin/env bash
# Census a LARGE, UNCHOSEN corpus of official Lean declarations, one export
# stream per declaration, under a per-stream time and memory bound.
#
# Why this exists next to `scripts/lean-import-census.sh`. That script's corpus
# is forty declarations picked by hand to span known reduction behaviours, and
# it now reports 40 of 40 clean — so it has stopped measuring. This one takes
# the corpus from the environment itself: export the whole of `Init`+`Std` once
# with no constant list (`lean4export Init Std`, 96,591 declarations in Lean
# 4.30.0), sample from that name list with a recorded seed, and census each
# sampled declaration's own dependency closure.
#
# Two things this measures that a hand-picked corpus cannot:
#
#   1. A DECLINE DISTRIBUTION over declarations nobody chose, with roots
#      separated from cascades (the census example does that separation).
#   2. A RESOURCE class. A single stream through the trusted gate can also
#      neither admit nor decline: it can diverge. Measured 2026-08-15,
#      `Nat.Linear.Expr.denote_toPoly_go` consumed 25 GB in under four minutes
#      without finishing, and it is the reason the whole-environment stream
#      cannot be censused in one pass. A gate that only counts admit/decline
#      reports that declaration as neither, so it gets its own bucket and its
#      own bound.
#
# Bounds are per-stream and enforced by the OS, not by the kernel under test:
# `timeout` for wall clock, `ulimit -v` for address space. A stream that trips
# either is RESOURCE, never CLEAN.
#
# `lean4export` is NOT vendored. Point AXEYUM_LEAN4EXPORT at a checkout whose
# `.lake/build/bin/lean4export` exists, or let the script find one under
# ~/.cache. With none present it exits 2 rather than reporting an empty census.
#
# Usage:
#   scripts/lean-import-scale-census.sh --names names.tsv --sample 500 --seed 20260815
#   scripts/lean-import-scale-census.sh --list names.txt        # explicit names
#   AXEYUM_SCALE_OUT=dir  AXEYUM_SCALE_JOBS=8  AXEYUM_SCALE_TIMEOUT=60
#   AXEYUM_SCALE_MEM_MB=4096
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2
repo="$PWD"

names_file=""
list_file=""
streams_dir=""
sample=0
seed=20260815
while [ "$#" -gt 0 ]; do
  case "$1" in
    --names) names_file="$2"; shift 2 ;;
    --list) list_file="$2"; shift 2 ;;
    --streams) streams_dir="$2"; shift 2 ;;
    --sample) sample="$2"; shift 2 ;;
    --seed) seed="$2"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

out="${AXEYUM_SCALE_OUT:-$(mktemp -d)}"
mkdir -p "$out/streams" || exit 2
jobs="${AXEYUM_SCALE_JOBS:-8}"
per_timeout="${AXEYUM_SCALE_TIMEOUT:-60}"
mem_mb="${AXEYUM_SCALE_MEM_MB:-4096}"

# --- already-exported streams ----------------------------------------------
# `--streams <dir>` censuses `<dir>/*.ndjson` that some other machine produced.
# Mathlib is the case that needs it: its oleans are 6 GB and live on a different
# host from this checkout, so the export and the census cannot share a process.
# The bounds, the classification and the aggregation are identical either way.
if [ -n "$streams_dir" ]; then
  cargo build --release -q -p axeyum-lean-import --example lean4export_census || exit 2
  bin="$repo/target/release/examples/lean4export_census"
  [ -x "$bin" ] || { echo "census example not built" >&2; exit 2; }
  jobs="${AXEYUM_SCALE_JOBS:-8}"
  mapfile -t pre_streams < <(find "$streams_dir" -name '*.ndjson' | sort)
  total="${#pre_streams[@]}"
  [ "$total" -gt 0 ] || { echo "no streams in $streams_dir" >&2; exit 2; }
  echo "streams=$total jobs=$jobs timeout=${per_timeout}s mem=${mem_mb}MB out=$out"
  cat >"$out/one-stream.sh" <<EOF
#!/usr/bin/env bash
set -uo pipefail
idx="\$1"; stream="\$2"
out="$out"; bin="$bin"
name="\$(basename "\$stream" .ndjson)"
if [ "\$(wc -l <"\$stream")" -lt 2 ]; then
  echo "RESULT|\$idx|\$name|EXPORT-FAILED|0|0|0"; exit 0
fi
report="\$out/streams/\$idx.census"
( ulimit -v \$(( $mem_mb * 1024 )); exec timeout -s KILL $per_timeout "\$bin" "\$stream" ) >"\$report" 2>"\$report.err"
rc=\$?
if [ "\$rc" -ne 0 ]; then echo "RESULT|\$idx|\$name|RESOURCE|\$rc|0|0"; exit 0; fi
if grep -q '|reader-error|' "\$report"; then
  why="\$(sed -n 's/.*|reader-error|//p' "\$report" | head -1 | sed 's/.*: //')"
  echo "RESULT|\$idx|\$name|UNSUPPORTED(\$why)|0|0|0"; exit 0
fi
line="\$(grep '^CENSUS|' "\$report")"
recs="\$(echo "\$line" | sed -n 's/.*decl_records=\([0-9]*\).*/\1/p')"
decl="\$(echo "\$line" | sed -n 's/.*|declines=\([0-9]*\).*/\1/p')"
if [ "\${decl:-1}" -eq 0 ]; then
  echo "RESULT|\$idx|\$name|CLEAN|0|\${recs:-0}|0"
else
  echo "RESULT|\$idx|\$name|DECLINED|0|\${recs:-0}|\$decl"
fi
EOF
  chmod +x "$out/one-stream.sh"
  printf '%s\n' "${pre_streams[@]}" | nl -ba -w1 -s$'\t' \
    | xargs -P "$jobs" -d'\n' -I{} bash -c 'IFS=$'"'"'\t'"'"' read -r i n <<<"$1"; "'"$out"'/one-stream.sh" "$i" "$n"' _ {} \
    >"$out/results.txt"
  python3 - "$out" "$total" <<'PY2'
import collections, pathlib, sys
out = pathlib.Path(sys.argv[1]); total = int(sys.argv[2])
status = collections.Counter(); roots = collections.Counter(); cascades = set()
codes = collections.Counter(); clusters = collections.Counter(); records = 0
for line in (out / "results.txt").read_text().splitlines():
    if not line.startswith("RESULT|"):
        continue
    _, idx, name, st, rc, recs, dec = line.split("|", 6)
    status[st if st != "RESOURCE" else f"RESOURCE(rc={rc})"] += 1
    records += int(recs)
    if st == "DECLINED":
        for row in (out / "streams" / f"{idx}.census").read_text().splitlines():
            row = row.strip()
            if not row.startswith("DECLINE|"):
                continue
            _, _line, decl, code, cluster, kind = row.split("|", 5)
            codes[code] += 1; clusters[cluster] += 1
            if kind == "root":
                roots[decl] += 1
            else:
                cascades.add(decl)
print(f"SCALE-CENSUS|corpus={total}|declaration_records={records}")
for st, n in sorted(status.items()):
    print(f"STATUS|{st}|{n}")
print(f"DISTINCT-ROOT|{len(roots)}|DISTINCT-CASCADE|{len(cascades)}")
for code, n in codes.most_common():
    print(f"CODE|{code}|{n}")
for cluster, n in clusters.most_common():
    print(f"CLUSTER|{cluster}|{n}")
for decl, n in roots.most_common(60):
    print(f"ROOT|{decl}|streams={n}")
PY2
  echo "artifacts: $out"
  exit 0
fi

# --- the corpus ------------------------------------------------------------
corpus="$out/corpus.txt"
if [ -n "$list_file" ]; then
  cp "$list_file" "$corpus" || exit 2
elif [ -n "$names_file" ]; then
  [ "$sample" -gt 0 ] || { echo "--names needs --sample N" >&2; exit 2; }
  # Seeded, reproducible, and NOT filtered by anything that would make the
  # sample easier: every non-internal declaration name in the environment is
  # eligible, including compiler-generated auxiliaries.
  python3 - "$names_file" "$sample" "$seed" >"$corpus" <<'PY' || exit 2
import random, sys
names = [line.split("\t")[-1].strip() for line in open(sys.argv[1]) if line.strip()]
names = sorted(set(names))
rng = random.Random(int(sys.argv[3]))
k = min(int(sys.argv[2]), len(names))
for n in rng.sample(names, k):
    print(n)
PY
else
  echo "need --names <tsv> --sample N, or --list <file>" >&2
  exit 2
fi
total="$(wc -l <"$corpus")"
[ "$total" -gt 0 ] || { echo "empty corpus; refusing to census nothing" >&2; exit 2; }

# --- toolchain discovery (elan does not put lean/lake on PATH) --------------
lake_bin="${AXEYUM_LAKE_BIN:-}"
if [ -z "$lake_bin" ]; then
  if command -v lake >/dev/null 2>&1; then
    lake_bin="$(command -v lake)"
  else
    for candidate in "${ELAN_HOME:-$HOME/.elan}"/toolchains/*/bin/lake; do
      [ -x "$candidate" ] && lake_bin="$candidate" && break
    done
  fi
fi
export_dir="${AXEYUM_LEAN4EXPORT:-}"
if [ -z "$export_dir" ]; then
  for candidate in "$HOME"/.cache/*/lean4export; do
    [ -x "$candidate/.lake/build/bin/lean4export" ] && export_dir="$candidate" && break
  done
fi
if [ -z "$lake_bin" ] || [ -z "$export_dir" ]; then
  echo "CENSUS-UNAVAILABLE lake='${lake_bin:-none}' lean4export='${export_dir:-none}'" >&2
  echo "Set AXEYUM_LAKE_BIN and AXEYUM_LEAN4EXPORT. Refusing to report an empty census." >&2
  exit 2
fi
PATH="$(dirname "$lake_bin"):$PATH"
export PATH

cargo build --release -q -p axeyum-lean-import --example lean4export_census || exit 2
bin="$repo/target/release/examples/lean4export_census"
[ -x "$bin" ] || { echo "census example not built" >&2; exit 2; }

echo "corpus=$total seed=$seed jobs=$jobs timeout=${per_timeout}s mem=${mem_mb}MB out=$out"
echo "lake=$lake_bin lean4export=$export_dir"

# --- one declaration: export, then census under bounds ---------------------
# Streams are named by index, not by declaration: Lean names contain characters
# (and lengths) a filename cannot always carry, and `_private.…` names are
# routine in a whole-environment sample.
cat >"$out/one.sh" <<EOF
#!/usr/bin/env bash
set -uo pipefail
idx="\$1"; name="\$2"
out="$out"; export_dir="$export_dir"; lake_bin="$lake_bin"; bin="$bin"
stream="\$out/streams/\$idx.ndjson"
err="\$out/streams/\$idx.err"
(cd "\$export_dir" && "\$lake_bin" env ./.lake/build/bin/lean4export Init Std -- "\$name" >"\$stream" 2>"\$err")
# \`lean4export\` EXITS 0 on an unknown constant: it panics to stderr and writes a
# metadata-only stream, which then scores as a CLEAN import. Both signals are
# checked, exactly as scripts/lean-import-census.sh does.
if grep -q "^PANIC" "\$err" 2>/dev/null || [ "\$(wc -l <"\$stream")" -lt 2 ]; then
  echo "RESULT|\$idx|\$name|EXPORT-FAILED|0|0|0"
  rm -f "\$stream"
  exit 0
fi
report="\$out/streams/\$idx.census"
( ulimit -v \$(( $mem_mb * 1024 )); exec timeout -s KILL $per_timeout "\$bin" "\$stream" ) >"\$report" 2>"\$report.err"
rc=\$?
if [ "\$rc" -ne 0 ]; then
  # 137 = SIGKILL from \`timeout\`; anything else here is the address-space cap
  # or an abort. Either way the trusted gate neither admitted nor declined.
  echo "RESULT|\$idx|\$name|RESOURCE|\$rc|0|0"
  rm -f "\$stream"
  exit 0
fi
# A stream the READER refused never reaches the kernel gate, so it has zero
# declaration records and zero declines — which would score as CLEAN on the
# counts alone. census_ndjson is fail-closed on malformed or unsupported
# bytes by design (only a kernel decline is recoverable), so this is a third
# outcome and needs its own bucket, carrying the construct that stopped it.
if grep -q '|reader-error|' "\$report"; then
  why="\$(sed -n 's/.*|reader-error|//p' "\$report" | head -1 | sed 's/.*: //')"
  echo "RESULT|\$idx|\$name|UNSUPPORTED(\$why)|0|0|0"
  rm -f "\$stream"
  exit 0
fi
line="\$(grep '^CENSUS|' "\$report")"
recs="\$(echo "\$line" | sed -n 's/.*decl_records=\([0-9]*\).*/\1/p')"
decl="\$(echo "\$line" | sed -n 's/.*|declines=\([0-9]*\).*/\1/p')"
if [ "\${decl:-1}" -eq 0 ]; then
  echo "RESULT|\$idx|\$name|CLEAN|0|\${recs:-0}|0"
else
  echo "RESULT|\$idx|\$name|DECLINED|0|\${recs:-0}|\$decl"
fi
# The stream is large and reproducible from the name; the census report is not.
rm -f "\$stream"
EOF
chmod +x "$out/one.sh"

nl -ba -w1 -s$'\t' "$corpus" \
  | xargs -P "$jobs" -d'\n' -I{} bash -c 'IFS=$'"'"'\t'"'"' read -r i n <<<"$1"; "'"$out"'/one.sh" "$i" "$n"' _ {} \
  >"$out/results.txt"

# --- aggregate -------------------------------------------------------------
python3 - "$out" "$total" <<'PY'
import collections, pathlib, sys
out = pathlib.Path(sys.argv[1]); total = int(sys.argv[2])
status = collections.Counter()
roots, cascades = collections.Counter(), set()
codes, clusters = collections.Counter(), collections.Counter()
records = 0
for line in (out / "results.txt").read_text().splitlines():
    if not line.startswith("RESULT|"):
        continue
    _, idx, name, st, rc, recs, dec = line.split("|", 6)
    status[st if st != "RESOURCE" else f"RESOURCE(rc={rc})"] += 1
    records += int(recs)
    if st == "DECLINED":
        report = out / "streams" / f"{idx}.census"
        for row in report.read_text().splitlines():
            row = row.strip()
            if not row.startswith("DECLINE|"):
                continue
            _, _line, decl, code, cluster, kind = row.split("|", 5)
            codes[code] += 1
            clusters[cluster] += 1
            (roots.__setitem__(decl, roots[decl] + 1) if kind == "root"
             else cascades.add(decl))
print(f"SCALE-CENSUS|corpus={total}|declaration_records={records}")
for st, n in sorted(status.items()):
    print(f"STATUS|{st}|{n}")
print(f"DISTINCT-ROOT|{len(roots)}|DISTINCT-CASCADE|{len(cascades)}")
for code, n in codes.most_common():
    print(f"CODE|{code}|{n}")
for cluster, n in clusters.most_common():
    print(f"CLUSTER|{cluster}|{n}")
for decl, n in roots.most_common(60):
    print(f"ROOT|{decl}|streams={n}")
PY
echo "artifacts: $out"
