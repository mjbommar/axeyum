#!/usr/bin/env bash
# Fetch public benchmark corpora into corpus/public/.
# Sources verified 2026-06-10; all are Zenodo, plain HTTPS, CC-BY 4.0.
# Downloads are large — pass one or more targets explicitly:
#
#   scripts/fetch-corpus.sh qf_abv      #  ~140 MB  SMT-LIB QF_ABV (start here)
#   scripts/fetch-corpus.sh qf_bv       #  ~1.7 GB  SMT-LIB QF_BV
#   scripts/fetch-corpus.sh hwmcc       #  ~1.2 GB  HWMCC'24 BTOR2 (bv + array)
#   scripts/fetch-corpus.sh sat2024     #  ~4.3 GB  SAT Competition 2024 main track
#   scripts/fetch-corpus.sh all
#
# Decompressors needed: zstd (SMT-LIB), unzip (SAT), gzip (HWMCC).
set -euo pipefail

self="$(readlink -f "$0")"
dest="$(dirname "$self")/../corpus/public"
mkdir -p "$dest"
cd "$dest"

fetch() { # url filename [md5]
  local url="$1" file="$2" md5="${3:-}"
  if [ -e "$file" ] || [ -e "${file%.tar.*}" ] || [ -e "${file%.zip}" ]; then
    echo "skip $file (exists)"
    return
  fi
  echo "fetch $file"
  curl -L -C - -o "$file" "$url"
  if [ -n "$md5" ]; then
    echo "$md5  $file" | md5sum -c -
  fi
}

want() { # target
  [ "$#" -gt 0 ] || return 1
  for t in "${targets[@]}"; do
    [ "$t" = "$1" ] || [ "$t" = "all" ] && return 0
  done
  return 1
}

if [ "$#" -eq 0 ]; then
  sed -n '2,12p' "$self"
  exit 1
fi
targets=("$@")

# SMT-LIB release 2024 non-incremental (zenodo record 11061097)
if want qf_abv; then
  fetch "https://zenodo.org/records/11061097/files/QF_ABV.tar.zst?download=1" \
    QF_ABV.tar.zst
  tar --zstd -xf QF_ABV.tar.zst
fi
if want qf_bv; then
  fetch "https://zenodo.org/records/11061097/files/QF_BV.tar.zst?download=1" \
    QF_BV.tar.zst
  tar --zstd -xf QF_BV.tar.zst
fi

# HWMCC'24 word-level BTOR2 (zenodo record 13958851)
if want hwmcc; then
  fetch "https://zenodo.org/records/13958851/files/benchmarks_btor2_bv.tar.gz?download=1" \
    benchmarks_btor2_bv.tar.gz 36c274ed7657680c639ab7107803f3fb
  fetch "https://zenodo.org/records/13958851/files/benchmarks_btor2_array.tar.gz?download=1" \
    benchmarks_btor2_array.tar.gz 221b982042d5fb6a226cdc600cd3f809
  tar -xzf benchmarks_btor2_bv.tar.gz
  tar -xzf benchmarks_btor2_array.tar.gz
fi

# SAT Competition 2024 main track, 400 CNF (zenodo record 15095752)
if want sat2024; then
  fetch "https://zenodo.org/records/15095752/files/sat-competition-2024-main-benchmarks.zip?download=1" \
    sat-competition-2024-main-benchmarks.zip 4873f72ffb3a5ae89b39ea08be30a7df
  unzip -q -n sat-competition-2024-main-benchmarks.zip
fi

echo "done; corpus/public contents:"
du -sh -- */ 2>/dev/null || true
