#!/usr/bin/env bash
# Run one Python proposer with only a verified catalog and an empty output dir.
set -euo pipefail

cd "$(dirname "$0")/.."

usage() {
  echo "usage: $0 --snapshot PATH --catalog PATH --output-dir DIR --program PATH [--premise-evidence PATH --premise-transition PATH --accepted-transition-event PATH]" >&2
  exit 2
}

snapshot=
catalog=
output_dir=
program=
premise_evidence=
premise_transition=
accepted_transition_event=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --snapshot) snapshot="${2:-}"; shift 2 ;;
    --catalog) catalog="${2:-}"; shift 2 ;;
    --output-dir) output_dir="${2:-}"; shift 2 ;;
    --program) program="${2:-}"; shift 2 ;;
    --premise-evidence) premise_evidence="${2:-}"; shift 2 ;;
    --premise-transition) premise_transition="${2:-}"; shift 2 ;;
    --accepted-transition-event) accepted_transition_event="${2:-}"; shift 2 ;;
    *) usage ;;
  esac
done
[ -n "$snapshot" ] && [ -n "$catalog" ] && [ -n "$output_dir" ] && [ -n "$program" ] || usage
command -v bwrap >/dev/null || {
  echo "AUTOGENESIS_PROPOSER_ERROR|bubblewrap is required; isolation cannot degrade silently" >&2
  exit 1
}
[ -f "$snapshot" ] && [ -f "$catalog" ] && [ -f "$program" ] || {
  echo "AUTOGENESIS_PROPOSER_ERROR|snapshot, catalog, and program must be regular files" >&2
  exit 1
}
[ -d "$output_dir" ] || {
  echo "AUTOGENESIS_PROPOSER_ERROR|output directory does not exist" >&2
  exit 1
}
[ -z "$(find "$output_dir" -mindepth 1 -maxdepth 1 -print -quit)" ] || {
  echo "AUTOGENESIS_PROPOSER_ERROR|output directory must start empty" >&2
  exit 1
}

snapshot=$(realpath "$snapshot")
catalog=$(realpath "$catalog")
output_dir=$(realpath "$output_dir")
program=$(realpath "$program")
runtime=$(mktemp -d /tmp/axeyum-autogenesis-runtime.XXXXXX)
trap 'rm -r "$runtime"' EXIT
install -m 0444 "$catalog" "$runtime/catalog.json"
install -m 0555 "$program" "$runtime/program.py"
catalog="$runtime/catalog.json"
program="$runtime/program.py"
phase=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["phase"])' "$catalog")
catalog_verify=(--snapshot "$snapshot" --phase "$phase" --verify "$catalog")
if [ "$phase" = post_b ]; then
  [ -n "$premise_evidence" ] && [ -n "$premise_transition" ] && [ -n "$accepted_transition_event" ] || {
    echo "AUTOGENESIS_PROPOSER_ERROR|post_b requires the accepted-transition chain" >&2
    exit 1
  }
  catalog_verify+=(
    --premise-evidence "$premise_evidence"
    --premise-transition "$premise_transition"
    --accepted-transition-event "$accepted_transition_event"
  )
elif [ -n "$premise_evidence$premise_transition$accepted_transition_event" ]; then
  echo "AUTOGENESIS_PROPOSER_ERROR|accepted-transition inputs are valid only for post_b" >&2
  exit 1
fi
python3 scripts/create-autogenesis-proposer-catalog.py "${catalog_verify[@]}" >/dev/null
[ -z "$(find "$output_dir" -mindepth 1 -maxdepth 1 -print -quit)" ] || {
  echo "AUTOGENESIS_PROPOSER_ERROR|output directory changed before sandbox launch" >&2
  exit 1
}

mounts=(--ro-bind /usr /usr)
for library in /lib /lib64; do
  [ ! -e "$library" ] || mounts+=(--ro-bind "$library" "$library")
done

bwrap \
  --unshare-all \
  --cap-drop ALL \
  --die-with-parent \
  --new-session \
  --clearenv \
  --setenv PATH /usr/bin \
  --setenv HOME /nonexistent \
  "${mounts[@]}" \
  --dir /input \
  --ro-bind "$catalog" /input/catalog.json \
  --ro-bind "$program" /program.py \
  --bind "$output_dir" /output \
  --tmpfs /tmp \
  --proc /proc \
  --dev /dev \
  --chdir /input \
  /usr/bin/python3 /program.py /input/catalog.json /output

echo "AUTOGENESIS_PROPOSER_OK|phase=$phase|output=$output_dir"
