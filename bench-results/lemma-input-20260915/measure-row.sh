#!/usr/bin/env bash
# LEMMA-INPUT -- one `core<TAB>file<TAB>budget` record, so `xargs -I{}` can pass
# the whole record as a single argument and the file name may contain anything
# but a tab.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
IFS=$'\t' read -r core file budget <<< "$1"
bash "$HERE/measure-one.sh" "$file" "$budget" "$core"
