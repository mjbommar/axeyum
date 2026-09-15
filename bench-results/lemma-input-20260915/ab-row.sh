#!/usr/bin/env bash
# LEMMA-INPUT -- one `core<TAB>file<TAB>budget<TAB>ordinal` record, so `xargs
# -I{}` passes the whole record as a single argument.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
bash "$HERE/ab-one.sh" "$1"
