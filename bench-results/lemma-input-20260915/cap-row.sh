#!/usr/bin/env bash
# LEMMA-INPUT -- one `core<TAB>file<TAB>budget<TAB>ordinal` record for cap-arm.sh.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
bash "$HERE/cap-arm.sh" "$1"
