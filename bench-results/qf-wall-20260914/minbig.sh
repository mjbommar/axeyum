#!/usr/bin/env bash
set -u
W="$(cd "$(dirname "$0")" && pwd)"
for id in f06 f09 f13 f07 f10; do
  echo "--- $id start $(date -Is)"
  timeout 5400 python3 "$W/minimize.py" "$W/skel/$id.smt2" "$W/core/$id.core.smt2" --tlimit 60 2>&1 | tail -2
  echo "--- $id rc=$? $(date -Is)"
done
echo ALLDONE
