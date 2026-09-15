#!/usr/bin/env bash
# Round-robin a list into 6 shards, so every shard sees a comparable mix of
# hardness (a contiguous split would put whole benchmark families on one core).
# Usage: shard.sh <src-list> <prefix>   ->  <prefix>0.txt .. <prefix>5.txt
set -eu
SRC="$1"; PRE="$2"
for i in 0 1 2 3 4 5; do : > "$PRE$i.txt"; done
n=0
while read -r f; do
  [ -z "$f" ] && continue
  echo "$f" >> "$PRE$((n % 6)).txt"
  n=$((n + 1))
done < "$SRC"
echo "sharded $n files"
wc -l "$PRE"*.txt
