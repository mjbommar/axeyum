#!/usr/bin/env bash
# Where the flywheel stands, in one screen, from artifacts that already exist.
#
# CLAUDE.md describes a cycle — library → solver → reconstruction →
# kernel-checked theorem → ledger → DAG picks the next goal — and every arrow is
# already measured by something committed. What was missing was anywhere to see
# them together.
#
# Measured 2026-08-17: `docs/plan/generated/` holds 25 generated views, 840 KB,
# and **24 of them are referenced from no entry point at all** — not CLAUDE.md,
# not PLAN.md, not the justfile, not check.sh. `scripts/fact-frontier.py`, which
# answers "what should I prove next", was referenced by nothing either; one lane
# hand-wrote its query three times in a day without knowing it existed.
#
# So this is deliberately NOT new analysis. It runs the queue and reads the
# committed generated files, and its whole job is to make what already exists
# reachable. Anything expensive stays where it is, behind its own gate.
#
# Usage:  scripts/flywheel-status.sh      (or: just flywheel)
#
# It does not fail on a bad state — it is a view, not a gate. The gates are
# `just check`; this tells you where to point them.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

section() { printf '\n\033[1m== %s ==\033[0m\n' "$1"; }

section "LEDGER — what is settled, and what the DAG can hand out"
python3 - <<'PY'
import json, pathlib, collections
facts = {}
for p in pathlib.Path("artifacts/facts").glob("*.json"):
    d = json.loads(p.read_text(encoding="utf-8"))
    facts[d["id"]] = d
settled = {i for i, d in facts.items() if d["epistemic_status"] in ("proved", "computed")}
route = collections.Counter(d.get("proof_route", "-") for i, d in facts.items() if i in settled)
# Report the STATUSES, not settled-and-the-rest. Subtracting lumps `refuted`
# and `conjectured` in with `open`, which made this line disagree with the queue
# below it (13 vs 10 banded) and sent me looking for facts the queue had missed.
# It had missed none: it bands open + conjectured, and rightly leaves `refuted`
# out. A summary that does not reconcile with the thing under it is worse than
# no summary.
status = collections.Counter(d["epistemic_status"] for d in facts.values())
print(f"  {len(facts)} facts · " + " · ".join(f"{v} {k}" for k, v in sorted(status.items())))
print("  settled by route: " + ", ".join(f"{k} {v}" for k, v in route.most_common()))
PY
python3 scripts/check-fact-dag.py --quiet 2>/dev/null | tail -1 | sed 's/^/  /'

section "TRUSTED BASE — the headline metric, and it was not in this view"
# CLAUDE.md: "The metric is the trusted base, not the output volume. Assumptions
# remaining per prelude, and results the system established with nobody writing
# the proof. A referee checks both in one command." This view showed the second
# and not the first, so the one command did not exist.
#
# Read from the COMMITTED ledger, which derives every number from two kernel
# measurements rather than authoring them (the previous revision hard-coded the
# counts and kept publishing a trusted base 33 rows too large after the Int
# development was proved down). The authority is
# `python3 scripts/gen-lean-axiom-ledger.py --check`, which rebuilds the
# isolated preludes; this is its pinned output.
if [ -f docs/plan/generated/lean-axiom-ledger.md ]; then
  # FIRST table only. The ledger has two whose header starts `| Prelude `, and
  # a `sed` range prints both -- the second is 77 rows of per-axiom SHA-256,
  # which buries the six-line summary this section exists to show.
  awk '/^\| Prelude \| Axiom \|/{p=1} p{print} p&&/^$/{exit}' \
    docs/plan/generated/lean-axiom-ledger.md | sed 's/^/  /'
  grep -E '^- \*\*[0-9]+ total assumptions|^- \*\*[0-9]+ assumptions have been retired' \
    docs/plan/generated/lean-axiom-ledger.md | sed 's/^/  /'
  echo "  authority: python3 scripts/gen-lean-axiom-ledger.py --check   (rebuilds the preludes)"
  # The constructed carriers ARE in the table above as of 2026-08-18: the
  # ledger's coverage command now passes `--include-constructed`, and
  # `EXPECTED_PRELUDES` lists `creal`/`complex` so dropping that flag is a gate
  # failure rather than a quieter ledger. Before that they were absent, and
  # grepping the inventory for them returned an empty answer to a question it
  # was never asked -- which is how one brief concluded ℝ-as-constructed was
  # axiom-free from evidence that did not exist.
  echo "  every row above is pinned BY VALUE; a moved number fails --check with"
  echo "  its direction (a rise is a regression, a fall is a result to publish)."
else
  echo "  (docs/plan/generated/lean-axiom-ledger.md absent — run scripts/gen-lean-axiom-ledger.py)"
fi

section "PRODUCTION — how much library exists, and how much of it assumes nothing"
# The other half of the headline metric. CLAUDE.md asks for "assumptions
# remaining per prelude, and results the system established" -- this view showed
# assumptions and, until 2026-08-22, had no cross-prelude theorem count to show
# beside them because none existed. Pinned output; authority is the generator.
if [ -f docs/plan/generated/theorem-production-ledger.md ]; then
  awk '/^\| Prelude \| Theorems/{p=1} p{print} p&&/^$/{exit}' \
    docs/plan/generated/theorem-production-ledger.md | sed 's/^/  /'
  grep -E '^- \*\*[0-9]+ distinct theorems' \
    docs/plan/generated/theorem-production-ledger.md | sed 's/^/  /'
  # ADR-1511: this file's own `--check` needs a release kernel build (~40s
  # warm, ~3min cold) so it cannot run here on every view -- print the date
  # this artifact was last regenerated instead, so a reader can see
  # staleness rather than trusting a number that may be days old. The
  # ledger went stale for five days (1,448 -> 2,340 distinct theorems, an
  # undercount of about a third) with no signal in this view that it had.
  ledger_date=$(git log -1 --format=%cd --date=short \
    -- docs/plan/generated/theorem-production-ledger.md 2>/dev/null)
  echo "  as of: ${ledger_date:-unknown} (git log date of this committed file)"
  echo "  DO NOT SUM the cumulative column; 'Originated here' is the partition."
  echo "  authority: python3 scripts/gen-theorem-production-ledger.py --check"
  echo "  counts theorems, NOT autonomous ones -- the split is below."
fi

section "AUTONOMY — how much of it the system produced with nobody writing the proof"
# The metric CLAUDE.md actually names, and the one the theorem count above does
# NOT answer. Derived from applicability.fact_ids, never self-reported.
if [ -f docs/plan/generated/production-provenance-ledger.md ]; then
  awk '/^\| Established facts/{p=1} p{print} p&&/^$/{exit}' \
    docs/plan/generated/production-provenance-ledger.md | sed 's/^/  /'
  echo "  authority: python3 scripts/gen-production-provenance-ledger.py --check"
else
  echo "  (docs/plan/generated/theorem-production-ledger.md absent — run scripts/gen-theorem-production-ledger.py)"
fi

section "NEXT — what to work on (just next, or --unlocks for the full queue)"
python3 scripts/fact-frontier.py 2>/dev/null | sed 's/^/  /'

section "PROOF GAP — decided, certified, independently checked, Lean-reconstructed"
if [ -f docs/plan/generated/proof-gap-matrix.md ]; then
  sed -n '/^| Stage /,/^$/p' docs/plan/generated/proof-gap-matrix.md | sed 's/^/  /'
  echo "  full: docs/plan/generated/proof-gap-matrix.md (regenerate: scripts/gen-proof-gap-matrix.py)"
else
  echo "  (docs/plan/generated/proof-gap-matrix.md absent — run scripts/gen-proof-gap-matrix.py)"
fi

section "TRANSCRIPTION — does a rendered module say anything about its query?"
# Read from the COMMITTED manifests, not by re-running: the gate takes ~35s and
# this view must stay instant. `scripts/check-lra-hypothesis-binding.py` is the
# authority; these files are its pinned output.
#
# Lean accepting a module proves `False` follows from the axioms the module
# DECLARES. It says nothing about whether those axioms are the `.smt2` file's
# `(assert ...)` lines. That is the link the residual-trust audit ranks as
# WEAKER THAN THE KERNEL, and these verdicts are what measure it.
for spec in "structural-instances:structural:equated terms are subterms of the query" \
            "structural-anchored-instances:structural-anchored:both of the two below" \
            "anchored-instances:anchored:the query FORCES the assumed disequality" \
            "attestations:attested:transcribes NOTHING — the honest other half"; do
  stem="${spec%%:*}"; rest="${spec#*:}"; label="${rest%%:*}"; gloss="${rest#*:}"
  file="scripts/hypothesis-binding-$stem.txt"
  n=$(grep -cvE '^[[:space:]]*#|^[[:space:]]*$' "$file" 2>/dev/null || echo '?')
  printf '  %-20s %6s  %s\n' "$label" "$n" "$gloss"
done
printf '  %-20s %6s  %s\n' "bound" "(gate)" "every hypothesis binds back to an (assert ...) line"
echo "  authority: python3 scripts/check-lra-hypothesis-binding.py  (~35s)"

section "CERTIFICATE GAP — logics we decide but no external checker reads"
python3 scripts/check-capability-assurance.py --rank --quiet 2>/dev/null \
  | grep -v '^CAPABILITY_ASSURANCE|' | sed 's/^/  /'

section "LEAN — how much of what Lean reads is REASONING, not attestation"
echo "  A structural attestation is an axiom pair Lean cannot fail on the merits."
echo "  Floors live in scripts/check-lean-gate.sh; the split is printed by"
echo "  lean_crosscheck_content_split_is_visible_and_ratcheted."
grep -oE 'THEORY_FAMILY_FLOOR="\$\{AXEYUM_LEAN_THEORY_FLOOR:-[0-9]+\}"' scripts/check-lean-gate.sh 2>/dev/null \
  | sed 's/^/  /' || true

section "WHERE TO GO DEEPER — generated views, none of which used to be linked"
ls docs/plan/generated/*.md 2>/dev/null | sed 's|^|  |' | head -30
echo
echo "  Gates:  just check   ·   scripts/check.sh (no-just fallback, NOT the same set)"
echo "  Queue:  just next    ·   just next-unlocks"
