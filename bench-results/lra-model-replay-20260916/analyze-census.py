#!/usr/bin/env python3
"""Parse the LRA-MODEL-REPLAY census sweep into the per-file table and the
histogram.

Input:  <capture-dir> <arm> <ledger.tsv> <outdir>
Output: <outdir>/per-file.tsv, <outdir>/histogram.tsv, summary on stdout.

Three sources are read per file, all from the SAME capture:

  * `; LRACENSUS ...`      -- this lane's instrument (see census-patch*.py).
  * `; LRAMODELPROBE ...`  -- the pre-existing five-way reconstruction probe.
  * `; theory-layer ...` / `; route ...` / `; lazy-smt ... online_probe=`
    -- the shipped route trace, which is in every `--trace` capture already
    and says where the budget went.

A file may run the online route more than once, so each yields one or more
census BLOCKS. We report the block count, the arm of the LAST block, and the
failing-assertion labels summed over every block.

WHY THE TABLE IS KEYED ON THE FAILING ASSERTION. `replays`
(`lra_online.rs:5728`) evaluates the ORIGINAL assertion, so an atom the theory
dropped costs nothing when the skeleton satisfies its assertion anyway. Only a
failing assertion is a lost verdict.
"""

import collections
import pathlib
import re
import sys

capdir, arm, ledger_path, outdir = sys.argv[1:5]
capdir = pathlib.Path(capdir)
outdir = pathlib.Path(outdir)
outdir.mkdir(parents=True, exist_ok=True)

P = r"; (?:partial )?"
RE_ARM = re.compile(
    P + r"LRACENSUS arm=(\S+) atoms=(\d+) order=(\d+) equality=(\d+) "
    r"unsupported=(\d+) eq_asserted_false=(\d+)"
)
RE_UNSUP = re.compile(P + r"LRACENSUS unsupported_kind (\d+) (.+)")
RE_ASSERT = re.compile(
    P + r"LRACENSUS assertions total=(\d+) sat=(\d+) false=(\d+) eval_err=(\d+)"
)
RE_FAIL = re.compile(P + r"LRACENSUS failassert (\d+) (.+)")
RE_OFF = re.compile(P + r"LRACENSUS offender (\d+) (.+)")
RE_DECL = re.compile(
    P + r"LRACENSUS model_decline site=(\S+) deadline_passed=(\S+) watchdog=(\S+)"
)
RE_PROBE = re.compile(P + r"LRAMODELPROBE site=(\S+)")
RE_ONLINE_PROBE = re.compile(r"online_probe=(\S+)")
RE_TL = re.compile(r"; (?:partial )?theory-layer (.*)")
RE_ROUTE = re.compile(r"; (?:partial )?route decided_by=(\S+) bound_by=(\S+)")
RE_CFG = re.compile(r"; (?:partial )?config digest=\S+ .*?consulted=\d+ (.*)")

TL_KEYS = [
    "theory_propagate_ms",
    "theory_final_check_ms",
    "theory_assert_ms",
    "decisions",
    "final_checks",
    "simplex_checks",
    "simplex_rows",
    "bound_scan_atoms",
]

ledger = {}
with open(ledger_path) as fh:
    head = fh.readline().rstrip("\n").split("\t")
    for line in fh:
        row = dict(zip(head, line.rstrip("\n").split("\t")))
        ledger[row["file"]] = row

rows = []
for rel, lrow in sorted(ledger.items()):
    slug = rel.replace("/", "_")
    err = capdir / f"{arm}.{slug}.err"
    out = capdir / f"{arm}.{slug}.out"
    blocks = 0
    last_arm = ""
    atoms = order = equality = unsup = eqfalse = 0
    fails = collections.Counter()
    unsup_kinds = collections.Counter()
    probes = collections.Counter()
    declines = collections.Counter()
    ass_total = ass_false = ass_err = 0

    if err.exists():
        for line in err.read_text(errors="replace").splitlines():
            m = RE_ARM.search(line)
            if m:
                blocks += 1
                last_arm = m.group(1)
                atoms, order, equality, unsup, eqfalse = (int(m.group(i)) for i in range(2, 7))
                continue
            m = RE_UNSUP.search(line)
            if m:
                unsup_kinds[m.group(2)] += int(m.group(1))
                continue
            m = RE_ASSERT.search(line)
            if m:
                ass_total = int(m.group(1))
                ass_false += int(m.group(3))
                ass_err += int(m.group(4))
                continue
            m = RE_FAIL.search(line)
            if m:
                fails[m.group(2)] += int(m.group(1))
                continue
            m = RE_DECL.search(line)
            if m:
                declines[f"{m.group(1)}|deadline={m.group(2)}|wd={m.group(3)}"] += 1
                continue
            m = RE_PROBE.search(line)
            if m:
                probes[m.group(1)] += 1

    tl = {}
    online_probe = ""
    decided_by = ""
    cfg_crossed = ""
    for src in (out, err):
        if not src.exists():
            continue
        text = src.read_text(errors="replace")
        m = RE_TL.search(text)
        if m:
            for kv in m.group(1).split():
                if "=" in kv:
                    k, v = kv.split("=", 1)
                    if k in TL_KEYS:
                        tl[k] = v
        m = RE_ONLINE_PROBE.search(text)
        if m:
            online_probe = m.group(1)
        m = RE_ROUTE.search(text)
        if m:
            decided_by = m.group(1)
        m = RE_CFG.search(text)
        if m:
            cfg_crossed = ",".join(
                x.rsplit("::", 1)[-1] for x in m.group(1).split()
            )

    dominant_fail = max(sorted(fails.items()), key=lambda kv: kv[1])[0] if fails else ""
    # `status|construct+construct` -> just the construct half.
    construct = dominant_fail.split("|", 1)[1] if "|" in dominant_fail else ""
    dominant_decline = (
        max(sorted(declines.items()), key=lambda kv: kv[1])[0] if declines else ""
    )

    r = dict(
        file=rel,
        verdict=lrow["verdict"],
        exit=lrow["exit"],
        ms=lrow["ms"],
        online_probe=online_probe,
        decided_by=decided_by,
        census_blocks=blocks,
        last_arm=last_arm,
        atoms=atoms,
        order=order,
        equality=equality,
        unsupported=unsup,
        eq_asserted_false=eqfalse,
        assertions=ass_total,
        assert_false=ass_false,
        assert_eval_err=ass_err,
        dominant_fail_label=dominant_fail,
        construct=construct,
        unsupported_kinds=";".join(f"{k}={v}" for k, v in sorted(unsup_kinds.items())),
        model_decline=dominant_decline,
        config_crossed=cfg_crossed,
        probe_sites=";".join(f"{k}={v}" for k, v in sorted(probes.items())),
    )
    for k in TL_KEYS:
        r[k] = tl.get(k, "")
    rows.append(r)

cols = list(rows[0].keys()) if rows else []
with open(outdir / "per-file.tsv", "w") as fh:
    fh.write("\t".join(cols) + "\n")
    for r in rows:
        fh.write("\t".join(str(r[c]) for c in cols) + "\n")

# TARGET POPULATION: reached the online engine, produced a Boolean model, and
# the query still came back `model-did-not-replay`.
target = [r for r in rows if r["last_arm"] in ("no-replay", "no-model")]


def label(r):
    if r["last_arm"] == "no-model":
        site = r["model_decline"].split("|")[0] if r["model_decline"] else "?"
        dl = "deadline" in r["model_decline"] and "deadline=true" in r["model_decline"]
        return f"NO-MODEL:{site}" + (":clock-gone" if dl else ":clock-left")
    return r["construct"] or "no-replay:(no-offending-atom)"


hist = collections.Counter(label(r) for r in target)
with open(outdir / "histogram.tsv", "w") as fh:
    fh.write("bucket\tfiles\n")
    for k, v in sorted(hist.items(), key=lambda kv: (-kv[1], kv[0])):
        fh.write(f"{k}\t{v}\n")

print(f"files in ledger:                          {len(rows)}")
print(f"files with any census block:              {sum(1 for r in rows if r['census_blocks'])}")
print(f"online_probe=model-did-not-replay:        "
      f"{sum(1 for r in rows if r['online_probe'] == 'model-did-not-replay')}")
print(f"last_arm=no-replay:                       {sum(1 for r in rows if r['last_arm'] == 'no-replay')}")
print(f"last_arm=no-model:                        {sum(1 for r in rows if r['last_arm'] == 'no-model')}")
print(f"last_arm=replayed:                        {sum(1 for r in rows if r['last_arm'] == 'replayed')}")
print(f"TARGET population (no-replay + no-model): {len(target)}")
print()
print("HISTOGRAM over the target population:")
for k, v in sorted(hist.items(), key=lambda kv: (-kv[1], kv[0])):
    print(f"  {v:4d}  {k}")
print()
print("Model-decline discriminator (no-model files only):")
for k, v in sorted(collections.Counter(
    r["model_decline"] for r in target if r["last_arm"] == "no-model"
).items(), key=lambda kv: -kv[1]):
    print(f"  {v:4d}  {k or '(none recorded)'}")
print()
print("Verdicts over the whole sweep:")
for k, v in sorted(collections.Counter(r["verdict"] for r in rows).items()):
    print(f"  {v:4d}  {k}")
print()
print("Exit statuses:")
for k, v in sorted(collections.Counter(r["exit"] for r in rows).items()):
    print(f"  {v:4d}  exit={k}")
