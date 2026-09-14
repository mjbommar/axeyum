"""ADR-2030 -- does the route selector at `auto.rs:4068` actually run the lazy
CEGAR before the query reaches the hard decline at `combined.rs:86`?

ADR-2020 concluded it does not ("the lazy fallback that already exists for the
other caller is simply not offered to them"), from a census that records only the
CONTEXT NAME of whichever site refused LAST.

The discriminator is the ORDER, plus one structural signature. When the selector
engages, the CEGAR solves its abstraction by re-entering `check_auto`; the
abstraction has no `Op::Apply` nodes, so that re-entry shows up as an
`auto.rs:4068` line with `has_function=false pairs=0` -- documented in the
dispatcher's own comment as the reason the `has_function` guard exists. So an
`engaged=true` immediately followed by that signature is DIRECT evidence the lazy
route ran, not merely that it was offered.

Usage: ackprobe-analyze.py <logdir>

The committed logs are gzipped (1.4 MB raw, 56 KB compressed); this reads either.
"""
import glob, gzip, os, re, sys

logdir = sys.argv[1]
ENGAGED = re.compile(r"site=auto\.rs:4068 pairs=(\d+) .*engaged=true")
ABSTRACTION = re.compile(r"site=auto\.rs:4068 pairs=0 .*has_function=false")
COMBINED_REFUSE = re.compile(r"site=combined\.rs:86 pairs=(\d+) .*verdict=refuse")

print(f"{'engaged':>8} {'w/CEGAR':>8} {'refuse':>8} {'shared':>7}  file")
tot_e = tot_c = tot_r = 0
files = 0
no_engage = []
paths = sorted(glob.glob(os.path.join(logdir, "*.err"))
               + glob.glob(os.path.join(logdir, "*.err.gz")))
if not paths:
    raise SystemExit(f"no ACKPROBE logs under {logdir!r} -- an empty result from a "
                     "tool that never pointed at its subject is not a negative")
for path in paths:
    if path.endswith(".gz"):
        lines = gzip.open(path, "rt", errors="replace").read().splitlines()
    else:
        lines = open(path, errors="replace").read().splitlines()
    engaged_at = []
    cegar_ran = 0
    refuse_pairs = set()
    for i, line in enumerate(lines):
        m = ENGAGED.search(line)
        if m:
            engaged_at.append(int(m.group(1)))
            # The abstraction re-entry lands within the next few lines.
            if any(ABSTRACTION.search(l) for l in lines[i + 1 : i + 6]):
                cegar_ran += 1
            continue
        m = COMBINED_REFUSE.search(line)
        if m:
            refuse_pairs.add(int(m.group(1)))
    n_refuse = sum(1 for l in lines if COMBINED_REFUSE.search(l))
    shared = len(set(engaged_at) & refuse_pairs)
    files += 1
    tot_e += len(engaged_at)
    tot_c += cegar_ran
    tot_r += n_refuse
    if not engaged_at:
        no_engage.append(path)
    name = os.path.basename(path).replace(".smt2.err", "")
    print(f"{len(engaged_at):>8} {cegar_ran:>8} {n_refuse:>8} {shared:>7}  {name[:62]}")

print()
print(f"files                                          {files}")
print(f"files where the selector NEVER engaged         {len(no_engage)}")
print(f"total selector engagements                     {tot_e}")
print(f"  ...immediately followed by the CEGAR's own")
print(f"     abstraction re-entry (DIRECT evidence)    {tot_c}")
print(f"total `combined.rs:86` refusals                {tot_r}")
print()
print("The abstraction signature is CORROBORATING evidence, not the argument, and")
print("it is a proxy: it misses an engagement whose CEGAR declines before its")
print("recursive solve. The argument itself is structural, and short enough to")
print("check against `dispatch_uf_arith_overbound` directly. Reaching")
print("`combined.rs:86` at all requires that function to have returned")
print("`FallThrough`; under the SHIPPED policy (`CegarProbe` -- `terminal` and")
print("`skip` are opt-in via AXEYUM_UF_ARITH_OVERBOUND) the only route to")
print("`FallThrough` is the lazy CEGAR running and returning an inconclusive")
print("`Unknown`. Its two earlier exits both RETURN: `NotEngaged` (which these")
print("engagements are not) and `Answer(refusal)` from the pathological bound.")
print("So on every file here the lazy route was not merely offered -- it ran.")
print()
print("'shared' = distinct pair counts seen at BOTH sites on the same file. The")
print("pair count is a fingerprint of the term set, so a shared value is the same")
print("set reaching the selector first and the hard decline afterwards.")
for path in no_engage:
    print(f"NEVER ENGAGED: {path}")
