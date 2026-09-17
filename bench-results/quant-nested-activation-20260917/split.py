#!/usr/bin/env python3
"""A13-QUANT (ADR-2149): the per-core split of `inactive_dropped`
(`rej_nocontext`) into crossed-binder / negative / untracked, plus the lazy
discovery driver's counters, read from the `AXEYUM_QPROBE` stderr captures
`census-run.sh` produced.

    split.py <census-dir> [<census-dir> ...] > split.tsv

Each <census-dir> is one arm (`run-summary.tsv` + `raw/*.err`). One row per
(core, arm). Every column is a SUM over the loop exits the core printed — the
per-universal table is printed once per loop invocation at its exit, and the
counters carry across discovery rebuilds inside an invocation (both are this
lane's instrument fixes), so the sum over exits is the whole run's count. A
core that never printed a table (`invocations=0`) is reported with zeros AND
`invocations=0`, never silently as zeros: on the previous instrument that was
35 of 53 cores (ADR-2120 s7a), and "no row" and "row of zeros" are different
findings.

The regex is compiled with re.M and anchored per LINE. QUANT-REACH-DIFF's
classifier had a `$` anchor without re.M and matched only when the target line
was the LAST line of the capture; the unit check at the bottom of this file
(`--self-test`) has a fixture with trailing content after the target line and
fails without re.M.
"""
import os
import re
import sys

UNIVERSAL_RE = re.compile(
    r"^QPROBE\s+universal\[(?P<index>\d+)\] .*?joined=(?P<joined>\d+) .*?"
    r"rej_handoff=(?P<handoff>\d+) rej_poscap=(?P<poscap>\d+) "
    r"rej_nocontext=(?P<nocontext>\d+) .*?exit=(?P<exit>\S+) kind=(?P<kind>\S+) "
    r"rej_nocontext_crossed=(?P<crossed>\d+) rej_nocontext_negative=(?P<negative>\d+) "
    r"rej_nocontext_untracked=(?P<untracked>\d+)\s*$",
    re.M,
)
DISCOVERY_RE = re.compile(
    r"^QPROBE nested-discovery exit=(?P<exit>\S+) registered=(?P<registered>\d+) "
    r"uncompiled=(?P<uncompiled>\d+) rebuilds=(?P<rebuilds>\d+) positive=(?P<positive>\d+) "
    r"staged=(?P<staged>\d+) promoted=(?P<promoted>\d+) rejected=(?P<rejected>\d+) "
    r"rejected_checker=(?P<rejected_checker>\d+)(?: outside_scope=(?P<outside_scope>\d+) unscanned=(?P<unscanned>\d+))?\s*$",
    re.M,
)
DISCOVERY_NONE_RE = re.compile(r"^QPROBE nested-discovery exit=\S+ none\s*$", re.M)

# The caps in qinst_egraph.rs at faa6cac11; a census that reads a cap being
# hit has to name the constant, so they are pinned here and checked by
# --self-test against the source when it is reachable.
MAX_DISCOVERED_REGISTRATIONS = 256
MAX_DISCOVERY_REBUILDS = 8
MAX_POSITIVE_INSTANCES = 4096

COLUMNS = [
    "core", "arm", "verdict", "decided_by", "elapsed_ms", "invocations",
    "regs_context", "regs_crossed", "regs_negative", "regs_untracked", "regs_asserted",
    "joined_inactive", "handoff", "poscap",
    "nocontext", "nocontext_crossed", "nocontext_negative", "nocontext_untracked",
    "disc_registered", "disc_uncompiled", "disc_rebuilds", "disc_positive", "disc_staged",
    "disc_promoted", "disc_rejected", "disc_rejected_checker", "disc_outside_scope",
    "disc_unscanned",
    "cap_registrations_hit", "cap_rebuilds_hit", "cap_positive_hit",
]


def parse_err(text):
    """One arm's stderr capture -> dict of summed counters."""
    row = {c: 0 for c in COLUMNS if c not in ("core", "arm", "verdict", "decided_by", "elapsed_ms")}
    row["cap_registrations_hit"] = 0
    row["cap_rebuilds_hit"] = 0
    row["cap_positive_hit"] = 0
    exits_seen = 0
    for m in UNIVERSAL_RE.finditer(text):
        kind = m.group("kind")
        if kind == "asserted":
            row["regs_asserted"] += 1
            continue
        key = {
            "context": "regs_context",
            "crossed-binder": "regs_crossed",
            "negative": "regs_negative",
            "untracked": "regs_untracked",
        }[kind]
        row[key] += 1
        row["joined_inactive"] += int(m.group("joined"))
        row["handoff"] += int(m.group("handoff"))
        row["poscap"] += int(m.group("poscap"))
        row["nocontext"] += int(m.group("nocontext"))
        row["nocontext_crossed"] += int(m.group("crossed"))
        row["nocontext_negative"] += int(m.group("negative"))
        row["nocontext_untracked"] += int(m.group("untracked"))
    for m in DISCOVERY_RE.finditer(text):
        exits_seen += 1
        registered = int(m.group("registered"))
        rebuilds = int(m.group("rebuilds"))
        positive = int(m.group("positive"))
        row["disc_registered"] += registered
        row["disc_uncompiled"] += int(m.group("uncompiled"))
        row["disc_rebuilds"] += rebuilds
        row["disc_positive"] += positive
        row["disc_staged"] += int(m.group("staged"))
        row["disc_promoted"] += int(m.group("promoted"))
        row["disc_rejected"] += int(m.group("rejected"))
        row["disc_rejected_checker"] += int(m.group("rejected_checker"))
        row["disc_outside_scope"] += int(m.group("outside_scope") or 0)
        row["disc_unscanned"] += int(m.group("unscanned") or 0)
        if registered >= MAX_DISCOVERED_REGISTRATIONS:
            row["cap_registrations_hit"] += 1
        if rebuilds >= MAX_DISCOVERY_REBUILDS:
            row["cap_rebuilds_hit"] += 1
        if positive >= MAX_POSITIVE_INSTANCES:
            row["cap_positive_hit"] += 1
    exits_seen += len(DISCOVERY_NONE_RE.findall(text))
    row["invocations"] = exits_seen
    return row


def read_summary(path):
    rows = {}
    with open(path, encoding="utf-8") as f:
        header = f.readline().rstrip("\n").split("\t")
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) != len(header):
                continue
            d = dict(zip(header, parts))
            rows[d["core"]] = d
    return rows


def main(argv):
    if argv[1:] == ["--self-test"]:
        return self_test()
    out = [COLUMNS]
    for census_dir in argv[1:]:
        summary = read_summary(os.path.join(census_dir, "run-summary.tsv"))
        for core in sorted(summary):
            s = summary[core]
            err_path = os.path.join(census_dir, "raw", core + ".err")
            text = ""
            if os.path.exists(err_path):
                with open(err_path, encoding="utf-8", errors="replace") as f:
                    text = f.read()
            row = parse_err(text)
            row["core"] = core
            row["arm"] = s["arm"]
            row["verdict"] = s["verdict"]
            row["decided_by"] = s["decided_by"]
            row["elapsed_ms"] = s["elapsed_ms"]
            out.append([str(row[c]) for c in COLUMNS])
    for line in out:
        print("\t".join(line))
    return 0


def self_test():
    fixture = (
        "QPROBE loop-exit kind=CLOCK exit=GrowthHeadroom rounds=4 ground=2180\n"
        "QPROBE   universal[0] vars=3 patterns=1 joined=10 starved_joins=0 admitted=0 "
        "rej_handoff=7 rej_poscap=0 rej_nocontext=0 rej_expired=0 rej_subst=0 rej_true=0 "
        "rej_unreleased=0 rej_flood=0 rej_ceiling=0 rej_check=0 rej_seen=0 rej_dupother=0 "
        "rej_true_newterm=0 census_admitted=0 exit=CLOCK kind=context rej_nocontext_crossed=0 "
        "rej_nocontext_negative=0 rej_nocontext_untracked=0\n"
        "QPROBE   universal[1] vars=2 patterns=1 joined=9 starved_joins=0 admitted=0 "
        "rej_handoff=0 rej_poscap=0 rej_nocontext=9 rej_expired=0 rej_subst=0 rej_true=0 "
        "rej_unreleased=0 rej_flood=0 rej_ceiling=0 rej_check=0 rej_seen=0 rej_dupother=0 "
        "rej_true_newterm=0 census_admitted=0 exit=CLOCK kind=crossed-binder rej_nocontext_crossed=9 "
        "rej_nocontext_negative=0 rej_nocontext_untracked=0\n"
        "QPROBE   universal[2] vars=1 patterns=1 joined=0 starved_joins=0 admitted=3 "
        "rej_handoff=0 rej_poscap=0 rej_nocontext=0 rej_expired=0 rej_subst=0 rej_true=0 "
        "rej_unreleased=0 rej_flood=0 rej_ceiling=0 rej_check=0 rej_seen=0 rej_dupother=0 "
        "rej_true_newterm=0 census_admitted=3 exit=CLOCK kind=asserted rej_nocontext_crossed=0 "
        "rej_nocontext_negative=0 rej_nocontext_untracked=0\n"
        "QPROBE nested-discovery exit=CLOCK registered=256 uncompiled=3 rebuilds=8 "
        "positive=567 staged=329 promoted=0 rejected=55 rejected_checker=55\n"
        "trailing content so the target lines are NOT the last line of the capture\n"
        "QPROBE nested-discovery exit=fixpoint none\n"
    )
    row = parse_err(fixture)
    expect = {
        "regs_context": 1, "regs_crossed": 1, "regs_asserted": 1, "regs_negative": 0,
        "joined_inactive": 19, "handoff": 7, "nocontext": 9, "nocontext_crossed": 9,
        "disc_registered": 256, "disc_uncompiled": 3, "disc_rebuilds": 8,
        "cap_registrations_hit": 1, "cap_rebuilds_hit": 1, "cap_positive_hit": 0,
        "invocations": 2,
    }
    bad = {k: (row[k], v) for k, v in expect.items() if row[k] != v}
    if bad:
        print("SELF-TEST FAIL", bad)
        return 1
    # The pinned caps against the source, when it is reachable from here.
    src = os.path.join(os.path.dirname(__file__), "..", "..", "crates", "axeyum-solver", "src", "qinst_egraph.rs")
    if os.path.exists(src):
        text = open(src, encoding="utf-8").read()
        for name, value in (
            ("MAX_DISCOVERED_REGISTRATIONS", MAX_DISCOVERED_REGISTRATIONS),
            ("MAX_DISCOVERY_REBUILDS", MAX_DISCOVERY_REBUILDS),
            ("MAX_POSITIVE_INSTANCES", MAX_POSITIVE_INSTANCES),
        ):
            m = re.search(r"^const " + name + r": usize = (\d+);", text, re.M)
            if not m or int(m.group(1)) != value:
                print(f"SELF-TEST FAIL: {name} pinned {value}, source says {m.group(1) if m else 'absent'}")
                return 1
    print("SELF-TEST PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
