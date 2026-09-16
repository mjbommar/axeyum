#!/usr/bin/env python3
"""Third part of the LRA-MODEL-REPLAY census instrument (snapshot only).

The smoke test on `_standard_init5_ground.i_3_2_2.bpl_7.smt2` -- the very file
LRA-ATOM-SCREEN confirmed its lever on -- came back
`LRAMODELPROBE site=simplex-declined`, i.e. the model was never reconstructed
because `Incremental::check` answered `Status::Unknown`. That status covers
FOUR different events (`simplex.rs:1441` deadline, `:1453` memory watchdog,
`:1465` MAX_PIVOTS, `:2180` overflow-poisoned), and the four demand completely
different work. Without separating them, "arithmetic outside the incremental
engine" could be anything from a missing disequality split to a plain timeout.

So: on every `None` arm of `LraTheory::model`, say whether the deadline had
already passed and whether the memory watchdog had tripped, next to the site.

Usage: census-patch3.py <snapshot-root>
"""

import sys
import pathlib

root = pathlib.Path(sys.argv[1])
online = root / "crates/axeyum-solver/src/lra_online.rs"

ANCHOR_FN = '''pub(crate) fn model_probe(site: &str) {'''
if not ANCHOR_FN:
    raise SystemExit("bad anchor")

HELPER = '''/// CENSUS DIAGNOSTIC (lane LRA-MODEL-REPLAY, snapshot only).
/// `Status::Unknown` from the simplex covers four different events and
/// `model_probe` names none of them. This says which pressure was on at the
/// moment the reconstruction declined.
pub(crate) fn model_decline_census(site: &str, deadline: Option<Instant>) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*ON.get_or_init(|| {
        std::env::var("AXEYUM_LRA_REPLAY_CENSUS").is_ok_and(|v| v.trim() == "1")
    }) {
        return;
    }
    let past = deadline.is_some_and(|d| Instant::now() >= d);
    let watchdog = crate::memory_budget::watchdog_tripped();
    eprintln!(
        "; LRACENSUS model_decline site={site} deadline_passed={past} watchdog={watchdog}"
    );
}

'''

SITES = [
    ('                model_probe("sync-failed");',
     '                model_probe("sync-failed");\n'
     '                model_decline_census("sync-failed", self.deadline);'),
    ('                        model_probe("feasible-but-witness-out-of-i128");',
     '                        model_probe("feasible-but-witness-out-of-i128");\n'
     '                        model_decline_census("feasible-but-witness-out-of-i128", self.deadline);'),
    ('                    model_probe("live-system-infeasible");',
     '                    model_probe("live-system-infeasible");\n'
     '                    model_decline_census("live-system-infeasible", self.deadline);'),
    ('                    model_probe("simplex-declined");',
     '                    model_probe("simplex-declined");\n'
     '                    model_decline_census("simplex-declined", self.deadline);'),
    ('                model_probe("fm-fallback-declined");',
     '                model_probe("fm-fallback-declined");\n'
     '                model_decline_census("fm-fallback-declined", self.deadline);'),
]

text = online.read_text()
if "fn model_decline_census" in text:
    raise SystemExit("ABORT: patch 3 already applied")
n = text.count(ANCHOR_FN)
if n != 1:
    raise SystemExit(f"ABORT: model_probe anchor occurs {n} times (want 1)")
text = text.replace(ANCHOR_FN, HELPER + ANCHOR_FN)

for anchor, repl in SITES:
    c = text.count(anchor)
    if c != 1:
        raise SystemExit(f"ABORT: site anchor occurs {c} times (want 1): {anchor.strip()}")
    text = text.replace(anchor, repl)

online.write_text(text)
print(f"patched {len(SITES)} model-decline sites + the helper")
