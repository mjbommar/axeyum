#!/usr/bin/env python3
"""Fourth part of the LRA-MODEL-REPLAY census instrument (snapshot only).

Patch 3 established that the reconstruction declines with the deadline ALREADY
PAST. That gives a hypothesis with a large consequence -- "the witness was
already sitting in the tableau and we threw it away on the clock" -- and a
hypothesis is not a finding. `Incremental::point` (`simplex.rs:2287`) takes
`&self` and only materializes; it does no solving. `LraTheory::model`
(`lra_online.rs:2439`) nevertheless re-runs `Incremental::check` first, and
`Tableau::run` polls the deadline at pivot 0 (`simplex.rs:1441`), so an expired
clock returns `Unknown` before a single pivot.

But `model` calls `sync` BEFORE that check, and if `sync` moved bounds the
tableau's stored assignment need not satisfy the live system any more. So the
hypothesis is only true if BOTH hold at the decline: `sync` moved nothing, and
the materialized point actually satisfies every live constraint.

This patch measures exactly those two things at the `simplex-declined` arm.
It asserts nothing and changes no verdict -- it prints and returns `None` as
before.

Usage: census-patch4.py <snapshot-root>
"""

import sys
import pathlib

root = pathlib.Path(sys.argv[1])
online = root / "crates/axeyum-solver/src/lra_online.rs"

ANCHOR = """            if !engine.sync(&self.live) {
                model_probe("sync-failed");
                model_decline_census("sync-failed", self.deadline);
                return None;
            }
            match engine.inner.check(self.deadline) {"""

REPL = """            let sync_before = (engine.sync_retractions, engine.sync_assertions);
            if !engine.sync(&self.live) {
                model_probe("sync-failed");
                model_decline_census("sync-failed", self.deadline);
                return None;
            }
            let sync_moved = (
                engine.sync_retractions - sync_before.0,
                engine.sync_assertions - sync_before.1,
            );
            match engine.inner.check(self.deadline) {"""

ANCHOR2 = """                simplex::Status::Unknown => {
                    model_probe("simplex-declined");
                    model_decline_census("simplex-declined", self.deadline);
                    return None;
                }"""

REPL2 = """                simplex::Status::Unknown => {
                    model_probe("simplex-declined");
                    model_decline_census("simplex-declined", self.deadline);
                    // CENSUS: was the witness already there? Report whether
                    // `sync` moved anything and whether the tableau's stored
                    // point satisfies every live constraint AS IT STANDS.
                    census_stranded_witness(&engine, &self.live, sync_moved);
                    return None;
                }"""

HELPER = '''/// CENSUS DIAGNOSTIC (lane LRA-MODEL-REPLAY, snapshot only). At a
/// `simplex-declined` reconstruction, says whether the point the tableau
/// already holds is a witness for the live system. Read-only; changes nothing.
fn census_stranded_witness(engine: &SimplexEngine, live: &[Constraint], sync_moved: (u64, u64)) {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if !*ON.get_or_init(|| {
        std::env::var("AXEYUM_LRA_REPLAY_CENSUS").is_ok_and(|v| v.trim() == "1")
    }) {
        return;
    }
    let Some(point) = engine.inner.point() else {
        eprintln!(
            "; LRACENSUS stranded sync_retracted={} sync_asserted={} point=none live={}",
            sync_moved.0,
            sync_moved.1,
            live.len()
        );
        return;
    };
    let mut ok = 0usize;
    let mut bad = 0usize;
    let mut unreadable = 0usize;
    for c in live {
        let mut acc = c.expr.constant;
        let mut broke = false;
        for (&j, coeff) in &c.expr.coeffs {
            let Some(v) = point.get(j) else {
                broke = true;
                break;
            };
            let Some(term) = coeff.checked_mul(*v) else {
                broke = true;
                break;
            };
            let Some(next) = acc.checked_add(term) else {
                broke = true;
                break;
            };
            acc = next;
        }
        if broke {
            unreadable += 1;
        } else if (c.strict && acc < Rational::zero()) || (!c.strict && acc <= Rational::zero()) {
            ok += 1;
        } else {
            bad += 1;
        }
    }
    eprintln!(
        "; LRACENSUS stranded sync_retracted={} sync_asserted={} point=some live={} \\
sat={ok} violated={bad} unreadable={unreadable}",
        sync_moved.0,
        sync_moved.1,
        live.len()
    );
}

'''

ANCHOR_FN = "pub(crate) fn model_decline_census(site: &str, deadline: Option<Instant>) {"

text = online.read_text()
if "fn census_stranded_witness" in text:
    raise SystemExit("ABORT: patch 4 already applied")
for a, r, name in ((ANCHOR, REPL, "sync counters"), (ANCHOR2, REPL2, "declined arm")):
    n = text.count(a)
    if n != 1:
        raise SystemExit(f"ABORT: anchor '{name}' occurs {n} times (want 1)")
    text = text.replace(a, r)
n = text.count(ANCHOR_FN)
if n != 1:
    raise SystemExit(f"ABORT: helper anchor occurs {n} times (want 1)")
text = text.replace(ANCHOR_FN, HELPER + ANCHOR_FN)
online.write_text(text)
print("patched the stranded-witness measurement")
