#!/usr/bin/env python3
"""LEMMA-INPUT -- patch a SNAPSHOT tree with the attribution instrument.

This is applied to a `scripts/lane-snapshot.sh` tree only, never to the lane's
worktree, and the binary it produces is an ATTRIBUTION BINARY ONLY (R2): no
verdict, no A/B wall time and no decision in this lane comes from it.

What it records, globally (atomics, so the main thread can read them while the
worker is still inside the pass) and reports once a second on stderr as
`; li-stats ...`, because the rows under study are killed by the watchdog and a
report printed at return would never print at all:

  calls        entries to `refresh_initial_lemmas`
  mutex_ms     wall inside `initial_int_bound_mutex_lemmas`
  impl_ms      wall inside `initial_int_bound_implication_lemmas`
  extract_ms   wall inside the per-atom `simple_int_literal_bounds` scan of the
               mutex pass -- the LINEAR half
  pair_iters   (i,j) iterations of the mutex pair loop -- the QUADRATIC half
  pair_expr_ok pairs that survived the `a.expr == b.expr && a.side != b.side`
               test, i.e. the ones the loop is actually for
  max_atoms    max `ctx.atoms.len()` the pass ever read   <- THE INPUT
  max_bounds   max `bounds.len()` the pass ever built     <- THE INPUT
  cap_hits     calls where MAX_INITIAL_BOUND_MUTEX_LEMMAS truncated
"""

import pathlib
import sys

SNAP = pathlib.Path(sys.argv[1])
src = SNAP / "crates/axeyum-solver/src/dpll_lia.rs"
text = src.read_text()

STATS = '''
// ---- LEMMA-INPUT attribution instrument (snapshot build only) -------------
pub mod li_stats {
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    pub static CALLS: AtomicU64 = AtomicU64::new(0);
    pub static MUTEX_NS: AtomicU64 = AtomicU64::new(0);
    pub static IMPL_NS: AtomicU64 = AtomicU64::new(0);
    pub static EXTRACT_NS: AtomicU64 = AtomicU64::new(0);
    pub static PAIR_ITERS: AtomicU64 = AtomicU64::new(0);
    pub static PAIR_EXPR_OK: AtomicU64 = AtomicU64::new(0);
    pub static MAX_ATOMS: AtomicU64 = AtomicU64::new(0);
    pub static MAX_BOUNDS: AtomicU64 = AtomicU64::new(0);
    pub static CAP_HITS: AtomicU64 = AtomicU64::new(0);
    static STARTED: AtomicBool = AtomicBool::new(false);

    pub fn bump_max(cell: &AtomicU64, v: u64) {
        let mut cur = cell.load(Ordering::Relaxed);
        while v > cur {
            match cell.compare_exchange_weak(cur, v, Ordering::Relaxed, Ordering::Relaxed) {
                Ok(_) => return,
                Err(seen) => cur = seen,
            }
        }
    }

    pub fn line() -> String {
        format!(
            "; li-stats calls={} mutex_ms={} impl_ms={} extract_ms={} pair_iters={} \\
pair_expr_ok={} max_atoms={} max_bounds={} cap_hits={}",
            CALLS.load(Ordering::Relaxed),
            MUTEX_NS.load(Ordering::Relaxed) / 1_000_000,
            IMPL_NS.load(Ordering::Relaxed) / 1_000_000,
            EXTRACT_NS.load(Ordering::Relaxed) / 1_000_000,
            PAIR_ITERS.load(Ordering::Relaxed),
            PAIR_EXPR_OK.load(Ordering::Relaxed),
            MAX_ATOMS.load(Ordering::Relaxed),
            MAX_BOUNDS.load(Ordering::Relaxed),
            CAP_HITS.load(Ordering::Relaxed),
        )
    }

    /// One reporter thread, started on the first entry to the pass. The rows
    /// under study never RETURN, so a report emitted at return is a report that
    /// never exists; this one is at most one second stale.
    pub fn arm_reporter() {
        if STARTED.swap(true, Ordering::SeqCst) {
            return;
        }
        std::thread::spawn(|| {
            loop {
                std::thread::sleep(std::time::Duration::from_millis(1000));
                eprintln!("{}", line());
            }
        });
    }
}
// ---- end LEMMA-INPUT instrument -------------------------------------------
'''

anchor = "const ATOM_PREFIX: &str = \"!arith_atom_\";"
assert text.count(anchor) == 1, "ATOM_PREFIX anchor not unique"
text = text.replace(anchor, STATS + "\n" + anchor)

# --- refresh_initial_lemmas: call count + reporter arm ----------------------
old = """    fn refresh_initial_lemmas(&mut self, arena: &mut TermArena) -> Result<(), SolverError> {
        let mut initial_lemmas = initial_int_bound_mutex_lemmas(arena, &self.ctx)?;
        initial_lemmas.extend(initial_int_bound_implication_lemmas(arena, &self.ctx)?);"""
new = """    fn refresh_initial_lemmas(&mut self, arena: &mut TermArena) -> Result<(), SolverError> {
        li_stats::arm_reporter();
        li_stats::CALLS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let li_t0 = std::time::Instant::now();
        let mut initial_lemmas = initial_int_bound_mutex_lemmas(arena, &self.ctx)?;
        li_stats::MUTEX_NS.fetch_add(
            u64::try_from(li_t0.elapsed().as_nanos()).unwrap_or(u64::MAX),
            std::sync::atomic::Ordering::Relaxed,
        );
        let li_t1 = std::time::Instant::now();
        initial_lemmas.extend(initial_int_bound_implication_lemmas(arena, &self.ctx)?);
        li_stats::IMPL_NS.fetch_add(
            u64::try_from(li_t1.elapsed().as_nanos()).unwrap_or(u64::MAX),
            std::sync::atomic::Ordering::Relaxed,
        );"""
assert text.count(old) == 1, "refresh_initial_lemmas anchor not unique"
text = text.replace(old, new)

# --- the mutex pass: input sizes, extraction time, pair-loop iterations ------
old = """    let mut bounds = Vec::new();
    for (idx, atom) in ctx.atoms.iter().enumerate() {
        bounds.extend(simple_int_literal_bounds(arena, idx, atom));
    }

    let mut conflicts = Vec::new();
    let mut seen = HashSet::new();
    for i in 0..bounds.len() {
        for j in (i + 1)..bounds.len() {
            let Some((lower, upper)) = conflicting_bounds(&bounds[i], &bounds[j]) else {
                continue;
            };"""
new = """    let li_e0 = std::time::Instant::now();
    let mut bounds = Vec::new();
    for (idx, atom) in ctx.atoms.iter().enumerate() {
        bounds.extend(simple_int_literal_bounds(arena, idx, atom));
    }
    li_stats::EXTRACT_NS.fetch_add(
        u64::try_from(li_e0.elapsed().as_nanos()).unwrap_or(u64::MAX),
        std::sync::atomic::Ordering::Relaxed,
    );
    li_stats::bump_max(&li_stats::MAX_ATOMS, ctx.atoms.len() as u64);
    li_stats::bump_max(&li_stats::MAX_BOUNDS, bounds.len() as u64);

    let mut conflicts = Vec::new();
    let mut seen = HashSet::new();
    for i in 0..bounds.len() {
        li_stats::PAIR_ITERS.fetch_add(
            (bounds.len().saturating_sub(i + 1)) as u64,
            std::sync::atomic::Ordering::Relaxed,
        );
        for j in (i + 1)..bounds.len() {
            let Some((lower, upper)) = conflicting_bounds(&bounds[i], &bounds[j]) else {
                continue;
            };
            li_stats::PAIR_EXPR_OK.fetch_add(1, std::sync::atomic::Ordering::Relaxed);"""
assert text.count(old) == 1, "mutex pair-loop anchor not unique"
text = text.replace(old, new)

old = """        if conflicts.len() >= MAX_INITIAL_BOUND_MUTEX_LEMMAS {
            break;
        }
    }

    let mut out = Vec::with_capacity(conflicts.len());
    for (lower, upper) in conflicts {
        let mut truths = vec![false; ctx.atoms.len()];
        truths[lower.atom_idx] = lower.truth;"""
new = """        if conflicts.len() >= MAX_INITIAL_BOUND_MUTEX_LEMMAS {
            li_stats::CAP_HITS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            break;
        }
    }

    let mut out = Vec::with_capacity(conflicts.len());
    for (lower, upper) in conflicts {
        let mut truths = vec![false; ctx.atoms.len()];
        truths[lower.atom_idx] = lower.truth;"""
assert text.count(old) == 1, "cap-hit anchor not unique"
text = text.replace(old, new)

src.write_text(text)
print("instrumented", src)
