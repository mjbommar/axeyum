#!/usr/bin/env python3
"""LEMMA-INPUT -- patch a SNAPSHOT of THIS lane's commit so BOTH refresh paths
report, and the A/B's mechanism can be read rather than argued.

Attribution binary only (R2).  Every anchor is asserted unique, so a rename in
the tree makes this fail loudly rather than instrument nothing -- an instrument
that silently patches zero sites is the "tools that omit rather than refuse"
shape.

Reports, once a second on stderr:
  calls       entries to the refresh (BOTH paths -- counted before the branch)
  noop_calls  indexed refreshes that returned early on an unchanged atom count
  refresh_ms  wall inside the refresh body
  extract_ms  wall inside bound extraction (full rescan on base, suffix on arm)
  pair_iters  inner-loop iterations of whichever scan ran
  max_atoms / max_bounds   the pass's INPUT high-water marks
"""

import pathlib
import sys

SNAP = pathlib.Path(sys.argv[1])
src = SNAP / "crates/axeyum-solver/src/dpll_lia.rs"
text = src.read_text()

REL = "std::sync::atomic::Ordering::Relaxed"

STATS = '''
// ---- LEMMA-INPUT attribution instrument (snapshot build only) -------------
pub mod li_stats {
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    pub static CALLS: AtomicU64 = AtomicU64::new(0);
    pub static NOOP_CALLS: AtomicU64 = AtomicU64::new(0);
    pub static REFRESH_NS: AtomicU64 = AtomicU64::new(0);
    pub static EXTRACT_NS: AtomicU64 = AtomicU64::new(0);
    pub static PAIR_ITERS: AtomicU64 = AtomicU64::new(0);
    pub static MAX_ATOMS: AtomicU64 = AtomicU64::new(0);
    pub static MAX_BOUNDS: AtomicU64 = AtomicU64::new(0);
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
            "; li-stats calls={} noop_calls={} refresh_ms={} extract_ms={} \\
pair_iters={} max_atoms={} max_bounds={}",
            CALLS.load(Ordering::Relaxed),
            NOOP_CALLS.load(Ordering::Relaxed),
            REFRESH_NS.load(Ordering::Relaxed) / 1_000_000,
            EXTRACT_NS.load(Ordering::Relaxed) / 1_000_000,
            PAIR_ITERS.load(Ordering::Relaxed),
            MAX_ATOMS.load(Ordering::Relaxed),
            MAX_BOUNDS.load(Ordering::Relaxed),
        )
    }

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


def swap(old, new, label):
    global text
    assert text.count(old) == 1, f"anchor not unique ({text.count(old)}): {label}"
    text = text.replace(old, new)


swap(
    'const ATOM_PREFIX: &str = "!arith_atom_";',
    STATS + '\nconst ATOM_PREFIX: &str = "!arith_atom_";',
    "stats module",
)

# 1. Both paths counted, before the branch, and the whole body timed.
swap(
    """    fn refresh_initial_lemmas(&mut self, arena: &mut TermArena) -> Result<(), SolverError> {
        if initial_bound_index_enabled() {
            return self.refresh_initial_lemmas_indexed(arena);
        }""",
    f"""    fn refresh_initial_lemmas(&mut self, arena: &mut TermArena) -> Result<(), SolverError> {{
        li_stats::arm_reporter();
        li_stats::CALLS.fetch_add(1, {REL});
        li_stats::bump_max(&li_stats::MAX_ATOMS, self.ctx.atoms.len() as u64);
        let li_t0 = std::time::Instant::now();
        let li_out = self.refresh_initial_lemmas_inner(arena);
        li_stats::REFRESH_NS.fetch_add(
            u64::try_from(li_t0.elapsed().as_nanos()).unwrap_or(u64::MAX),
            {REL},
        );
        li_out
    }}

    fn refresh_initial_lemmas_inner(&mut self, arena: &mut TermArena) -> Result<(), SolverError> {{
        if initial_bound_index_enabled() {{
            return self.refresh_initial_lemmas_indexed(arena);
        }}""",
    "refresh entry",
)

# 2. The indexed early return -- the (a) half of the change.
swap(
    """        if self.initial_bounds_atoms == Some(self.ctx.atoms.len()) {
            return Ok(());
        }
        let from = self.initial_bounds_atoms.unwrap_or(0);
        for idx in from..self.ctx.atoms.len() {
            let more = simple_int_literal_bounds(arena, idx, &self.ctx.atoms[idx]);
            self.initial_bounds.extend(more);
        }""",
    f"""        if self.initial_bounds_atoms == Some(self.ctx.atoms.len()) {{
            li_stats::NOOP_CALLS.fetch_add(1, {REL});
            return Ok(());
        }}
        let li_e0 = std::time::Instant::now();
        let from = self.initial_bounds_atoms.unwrap_or(0);
        for idx in from..self.ctx.atoms.len() {{
            let more = simple_int_literal_bounds(arena, idx, &self.ctx.atoms[idx]);
            self.initial_bounds.extend(more);
        }}
        li_stats::EXTRACT_NS.fetch_add(
            u64::try_from(li_e0.elapsed().as_nanos()).unwrap_or(u64::MAX),
            {REL},
        );
        li_stats::bump_max(&li_stats::MAX_BOUNDS, self.initial_bounds.len() as u64);""",
    "indexed early return + suffix extraction",
)

# 3. The base full rescan.
swap(
    """    let mut bounds = Vec::new();
    for (idx, atom) in ctx.atoms.iter().enumerate() {
        bounds.extend(simple_int_literal_bounds(arena, idx, atom));
    }
    let conflicts = scan_bound_conflicts(&bounds);""",
    f"""    let li_e0 = std::time::Instant::now();
    let mut bounds = Vec::new();
    for (idx, atom) in ctx.atoms.iter().enumerate() {{
        bounds.extend(simple_int_literal_bounds(arena, idx, atom));
    }}
    li_stats::EXTRACT_NS.fetch_add(
        u64::try_from(li_e0.elapsed().as_nanos()).unwrap_or(u64::MAX),
        {REL},
    );
    li_stats::bump_max(&li_stats::MAX_BOUNDS, bounds.len() as u64);
    let conflicts = scan_bound_conflicts(&bounds);""",
    "base full rescan",
)

# 4. The two scans' inner-loop iteration counts -- the P3 measurement.
swap(
    """    for i in 0..bounds.len() {
        for j in (i + 1)..bounds.len() {
            let Some((lower, upper)) = conflicting_bounds(&bounds[i], &bounds[j]) else {""",
    f"""    for i in 0..bounds.len() {{
        li_stats::PAIR_ITERS.fetch_add(bounds.len().saturating_sub(i + 1) as u64, {REL});
        for j in (i + 1)..bounds.len() {{
            let Some((lower, upper)) = conflicting_bounds(&bounds[i], &bounds[j]) else {{""",
    "base pair loop",
)

swap(
    """        let start = group.partition_point(|&j| j <= i);
        for &j in &group[start..] {""",
    f"""        let start = group.partition_point(|&j| j <= i);
        li_stats::PAIR_ITERS.fetch_add(group[start..].len() as u64, {REL});
        for &j in &group[start..] {{""",
    "indexed pair loop",
)

src.write_text(text)
print("instrumented", src)
