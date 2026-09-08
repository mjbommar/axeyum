#!/usr/bin/env python3
"""Apply one named mutation to the warm decider in a snapshot, or restore it.

Usage: lia-warm-mutate.py <snapshot-root> <mutation-name|restore|list>

Every mutation below is a plausible way for a warm cache to go stale or to
drift from the cold path. The point of running them is that at least one test
must die for each: a differential nobody has seen fail is not a differential.
"""
import sys
import pathlib

SNAP = pathlib.Path(sys.argv[1])
NAME = sys.argv[2]
WARM = SNAP / "crates/axeyum-solver/src/lra/warm.rs"
BACKUP = SNAP / "crates/axeyum-solver/src/lra/warm.rs.orig"

if not BACKUP.exists():
    BACKUP.write_text(WARM.read_text())

s = BACKUP.read_text()

MUTATIONS = {
    # M1: a retracted literal's columns keep their local mapping, so the next
    # assembly reuses stale column numbers.
    "stale-columns": (
        """        for &global in &self.local_to_global[columns..] {
            self.global_to_local[global] = NO_LOCAL;
        }
        self.local_to_global.truncate(columns);""",
        """        self.local_to_global.truncate(columns);""",
    ),
    # M2: reuse a prefix that is not actually shared -- the classic stale cache.
    "unchecked-prefix": (
        """        let shared = self
            .assembly
            .keys
            .iter()
            .zip(live)
            .take_while(|(a, b)| a == b)
            .count();""",
        """        let shared = self.assembly.keys.len().min(live.len());""",
    ),
    # M3: a retracted literal's constraints stay in the system.
    "stale-constraints": (
        """        self.local_to_global.truncate(columns);
        self.constraints.truncate(constraints);""",
        """        self.local_to_global.truncate(columns);
        let _ = constraints;""",
    ),
    # M4: skip the tightening a cached literal is supposed to carry.
    "no-tightening": (
        """        let mut constraints = std::mem::take(&mut self.collector.constraints);
        tighten_strict_integer_constraints(&mut constraints);""",
        """        let constraints = std::mem::take(&mut self.collector.constraints);""",
    ),
    # M5: allocate local columns in ascending global order instead of touch
    # order -- a sound but DIFFERENTLY-NUMBERED system, the exact drift a
    # verdict-only differential cannot see.
    "sorted-columns": (
        """        for &global in &entry.touched {
            let _ = self.local_of(global);
        }""",
        """        let mut sorted = entry.touched.clone();
        sorted.sort_unstable();
        for &global in &sorted {
            let _ = self.local_of(global);
        }""",
    ),
}

if NAME == "list":
    for key in MUTATIONS:
        print(key)
    sys.exit(0)

if NAME == "restore":
    WARM.write_text(s)
    print("restored")
    sys.exit(0)

old, new = MUTATIONS[NAME]
if s.count(old) != 1:
    print(f"ANCHOR MISS for {NAME}: {s.count(old)} occurrences", file=sys.stderr)
    sys.exit(2)
WARM.write_text(s.replace(old, new))
print(f"applied {NAME}")
