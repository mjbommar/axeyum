#!/usr/bin/env python3
"""Apply one of the two S1b mutations to a copy of the AFTER tree on s5.

usage: mutate.py <nomin|noheap> <tree-root>

Each mutation removes exactly one of the two things this slice added, so the
measurement that follows can fail. Both edits assert their anchor occurs
exactly once, so a silent no-op mutation (which would print "the guard is
load-bearing" while changing nothing) is impossible.
"""

import sys

which, root = sys.argv[1], sys.argv[2]
path = f"{root}/crates/axeyum-solver/src/cdclt.rs"
src = open(path).read()

if which == "nomin":
    anchor = "                if !all_theory {\n                    self.minimize(&mut learned, &mut seen);\n                }\n"
    assert src.count(anchor) == 1, f"anchor count {src.count(anchor)}"
    src = src.replace(
        anchor,
        "                if false && !all_theory {\n"
        "                    self.minimize(&mut learned, &mut seen);\n"
        "                }\n"
        "                let _ = &seen;\n",
    )
elif which == "noheap":
    anchor = """    fn pick_unassigned(&mut self) -> Option<usize> {
        while !self.heap.is_empty() {
            let var = self.heap_remove_max();
            if self.active[var] && self.value[var].is_none() {
                return Some(var);
            }
        }
        None
    }"""
    assert src.count(anchor) == 1, f"anchor count {src.count(anchor)}"
    src = src.replace(
        anchor,
        """    fn pick_unassigned(&mut self) -> Option<usize> {
        let mut best = None;
        for var in 0..self.var_count {
            if !self.active[var] || self.value[var].is_some() {
                continue;
            }
            match best {
                None => best = Some(var),
                Some(current) if self.activity[var] > self.activity[current] => {
                    best = Some(var);
                }
                Some(_) => {}
            }
        }
        best
    }""",
    )
else:
    raise SystemExit(f"unknown mutation {which}")

open(path, "w").write(src)
print(f"mutated {which} in {path}")
