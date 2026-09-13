#!/usr/bin/env python3
"""Apply the ADR-1946 SIZING CENSUS block to `datatype_native.rs`.

This is a MEASUREMENT patch and is deliberately not committed to the shipped
source: it would be dead code in every build, and its output is a
classification the refusal messages already carry one at a time.

What it measures, and why it is not the ADR-1942 census re-read
----------------------------------------------------------------
`collect_ackermann_groups` returns at the FIRST datatype-sorted argument it
cannot handle, so the refusal string a blocker census reads cannot say how many
files a fix would reach.  ADR-1942's census fixed that for the ARGUMENT axis by
classifying every datatype-sorted argument of every COLLECTED application.

This lane's change also widens WHICH applications are collected -- a UF whose
RESULT sort is a datatype becomes a site even when none of its arguments is
datatype-sorted -- so the ADR-1942 rows cannot price it: they never saw those
applications, and therefore never saw the congruence pairs they add.  This block
recomputes the collection under the WIDENED rule and classifies that.

Emitted once per entry into the datatype route, as a single line:

    DTRES-CENSUS narrow_sites=.. wide_sites=.. narrow_pairs=.. wide_pairs=..
                 dtres_funcs=.. dtres_inexact=.. dtres_nondt=..
                 sym_exact=.. sym_inexact=.. ctor_exact=.. ctor_inexact=..
                 apply_exact=.. apply_inexact=.. other=.. other_kinds=..
                 ELIGIBLE_A=.. ELIGIBLE_C=..

`ELIGIBLE_A` is the arm as it stands (ADR-1942): every datatype-sorted argument
a variable or a constructor over an exact datatype, no function's result sort
mentioning a datatype, narrow pair count within bound.  `ELIGIBLE_C` is this
lane's proposal: `Op::Apply` arguments admitted too, and a `Sort::Datatype`
result admitted when its expansion is exact -- with the pair count taken over
the WIDENED site set, which is the term this census exists to add.

Usage (from the worktree root):  python3 <this file> [--revert]
"""

import sys

PATH = "crates/axeyum-solver/src/datatype_native.rs"
ANCHOR = "    let mut pairs = 0usize;\n"
BEGIN = "    // ---- ADR-1946 SIZING CENSUS (lane dt-valued-result, NOT COMMITTED) ----\n"
END = "    // ---- end ADR-1946 SIZING CENSUS ----\n"

BLOCK = BEGIN + r'''    if std::env::var_os("AXEYUM_DTRES_CENSUS").is_some() {
        // Recollect under the WIDENED rule: an application is a site when it has
        // a datatype-sorted ARGUMENT *or* a datatype-sorted RESULT.
        let mut wide: BTreeMap<axeyum_ir::FuncId, Vec<TermId>> = BTreeMap::new();
        let mut seen_w = BTreeSet::new();
        let mut stack_w: Vec<TermId> = assertions.to_vec();
        while let Some(term) = stack_w.pop() {
            if !seen_w.insert(term) {
                continue;
            }
            let TermNode::App { op, args } = arena.node(term) else {
                continue;
            };
            let op = *op;
            let args = args.clone();
            if let Op::Apply(func) = op {
                let (_, _, result) = arena.function(func);
                if args.iter().any(|&a| is_datatype_sorted(arena, a))
                    || matches!(result, Sort::Datatype(_))
                {
                    wide.entry(func).or_default().push(term);
                }
            }
            stack_w.extend(args);
        }
        let mut wide_sites = 0usize;
        let mut wide_pairs = 0usize;
        for sites in wide.values_mut() {
            sites.sort_unstable();
            wide_sites += sites.len();
            wide_pairs =
                wide_pairs.saturating_add(sites.len().saturating_mul(sites.len() - 1) / 2);
        }
        let mut narrow_sites = 0usize;
        let mut narrow_pairs = 0usize;
        for sites in groups.values() {
            narrow_sites += sites.len();
            narrow_pairs =
                narrow_pairs.saturating_add(sites.len().saturating_mul(sites.len() - 1) / 2);
        }

        // Result sorts, over the WIDENED function set.
        let mut dtres_funcs = 0usize;
        let mut dtres_inexact = 0usize;
        let mut dtres_nondt = 0usize;
        for &func in wide.keys() {
            let (_, _, result) = arena.function(func);
            match result {
                Sort::Datatype(d) => {
                    dtres_funcs += 1;
                    if !datatype_expansion_is_exact(arena, d) {
                        dtres_inexact += 1;
                    }
                }
                // An array whose element or index sort mentions a datatype: the
                // witness would be array-sorted and the expansion cannot reach
                // into it.  Refused by this lane too, and counted separately so
                // the note does not conflate it with the datatype case.
                s if crate::datatype_elim::sort_mentions_datatype(s) => dtres_nondt += 1,
                _ => {}
            }
        }

        // Every datatype-sorted argument of every WIDENED site, classified.
        let (mut sym_exact, mut sym_inexact) = (0usize, 0usize);
        let (mut ctor_exact, mut ctor_inexact) = (0usize, 0usize);
        let (mut apply_exact, mut apply_inexact) = (0usize, 0usize);
        let mut other = 0usize;
        let mut other_kinds: BTreeSet<String> = BTreeSet::new();
        for sites in wide.values() {
            for &site in sites {
                let TermNode::App { args, .. } = arena.node(site) else {
                    continue;
                };
                for &arg in &args.clone() {
                    if !is_datatype_sorted(arena, arg) {
                        continue;
                    }
                    let Sort::Datatype(dt) = arena.sort_of(arg) else {
                        continue;
                    };
                    let exact = datatype_expansion_is_exact(arena, dt);
                    match arena.node(arg) {
                        TermNode::Symbol(_) => {
                            if exact {
                                sym_exact += 1;
                            } else {
                                sym_inexact += 1;
                            }
                        }
                        TermNode::App {
                            op: Op::DtConstruct { .. },
                            ..
                        } => {
                            if exact {
                                ctor_exact += 1;
                            } else {
                                ctor_inexact += 1;
                            }
                        }
                        TermNode::App {
                            op: Op::Apply(_), ..
                        } => {
                            if exact {
                                apply_exact += 1;
                            } else {
                                apply_inexact += 1;
                            }
                        }
                        TermNode::App { op, .. } => {
                            other += 1;
                            other_kinds.insert(format!("{op:?}").split('(').next().unwrap_or("?").to_string());
                        }
                        _ => {
                            other += 1;
                            other_kinds.insert("Other".to_string());
                        }
                    }
                }
            }
        }

        // The arm as it stands (ADR-1942).
        let eligible_a = usize::from(
            sym_inexact == 0
                && ctor_inexact == 0
                && apply_exact == 0
                && apply_inexact == 0
                && other == 0
                && dtres_funcs == 0
                && dtres_nondt == 0
                && narrow_pairs <= MAX_ACK_PAIRS,
        );
        // This lane's proposal.
        let eligible_c = usize::from(
            sym_inexact == 0
                && ctor_inexact == 0
                && apply_inexact == 0
                && other == 0
                && dtres_inexact == 0
                && dtres_nondt == 0
                && wide_pairs <= MAX_ACK_PAIRS,
        );
        let kinds = if other_kinds.is_empty() {
            "-".to_string()
        } else {
            other_kinds.iter().cloned().collect::<Vec<_>>().join(",")
        };
        eprintln!(
            "DTRES-CENSUS narrow_sites={narrow_sites} wide_sites={wide_sites} \
             narrow_pairs={narrow_pairs} wide_pairs={wide_pairs} \
             dtres_funcs={dtres_funcs} dtres_inexact={dtres_inexact} dtres_nondt={dtres_nondt} \
             sym_exact={sym_exact} sym_inexact={sym_inexact} \
             ctor_exact={ctor_exact} ctor_inexact={ctor_inexact} \
             apply_exact={apply_exact} apply_inexact={apply_inexact} \
             other={other} other_kinds={kinds} \
             ELIGIBLE_A={eligible_a} ELIGIBLE_C={eligible_c}"
        );
    }
''' + END


def main() -> int:
    src = open(PATH).read()
    if "--revert" in sys.argv:
        if BEGIN not in src:
            print("census block not present; nothing to revert")
            return 0
        start = src.index(BEGIN)
        stop = src.index(END) + len(END)
        open(PATH, "w").write(src[:start] + src[stop:])
        print("census block removed")
        return 0
    if BEGIN in src:
        print("census block already applied")
        return 0
    assert src.count(ANCHOR) == 1, f"anchor appears {src.count(ANCHOR)} times"
    open(PATH, "w").write(src.replace(ANCHOR, BLOCK + ANCHOR))
    print("census block applied")
    return 0


if __name__ == "__main__":
    sys.exit(main())
