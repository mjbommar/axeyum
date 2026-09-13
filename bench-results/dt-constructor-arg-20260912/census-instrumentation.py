import sys

p = "crates/axeyum-solver/src/datatype_native.rs"
src = open(p).read()
anchor = "    // Validate BEFORE declaring anything, so a refusal leaves the arena clean.\n"
assert src.count(anchor) == 1, src.count(anchor)
block = r'''    // ---- TEMPORARY SIZING CENSUS v2 (lane dt-constructor-arg, NOT COMMITTED) ----
    if std::env::var_os("AXEYUM_DTARG_CENSUS").is_some() {
        let mut dt_result_funcs = 0usize;
        let mut dt_result_inexact = 0usize;
        let mut args_total = 0usize;
        let (mut sym_exact, mut sym_inexact) = (0usize, 0usize);
        let (mut ctor_exact, mut ctor_inexact) = (0usize, 0usize);
        let (mut apply_exact, mut apply_inexact) = (0usize, 0usize);
        let mut other = 0usize;
        let mut other_kinds: BTreeSet<String> = BTreeSet::new();
        for (&func, sites) in &groups {
            let (_, _, result) = arena.function(func);
            if crate::datatype_elim::sort_mentions_datatype(result) {
                dt_result_funcs += 1;
                match result {
                    Sort::Datatype(d) if datatype_expansion_is_exact(arena, d) => {}
                    _ => dt_result_inexact += 1,
                }
            }
            for &site in sites {
                let TermNode::App { args, .. } = arena.node(site) else {
                    continue;
                };
                for &arg in &args.clone() {
                    if !is_datatype_sorted(arena, arg) {
                        continue;
                    }
                    args_total += 1;
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
                            let d = format!("{op:?}");
                            let head: String =
                                d.chars().take_while(|c| c.is_alphanumeric()).collect();
                            other_kinds.insert(head);
                        }
                        _ => {
                            other += 1;
                            other_kinds.insert("literal".to_owned());
                        }
                    }
                }
            }
        }
        let bounded = pairs <= MAX_ACK_PAIRS;
        // Slice A: constructor arguments only (this lane, ADR-1942).
        let elig_a = usize::from(
            bounded
                && dt_result_funcs == 0
                && sym_inexact == 0
                && ctor_inexact == 0
                && apply_exact + apply_inexact == 0
                && other == 0
                && ctor_exact > 0,
        );
        // Slice B: A, plus Ackermannising a datatype-VALUED uf result into a
        // fresh datatype VARIABLE (the row ADR-1935 refused).
        let elig_b = usize::from(
            bounded
                && dt_result_inexact == 0
                && sym_inexact == 0
                && ctor_inexact == 0
                && apply_inexact == 0
                && other == 0,
        );
        let kinds: Vec<&str> = other_kinds.iter().map(String::as_str).collect();
        let kinds = if kinds.is_empty() {
            "-".to_owned()
        } else {
            kinds.join(",")
        };
        eprintln!(
            "DTARG-CENSUS pairs={pairs} dt_result={dt_result_funcs} dt_result_inexact={dt_result_inexact} args={args_total} sym_exact={sym_exact} sym_inexact={sym_inexact} ctor_exact={ctor_exact} ctor_inexact={ctor_inexact} apply_exact={apply_exact} apply_inexact={apply_inexact} other={other} other_kinds={kinds} ELIGIBLE={elig_a} ELIGIBLE_B={elig_b}"
        );
    }
    // ---- END TEMPORARY SIZING CENSUS v2 ----
'''
src = src.replace(anchor, block + anchor)
open(p, "w").write(src)
print("patched v2")
