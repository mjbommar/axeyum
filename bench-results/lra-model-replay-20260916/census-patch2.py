#!/usr/bin/env python3
"""Second half of the LRA-MODEL-REPLAY census instrument (snapshot only).

Patch 1 answered "which atoms did the theory fail to enforce". This answers the
deliverable's actual question -- "WHICH assertions does the model fail to
satisfy, and what construct do THEY contain" -- by keying the report on the
failing ASSERTION rather than on the atom population.

The distinction is load-bearing. `replays` (`lra_online.rs:5728`) evaluates the
ORIGINAL assertion, so an atom the theory dropped costs nothing when the
Boolean skeleton makes its assertion true anyway -- the same effect z3 gets
deliberately with its relevancy filter over `m_not_handled`
(`theory_lra.cpp:1793-1810`). Counting offending atoms therefore OVERSTATES the
wall. Counting failing assertions, and naming the constructs inside each one,
does not.

Usage: census-patch2.py <snapshot-root>
"""

import sys
import pathlib

root = pathlib.Path(sys.argv[1])
theory = root / "crates/axeyum-solver/src/lra_theory.rs"

ANCHOR = """    for &a in assertions {
        match axeyum_ir::eval(arena, a, &assign) {
            Ok(Value::Bool(true)) => ass_true += 1,
            Ok(_) => ass_false += 1,
            Err(_) => ass_err += 1,
        }
    }"""

REPL = """    // Per FAILING assertion: the constructs its own atoms carry. `atom_index`
    // is position in `atom_terms`, which is exactly the theory's atom numbering
    // and the driver's first `atom_count` SAT variables.
    let mut atom_index: std::collections::HashMap<TermId, usize> =
        std::collections::HashMap::new();
    for (i, &t) in atom_terms.iter().enumerate() {
        atom_index.insert(t, i);
    }
    let mut fail_labels: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    for &a in assertions {
        let status = match axeyum_ir::eval(arena, a, &assign) {
            Ok(Value::Bool(true)) => {
                ass_true += 1;
                continue;
            }
            Ok(_) => {
                ass_false += 1;
                "false"
            }
            Err(_) => {
                ass_err += 1;
                "eval-err"
            }
        };
        // The atoms of THIS assertion, and which of them the theory dropped.
        let mut here: Vec<TermId> = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::new();
        crate::lra_online::collect_lra_atoms(arena, a, &mut here, &mut seen);
        let mut constructs: std::collections::BTreeSet<String> =
            std::collections::BTreeSet::new();
        for t in here {
            let Some(&i) = atom_index.get(&t) else {
                constructs.insert("atom-not-registered".to_owned());
                continue;
            };
            let Some(sat) = assignment.value(i) else {
                continue;
            };
            let agrees = matches!(
                axeyum_ir::eval(arena, t, &assign),
                Ok(Value::Bool(b)) if b == sat
            );
            if agrees {
                continue;
            }
            let tag = tags.get(i).copied().unwrap_or(2);
            constructs.insert(census_atom_label(arena, t, tag, Some(sat)));
        }
        let label = if constructs.is_empty() {
            "no-offending-atom".to_owned()
        } else {
            constructs.into_iter().collect::<Vec<_>>().join("+")
        };
        *fail_labels.entry(format!("{status}|{label}")).or_default() += 1;
    }
    for (label, count) in &fail_labels {
        eprintln!("; LRACENSUS failassert {count} {label}");
    }"""

text = theory.read_text()
n = text.count(ANCHOR)
if n != 1:
    raise SystemExit(f"ABORT: assertion-loop anchor occurs {n} times (want 1)")
theory.write_text(text.replace(ANCHOR, REPL))
print("patched the assertion loop to key on the FAILING ASSERTION")
