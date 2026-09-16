#!/usr/bin/env python3
"""Apply the LRA-MODEL-REPLAY one-off census diagnostic to a SNAPSHOT tree.

This is a MEASUREMENT instrument, not a shipped change. It is applied to a
`scripts/lane-snapshot.sh` tree only; nothing here is committed to the crate.

What it adds:

  * `AXEYUM_LRA_REPLAY_CENSUS=1` -- on the `Sat` arm of
    `check_qf_lra_online_cdclt`, print to stderr, for the query that just
    produced a candidate model:
      - the atom-kind split (Order / Equality / Unsupported) of the registered
        atoms, straight off the live `LraTheory`;
      - how many `Equality` atoms the SAT assignment set FALSE (the theory
        treats a false equality as a no-op: `lra_online.rs:2082`);
      - every OFFENDING atom: one whose SAT truth value differs from its value
        under the reconstructed model (or whose evaluation errors), aggregated
        by (atom kind, SAT polarity, evaluation status, the construct that put
        it outside `linearize`);
      - the count of ORIGINAL assertions that fail to replay, split into
        "evaluated false" and "evaluation errored" (a missing symbol value).

  * The construct naming mirrors `AtomBuilder::linearize`
    (`lra_online.rs:3556`) exactly: a node it accepts is silent, a node it
    rejects is named. So "which construct is outside the incremental engine"
    is read off the same acceptance rule the engine itself uses, not guessed.

Usage: census-patch.py <snapshot-root>
"""

import sys
import pathlib

root = pathlib.Path(sys.argv[1])
online = root / "crates/axeyum-solver/src/lra_online.rs"
theory = root / "crates/axeyum-solver/src/lra_theory.rs"

# ---------------------------------------------------------------- lra_online.rs
ANCHOR_ONLINE = """    #[must_use]
    pub(crate) fn real_model(&self) -> Option<Model> {
        self.model(&self.vars)
    }
"""
ADD_ONLINE = ANCHOR_ONLINE + """
    /// CENSUS DIAGNOSTIC (lane LRA-MODEL-REPLAY, snapshot only). Per registered
    /// atom, the `AtomKind` the builder assigned it: 0 = Order, 1 = Equality,
    /// 2 = Unsupported. Read straight off `self.atoms`, so it is the engine's
    /// own classification and not a re-derivation.
    #[must_use]
    pub(crate) fn census_atom_tags(&self) -> Vec<u8> {
        self.atoms
            .iter()
            .map(|a| match a {
                AtomKind::Order { .. } => 0u8,
                AtomKind::Equality { .. } => 1u8,
                AtomKind::Unsupported => 2u8,
            })
            .collect()
    }
"""

# ---------------------------------------------------------------- lra_theory.rs
ANCHOR_NOMODEL = """            let Some(mut model) = theory.inner().real_model() else {
                crate::lazy_smt_counters::record_online_probe(OnlineProbe::ModelDidNotReplay);
                crate::lra_online::model_probe("lra_theory:no-model-reconstructed");"""
ADD_NOMODEL = """            let Some(mut model) = theory.inner().real_model() else {
                crate::lazy_smt_counters::record_online_probe(OnlineProbe::ModelDidNotReplay);
                census_no_model(arena, &atom_terms, theory.inner(), &assignment);
                crate::lra_online::model_probe("lra_theory:no-model-reconstructed");"""

ANCHOR_REPLAY = """            add_boolean_leaf_values(arena, &enc, atom_count, &assignment, &mut model);
            if replays(arena, assertions, &model) {"""
ADD_REPLAY = """            add_boolean_leaf_values(arena, &enc, atom_count, &assignment, &mut model);
            census_report(
                arena,
                assertions,
                &atom_terms,
                theory.inner(),
                &assignment,
                &model,
            );
            if replays(arena, assertions, &model) {"""

CENSUS_FNS = r'''
// ============================================================================
// CENSUS DIAGNOSTIC -- lane LRA-MODEL-REPLAY, snapshot only, NOT shipped.
// `AXEYUM_LRA_REPLAY_CENSUS=1`. Everything below is behind that env var and
// writes only to stderr.
// ============================================================================

fn census_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("AXEYUM_LRA_REPLAY_CENSUS").is_ok_and(|v| v.trim() == "1")
    })
}

/// Names every construct in `term` that `AtomBuilder::linearize`
/// (`lra_online.rs:3556`) REFUSES. A term whose every node that function
/// accepts yields an empty set; anything else names why the atom became
/// `AtomKind::Unsupported`. Mirrors that function's match arms one for one.
fn census_lin_refusals(
    arena: &TermArena,
    term: TermId,
    out: &mut std::collections::BTreeSet<String>,
    depth: usize,
) {
    if depth > 64 {
        out.insert("deep".to_owned());
        return;
    }
    use axeyum_ir::Op;
    match arena.node(term) {
        TermNode::RealConst(_) => {}
        TermNode::Symbol(_) => {
            if arena.sort_of(term) != Sort::Real {
                out.insert(format!("symbol-sort:{:?}", arena.sort_of(term)));
            }
        }
        TermNode::App { op, args } => match op {
            Op::RealNeg => census_lin_refusals(arena, args[0], out, depth + 1),
            Op::RealAdd | Op::RealSub => {
                census_lin_refusals(arena, args[0], out, depth + 1);
                census_lin_refusals(arena, args[1], out, depth + 1);
            }
            Op::RealMul => {
                let a_const = census_is_const(arena, args[0], 0);
                let b_const = census_is_const(arena, args[1], 0);
                if !a_const && !b_const {
                    out.insert("nonlinear-mul".to_owned());
                }
                census_lin_refusals(arena, args[0], out, depth + 1);
                census_lin_refusals(arena, args[1], out, depth + 1);
            }
            Op::RealDiv => {
                if census_is_const(arena, args[1], 0) {
                    out.insert("div-by-const".to_owned());
                } else {
                    out.insert("div-by-nonconst".to_owned());
                }
                census_lin_refusals(arena, args[0], out, depth + 1);
            }
            Op::Ite => {
                out.insert("ite".to_owned());
                census_lin_refusals(arena, args[1], out, depth + 1);
                census_lin_refusals(arena, args[2], out, depth + 1);
            }
            Op::IntToReal => {
                out.insert("to_real".to_owned());
            }
            Op::RealToInt => {
                out.insert("to_int".to_owned());
            }
            other => {
                out.insert(format!("app:{other:?}"));
            }
        },
        _ => {
            out.insert("other-node".to_owned());
        }
    }
}

/// Whether `term` is a constant real expression under `linearize`'s own rule
/// (`LinExpr::is_constant`): built only from real constants and +,-,*,neg.
fn census_is_const(arena: &TermArena, term: TermId, depth: usize) -> bool {
    use axeyum_ir::Op;
    if depth > 32 {
        return false;
    }
    match arena.node(term) {
        TermNode::RealConst(_) => true,
        TermNode::App { op, args } => match op {
            Op::RealNeg => census_is_const(arena, args[0], depth + 1),
            Op::RealAdd | Op::RealSub | Op::RealMul => {
                census_is_const(arena, args[0], depth + 1)
                    && census_is_const(arena, args[1], depth + 1)
            }
            _ => false,
        },
        _ => false,
    }
}

/// The construct an atom carries, as one label. `Order`/`Equality` atoms are
/// fully hosted, so they are labelled by their ROLE (an equality asserted false
/// is the disequality no-op at `lra_online.rs:2082`); an `Unsupported` atom is
/// labelled by what `linearize` refused.
fn census_atom_label(arena: &TermArena, term: TermId, tag: u8, sat_value: Option<bool>) -> String {
    match tag {
        0 => "order-atom".to_owned(),
        1 => match sat_value {
            Some(false) => "disequality(eq-asserted-false)".to_owned(),
            _ => "equality-atom".to_owned(),
        },
        _ => {
            let mut set = std::collections::BTreeSet::new();
            census_lin_refusals(arena, term, &mut set, 0);
            if set.is_empty() {
                "unsupported(no-refusal-found)".to_owned()
            } else {
                let v: Vec<String> = set.into_iter().collect();
                format!("unsupported({})", v.join("+"))
            }
        }
    }
}

fn census_no_model(
    arena: &TermArena,
    atom_terms: &[TermId],
    theory: &LraTheory,
    assignment: &NativeModel,
) {
    if !census_on() {
        return;
    }
    let tags = theory.census_atom_tags();
    census_kind_split(arena, atom_terms, &tags, assignment, "no-model");
}

fn census_kind_split(
    arena: &TermArena,
    atom_terms: &[TermId],
    tags: &[u8],
    assignment: &NativeModel,
    arm: &str,
) {
    let mut order = 0usize;
    let mut eq = 0usize;
    let mut unsup = 0usize;
    let mut eq_false = 0usize;
    let mut unsup_labels: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    for (i, &tag) in tags.iter().enumerate() {
        match tag {
            0 => order += 1,
            1 => {
                eq += 1;
                if assignment.value(i) == Some(false) {
                    eq_false += 1;
                }
            }
            _ => {
                unsup += 1;
                if let Some(&t) = atom_terms.get(i) {
                    let label = census_atom_label(arena, t, 2, assignment.value(i));
                    *unsup_labels.entry(label).or_default() += 1;
                }
            }
        }
    }
    eprintln!(
        "; LRACENSUS arm={arm} atoms={} order={order} equality={eq} unsupported={unsup} \
         eq_asserted_false={eq_false}",
        tags.len()
    );
    for (label, count) in unsup_labels {
        eprintln!("; LRACENSUS unsupported_kind {count} {label}");
    }
}

fn census_report(
    arena: &TermArena,
    assertions: &[TermId],
    atom_terms: &[TermId],
    theory: &LraTheory,
    assignment: &NativeModel,
    model: &Model,
) {
    if !census_on() {
        return;
    }
    let tags = theory.census_atom_tags();

    // Assertion-level replay outcome, the thing `replays` collapses to a bool.
    let mut ass_true = 0usize;
    let mut ass_false = 0usize;
    let mut ass_err = 0usize;
    let mut assign = axeyum_ir::Assignment::new();
    for (symbol, value) in model.iter() {
        assign.set(symbol, value);
    }
    for &a in assertions {
        match axeyum_ir::eval(arena, a, &assign) {
            Ok(Value::Bool(true)) => ass_true += 1,
            Ok(_) => ass_false += 1,
            Err(_) => ass_err += 1,
        }
    }
    let arm = if ass_false == 0 && ass_err == 0 {
        "replayed"
    } else {
        "no-replay"
    };
    census_kind_split(arena, atom_terms, &tags, assignment, arm);
    eprintln!(
        "; LRACENSUS assertions total={} sat={ass_true} false={ass_false} eval_err={ass_err}",
        assertions.len()
    );

    // OFFENDING ATOMS: the SAT solver committed to a truth value the model does
    // not deliver. This is the exact set the theory failed to enforce, and the
    // label says which construct each one carries.
    let mut offenders: std::collections::BTreeMap<String, usize> =
        std::collections::BTreeMap::new();
    let mut offend_total = 0usize;
    for (i, &t) in atom_terms.iter().enumerate() {
        let Some(sat) = assignment.value(i) else {
            continue;
        };
        let tag = tags.get(i).copied().unwrap_or(2);
        let evaluated = axeyum_ir::eval(arena, t, &assign);
        let status = match &evaluated {
            Ok(Value::Bool(b)) if *b == sat => continue, // agrees; not an offender
            Ok(Value::Bool(_)) => "mismatch",
            Ok(_) => "non-bool",
            Err(_) => "eval-err",
        };
        offend_total += 1;
        let label = census_atom_label(arena, t, tag, Some(sat));
        *offenders
            .entry(format!("{label}|sat={sat}|{status}"))
            .or_default() += 1;
    }
    eprintln!("; LRACENSUS offending_atoms total={offend_total}");
    for (key, count) in offenders {
        eprintln!("; LRACENSUS offender {count} {key}");
    }
}
'''

def patch(path, anchor, replacement, label):
    text = path.read_text()
    n = text.count(anchor)
    if n != 1:
        raise SystemExit(f"ABORT: anchor {label} occurs {n} times in {path} (want 1)")
    path.write_text(text.replace(anchor, replacement))
    print(f"patched {label} in {path.name}")

patch(online, ANCHOR_ONLINE, ADD_ONLINE, "census_atom_tags")
patch(theory, ANCHOR_NOMODEL, ADD_NOMODEL, "no-model arm")
patch(theory, ANCHOR_REPLAY, ADD_REPLAY, "replay arm")

t = theory.read_text()
if "fn census_report" in t:
    raise SystemExit("ABORT: census functions already present in lra_theory.rs")
theory.write_text(t + CENSUS_FNS)
print("appended census functions to lra_theory.rs")
