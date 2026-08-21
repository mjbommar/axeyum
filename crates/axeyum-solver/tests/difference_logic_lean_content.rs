#![cfg(feature = "full")]
//! Difference logic renders **reasoning**, not an attestation.
//!
//! `docs/mathematics-2026-08/01-decide-vs-certify.md` item B asks for the
//! externally-unchecked logics to be ranked by what a certificate would be
//! worth. Ranking `QF_IDL / QF_RDL` turned up something the capability table
//! could not express: they share one row, so they are assigned one assurance
//! tier, and measured 2026-08-17 they do not deserve the same one.
//!
//! ```text
//! qf_rdl  scan=Lra        -> OK fragment=Lra content=TheoryReconstruction 47538 bytes
//! qf_idl  scan=ArithDpll  -> DECLINED: emits only a structural attestation
//! ```
//!
//! `QF_RDL` refutations scan into `Lra` — the same fragment as `QF_LRA`, which
//! is externally checked — and render a real theory module. Handed to official
//! Lean 4.30.0 by hand, that module is accepted (0.20s), and two independent
//! mutations of it are rejected:
//!
//! ```text
//! lean qf_rdl.lean                       exit=0
//! lean qf_rdl.lean [hyp lt -> le]        exit=1
//! lean qf_rdl.lean [hyp sign flipped]    exit=1
//! ```
//!
//! `QF_IDL` declined, because integer difference logic routed through
//! `ArithDpll`, which has no theory reconstruction. **That gap closed the same
//! day**: `ProofFragment::IntFarkas` refutes a conjunctive integer system on its
//! rational relaxation, abstracts the Farkas proof over the ordered-ring laws,
//! and instantiates at `ℤ`. `qf_idl` now renders a 192 KB theory
//! reconstruction, and this test measures that rather than the old decline.
//!
//! # What this test does and does not claim
//!
//! It asserts the **precondition** for external checking — that the module
//! contains reasoning rather than an `axiom P` / `axiom ¬P` shim. It does NOT
//! claim `QF_RDL` is externally *gated*: `scripts/check-lean-gate.sh` hands
//! official Lean a one-module-per-*family* representative slice, and the `Lra`
//! representative is not a `QF_RDL` module. Closing that is the top item of the
//! ranking, precisely because it is plumbing rather than a proof format.
//!
//! The `QF_IDL` row was reported rather than asserted, precisely so that giving
//! it a reconstruction would not be punished as a failure. That is what
//! happened, and the row simply changed value.

use axeyum_smtlib::parse_script;
use axeyum_solver::{LeanModuleContent, prove_unsat_to_lean_theory_module, scan_proof_fragment};

/// `(name, smtlib2)` — each must be genuinely `unsat`.
const QUERIES: &[(&str, &str)] = &[
    (
        "qf_rdl",
        "(set-logic QF_RDL)\n\
         (declare-fun x () Real)\n\
         (declare-fun y () Real)\n\
         (assert (< (- x y) 1.0))\n\
         (assert (< (- y x) (- 2.0)))\n\
         (check-sat)",
    ),
    (
        "qf_idl",
        "(set-logic QF_IDL)\n\
         (declare-fun x () Int)\n\
         (declare-fun y () Int)\n\
         (assert (<= (- x y) 1))\n\
         (assert (<= (- y x) (- 3)))\n\
         (check-sat)",
    ),
];

struct Row {
    name: &'static str,
    fragment: String,
    content: Option<LeanModuleContent>,
    bytes: usize,
}

fn measure() -> Vec<Row> {
    QUERIES
        .iter()
        .map(|(name, text)| {
            let mut parsed = parse_script(text).expect("query parses");
            let assertions = parsed.assertions.clone();
            let fragment = format!("{:?}", scan_proof_fragment(&parsed.arena, &assertions));
            match prove_unsat_to_lean_theory_module(&mut parsed.arena, &assertions) {
                Ok((_, source)) => Row {
                    name,
                    fragment,
                    content: Some(LeanModuleContent::of_module_source(&source)),
                    bytes: source.len(),
                },
                Err(_) => Row {
                    name,
                    fragment,
                    content: None,
                    bytes: 0,
                },
            }
        })
        .collect()
}

/// Whatever renders must be reasoning, and something must render.
#[test]
fn a_rendered_difference_logic_module_is_never_an_attestation() {
    let rows = measure();
    let mut rendered = 0;
    for row in &rows {
        println!(
            "  {:<8} fragment={:<12} content={:<24} bytes={}",
            row.name,
            row.fragment,
            row.content
                .map_or_else(|| "DECLINED".to_string(), |c| format!("{c:?}")),
            row.bytes
        );
        if let Some(content) = row.content {
            rendered += 1;
            assert!(
                !content.is_structural_attestation(),
                "{}: rendered a module that is a structural attestation (an `axiom P` refuted \
                 by `axiom Not P`, containing none of the reasoning) while reporting success. \
                 `prove_unsat_to_lean_theory_module` exists to decline exactly this",
                row.name
            );
        }
    }
    assert!(
        rendered >= 1,
        "no difference-logic query rendered a Lean module at all, so this test cannot tell a \
         working reconstruction from an absent one. QF_RDL rendered {} bytes on 2026-08-17",
        47538
    );
}

/// `QF_RDL` specifically — the row the ranking depends on.
#[test]
fn qf_rdl_reconstructs_through_the_same_fragment_as_qf_lra() {
    let row = measure()
        .into_iter()
        .find(|r| r.name == "qf_rdl")
        .expect("the corpus contains a QF_RDL query");
    assert_eq!(
        row.fragment, "Lra",
        "QF_RDL stopped scanning into the `Lra` fragment (now `{}`). That fragment is what \
         makes its refutation externally checkable by the same route as QF_LRA; a change here \
         moves QF_RDL back into the unchecked set",
        row.fragment
    );
    assert_eq!(
        row.content,
        Some(LeanModuleContent::TheoryReconstruction),
        "QF_RDL no longer renders a theory-reconstructed Lean module. Official Lean 4.30.0 \
         accepted this module on 2026-08-17 and rejected two mutations of it"
    );
}

/// Negative control: the discriminator can actually return the other answer.
///
/// The assertion above — "a rendered module is never an attestation" — is
/// worthless if `LeanModuleContent::of_module_source` never classifies anything
/// as one.
///
/// This originally used `QF_IDL`, whose plain route rendered the shim. On
/// 2026-08-17 `ProofFragment::IntFarkas` gave integer difference logic a real
/// reconstruction and the control fired, saying exactly that and asking to be
/// repointed. So it no longer names one query: it tries several shapes and
/// requires that SOME route still attests. If every candidate gains a
/// reconstruction, this fails loudly and asks for a new one — which is the right
/// failure, because at that point the guard above would be vacuous.
#[test]
fn the_attestation_class_is_reachable_so_the_guard_is_not_vacuous() {
    // Boolean-structured arithmetic: the lazy-SMT routes emit the `axiom P` /
    // `axiom Not P` shim rather than a term built from the query.
    const CANDIDATES: &[(&str, &str)] = &[
        (
            "bool_structured_int",
            "(set-logic QF_LIA)\n\
             (declare-fun x () Int)\n\
             (assert (>= x 0))\n\
             (assert (or (< x 0) (< x 0)))\n\
             (check-sat)",
        ),
        (
            "bool_structured_real",
            "(set-logic QF_LRA)\n\
             (declare-fun x () Real)\n\
             (assert (>= x 0.0))\n\
             (assert (or (< x 0.0) (< x 0.0)))\n\
             (check-sat)",
        ),
    ];

    let mut attesting = Vec::new();
    for (name, text) in CANDIDATES {
        let mut parsed = parse_script(text).expect("query parses");
        let assertions = parsed.assertions.clone();
        let Ok((fragment, source)) =
            axeyum_solver::prove_unsat_to_lean_module(&mut parsed.arena, &assertions)
        else {
            println!("  control candidate {name}: no module");
            continue;
        };
        let content = LeanModuleContent::of_module_source(&source);
        println!("  control candidate {name}: fragment={fragment:?} content={content:?}");
        if content.is_structural_attestation() {
            attesting.push(*name);
        }
    }
    assert!(
        !attesting.is_empty(),
        "no candidate rendered a structural attestation, so `of_module_source` may no longer \
         detect the marker — in which case the guard above passes on anything. Either point this \
         at a route that still attests, or, if genuinely nothing attests any more, delete the \
         guard because it has become unconditional"
    );
}
