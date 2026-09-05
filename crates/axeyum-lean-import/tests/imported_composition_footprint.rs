//! **Does an originated theorem that depends on an imported one carry the
//! import's axioms?** — the measurement ADR-1664 decides on.
//!
//! Two footprint regimes exist in this repository and nothing said whether they
//! may touch. Originated theorems carry `proof_route: kernel-lean` and an EMPTY
//! `Kernel::axiom_footprint`; ADR-1601 makes classical principles hypotheses
//! discharged at use, never axioms. Imports carry `proof_route:
//! imported-kernel-lean` (ADR-1090) and `scripts/validate-facts.py` refuses an
//! empty footprint on that route by construction. The undecided question was
//! what happens when a theorem *we* author cites a declaration *Lean* authored.
//!
//! This suite answers it by building the composed theorem instead of arguing
//! about it, in the department's standard method. Every number ADR-1664 quotes
//! is printed here on an `AXEYUM-COMPOSE|` marker line, so a suite that
//! compiled to zero tests — this repository's signature defect — cannot be read
//! as a passing measurement.
//!
//! ## What each test establishes
//!
//! * [`init_only_import_composes_to_an_empty_footprint`] — an Init-only stream
//!   (`bool-and-comm.ndjson`, 48 declarations) admits with an empty footprint,
//!   and an originated theorem citing `Bool.and_comm` still measures `[]`.
//!   Composition over an axiom-free import costs nothing *in axioms*.
//! * [`classical_import_propagates_its_axioms_and_a_sibling_proof_does_not`] —
//!   the discriminating pair. TWO originated theorems, the SAME type, the SAME
//!   kernel, differing only in whether the proof term reaches `Classical.em`.
//!   The citing one inherits the import's whole trusted closure; its sibling
//!   measures `[]`. This is the positive control the decision rests on: the
//!   footprint is a property of the PROOF TERM, not of the environment, so a
//!   composed tier is decidable per theorem rather than per session.
//! * [`nat_prelude_and_an_import_share_one_environment`] — whether our own
//!   prelude can be built into a kernel that already holds an import at all,
//!   and whether a prelude theorem's footprint survives the cohabitation.
//! * [`the_mathlib_case_is_measured_not_assumed`] — the other end of the range,
//!   re-derived from the pinned IVT stream rather than quoted from a doc.
//!
//! The first two are the regression guards and run in `lean-gate` (0.13 s
//! together). The last two are one-time measurements and are `#[ignore]`d,
//! because between them they cost 81 s; run `-- --ignored` to re-derive them.
//!
//! ## What this does NOT establish
//!
//! `axiom_footprint` reports what a proof term rests on *inside this kernel*.
//! It does not cover the trust the import itself adds — that the exporter
//! rendered Lean's environment faithfully, that our wire translation preserves
//! meaning, and that the delivered bytes are the producer's intended export
//! (format 3.1 has no footer). Those are why `imported-kernel-lean` is not in
//! the validator's `AXIOM_FREE_CAPABLE` set, and they do not go away when a
//! composed theorem's measured footprint is `[]`. ADR-1664 is written around
//! that gap, not in spite of it.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::time::Instant;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, KernelError, LevelId, NameId, build_nat_prelude,
};

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../artifacts/lean-imports")
        .canonicalize()
        .expect("artifacts/lean-imports must exist")
}

fn stream(name: &str) -> Vec<u8> {
    let path = fixture_dir().join(name);
    std::fs::read(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// The `NameId` whose rendered form is exactly `rendered`.
///
/// Rendered-name lookup, not `name_str`, because an imported stream interns its
/// own names and the only stable handle on one is what the kernel displays.
fn lookup(kernel: &Kernel, rendered: &str) -> NameId {
    kernel
        .environment()
        .iter()
        .map(|(_, d)| d.name())
        .find(|&n| kernel.display_name(n).to_string() == rendered)
        .unwrap_or_else(|| panic!("{rendered} is not in the environment"))
}

/// `Kernel::axiom_footprint`, rendered and sorted — this kernel's `#print axioms`.
fn footprint(kernel: &Kernel, name: NameId) -> Vec<String> {
    kernel
        .axiom_footprint(name)
        .into_iter()
        .map(|n| kernel.display_name(n).to_string())
        .collect()
}

fn render_footprint(f: &[String]) -> String {
    if f.is_empty() {
        "EMPTY".to_owned()
    } else {
        f.join(",")
    }
}

/// Intern a fresh dotted name for a theorem this test authors.
fn authored_name(kernel: &mut Kernel, segments: &[&str]) -> NameId {
    let mut n = kernel.anon();
    for s in segments {
        n = kernel.name_str(n, *s);
    }
    n
}

fn const0(kernel: &mut Kernel, name: NameId) -> ExprId {
    kernel.const_(name, Vec::new())
}

fn const_at(kernel: &mut Kernel, name: NameId, levels: Vec<LevelId>) -> ExprId {
    kernel.const_(name, levels)
}

fn app2(kernel: &mut Kernel, f: ExprId, a: ExprId, b: ExprId) -> ExprId {
    let fa = kernel.app(f, a);
    kernel.app(fa, b)
}

fn app3(kernel: &mut Kernel, f: ExprId, a: ExprId, b: ExprId, c: ExprId) -> ExprId {
    let fab = app2(kernel, f, a, b);
    kernel.app(fab, c)
}

/// Admit `value : ty` as an authored theorem and return its name plus the wall
/// time `Kernel::add_declaration` took — the trusted gate is what costs, and the
/// cost side of the decision is whether composition makes it worse.
fn admit_theorem(
    kernel: &mut Kernel,
    segments: &[&str],
    ty: ExprId,
    value: ExprId,
) -> (NameId, f64) {
    let name = authored_name(kernel, segments);
    let start = Instant::now();
    kernel
        .add_declaration(Declaration::Theorem {
            name,
            uparams: Vec::new(),
            ty,
            value,
        })
        .unwrap_or_else(|e| panic!("{} rejected: {e:?}", segments.join(".")));
    (name, start.elapsed().as_secs_f64() * 1000.0)
}

// ---------------------------------------------------------------------------
// 1. Init-only import: composition is free
// ---------------------------------------------------------------------------

/// `bool-and-comm.ndjson` is Lean `Init` only. Measure that the import itself is
/// axiom-free, then author `∀ x, Bool.and x true = Bool.and true x` whose proof
/// is `Bool.and_comm x true` and measure THAT.
#[test]
fn init_only_import_composes_to_an_empty_footprint() {
    let bytes = stream("bool-and-comm.ndjson");
    let t0 = Instant::now();
    let completed = import_ndjson(bytes.as_slice(), ImportLimits::default())
        .expect("bool-and-comm.ndjson must import");
    let import_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let (mut kernel, report) = completed.into_parts();
    let env_after_import = kernel.environment().len();

    let and_comm = lookup(&kernel, "Bool.and_comm");
    let imported_footprint = footprint(&kernel, and_comm);

    let bool_name = lookup(&kernel, "Bool");
    let and_name = lookup(&kernel, "Bool.and");
    let true_name = lookup(&kernel, "Bool.true");
    let eq_name = lookup(&kernel, "Eq");

    let bool_ty = const0(&mut kernel, bool_name);
    let and_c = const0(&mut kernel, and_name);
    let true_c = const0(&mut kernel, true_name);
    let one = {
        let z = kernel.level_zero();
        kernel.level_succ(z)
    };
    let eq_c = const_at(&mut kernel, eq_name, vec![one]);

    // (x : Bool) -> Eq.{1} Bool (Bool.and x Bool.true) (Bool.and Bool.true x)
    let x = kernel.bvar(0);
    let lhs = app2(&mut kernel, and_c, x, true_c);
    let rhs = app2(&mut kernel, and_c, true_c, x);
    let body = app3(&mut kernel, eq_c, bool_ty, lhs, rhs);
    let x_binder = authored_name(&mut kernel, &["x"]);
    let ty = kernel.pi(x_binder, bool_ty, body, BinderInfo::Default);

    // fun (x : Bool) => Bool.and_comm x Bool.true
    let and_comm_c = const0(&mut kernel, and_comm);
    let x = kernel.bvar(0);
    let proof_body = app2(&mut kernel, and_comm_c, x, true_c);
    let value = kernel.lam(x_binder, bool_ty, proof_body, BinderInfo::Default);

    let (composed, admit_ms) = admit_theorem(
        &mut kernel,
        &["Axeyum", "Composition", "bool_and_true_comm"],
        ty,
        value,
    );
    let composed_footprint = footprint(&kernel, composed);

    println!(
        "AXEYUM-COMPOSE|case=init-only|stream=bool-and-comm.ndjson|lean={}|\
         admitted={}|env_len={}|import_ms={import_ms:.1}|admit_ms={admit_ms:.3}|\
         imported_footprint={}|composed_footprint={}",
        report.lean_version,
        report.admitted_declarations,
        env_after_import,
        render_footprint(&imported_footprint),
        render_footprint(&composed_footprint),
    );

    assert!(
        imported_footprint.is_empty(),
        "an Init-only import was expected axiom-free, got {imported_footprint:?}"
    );
    assert!(
        composed_footprint.is_empty(),
        "composing over an axiom-free import must stay axiom-free, got \
         {composed_footprint:?}"
    );
    assert_eq!(
        report.admitted_declarations, 48,
        "pinned stream size moved; re-derive ADR-1664's numbers before editing this"
    );
}

// ---------------------------------------------------------------------------
// 2. The discriminating pair: propagation is per proof term
// ---------------------------------------------------------------------------

/// The measurement the ADR turns on.
///
/// `classical-em.ndjson` carries `Classical.em`, whose footprint is Lean's
/// classical closure. In ONE kernel holding that import, author two theorems of
/// the SAME type:
///
/// ```text
/// (p : Prop) -> (h : Or p (Not p)) -> Or p (Not p)
/// ```
///
/// one proved `fun p h => Classical.em p` (reaches the import) and one proved
/// `fun p h => h` (does not). If the footprint were a property of the
/// ENVIRONMENT, both would report the import's axioms and the second would be a
/// false positive. It is a property of the PROOF TERM, and that is what makes a
/// composed tier decidable per theorem rather than per session.
#[test]
fn classical_import_propagates_its_axioms_and_a_sibling_proof_does_not() {
    let bytes = stream("classical-em.ndjson");
    let t0 = Instant::now();
    let completed = import_ndjson(bytes.as_slice(), ImportLimits::default())
        .expect("classical-em.ndjson must import");
    let import_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let (mut kernel, report) = completed.into_parts();
    let env_after_import = kernel.environment().len();

    let em = lookup(&kernel, "Classical.em");
    let em_footprint = footprint(&kernel, em);

    let or_name = lookup(&kernel, "Or");
    let not_name = lookup(&kernel, "Not");
    let or_c = const0(&mut kernel, or_name);
    let not_c = const0(&mut kernel, not_name);
    let prop = kernel.sort_zero();

    // (p : Prop) -> (h : Or p (Not p)) -> Or p (Not p)
    let p_at_1 = kernel.bvar(0);
    let not_p_1 = kernel.app(not_c, p_at_1);
    let hyp = app2(&mut kernel, or_c, p_at_1, not_p_1);
    let p_at_2 = kernel.bvar(1);
    let not_p_2 = kernel.app(not_c, p_at_2);
    let concl = app2(&mut kernel, or_c, p_at_2, not_p_2);
    let h_binder = authored_name(&mut kernel, &["h"]);
    let p_binder = authored_name(&mut kernel, &["p"]);
    let inner_pi = kernel.pi(h_binder, hyp, concl, BinderInfo::Default);
    let ty = kernel.pi(p_binder, prop, inner_pi, BinderInfo::Default);

    // fun (p : Prop) (h : _) => Classical.em p   -- reaches the import
    let em_c = const0(&mut kernel, em);
    let p_deep = kernel.bvar(1);
    let via_import_body = kernel.app(em_c, p_deep);
    let via_import_inner = kernel.lam(h_binder, hyp, via_import_body, BinderInfo::Default);
    let via_import_value = kernel.lam(p_binder, prop, via_import_inner, BinderInfo::Default);

    let (via_import, via_import_ms) = admit_theorem(
        &mut kernel,
        &["Axeyum", "Composition", "em_stable_via_import"],
        ty,
        via_import_value,
    );
    let via_import_footprint = footprint(&kernel, via_import);

    // fun (p : Prop) (h : _) => h   -- same type, does not reach the import
    let h_deep = kernel.bvar(0);
    let control_inner = kernel.lam(h_binder, hyp, h_deep, BinderInfo::Default);
    let control_value = kernel.lam(p_binder, prop, control_inner, BinderInfo::Default);

    let (control, control_ms) = admit_theorem(
        &mut kernel,
        &["Axeyum", "Composition", "em_stable_originated_only"],
        ty,
        control_value,
    );
    let control_footprint = footprint(&kernel, control);

    println!(
        "AXEYUM-COMPOSE|case=classical|stream=classical-em.ndjson|lean={}|\
         admitted={}|env_len={}|import_ms={import_ms:.1}|\
         via_import_admit_ms={via_import_ms:.3}|control_admit_ms={control_ms:.3}|\
         import_footprint={}|composed_footprint={}|control_footprint={}",
        report.lean_version,
        report.admitted_declarations,
        env_after_import,
        render_footprint(&em_footprint),
        render_footprint(&via_import_footprint),
        render_footprint(&control_footprint),
    );

    assert!(
        !em_footprint.is_empty(),
        "Classical.em must import with a non-empty footprint; got EMPTY, which \
         would make the whole propagation question vacuous"
    );
    assert_eq!(
        via_import_footprint, em_footprint,
        "an originated theorem citing an imported one must inherit its WHOLE \
         footprint -- transitivity is what ADR-1664 relies on"
    );
    assert!(
        control_footprint.is_empty(),
        "a sibling proof of the SAME type that does not reach the import must \
         measure []; got {control_footprint:?}, which would mean the footprint \
         reads the environment rather than the proof term"
    );
}

// ---------------------------------------------------------------------------
// 3. Cohabitation: can our prelude and an import share one environment?
// ---------------------------------------------------------------------------

/// Build `nat_prelude` into a kernel that already holds an Init-only import.
///
/// A composed tier that lets one theorem cite both our library and an import
/// needs the two to live in ONE environment, so this is a precondition of
/// options (2) and (3) in ADR-1664 and is measured rather than assumed.
///
/// The order is FORCED by the API: `import_ndjson` constructs its own staging
/// `Kernel` (that is the fail-closed contract — nothing is published unless the
/// whole stream translates), so the only reachable order is import-then-prelude.
///
/// If the build is rejected, the error is `KernelError::DeclarationExists {
/// name: NameId(_) }` — a `NameId` NAMES NOTHING, exactly the failure mode
/// CLAUDE.md records for `UnboundFVar`. So the collision is resolved to its
/// rendered name here, and the whole shared-name set is enumerated beside it,
/// because "which names do the two vocabularies share" is what a bridge would
/// have to answer.
///
/// Ignored by default, for the same reason as the Mathlib endpoint below: it is
/// a one-time measurement, not a regression guard, and it is EXPENSIVE. Building
/// `nat_prelude` in a fresh kernel to get the comparison set costs 63.6 s of the
/// suite's 63.7 s in a debug binary (the two fast tests are 0.13 s together),
/// and the registered `lean-gate` step is not paying a minute for a fact that
/// only moves when item 4's bridge lands. Run with `-- --ignored` to re-measure.
#[test]
#[ignore = "builds nat_prelude in a fresh kernel: 63.6 s of the suite's 63.7 s"]
fn nat_prelude_and_an_import_share_one_environment() {
    let bytes = stream("bool-and-comm.ndjson");
    let completed = import_ndjson(bytes.as_slice(), ImportLimits::default())
        .expect("bool-and-comm.ndjson must import");
    let (mut kernel, report) = completed.into_parts();
    let env_after_import = kernel.environment().len();
    let imported_names: BTreeSet<String> = kernel
        .environment()
        .iter()
        .map(|(&n, _)| kernel.display_name(n).to_string())
        .collect();
    let import_declares_nat = imported_names.contains("Nat");

    let t0 = Instant::now();
    let built = build_nat_prelude(&mut kernel);
    let prelude_ms = t0.elapsed().as_secs_f64() * 1000.0;

    // Resolve the collision to a NAME. `{e:?}` prints `NameId(46)`, which
    // identifies nothing to a reader and moves with interning order.
    let outcome = match &built {
        Ok(_) => "ok".to_owned(),
        Err(KernelError::DeclarationExists { name }) => {
            format!("rejected:DeclarationExists({})", kernel.display_name(*name))
        }
        Err(e) => format!("rejected:{e:?}"),
    };
    let env_after_prelude = kernel.environment().len();

    // What the two vocabularies actually share. Built in a SEPARATE kernel so
    // the failed build above cannot contaminate the answer.
    let mut fresh = Kernel::new();
    let fresh_prelude =
        build_nat_prelude(&mut fresh).expect("nat_prelude must build in a fresh kernel");
    let prelude_names: BTreeSet<String> = fresh
        .environment()
        .iter()
        .map(|(&n, _)| fresh.display_name(n).to_string())
        .collect();
    let shared: Vec<&String> = imported_names.intersection(&prelude_names).collect();
    let shared_sample: Vec<&str> = shared.iter().take(12).map(|s| s.as_str()).collect();

    // A prelude theorem, measured in a kernel holding ONLY the prelude, and (if
    // cohabitation succeeded) in the shared one. If those differ, cohabitation
    // itself would contaminate the axiom-free headline.
    let alone = render_footprint(&footprint(&fresh, fresh_prelude.add_comm));
    let (prelude_theorem, prelude_footprint) = match &built {
        Ok(p) => {
            let name = p.add_comm;
            (
                kernel.display_name(name).to_string(),
                render_footprint(&footprint(&kernel, name)),
            )
        }
        Err(_) => ("n/a".to_owned(), "n/a".to_owned()),
    };

    println!(
        "AXEYUM-COMPOSE|case=cohabitation|stream=bool-and-comm.ndjson|\
         import_admitted={}|import_declares_Nat={import_declares_nat}|\
         env_after_import={env_after_import}|prelude_env_len={}|\
         nat_prelude={outcome}|nat_prelude_ms={prelude_ms:.1}|\
         env_after_prelude={env_after_prelude}|shared_names={}|\
         shared_sample={}|prelude_theorem={prelude_theorem}|\
         prelude_footprint_alone={alone}|prelude_footprint_shared={prelude_footprint}",
        report.admitted_declarations,
        prelude_names.len(),
        shared.len(),
        shared_sample.join(" "),
    );

    // No assertion on the OUTCOME: both answers are decision-relevant and the
    // marker line above is the measurement. What IS asserted is (a) that the
    // two vocabularies really do overlap, so a rejection is explained rather
    // than mysterious, and (b) that a successful cohabitation does not move a
    // prelude theorem's footprint -- an unnoticed move there would silently
    // change the headline.
    assert!(
        !shared.is_empty(),
        "the imported and prelude name sets were measured DISJOINT, which would \
         make a DeclarationExists rejection inexplicable -- re-measure before \
         quoting ADR-1664's cohabitation row"
    );
    if built.is_ok() {
        assert_eq!(
            prelude_footprint, alone,
            "a prelude theorem measured {alone} alone and {prelude_footprint} \
             beside an import -- cohabitation must not move a footprint"
        );
    }
}

// ---------------------------------------------------------------------------
// 4. The other end of the range: a real Mathlib import
// ---------------------------------------------------------------------------

/// Re-derive the Mathlib footprint from the pinned IVT stream.
///
/// ADR-1664 quotes both ends of the range and neither may be quoted from a
/// document: `docs/math-department/14-lean-lang.md` says imports carry
/// `[propext, Classical.choice, Quot.sound]`, and this is what the kernel
/// actually reports.
///
/// Ignored by default: the stream admits thousands of declarations and this is a
/// range endpoint, not a regression guard — `imported_fact_evidence` already
/// pins it on every run. Run with `-- --ignored` to re-measure.
#[test]
#[ignore = "3,585 declarations; imported_fact_evidence pins the same number on every run"]
fn the_mathlib_case_is_measured_not_assumed() {
    let bytes = stream("ivt-intermediate-value-icc.ndjson");
    let t0 = Instant::now();
    let completed = import_ndjson(bytes.as_slice(), ImportLimits::default())
        .expect("ivt-intermediate-value-icc.ndjson must import");
    let import_ms = t0.elapsed().as_secs_f64() * 1000.0;
    let (kernel, report) = completed.into_parts();
    let ivt = lookup(&kernel, "intermediate_value_Icc");
    let f = footprint(&kernel, ivt);
    println!(
        "AXEYUM-COMPOSE|case=mathlib|stream=ivt-intermediate-value-icc.ndjson|\
         admitted={}|env_len={}|import_ms={import_ms:.1}|footprint_len={}|footprint={}",
        report.admitted_declarations,
        kernel.environment().len(),
        f.len(),
        render_footprint(&f),
    );
    assert!(
        f.len() > 3,
        "expected the full classical closure, got {f:?}"
    );
}
