//! Adversarial kernel-vs-kernel differential: **does our kernel accept
//! anything the real Lean kernel rejects?**
//!
//! Every existing cross-check runs the *agreement* direction — we render a
//! term we chose to emit, Lean accepts it, 77 families pass. That corroborates
//! the terms we emit. It cannot corroborate the checker, because a checker
//! that accepted everything would pass all 77.
//!
//! This suite runs the soundness direction. It takes a development this kernel
//! checked, exports it as an official `lean4export` NDJSON 3.1.0 stream, and
//! then damages the stream in ways that stay *structurally valid* — every index
//! still refers to a real, earlier table entry — so what remains is a pure
//! type-checking question. The identical bytes then go to:
//!
//!   ours    `axeyum_lean_import::import_ndjson`, which rebuilds each
//!           declaration and puts it through this kernel's checked admission
//!           gates (`Kernel::add_declaration` / `add_inductive` / the quotient
//!           package). Nothing else can make a declaration exist.
//!   theirs  `lean --run scripts/lean/replay-lean4export.lean`, which hands the
//!           same declarations to `Lean.Environment.addDeclCore` from
//!           `mkEmptyEnvironment` — Lean's own kernel, no elaborator, no
//!           implicit-argument inference, no coercions, no `Init`.
//!
//! The asymmetry is the whole point and is enforced asymmetrically:
//!
//!   ours accepts + Lean rejects   -> **FAILURE**. We are more permissive than
//!                                    Lean somewhere, on a mutation that a real
//!                                    kernel refused. That is the shape an
//!                                    unsoundness has.
//!   ours rejects + Lean accepts   -> counted and printed, never fatal. Read
//!                                    it carefully: measured 2026-08-17, all 32
//!                                    such mutants land inside an `inductive`
//!                                    record, and the replay script
//!                                    deliberately does NOT replay the
//!                                    constructors and recursors an inductive
//!                                    group carries — Lean regenerates them. So
//!                                    Lean's acceptance there is not evidence
//!                                    about the mutated bytes; those positions
//!                                    are simply not delivered to its kernel.
//!                                    This is a limit of the protocol, and it is
//!                                    the reason the count is printed rather
//!                                    than asserted on.
//!   both reject / both accept     -> agreement.
//!
//! Why bytes and not terms: handing each kernel "the same term" through two
//! renderings needs an argument that the renderings agree. Handing them the
//! same *bytes* needs none.
//!
//! Liveness — this suite is worthless unless both channels demonstrably
//! discriminate, so three floors are enforced (`MIN_*`): the unmutated stream
//! must be accepted by both, a minimum number of mutants must draw a genuine
//! `REAL LEAN KERNEL REJECTED` (not a parse error — otherwise the corpus is
//! testing a JSON reader), and a minimum number must be declined by us.
//!
//! And the check is proved able to fail: at the end of the sweep the recorded
//! Lean verdicts are replayed against a deliberately permissive stand-in for our
//! kernel, and the audit must report violations against them.
//!
//! # It has already found one
//!
//! First run, 2026-08-17: **1 violation in 92 mutants.** `Acc.inv`'s proof, with
//! one application argument rewired, was admitted by this kernel and refused by
//! Lean's with `application type mismatch: @Acc Prop`. Every one of ten
//! different values in that argument position was accepted, which is what
//! "never checked" looks like from the outside.
//!
//! The cause was `Kernel::check_core`'s bidirectional fast path
//! (`axeyum-lean-kernel/src/tc.rs`): checking a `Lam` against an expected `Pi`
//! required only `def_eq_core(domain, expected_domain)` and then recursed into
//! the body, bypassing `infer_lambda` and with it the domain's sort check.
//! `def_eq_core` reduces, so an ill-typed domain that BETA-REDUCES to the
//! expected one was erased before anything looked at it. Lean's kernel has no
//! such path. Fixed in the same change; the minimal case is a permanent
//! regression test in
//! `axeyum-lean-kernel/tests/lambda_binder_domain_must_be_a_type.rs`.

use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{Declaration, Kernel, Lean4ExportMetadata, build_logic_prelude};
use serde_json::Value;

#[path = "../../axeyum-lean-kernel/tests/support/lean_probe.rs"]
mod lean_probe;

/// Genuine kernel rejections required. Below this the corpus is exercising a
/// JSON reader, not a type checker, and a clean pass would mean nothing.
const MIN_LEAN_KERNEL_REJECTIONS: usize = 8;
/// Mutants our own admission gates must decline. A kernel that admitted every
/// mutant would also produce zero violations if Lean happened to agree.
const MIN_OURS_DECLINED: usize = 8;
/// Distinct mutants required. A generator that goes blind emits none and every
/// count above reads as a clean result.
const MIN_MUTANTS: usize = 24;

/// The toolchain `lean-toolchain` pins, as elan names its directory.
///
/// A differential against "whatever Lean is installed" is not a differential
/// against the reference implementation. Measured 2026-08-17 on the development
/// host: `lean_probe` sorts elan's toolchains newest-first, v4.34.0-rc1 was
/// present alongside the pinned v4.30.0, and under it
/// `scripts/lean/replay-lean4export.lean` does not even elaborate
/// (`addDeclCore` gained a `USize` parameter). Every verdict in this file would
/// then have been `Malformed`, the corpus would have compared nothing, and the
/// suite would have failed for a reason unrelated to soundness.
fn pinned_lean() -> Option<PathBuf> {
    let requested =
        std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../lean-toolchain"))
            .ok()?;
    let requested = requested.trim().to_owned();
    if let Some(candidate) = lean_probe::lean_bin()
        && version_of(&candidate).is_some_and(|text| text.contains(&pinned_version(&requested)))
    {
        return Some(candidate);
    }
    let root = std::env::var_os("ELAN_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".elan")))?;
    let directory = requested.replace('/', "--").replace(':', "---");
    let candidate = root.join("toolchains").join(directory).join("bin/lean");
    candidate.is_file().then_some(candidate)
}

/// `leanprover/lean4:v4.30.0` -> `version 4.30.0`, as `lean --version` prints it.
fn pinned_version(toolchain: &str) -> String {
    format!(
        "version {}",
        toolchain.rsplit(":v").next().unwrap_or_default()
    )
}

fn version_of(lean: &Path) -> Option<String> {
    let output = Command::new(lean).arg("--version").output().ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).into_owned())
}

fn replay_script() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../scripts/lean/replay-lean4export.lean")
        .canonicalize()
        .expect("the replay script must exist")
}

/// A small self-contained development this kernel checked.
///
/// Deliberately the logic prelude only: it already contributes `Sort`, `Pi`,
/// `bvar`, `app`, `const` and an inductive group, which is every expression
/// record kind the mutator rewires, and it replays in well under a second so a
/// hundred mutants stay affordable.
fn development() -> String {
    let mut kernel = Kernel::new();
    let logic = build_logic_prelude(&mut kernel).expect("logic prelude must build");
    let anonymous = kernel.anon();
    let zero = kernel.level_zero();

    let true_const = kernel.const_(logic.true_, vec![]);
    let trivial = kernel.const_(logic.true_intro, vec![]);
    let first = kernel.name_str(anonymous, "axeyum_wire_trivial");
    kernel
        .add_declaration(Declaration::Theorem {
            name: first,
            uparams: Vec::new(),
            ty: true_const,
            value: trivial,
        })
        .expect("True must be provable");

    let eq = kernel.const_(logic.eq, vec![zero]);
    let goal = kernel.app(eq, true_const);
    let goal = kernel.app(goal, trivial);
    let goal = kernel.app(goal, trivial);
    let refl = kernel.const_(logic.eq_refl, vec![zero]);
    let proof = kernel.app(refl, true_const);
    let proof = kernel.app(proof, trivial);
    let second = kernel.name_str(anonymous, "axeyum_wire_refl");
    kernel
        .add_declaration(Declaration::Theorem {
            name: second,
            uparams: Vec::new(),
            ty: goal,
            value: proof,
        })
        .expect("reflexivity must be provable");

    kernel
        .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
        .expect("the checked development must export")
}

#[derive(Debug, Clone)]
struct Mutant {
    id: String,
    stream: String,
}

/// Positional table sizes as the replay script builds them, line by line.
///
/// Both readers push expression records onto a dense array, so "a valid target"
/// means "an index strictly below the number of expression records seen so far".
/// Keeping every rewired index inside that window is what makes a rejection a
/// *type* rejection rather than an out-of-range parse error.
struct Tables {
    exprs: usize,
    levels: usize,
}

fn record_kind(record: &Value) -> Option<&'static str> {
    for key in ["thm", "def", "opaque", "axiom", "inductive", "quot"] {
        if record.get(key).is_some() {
            return Some(match key {
                "thm" => "thm",
                "def" => "def",
                "opaque" => "opaque",
                "axiom" => "axiom",
                "inductive" => "inductive",
                _ => "quot",
            });
        }
    }
    None
}

/// Rebuild a stream with `line` replaced by `replacement`.
fn respell(lines: &[String], line: usize, replacement: &Value) -> String {
    let mut out = lines.to_vec();
    out[line] = serde_json::to_string(replacement).expect("re-serialize record");
    let mut text = out.join("\n");
    text.push('\n');
    text
}

/// Derive the mutation corpus from the stream itself.
///
/// Nothing here is a hand-written bad stream: each mutation is a rewiring of
/// fields that are already present, to targets that are already valid. The
/// families are the ones a kernel can actually get wrong — a proof attached to
/// the wrong statement, an application whose function and argument swap, a
/// `fun` silently becoming a `forall`, a de Bruijn index off by one, a universe
/// dropped by a level.
#[allow(clippy::too_many_lines)]
fn mutants(base: &str) -> Vec<Mutant> {
    let lines: Vec<String> = base.lines().map(str::to_owned).collect();
    let mut out = Vec::new();
    let mut tables = Tables {
        exprs: 0,
        levels: 1, // `Level.zero` occupies slot 0 before any record is read
    };
    let mut push = |id: String, stream: String| {
        if stream != base {
            out.push(Mutant { id, stream });
        }
    };

    for (index, raw) in lines.iter().enumerate() {
        let Ok(record) = serde_json::from_str::<Value>(raw) else {
            continue;
        };
        if record.get("in").is_some() {
            continue;
        }
        if record.get("il").is_some() {
            // A universe level. Retarget `succ`, which drops a level: the
            // classic way a kernel becomes inconsistent is a universe it does
            // not track.
            if tables.levels >= 2
                && let Some(target) = record.get("succ").and_then(Value::as_u64)
            {
                let mut m = record.clone();
                m["succ"] = Value::from((target + 1) % (tables.levels as u64));
                push(format!("level:{index}:succ"), respell(&lines, index, &m));
            }
            tables.levels += 1;
            continue;
        }
        if record.get("ie").is_some() {
            let here = tables.exprs;
            tables.exprs += 1;
            if here == 0 {
                continue;
            }
            if let Some(app) = record.get("app").cloned() {
                let (f, a) = (
                    app["fn"].as_u64().expect("fn index"),
                    app["arg"].as_u64().expect("arg index"),
                );
                if f != a {
                    let mut m = record.clone();
                    m["app"]["fn"] = Value::from(a);
                    m["app"]["arg"] = Value::from(f);
                    push(format!("expr:{index}:app-swap"), respell(&lines, index, &m));
                }
                let mut m = record.clone();
                m["app"]["arg"] = Value::from((a + 1) % here as u64);
                push(format!("expr:{index}:app-arg"), respell(&lines, index, &m));
                let mut m = record.clone();
                m["app"]["fn"] = Value::from((f + 1) % here as u64);
                push(format!("expr:{index}:app-fn"), respell(&lines, index, &m));
            }
            for binder in ["lam", "forallE"] {
                let Some(node) = record.get(binder).cloned() else {
                    continue;
                };
                let (ty, body) = (
                    node["type"].as_u64().expect("type index"),
                    node["body"].as_u64().expect("body index"),
                );
                if ty != body {
                    let mut m = record.clone();
                    m[binder]["type"] = Value::from(body);
                    m[binder]["body"] = Value::from(ty);
                    push(
                        format!("expr:{index}:{binder}-swap"),
                        respell(&lines, index, &m),
                    );
                }
                // `fun` becomes `forall` and vice versa: the same subterms, a
                // different sort. Nothing structural distinguishes them on the
                // wire, so only a type checker can refuse it.
                let flipped = if binder == "lam" { "forallE" } else { "lam" };
                let mut m = record.clone();
                let object = m.as_object_mut().expect("record is an object");
                let moved = object.remove(binder).expect("binder present");
                object.insert(flipped.to_owned(), moved);
                push(
                    format!("expr:{index}:{binder}-to-{flipped}"),
                    respell(&lines, index, &m),
                );
                let mut m = record.clone();
                m[binder]["type"] = Value::from((ty + 1) % here as u64);
                push(
                    format!("expr:{index}:{binder}-domain"),
                    respell(&lines, index, &m),
                );
            }
            if let Some(bvar) = record.get("bvar").and_then(Value::as_u64) {
                let mut m = record.clone();
                m["bvar"] = Value::from(bvar + 1);
                push(format!("expr:{index}:bvar+1"), respell(&lines, index, &m));
            }
            if let Some(level) = record.get("sort").and_then(Value::as_u64)
                && tables.levels >= 2
            {
                let mut m = record.clone();
                m["sort"] = Value::from((level + 1) % tables.levels as u64);
                push(format!("expr:{index}:sort"), respell(&lines, index, &m));
            }
            if let Some(proj) = record.get("proj").cloned() {
                let mut m = record.clone();
                m["proj"]["idx"] = Value::from(proj["idx"].as_u64().unwrap_or(0) + 1);
                push(format!("expr:{index}:proj-idx"), respell(&lines, index, &m));
            }
            continue;
        }
        // A declaration record: retarget its type and its value. A proof
        // attached to the wrong statement is the archetypal unsoundness, and it
        // is the one shape where "both kernels reject" is the only acceptable
        // answer.
        let Some(kind) = record_kind(&record) else {
            continue;
        };
        if kind == "inductive" || kind == "quot" {
            continue;
        }
        for field in ["type", "value"] {
            let Some(current) = record[kind].get(field).and_then(Value::as_u64) else {
                continue;
            };
            for step in [1_u64, 2, 3, 5, 8] {
                let target = (current + step) % tables.exprs as u64;
                if target == current {
                    continue;
                }
                let mut m = record.clone();
                m[kind][field] = Value::from(target);
                push(
                    format!("decl:{index}:{kind}.{field}->{target}"),
                    respell(&lines, index, &m),
                );
            }
        }
    }
    out
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Theirs {
    /// The real Lean kernel admitted every declaration.
    Accepted,
    /// `addDeclCore` refused a declaration — a genuine type-checking verdict.
    KernelRejected,
    /// The replay script could not read the stream. Still a rejection, but it
    /// is the parser talking, not the kernel, so it is counted separately.
    Malformed,
}

fn ours(stream: &str) -> Result<(), String> {
    import_ndjson(Cursor::new(stream.as_bytes()), ImportLimits::default())
        .map(|_| ())
        .map_err(|error| format!("{error:?}"))
}

fn theirs(lean: &Path, directory: &Path, stream: &str, name: &str) -> (Theirs, String) {
    let file = directory.join(format!("{name}.ndjson"));
    std::fs::write(&file, stream).expect("write mutant stream");
    let output = Command::new(lean)
        .arg("--run")
        .arg(replay_script())
        .arg(&file)
        .output()
        .expect("run the Lean replay script");
    let report = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let verdict = if output.status.success() {
        Theirs::Accepted
    } else if report.contains("REAL LEAN KERNEL REJECTED") {
        Theirs::KernelRejected
    } else {
        Theirs::Malformed
    };
    (verdict, report)
}

/// The soundness question, as one pure function so it can be driven to failure.
///
/// A violation is *our* kernel admitting a stream the real Lean kernel would
/// not. Nothing else is a violation: us being stricter is incompleteness, and
/// both refusing is agreement.
fn violation(id: &str, ours_admitted: bool, theirs: Theirs) -> Option<String> {
    (ours_admitted && theirs != Theirs::Accepted).then(|| {
        format!(
            "{id}: OUR kernel admitted a stream the real Lean kernel {}. \
             We are more permissive than Lean here.",
            match theirs {
                Theirs::KernelRejected => "type-checked and REFUSED",
                Theirs::Malformed => "could not even read",
                Theirs::Accepted => unreachable!(),
            }
        )
    })
}

fn budget() -> usize {
    std::env::var("AXEYUM_WIRE_MUTANTS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(96)
}

// The differential is one measurement: build the mutants, run BOTH kernels over
// the identical bytes, and classify every disagreement in one place. Splitting
// it would put the two verdicts and the classification in separate scopes,
// which is precisely where a differential stops being a differential.
#[allow(clippy::too_many_lines)]
#[test]
fn our_kernel_admits_nothing_the_real_lean_kernel_refuses() {
    let base = development();
    let all = mutants(&base);
    assert!(
        all.len() >= MIN_MUTANTS,
        "the mutator produced {} mutants (floor {MIN_MUTANTS}); a corpus that \
         shrinks to nothing makes every count below it a clean lie",
        all.len()
    );
    for mutant in &all {
        assert_ne!(mutant.stream, base, "{} changed no bytes", mutant.id);
    }

    // Deterministic thinning: a stride, never a shuffle, so a failure names a
    // mutant that the next run also produces.
    let stride = all.len().div_ceil(budget()).max(1);
    let corpus: Vec<&Mutant> = all.iter().step_by(stride).collect();

    let Some(lean) = pinned_lean() else {
        assert!(
            !lean_probe::lean_required(),
            "AXEYUM_REQUIRE_LEAN=1 but the toolchain `lean-toolchain` pins is not \
             installed.\n{}",
            lean_probe::discovery_report()
        );
        println!(
            "{} wire-differential not_checked={} reason=pinned-toolchain-missing\n{}",
            lean_probe::SKIPPED_MARKER,
            corpus.len() + 1,
            lean_probe::discovery_report()
        );
        return;
    };
    let version = version_of(&lean).expect("the located lean must report a version");
    assert!(
        version.contains("version 4.30.0"),
        "this differential is only meaningful against the pinned reference \
         implementation; got: {version}"
    );
    let directory = std::env::temp_dir().join(format!("axeyum_wire_diff_{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("create mutant directory");

    // Liveness, first: both channels must accept the undamaged development, or
    // "everything was rejected" would read as agreement.
    assert_eq!(ours(&base), Ok(()), "our own export must re-import");
    let (verdict, report) = theirs(&lean, &directory, &base, "base");
    assert_eq!(
        verdict,
        Theirs::Accepted,
        "the real Lean kernel rejected the undamaged development:\n{report}"
    );

    let mut violations = Vec::new();
    let mut kernel_rejections = 0_usize;
    let mut malformed = 0_usize;
    let mut ours_declined = 0_usize;
    let mut stricter_than_lean = Vec::new();
    let mut recorded = Vec::new();

    for (position, mutant) in corpus.iter().enumerate() {
        let admitted = ours(&mutant.stream).is_ok();
        let (verdict, report) = theirs(&lean, &directory, &mutant.stream, &format!("m{position}"));
        recorded.push((mutant.id.clone(), verdict));
        if !admitted {
            ours_declined += 1;
        }
        match verdict {
            Theirs::KernelRejected => kernel_rejections += 1,
            Theirs::Malformed => malformed += 1,
            Theirs::Accepted => {
                if !admitted {
                    stricter_than_lean.push(mutant.id.clone());
                }
            }
        }
        if let Some(found) = violation(&mutant.id, admitted, verdict) {
            // A violation nobody can reproduce is an anecdote. Keep the exact
            // bytes both kernels saw, and name the file in the failure.
            let kept = directory.join(format!("violation_{}.ndjson", violations.len()));
            std::fs::write(&kept, &mutant.stream).expect("keep the violating stream");
            violations.push(format!(
                "{found}\n  reproduce: lean --run {} {}\n--- lean said ---\n{report}",
                replay_script().display(),
                kept.display()
            ));
        }
    }

    println!(
        "WIRE_DIFFERENTIAL|generated={}|checked={}|lean_kernel_rejected={}|lean_malformed={}|\
         lean_accepted={}|ours_declined={}|stricter_than_lean={}|violations={}",
        all.len(),
        corpus.len(),
        kernel_rejections,
        malformed,
        corpus.len() - kernel_rejections - malformed,
        ours_declined,
        stricter_than_lean.len(),
        violations.len()
    );
    if !stricter_than_lean.is_empty() {
        println!("  stricter than Lean (incompleteness, not unsoundness): {stricter_than_lean:?}");
    }

    assert!(
        kernel_rejections >= MIN_LEAN_KERNEL_REJECTIONS,
        "only {kernel_rejections} mutants reached a real Lean KERNEL rejection \
         (floor {MIN_LEAN_KERNEL_REJECTIONS}); the rest were refused by the \
         reader, so this run compared JSON parsers, not type checkers"
    );
    assert!(
        ours_declined >= MIN_OURS_DECLINED,
        "our kernel declined only {ours_declined} of {} mutants (floor \
         {MIN_OURS_DECLINED}); a kernel that admits everything produces no \
         violations whenever Lean happens to agree",
        corpus.len()
    );
    assert!(
        violations.is_empty(),
        "OUR KERNEL IS MORE PERMISSIVE THAN LEAN'S on {} of {} mutants:\n{}",
        violations.len(),
        corpus.len(),
        violations.join("\n\n")
    );

    // Prove the comparison can fail, using THIS run's real Lean verdicts: swap
    // our kernel for a stand-in that admits everything and require the audit to
    // report it. Without this the assertion above is a checker that never fires.
    let permissive: Vec<String> = recorded
        .iter()
        .filter_map(|(id, verdict)| violation(id, true, *verdict))
        .collect();
    assert!(
        !permissive.is_empty(),
        "a kernel that admitted every mutant would have produced ZERO \
         violations against these Lean verdicts, so the check above proves \
         nothing about this run"
    );

    lean_probe::report_checked("wire-differential", corpus.len() + 1);
}

#[test]
fn the_audit_reports_a_more_permissive_kernel_and_nothing_else() {
    assert!(violation("m", true, Theirs::KernelRejected).is_some());
    assert!(violation("m", true, Theirs::Malformed).is_some());
    assert!(violation("m", true, Theirs::Accepted).is_none());
    // Stricter than Lean is incompleteness. If this ever became a violation the
    // suite would fail on correctness rather than on unsoundness.
    assert!(violation("m", false, Theirs::KernelRejected).is_none());
    assert!(violation("m", false, Theirs::Accepted).is_none());
}

#[test]
fn the_mutator_is_derived_from_the_stream_and_changes_bytes() {
    let base = development();
    let all = mutants(&base);
    assert!(all.len() >= MIN_MUTANTS, "generated {}", all.len());
    let mut ids: Vec<&str> = all.iter().map(|m| m.id.as_str()).collect();
    ids.sort_unstable();
    let before = ids.len();
    ids.dedup();
    assert_eq!(before, ids.len(), "mutant ids must be unique");
    for mutant in &all {
        assert_ne!(mutant.stream, base);
        assert_eq!(
            mutant.stream.lines().count(),
            base.lines().count(),
            "{}: a mutation may only rewire a record, never add or drop one",
            mutant.id
        );
    }
    // Every family the mutator claims must actually appear, or a silently
    // broken branch reads as "no such construct in this development".
    for family in ["app-swap", "app-fn", "lam-to-forallE", "bvar+1", ".value->"] {
        assert!(
            all.iter().any(|m| m.id.contains(family)),
            "no {family} mutant was generated"
        );
    }
}
