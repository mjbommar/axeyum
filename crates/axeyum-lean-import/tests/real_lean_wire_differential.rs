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
//!           implicit-argument inference, no coercions, no `Init` — and then
//!           compares every constructor and recursor the record carried against
//!           the ones Lean's kernel generated for itself.
//!
//! The asymmetry is the whole point and is enforced asymmetrically:
//!
//!   ours accepts + Lean rejects   -> **FAILURE**. We are more permissive than
//!                                    Lean somewhere, on a mutation that a real
//!                                    kernel refused. That is the shape an
//!                                    unsoundness has.
//!   ours rejects + Lean accepts   -> counted and printed, never fatal. This is
//!                                    incompleteness, not unsoundness.
//!   both reject / both accept     -> agreement.
//!
//! Why bytes and not terms: handing each kernel "the same term" through two
//! renderings needs an argument that the renderings agree. Handing them the
//! same *bytes* needs none.
//!
//! Liveness — this suite is worthless unless both channels demonstrably
//! discriminate, so four floors are enforced (`MIN_*`): the unmutated stream
//! must be accepted by both, a minimum number of mutants must draw a genuine
//! `addDeclCore` rejection (not a parse error — otherwise the corpus is testing
//! a JSON reader), a minimum number must draw a *regeneration* mismatch (the
//! channel added on 2026-08-18, below), and a minimum number must be declined
//! by us.
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
//!
//! # The blind spot that made 32 mutants meaningless, and how it was closed
//!
//! That first run also printed 32 mutants as "ours declined, Lean accepted".
//! Read literally that is incompleteness; read honestly it was **Lean accepting
//! bytes it never read**. Measured on this development: 225 of 603 expression
//! records — 37% of the stream — are reachable only from a recursor type or an
//! ι-reduction rule, and `addDeclCore` is handed neither. It receives an
//! `inductDecl` (families and constructor types) and *derives* the recursors,
//! so damaging a recursor-only expression changed nothing it looked at. All 32
//! were exactly that.
//!
//! The old comment said a later declaration mentioning the recursor would catch
//! it. That is only true when such a declaration exists, and in a development
//! this size it does not — so the claim was unfalsifiable, which is the failure
//! mode this repository is built to refuse.
//!
//! It is closed, not documented around: `scripts/lean/replay-lean4export.lean`
//! now looks every carried family, constructor and recursor up in the
//! environment Lean just built and compares it field by field against Lean's
//! own regeneration — arities, `cidx`, `k`, the ι-rules, and the types up to
//! universe-parameter *position* and binder names, falling back to
//! `Kernel.isDefEqGuarded`. That mirrors our importer's own
//! `validate_generated_recursor`, which compares the exported recursor against
//! the one our kernel derived with `def_eq`; putting both sides on the same
//! criterion is what stops a defeq-but-not-syntactic mutant from being reported
//! as a violation it is not. A disagreement is its own verdict
//! ([`Theirs::RegenerationMismatch`]) with its own liveness floor, so it can
//! never be confused with `addDeclCore` speaking.
//!
//! `isReflexive` is deliberately excluded from that comparison: our importer
//! reads it and discards it as descriptive metadata, Lean's kernel derives its
//! own, and neither would act on a difference. Comparing it would manufacture a
//! violation.
//!
//! # What the widened corpus found: eight more violations
//!
//! Run 2026-08-18 with the families below and the regeneration channel live:
//! **8 violations in 134 mutants across 51 families**, and `stricter_than_lean`
//! fell from 32 to 1. They were two defects, each reached several ways:
//!
//! * **Universe closure (5).** `decl.universe-param`, `level.param` and
//!   `level.succ` each leave a declaration whose type or value mentions a
//!   universe parameter its `levelParams` does not bind. Lean refused every one
//!   (`invalid reference to undefined universe level parameter 'u'`); we
//!   admitted every one. `Kernel::check_declaration` ran two *relative* checks
//!   — the type infers to a `Sort`, the value's type is def-eq to it — and both
//!   hold just as well with a free `u` on both sides, so the binding list was
//!   decorative. The inductive gate needed the same fix separately, because it
//!   type-checks its group itself and never routes through
//!   `check_declaration`; that was the one violation the first fix left behind.
//!   Regression:
//!   `axeyum-lean-kernel/tests/declaration_universe_params_must_be_bound.rs`.
//! * **The recursor `k` flag (3).** `ind.rec-k` flips the K-like flag. Our
//!   importer compared every other recursor field against the one this kernel
//!   generated and read `k` only to reject it on nested and mutual groups. `k`
//!   licenses ι-reducing a recursor application whose major premise is not a
//!   constructor, so it is not descriptive. Regression:
//!   `recursor_k_flag_is_validated.rs`.
//!
//! The single remaining "stricter than Lean" mutant is understood, which is the
//! whole difference from the 32 it replaced: `expr.const-name` rewrites `Or.inl`
//! to `Or.inr` inside `Or.rec`'s type. Both are proofs of the same `Prop`, so
//! Lean's `isDefEq` closes the gap by definitional proof irrelevance — its
//! inference is unchecked, so it types the ill-typed side anyway — while our
//! `def_eq` cannot infer a type for it and declines. That is incompleteness in
//! the safe direction, stated rather than counted.

use std::collections::BTreeMap;
use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_lean_import::{ImportLimits, import_ndjson};
use axeyum_lean_kernel::{
    BinderInfo, Declaration, Kernel, Lean4ExportMetadata, ReducibilityHint, build_logic_prelude,
};
use serde_json::Value;

#[path = "../../axeyum-lean-kernel/tests/support/lean_probe.rs"]
mod lean_probe;

/// Genuine `addDeclCore` rejections required. Below this the corpus is
/// exercising a JSON reader, not a type checker, and a clean pass would mean
/// nothing.
const MIN_LEAN_KERNEL_REJECTIONS: usize = 8;
/// Genuine *regeneration* mismatches required. This is the channel that makes
/// the recursor half of the stream visible to Lean at all; if it stops firing,
/// 37% of the expression records silently go back to being unread and every
/// count below reads as a clean result.
const MIN_REGENERATION_MISMATCHES: usize = 4;
/// Mutants our own admission gates must decline. A kernel that admitted every
/// mutant would also produce zero violations if Lean happened to agree.
const MIN_OURS_DECLINED: usize = 8;
/// Distinct mutants required. A generator that goes blind emits none and every
/// count above reads as a clean result.
const MIN_MUTANTS: usize = 24;
/// Distinct mutation families required. The corpus is stratified by family, so
/// a family that stops generating quietly removes a whole class of damage from
/// the sweep without changing the mutant count much.
const MIN_FAMILIES: usize = 32;

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
/// The logic prelude is the spine: it already contributes `Sort`, `Pi`, `bvar`,
/// `app`, `const` and ten inductive groups, and it replays in well under a
/// second so a large corpus stays affordable. Five declarations are added on
/// top for the sole purpose of putting the remaining wire constructs on the
/// stream — a mutation family whose construct never appears is a branch that
/// silently generates nothing, which is this repository's signature failure:
///
/// * `axeyum_wire_let` puts a `letE` record on the wire (a type, a value and a
///   body a kernel must keep in agreement — nothing else here emits one),
/// * `axeyum_wire_proj` puts a `proj` record on it,
/// * `axeyum_wire_max` / `axeyum_wire_imax` put `max` and `imax` universe
///   records on it. The logic prelude alone emits exactly one `succ` and three
///   `param` levels, so every universe family but one was dead.
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

    // `def axeyum_wire_let : True := let t : True := True.intro; t`
    let bound_name = kernel.name_str(anonymous, "t");
    let bound = kernel.bvar(0);
    let let_term = kernel.let_(bound_name, true_const, trivial, bound);
    let third = kernel.name_str(anonymous, "axeyum_wire_let");
    kernel
        .add_declaration(Declaration::Definition {
            name: third,
            uparams: Vec::new(),
            ty: true_const,
            value: let_term,
            hint: ReducibilityHint::Regular(1),
        })
        .expect("a let-bound True must check");

    // `def axeyum_wire_proj : And True True -> True := fun h => h.1`
    let and = kernel.const_(logic.and, vec![]);
    let conjunction = kernel.app(and, true_const);
    let conjunction = kernel.app(conjunction, true_const);
    let hypothesis = kernel.name_str(anonymous, "h");
    let subject = kernel.bvar(0);
    let projected = kernel.proj(logic.and, 0, subject);
    let value = kernel.lam(hypothesis, conjunction, projected, BinderInfo::Default);
    let ty = kernel.pi(hypothesis, conjunction, true_const, BinderInfo::Default);
    let fourth = kernel.name_str(anonymous, "axeyum_wire_proj");
    kernel
        .add_declaration(Declaration::Definition {
            name: fourth,
            uparams: Vec::new(),
            ty,
            value,
            hint: ReducibilityHint::Regular(1),
        })
        .expect("the first projection of a conjunction must check");

    // `def axeyum_wire_max.{u,v} : Sort (max u v) -> Sort (max u v) := fun x => x`
    // and the same at `imax`.
    let first_universe = kernel.name_str(anonymous, "u");
    let second_universe = kernel.name_str(anonymous, "v");
    let level_u = kernel.level_param(first_universe);
    let level_v = kernel.level_param(second_universe);
    let maximum = kernel.level_max(level_u, level_v);
    let impredicative = kernel.level_imax(level_u, level_v);
    for (label, level) in [
        ("axeyum_wire_max", maximum),
        ("axeyum_wire_imax", impredicative),
    ] {
        let sort = kernel.sort(level);
        let binder = kernel.name_str(anonymous, "x");
        let body = kernel.bvar(0);
        let value = kernel.lam(binder, sort, body, BinderInfo::Default);
        let ty = kernel.pi(binder, sort, sort, BinderInfo::Default);
        let name = kernel.name_str(anonymous, label);
        kernel
            .add_declaration(Declaration::Definition {
                name,
                uparams: vec![first_universe, second_universe],
                ty,
                value,
                hint: ReducibilityHint::Regular(1),
            })
            .expect("the identity on a universe-polymorphic Sort must check");
    }

    kernel
        .render_lean4export_ndjson(&Lean4ExportMetadata::axeyum("4.30.0"))
        .expect("the checked development must export")
}

/// One damaged stream, tagged with the family that produced it.
///
/// The family is carried rather than parsed back out of the id, because the
/// corpus is *stratified by family*: a family that stops generating must show
/// up as a missing family, not as a slightly smaller mutant count.
#[derive(Debug, Clone)]
struct Mutant {
    id: String,
    family: String,
    stream: String,
}

/// The stream as an indexable object.
///
/// Both readers push name, level and expression records onto dense arrays, so
/// "a valid target" means "an index strictly below the number of records of
/// that kind seen so far". Keeping every rewired index inside that window is
/// what makes a rejection a *type* rejection rather than an out-of-range parse
/// error.
struct Wire {
    base: String,
    lines: Vec<String>,
    records: Vec<Option<Value>>,
    /// The line that defines each expression index.
    expr_line: Vec<usize>,
    /// Table sizes visible to each line, i.e. the legal retarget windows.
    names_before: Vec<usize>,
    levels_before: Vec<usize>,
    exprs_before: Vec<usize>,
}

impl Wire {
    fn read(base: &str) -> Self {
        let lines: Vec<String> = base.lines().map(str::to_owned).collect();
        let records: Vec<Option<Value>> = lines
            .iter()
            .map(|line| serde_json::from_str(line).ok())
            .collect();
        // `Name.anonymous` occupies name slot 0 and `Level.zero` level slot 0
        // before any record is read; the expression table starts empty.
        let (mut names, mut levels, mut exprs) = (1_usize, 1_usize, 0_usize);
        let mut expr_line = Vec::new();
        let mut names_before = Vec::with_capacity(lines.len());
        let mut levels_before = Vec::with_capacity(lines.len());
        let mut exprs_before = Vec::with_capacity(lines.len());
        for (index, record) in records.iter().enumerate() {
            names_before.push(names);
            levels_before.push(levels);
            exprs_before.push(exprs);
            let Some(record) = record else { continue };
            if record.get("in").is_some() {
                names += 1;
            } else if record.get("il").is_some() {
                levels += 1;
            } else if record.get("ie").is_some() {
                expr_line.push(index);
                exprs += 1;
            }
        }
        Self {
            base: base.to_owned(),
            lines,
            records,
            expr_line,
            names_before,
            levels_before,
            exprs_before,
        }
    }

    /// Rebuild the stream with every `(line, record)` in `edits` replaced.
    ///
    /// A list, not a single line: binder-order permutation is only expressible
    /// as a simultaneous edit of two records, and a mutator that can only touch
    /// one line cannot generate it.
    fn respell(&self, edits: &[(usize, Value)]) -> String {
        let mut out = self.lines.clone();
        for (line, replacement) in edits {
            out[*line] = serde_json::to_string(replacement).expect("re-serialize record");
        }
        let mut text = out.join("\n");
        text.push('\n');
        text
    }
}

/// Retarget `current` by `step` inside a dense table of `size` entries.
///
/// `None` when the table is too small to offer a different target, which is the
/// only honest answer — wrapping onto the value already there is not a mutation.
fn retarget(current: u64, step: u64, size: usize) -> Option<u64> {
    if size == 0 {
        return None;
    }
    let target = (current + step) % size as u64;
    (target != current).then_some(target)
}

fn emit(wire: &Wire, out: &mut Vec<Mutant>, family: &str, detail: &str, edits: &[(usize, Value)]) {
    let stream = wire.respell(edits);
    if stream == wire.base {
        return;
    }
    let line = edits.first().map_or(0, |(line, _)| *line);
    out.push(Mutant {
        id: format!("{family}:{line}:{detail}"),
        family: family.to_owned(),
        stream,
    });
}

/// Derive the mutation corpus from the stream itself.
///
/// Nothing here is a hand-written bad stream: each mutation is a rewiring of
/// fields that are already present, to targets that are already valid. The
/// families are the ones a kernel can actually get wrong.
///
/// Not generated, deliberately: **name** records. Retargeting a name's parent
/// or text renames a constant consistently — every later reference is by table
/// index, so both kernels build the same development under a different
/// spelling and agree. It is a mutation that cannot discriminate.
#[allow(clippy::too_many_lines)]
fn mutants(base: &str) -> Vec<Mutant> {
    let wire = Wire::read(base);
    let mut out = Vec::new();

    for (index, record) in wire.records.iter().enumerate() {
        let Some(record) = record else { continue };
        if record.get("in").is_some() {
            continue;
        }
        if record.get("il").is_some() {
            level_mutants(&wire, &mut out, index, record);
            continue;
        }
        if record.get("ie").is_some() {
            expression_mutants(&wire, &mut out, index, record);
            continue;
        }
        if record.get("inductive").is_some() {
            inductive_mutants(&wire, &mut out, index, record);
            continue;
        }
        declaration_mutants(&wire, &mut out, index, record);
    }
    out
}

/// Universe levels: the classic way a kernel becomes inconsistent is a universe
/// it does not track.
fn level_mutants(wire: &Wire, out: &mut Vec<Mutant>, index: usize, record: &Value) {
    let table = wire.levels_before[index];
    if let Some(target) = record.get("succ").and_then(Value::as_u64)
        && let Some(next) = retarget(target, 1, table)
    {
        let mut m = record.clone();
        m["succ"] = Value::from(next);
        emit(wire, out, "level.succ", "+1", &[(index, m)]);
    }
    if let Some(name) = record.get("param").and_then(Value::as_u64)
        && let Some(next) = retarget(name, 1, wire.names_before[index])
    {
        // A universe parameter that names something the declaration does not
        // bind. Nothing structural distinguishes it; only scoping does.
        let mut m = record.clone();
        m["param"] = Value::from(next);
        emit(wire, out, "level.param", "rename", &[(index, m)]);
    }
    for kind in ["max", "imax"] {
        let Some(pair) = record.get(kind).and_then(Value::as_array).cloned() else {
            continue;
        };
        if pair.len() != 2 {
            continue;
        }
        let (left, right) = (pair[0].clone(), pair[1].clone());
        if left != right {
            let mut m = record.clone();
            m[kind] = Value::from(vec![right.clone(), left.clone()]);
            emit(wire, out, "level.max-swap", kind, &[(index, m)]);
        }
        // `max u v` and `imax u v` differ exactly when `v` can be zero, which
        // is the impredicativity of `Prop`. Only a level checker refuses this.
        let flipped = if kind == "max" { "imax" } else { "max" };
        let mut m = record.clone();
        let object = m.as_object_mut().expect("record is an object");
        let moved = object.remove(kind).expect("level present");
        object.insert(flipped.to_owned(), moved);
        emit(
            wire,
            out,
            "level.max-kind",
            &format!("{kind}-to-{flipped}"),
            &[(index, m)],
        );
        if let Some(current) = left.as_u64()
            && let Some(next) = retarget(current, 1, wire.levels_before[index])
        {
            let mut m = record.clone();
            m[kind][0] = Value::from(next);
            emit(wire, out, "level.max-operand", kind, &[(index, m)]);
        }
    }
}

#[allow(clippy::too_many_lines)]
fn expression_mutants(wire: &Wire, out: &mut Vec<Mutant>, index: usize, record: &Value) {
    let here = wire.exprs_before[index];
    if here == 0 {
        return;
    }
    if let Some(app) = record.get("app").cloned() {
        let (function, argument) = (
            app["fn"].as_u64().expect("fn index"),
            app["arg"].as_u64().expect("arg index"),
        );
        if function != argument {
            let mut m = record.clone();
            m["app"]["fn"] = Value::from(argument);
            m["app"]["arg"] = Value::from(function);
            emit(wire, out, "expr.app-swap", "swap", &[(index, m)]);
        }
        for step in [1_u64, 3] {
            if let Some(next) = retarget(argument, step, here) {
                let mut m = record.clone();
                m["app"]["arg"] = Value::from(next);
                emit(
                    wire,
                    out,
                    "expr.app-arg",
                    &format!("+{step}"),
                    &[(index, m)],
                );
            }
            if let Some(next) = retarget(function, step, here) {
                let mut m = record.clone();
                m["app"]["fn"] = Value::from(next);
                emit(wire, out, "expr.app-fn", &format!("+{step}"), &[(index, m)]);
            }
        }
    }
    for binder in ["lam", "forallE"] {
        let Some(node) = record.get(binder).cloned() else {
            continue;
        };
        let (domain, body) = (
            node["type"].as_u64().expect("type index"),
            node["body"].as_u64().expect("body index"),
        );
        if domain != body {
            let mut m = record.clone();
            m[binder]["type"] = Value::from(body);
            m[binder]["body"] = Value::from(domain);
            emit(wire, out, "expr.binder-swap", binder, &[(index, m)]);
        }
        // `fun` becomes `forall` and vice versa: the same subterms, a different
        // sort. Nothing structural distinguishes them on the wire, so only a
        // type checker can refuse it.
        let flipped = if binder == "lam" { "forallE" } else { "lam" };
        let mut m = record.clone();
        let object = m.as_object_mut().expect("record is an object");
        let moved = object.remove(binder).expect("binder present");
        object.insert(flipped.to_owned(), moved);
        emit(
            wire,
            out,
            "expr.binder-kind",
            &format!("{binder}-to-{flipped}"),
            &[(index, m)],
        );
        if let Some(next) = retarget(domain, 1, here) {
            let mut m = record.clone();
            m[binder]["type"] = Value::from(next);
            emit(wire, out, "expr.binder-domain", binder, &[(index, m)]);
        }
        if let Some(next) = retarget(body, 1, here) {
            let mut m = record.clone();
            m[binder]["body"] = Value::from(next);
            emit(wire, out, "expr.binder-body", binder, &[(index, m)]);
        }
        // Binder info is elaborator metadata that neither kernel type-checks,
        // so this family is expected to draw agreement on both sides. It earns
        // its place by proving that: a suite where every family disagrees is
        // one where the two kernels are being compared on the wrong axis.
        let current = node["binderInfo"].as_str().unwrap_or("default");
        let next = if current == "default" {
            "instImplicit"
        } else {
            "default"
        };
        let mut m = record.clone();
        m[binder]["binderInfo"] = Value::from(next);
        emit(wire, out, "expr.binder-info", binder, &[(index, m)]);

        // Binder ORDER: when this binder's body is itself a binder, exchange
        // the two domains. Every index stays in range and both records stay
        // well formed, but the de Bruijn numbering underneath now refers to the
        // wrong binder — the mutation a positional calculus is most exposed to,
        // and the only one here that needs two records changed at once.
        let inner_line = wire.expr_line[usize::try_from(body).expect("expression index fits")];
        let Some(inner) = wire.records[inner_line].clone() else {
            continue;
        };
        for inner_binder in ["lam", "forallE"] {
            let Some(inner_node) = inner.get(inner_binder).cloned() else {
                continue;
            };
            let inner_domain = inner_node["type"].as_u64().expect("type index");
            if inner_domain == domain {
                continue;
            }
            let mut outer = record.clone();
            outer[binder]["type"] = Value::from(inner_domain);
            let mut nested = inner.clone();
            nested[inner_binder]["type"] = Value::from(domain);
            emit(
                wire,
                out,
                "expr.binder-order",
                binder,
                &[(index, outer), (inner_line, nested)],
            );
        }
    }
    if let Some(bvar) = record.get("bvar").and_then(Value::as_u64) {
        let mut m = record.clone();
        m["bvar"] = Value::from(bvar + 1);
        emit(wire, out, "expr.bvar-up", "+1", &[(index, m)]);
        if bvar != 0 {
            let mut m = record.clone();
            m["bvar"] = Value::from(0_u64);
            emit(wire, out, "expr.bvar-zero", "0", &[(index, m)]);
        }
    }
    if let Some(level) = record.get("sort").and_then(Value::as_u64)
        && let Some(next) = retarget(level, 1, wire.levels_before[index])
    {
        let mut m = record.clone();
        m["sort"] = Value::from(next);
        emit(wire, out, "expr.sort", "+1", &[(index, m)]);
    }
    if let Some(constant) = record.get("const").cloned() {
        let name = constant["name"].as_u64().expect("name index");
        if let Some(next) = retarget(name, 1, wire.names_before[index]) {
            let mut m = record.clone();
            m["const"]["name"] = Value::from(next);
            emit(wire, out, "expr.const-name", "+1", &[(index, m)]);
        }
        let universes = constant["us"].as_array().cloned().unwrap_or_default();
        if let Some(first) = universes.first().and_then(Value::as_u64)
            && let Some(next) = retarget(first, 1, wire.levels_before[index])
        {
            let mut m = record.clone();
            m["const"]["us"][0] = Value::from(next);
            emit(wire, out, "expr.const-universe", "+1", &[(index, m)]);
        }
        // One universe argument too many: the constant's universe arity is
        // fixed by its declaration and nothing on the wire restates it.
        let mut widened = universes.clone();
        widened.push(Value::from(0_u64));
        let mut m = record.clone();
        m["const"]["us"] = Value::from(widened);
        emit(wire, out, "expr.const-arity", "extra", &[(index, m)]);
    }
    if let Some(proj) = record.get("proj").cloned() {
        let mut m = record.clone();
        m["proj"]["idx"] = Value::from(proj["idx"].as_u64().unwrap_or(0) + 1);
        emit(wire, out, "expr.proj-index", "+1", &[(index, m)]);
        if let Some(structure) = proj["struct"].as_u64()
            && let Some(next) = retarget(structure, 1, here)
        {
            let mut m = record.clone();
            m["proj"]["struct"] = Value::from(next);
            emit(wire, out, "expr.proj-struct", "+1", &[(index, m)]);
        }
        if let Some(type_name) = proj["typeName"].as_u64()
            && let Some(next) = retarget(type_name, 1, wire.names_before[index])
        {
            let mut m = record.clone();
            m["proj"]["typeName"] = Value::from(next);
            emit(wire, out, "expr.proj-type", "+1", &[(index, m)]);
        }
    }
    if let Some(binding) = record.get("letE").cloned() {
        let (ty, value, body) = (
            binding["type"].as_u64().expect("type index"),
            binding["value"].as_u64().expect("value index"),
            binding["body"].as_u64().expect("body index"),
        );
        for (field, current, family) in [
            ("type", ty, "expr.let-type"),
            ("value", value, "expr.let-value"),
            ("body", body, "expr.let-body"),
        ] {
            if let Some(next) = retarget(current, 1, here) {
                let mut m = record.clone();
                m["letE"][field] = Value::from(next);
                emit(wire, out, family, "+1", &[(index, m)]);
            }
        }
        // The ascribed type and the bound value trade places: a `let` is the
        // one former where a kernel checks one subterm *against* another, and
        // the swap is well formed whenever both are expressions.
        if ty != value {
            let mut m = record.clone();
            m["letE"]["type"] = Value::from(value);
            m["letE"]["value"] = Value::from(ty);
            emit(wire, out, "expr.let-type-value-swap", "swap", &[(index, m)]);
        }
    }
}

/// A proof attached to the wrong statement is the archetypal unsoundness, and
/// it is the one shape where "both kernels reject" is the only acceptable
/// answer.
fn declaration_mutants(wire: &Wire, out: &mut Vec<Mutant>, index: usize, record: &Value) {
    let Some(kind) = ["thm", "def", "opaque", "axiom"]
        .into_iter()
        .find(|key| record.get(*key).is_some())
    else {
        return;
    };
    let exprs = wire.exprs_before[index];
    for (field, family) in [("type", "decl.type"), ("value", "decl.value")] {
        let Some(current) = record[kind].get(field).and_then(Value::as_u64) else {
            continue;
        };
        for step in [1_u64, 2, 3, 5, 8] {
            let Some(target) = retarget(current, step, exprs) else {
                continue;
            };
            let mut m = record.clone();
            m[kind][field] = Value::from(target);
            emit(
                wire,
                out,
                family,
                &format!("{kind}->{target}"),
                &[(index, m)],
            );
        }
    }
    // A universe parameter renamed at the binding site: the body still mentions
    // the old one, which is now free. Lengths are preserved, so the arity of
    // every `const` reference to this declaration stays right.
    if let Some(uparams) = record[kind].get("levelParams").and_then(Value::as_array)
        && let Some(first) = uparams.first().and_then(Value::as_u64)
        && let Some(next) = retarget(first, 1, wire.names_before[index])
    {
        let mut m = record.clone();
        m[kind]["levelParams"][0] = Value::from(next);
        emit(wire, out, "decl.universe-param", kind, &[(index, m)]);
    }
}

/// The `inductive` record: previously skipped whole, and it is the largest
/// record on the wire.
///
/// These only became meaningful on 2026-08-18, when the replay script started
/// comparing the carried constructors and recursors against Lean's own
/// regeneration. Before that, `addDeclCore` received the families and
/// constructor types and derived everything else, so most of what follows was
/// damage no reference implementation ever looked at.
#[allow(clippy::too_many_lines)]
fn inductive_mutants(wire: &Wire, out: &mut Vec<Mutant>, index: usize, record: &Value) {
    let exprs = wire.exprs_before[index];
    let names = wire.names_before[index];
    let group = record["inductive"].clone();

    for (position, family) in group["types"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .enumerate()
    {
        if let Some(current) = family["type"].as_u64()
            && let Some(next) = retarget(current, 1, exprs)
        {
            let mut m = record.clone();
            m["inductive"]["types"][position]["type"] = Value::from(next);
            emit(
                wire,
                out,
                "ind.family-type",
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
        for (field, family_name) in [
            ("numParams", "ind.family-num-params"),
            ("numIndices", "ind.family-num-indices"),
            ("numNested", "ind.family-num-nested"),
        ] {
            let current = family[field].as_u64().unwrap_or(0);
            for next in [current + 1, current.saturating_sub(1)] {
                if next == current {
                    continue;
                }
                let mut m = record.clone();
                m["inductive"]["types"][position][field] = Value::from(next);
                emit(
                    wire,
                    out,
                    family_name,
                    &format!("{position}:{current}->{next}"),
                    &[(index, m)],
                );
            }
        }
        let is_recursive = family["isRec"].as_bool().unwrap_or(false);
        let mut m = record.clone();
        m["inductive"]["types"][position]["isRec"] = Value::from(!is_recursive);
        emit(
            wire,
            out,
            "ind.family-is-rec",
            &format!("{position}flip"),
            &[(index, m)],
        );
        if let Some(first) = family["ctors"]
            .as_array()
            .and_then(|list| list.first())
            .and_then(Value::as_u64)
            && let Some(next) = retarget(first, 1, names)
        {
            let mut m = record.clone();
            m["inductive"]["types"][position]["ctors"][0] = Value::from(next);
            emit(
                wire,
                out,
                "ind.family-ctors",
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
    }

    for (position, constructor) in group["ctors"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .enumerate()
    {
        if let Some(current) = constructor["type"].as_u64()
            && let Some(next) = retarget(current, 1, exprs)
        {
            let mut m = record.clone();
            m["inductive"]["ctors"][position]["type"] = Value::from(next);
            emit(
                wire,
                out,
                "ind.ctor-type",
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
        for (field, family_name) in [
            ("cidx", "ind.ctor-cidx"),
            ("numFields", "ind.ctor-num-fields"),
            ("numParams", "ind.ctor-num-params"),
        ] {
            let current = constructor[field].as_u64().unwrap_or(0);
            let mut m = record.clone();
            m["inductive"]["ctors"][position][field] = Value::from(current + 1);
            emit(
                wire,
                out,
                family_name,
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
        if let Some(current) = constructor["induct"].as_u64()
            && let Some(next) = retarget(current, 1, names)
        {
            let mut m = record.clone();
            m["inductive"]["ctors"][position]["induct"] = Value::from(next);
            emit(
                wire,
                out,
                "ind.ctor-induct",
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
    }

    for (position, recursor) in group["recs"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .enumerate()
    {
        if let Some(current) = recursor["type"].as_u64()
            && let Some(next) = retarget(current, 1, exprs)
        {
            let mut m = record.clone();
            m["inductive"]["recs"][position]["type"] = Value::from(next);
            emit(
                wire,
                out,
                "ind.rec-type",
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
        for (field, family_name) in [
            ("numParams", "ind.rec-num-params"),
            ("numIndices", "ind.rec-num-indices"),
            ("numMotives", "ind.rec-num-motives"),
            ("numMinors", "ind.rec-num-minors"),
        ] {
            let current = recursor[field].as_u64().unwrap_or(0);
            let mut m = record.clone();
            m["inductive"]["recs"][position][field] = Value::from(current + 1);
            emit(
                wire,
                out,
                family_name,
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
        // `k` is the definitional-proof-irrelevance shortcut. Turning it on for
        // a family that has not earned it is how large elimination leaks.
        let k = recursor["k"].as_bool().unwrap_or(false);
        let mut m = record.clone();
        m["inductive"]["recs"][position]["k"] = Value::from(!k);
        emit(
            wire,
            out,
            "ind.rec-k",
            &format!("{position}flip"),
            &[(index, m)],
        );
        if let Some(current) = recursor["name"].as_u64()
            && let Some(next) = retarget(current, 1, names)
        {
            let mut m = record.clone();
            m["inductive"]["recs"][position]["name"] = Value::from(next);
            emit(
                wire,
                out,
                "ind.rec-name",
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
        for (rule_position, rule) in recursor["rules"]
            .as_array()
            .cloned()
            .unwrap_or_default()
            .iter()
            .enumerate()
        {
            if let Some(current) = rule["rhs"].as_u64()
                && let Some(next) = retarget(current, 1, exprs)
            {
                let mut m = record.clone();
                m["inductive"]["recs"][position]["rules"][rule_position]["rhs"] = Value::from(next);
                emit(
                    wire,
                    out,
                    "ind.rule-rhs",
                    &format!("{position}.{rule_position}+1"),
                    &[(index, m)],
                );
            }
            let fields = rule["nfields"].as_u64().unwrap_or(0);
            let mut m = record.clone();
            m["inductive"]["recs"][position]["rules"][rule_position]["nfields"] =
                Value::from(fields + 1);
            emit(
                wire,
                out,
                "ind.rule-nfields",
                &format!("{position}.{rule_position}+1"),
                &[(index, m)],
            );
            if let Some(current) = rule["ctor"].as_u64()
                && let Some(next) = retarget(current, 1, names)
            {
                let mut m = record.clone();
                m["inductive"]["recs"][position]["rules"][rule_position]["ctor"] =
                    Value::from(next);
                emit(
                    wire,
                    out,
                    "ind.rule-ctor",
                    &format!("{position}.{rule_position}+1"),
                    &[(index, m)],
                );
            }
        }
    }
}

/// Pick the corpus: up to `budget` mutants, **spread across every family**.
///
/// A plain stride over the whole list is what the first version did, and with
/// one mutation family that is fine. With forty-eight it is not: families are
/// generated in stream order, so a stride samples whichever families happen to
/// be dense and can miss narrow ones entirely — a family that generates three
/// mutants out of ten thousand would essentially never be checked, and its
/// absence would be invisible in the mutant count.
fn stratified(all: &[Mutant], budget: usize) -> Vec<&Mutant> {
    let mut by_family: BTreeMap<&str, Vec<&Mutant>> = BTreeMap::new();
    for mutant in all {
        by_family
            .entry(mutant.family.as_str())
            .or_default()
            .push(mutant);
    }
    let quota = budget.div_ceil(by_family.len().max(1)).max(1);
    let mut chosen: Vec<&Mutant> = Vec::new();
    for members in by_family.values() {
        // A stride within the family, never its first `quota` members: the
        // early members of a family all sit in the same declaration.
        let stride = members.len().div_ceil(quota).max(1);
        chosen.extend(members.iter().copied().step_by(stride).take(quota));
    }
    chosen.sort_by(|left, right| left.id.cmp(&right.id));
    chosen
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Theirs {
    /// The real Lean kernel admitted every declaration, and every constructor
    /// and recursor it regenerated matched the ones the stream carried.
    Accepted,
    /// `addDeclCore` refused a declaration — a genuine type-checking verdict.
    KernelRejected,
    /// `addDeclCore` accepted the family, but a constructor or recursor Lean's
    /// kernel generated for it disagrees with the one the record carried. This
    /// is the only verdict that can reach a recursor-only expression record.
    RegenerationMismatch,
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
    } else if report.contains("LEAN KERNEL REGENERATION MISMATCH") {
        Theirs::RegenerationMismatch
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
                Theirs::RegenerationMismatch =>
                    "contradicted: the constructors/recursors it generated for that \
                     inductive differ from the ones the stream carried",
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
        .unwrap_or(144)
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
    let corpus = stratified(&all, budget());
    let families: BTreeMap<&str, usize> =
        corpus.iter().fold(BTreeMap::new(), |mut counts, mutant| {
            *counts.entry(mutant.family.as_str()).or_default() += 1;
            counts
        });
    assert!(
        families.len() >= MIN_FAMILIES,
        "the corpus covers {} mutation families (floor {MIN_FAMILIES}); a family \
         that stops generating removes a whole class of damage from the sweep \
         without moving the mutant count much: {families:?}",
        families.len()
    );

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
    let mut regeneration_mismatches = 0_usize;
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
            Theirs::RegenerationMismatch => regeneration_mismatches += 1,
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
        "WIRE_DIFFERENTIAL|generated={}|checked={}|families={}|lean_kernel_rejected={}|\
         lean_regeneration_mismatch={}|lean_malformed={}|lean_accepted={}|ours_declined={}|\
         stricter_than_lean={}|violations={}",
        all.len(),
        corpus.len(),
        families.len(),
        kernel_rejections,
        regeneration_mismatches,
        malformed,
        corpus.len() - kernel_rejections - regeneration_mismatches - malformed,
        ours_declined,
        stricter_than_lean.len(),
        violations.len()
    );
    println!("  families sampled: {families:?}");
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
        regeneration_mismatches >= MIN_REGENERATION_MISMATCHES,
        "only {regeneration_mismatches} mutants reached a regeneration mismatch \
         (floor {MIN_REGENERATION_MISMATCHES}); that is the ONLY channel through \
         which Lean sees a recursor-only expression record, and 37% of this \
         stream is reachable no other way"
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
    assert!(violation("m", true, Theirs::RegenerationMismatch).is_some());
    assert!(violation("m", true, Theirs::Malformed).is_some());
    assert!(violation("m", true, Theirs::Accepted).is_none());
    // Stricter than Lean is incompleteness. If this ever became a violation the
    // suite would fail on correctness rather than on unsoundness.
    assert!(violation("m", false, Theirs::KernelRejected).is_none());
    assert!(violation("m", false, Theirs::RegenerationMismatch).is_none());
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
            "{}: a mutation may only rewire records, never add or drop one",
            mutant.id
        );
    }
    // Every family the mutator claims must actually appear, or a silently
    // broken branch reads as "no such construct in this development". The list
    // is exhaustive on purpose: a new family that never fires is the exact
    // failure this repository keeps rediscovering, and an exhaustive list means
    // adding one without also putting its construct on the wire fails here.
    let present: std::collections::BTreeSet<&str> = all.iter().map(|m| m.family.as_str()).collect();
    let expected = [
        "decl.type",
        "decl.universe-param",
        "decl.value",
        "expr.app-arg",
        "expr.app-fn",
        "expr.app-swap",
        "expr.binder-body",
        "expr.binder-domain",
        "expr.binder-info",
        "expr.binder-kind",
        "expr.binder-order",
        "expr.binder-swap",
        "expr.bvar-up",
        "expr.bvar-zero",
        "expr.const-arity",
        "expr.const-name",
        "expr.const-universe",
        "expr.let-body",
        "expr.let-type",
        "expr.let-type-value-swap",
        "expr.let-value",
        "expr.proj-index",
        "expr.proj-struct",
        "expr.proj-type",
        "expr.sort",
        "ind.ctor-cidx",
        "ind.ctor-induct",
        "ind.ctor-num-fields",
        "ind.ctor-num-params",
        "ind.ctor-type",
        "ind.family-ctors",
        "ind.family-is-rec",
        "ind.family-num-indices",
        "ind.family-num-nested",
        "ind.family-num-params",
        "ind.family-type",
        "ind.rec-k",
        "ind.rec-name",
        "ind.rec-num-indices",
        "ind.rec-num-minors",
        "ind.rec-num-motives",
        "ind.rec-num-params",
        "ind.rec-type",
        "ind.rule-ctor",
        "ind.rule-nfields",
        "ind.rule-rhs",
        "level.max-kind",
        "level.max-operand",
        "level.max-swap",
        "level.param",
        "level.succ",
    ];
    for family in expected {
        assert!(
            present.contains(family),
            "no {family} mutant was generated; the construct it damages is not \
             on this development's wire, so the family is dead code"
        );
    }
    assert!(
        present.len() >= MIN_FAMILIES,
        "only {} families generated (floor {MIN_FAMILIES})",
        present.len()
    );
}

#[test]
fn the_corpus_is_stratified_so_no_family_can_vanish_quietly() {
    // A stride over the whole list — the previous selection — is what this
    // replaces. Build a corpus where one family is rare and confirm it is still
    // sampled, because that is the property the stratifier exists for.
    let mut all = Vec::new();
    for index in 0..500 {
        all.push(Mutant {
            id: format!("common:{index}"),
            family: "common".to_owned(),
            stream: format!("common {index}"),
        });
    }
    all.push(Mutant {
        id: "rare:0".to_owned(),
        family: "rare".to_owned(),
        stream: "rare".to_owned(),
    });
    let corpus = stratified(&all, 20);
    assert!(
        corpus.iter().any(|mutant| mutant.family == "rare"),
        "a family with one member out of 501 was dropped by the selector"
    );
    assert!(
        corpus.len() <= 20 + 2,
        "selector overshot: {}",
        corpus.len()
    );
    // Deterministic: a failure must name a mutant the next run also produces.
    let again = stratified(&all, 20);
    assert_eq!(
        corpus.iter().map(|m| &m.id).collect::<Vec<_>>(),
        again.iter().map(|m| &m.id).collect::<Vec<_>>()
    );
}
