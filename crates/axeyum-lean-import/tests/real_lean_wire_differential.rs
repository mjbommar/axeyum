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
//! # Round 3: two more violations, and where the corpus was still blind
//!
//! Run 2026-08-18 against Lean 4.30.0. Round 2's 51 families all damaged the
//! same handful of record shapes, because the development was the logic prelude
//! plus five definitions — every inductive on it was `Prop`-valued or a nullary
//! enum. Round 3 widened the development (a Type-valued STRUCTURE and a theorem
//! provable only by structure eta; a `Lit::Nat` and a theorem provable only by
//! literal/constructor conversion; an INDEXED family; a PARAMETERIZED recursive
//! family; a MUTUAL group; an `axiom`, an `opaque`, and the `abbrev`/`opaque`
//! reducibility hints) and added fifteen families for wire fields nothing had
//! ever damaged: `levelParams` and `all` on families, constructors and
//! recursors; universe-parameter PERMUTATION at both the binding site and the
//! `Const` reference; a short universe-argument list; ι-rule right-hand sides
//! exchanged between rules of one recursor, and the rules permuted.
//!
//! **2 violations in 126 mutants across 66 families**, one defect reached two
//! ways (`True.rec` and `Acc.rec`), and it is the same shape as round 2's:
//!
//! * **A recursor's `levelParams` was decorative (2).** `ind.rec-uparams`
//!   renames the motive universe parameter at the binding site, leaving the
//!   recursor's type and every ι-rule mentioning the old name, now free. Lean's
//!   kernel generated `Sort uparam.0` where the stream said `Sort u`; we
//!   admitted it. `Kernel::check_declaration`'s universe-closure check — added
//!   in round 2 for exactly this — never sees a recursor record, because a
//!   recursor is *generated* by this kernel and then compared, never admitted
//!   from the stream. And the comparison alpha-renames the exported parameters
//!   onto the generated ones POSITIONALLY, so a parameter the exported list
//!   does not bind is not in the map and passes through untouched; when it
//!   spells the name the generated recursor uses, `def_eq` succeeds. Fixed in
//!   `axeyum-lean-import`'s `validate_generated_recursor` /`validate_rec_rules`
//!   (the importer is the only place that can check it, since the kernel is
//!   never handed the exported binding list). Regression:
//!   `recursor_universe_params_must_be_bound.rs`.
//!
//! # Round 4: the fourth admission gate, and the blind spot that was ours
//!
//! Round 3 stated a gap rather than papering over it: a NESTED group was off
//! the wire because the *undamaged* stream failed on `axeyum_wire_rose.rec_1`,
//! and the reading was that `addDeclCore` regenerates a nested group's own
//! recursor but not the auxiliary one, so every field of an auxiliary recursor
//! is a byte Lean never reads. Stating it was right. The reading was wrong.
//!
//! Lean's **kernel** does build `X.rec_1`. What does not know about it is
//! `Environment.find?`, which this script was using and which is the
//! *elaborator's* view: `addDeclCore` republishes only
//! `Declaration.getNames`, whose own docstring says the list "does not include
//! ... auxiliary recursors computed by the kernel for nested inductive types".
//! Measured 2026-08-18 on pinned 4.30.0, on the same environment value:
//! `env.find? …rec_1` is `none`, `env.constants.find? …rec_1` is a recursor
//! with two motives, three minors and both ι-rules. The replay script now looks
//! constants up in `env.toKernelEnv`; all three official nested fixtures
//! replay clean where each previously failed with exactly one disagreement.
//!
//! So the fix is a lookup, not an exemption, and the uncovered residue is
//! **zero bytes** rather than a bounded allowance. `axeyum_wire_rose` is on the
//! wire, fourteen `ind.aux-*` families damage the auxiliary recursor
//! specifically (a separate family per field, so the stratifier cannot sample
//! only main recursors and read as covered), and 17 of 17 such mutants were
//! discriminated by Lean's kernel. **0 violations in 274 mutants across 80
//! families** at the default budget and **0 in 752** at
//! `AXEYUM_WIRE_MUTANTS=1600`; `stricter_than_lean` 0 and 1. [`MIN_AUX_RECURSOR_DISCRIMINATED`] is
//! the floor that fails if the lookup regresses or an absent constant is ever
//! exempted rather than reported, and
//! [`the_official_nested_fixtures_reach_the_auxiliary_recursor`] fails the same
//! two ways on official `lean4export` bytes.
//!
//! The residue was measured rather than asserted, twice, and both are the
//! numbers a reader should hold this against:
//!
//! * **The nested `inductive` record, exhaustively.** All 42 mutants the
//!   generator can produce against it: our importer declined 42, Lean's kernel
//!   discriminated 42, Lean accepted none, 0 violations.
//! * **The expression records only the auxiliary recursor reaches.** Of 888
//!   expression records on this development, 69 are reachable from the
//!   auxiliary recursor's type or ι-rules and **33 are reachable from nothing
//!   else** — the auxiliary analogue of the 37% hole above. All 178 mutants
//!   damaging those 33 were checked: Lean discriminated 160 and accepted 18,
//!   and every one of the 18 is `expr.binder-info`, the family this file
//!   documents as *expected* to agree because binder info is elaborator
//!   metadata neither kernel type-checks (`normExpr` erases it). 0 violations.
//!   So the uncovered residue on this gate is one non-type-checking field, not
//!   a class of unread bytes.
//!
//! The general lesson is one this repository already knows: **an empty answer
//! from a tool that was never pointed at your subject is indistinguishable from
//! a strong negative result.** `Environment.find?` ran, exited cleanly, and
//! returned a correct `none` to a question about the elaborator that had been
//! asked about the kernel.
//!
//! Still unreachable, and for a reason that is about the interface rather than
//! about where we looked: `quot` records. `addDeclCore` ignores a quotient
//! package's carried types and adds its own, so it accepts every damaged
//! quotient record and the axis cannot discriminate.
//!
//! The one "stricter than Lean" mutant round 2 recorded is understood, which is
//! the whole difference from the 32 it replaced (round 3's wider sample did not
//! draw it): `expr.const-name` rewrites `Or.inl` to `Or.inr` inside `Or.rec`'s
//! type. Both are proofs of the same `Prop`, so
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
    BinderInfo, Declaration, InductiveFamilySpec, Kernel, Lean4ExportMetadata, Lit, NatLit,
    ReducibilityHint, build_logic_prelude,
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
/// Distinct mutants the generator must produce. A generator that goes blind
/// emits none and every count above reads as a clean result — but a floor of 24
/// against 4,747 generated (measured 2026-08-18) would not notice 99% of the
/// corpus disappearing either. This is a ratchet on the GENERATOR, independent
/// of the sampling budget, so it can be tight.
const MIN_MUTANTS: usize = 4_800;
/// Distinct mutation families required. The corpus is stratified by family, so
/// a family that stops generating quietly removes a whole class of damage from
/// the sweep without changing the mutant count much.
const MIN_FAMILIES: usize = 78;
/// Mutants confined to a NESTED group's auxiliary recursor that Lean's kernel
/// must discriminate.
///
/// This is the floor that keeps the fourth admission gate covered. An auxiliary
/// recursor is republished by `Kernel::restore_nested_inductive_group` and by
/// nothing else, and Lean's kernel builds its own — but `addDeclCore` does not
/// announce it, so a lookup through `Environment.find?` finds nothing. Round 3
/// read that as "Lean never reads these bytes" and left the group off the wire;
/// the truth was that the replay script was asking the wrong environment.
/// Should anyone reintroduce that lookup, or exempt an absent constant instead
/// of reporting it, every `ind.aux-*` mutant goes back to `Accepted` and this
/// floor is what fails. Measured 2026-08-18: 16 of 16 were discriminated.
const MIN_AUX_RECURSOR_DISCRIMINATED: usize = 12;

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
#[allow(clippy::too_many_lines)]
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

    // ---------------------------------------------------------------------
    // Round 3 widening. Everything above is `Prop`-valued logic plus `Bool`
    // and `Nat`, so the 51 families were damaging the same handful of record
    // shapes over and over. These put the constructs the kernel does its
    // *hardest* work on onto the wire, each because a specific trusted routine
    // is unreachable without it:
    //
    //   `axeyum_wire_box`     a Type-valued STRUCTURE, plus a theorem provable
    //                         only by `Kernel::try_eta_structure`,
    //   a `Lit::Nat`          plus a theorem provable only by literal <->
    //                         constructor conversion (`nat_offset`,
    //                         `nat_literal_to_constructor`),
    //   `axeyum_wire_vec`     an INDEXED family: ι-rules whose major premise
    //                         carries indices,
    //   `axeyum_wire_list`    a PARAMETERIZED recursive family,
    //   tree / forest         a MUTUAL group: two motives, globally ordered
    //                         minors, one recursor per family,
    //   `axeyum_wire_rose`    a NESTED group, i.e. the fourth admission gate
    //                         (`restore_nested_inductive_group`), which had no
    //                         adversarial coverage until round 4 (see below),
    //   an `axiom`, an `opaque`, an `abbrev`-hinted and an `opaque`-hinted
    //                         definition, so the `decl.*` families stop firing
    //                         on two of the four declaration kinds they claim.
    let one = kernel.level_succ(zero);
    let type_ = kernel.sort(one);
    let naturals = kernel.const_(logic.nat, vec![]);
    let booleans = kernel.const_(logic.bool_, vec![]);
    let naught = kernel.const_(logic.nat_zero, vec![]);
    let successor = kernel.const_(logic.nat_succ, vec![]);
    let eq_one = kernel.const_(logic.eq, vec![one]);
    let refl_one = kernel.const_(logic.eq_refl, vec![one]);

    // `structure axeyum_wire_box where fst : Nat; snd : Bool`
    let box_name = kernel.name_str(anonymous, "axeyum_wire_box");
    let box_mk = kernel.name_str(box_name, "mk");
    let box_const = kernel.const_(box_name, vec![]);
    {
        let inner = kernel.pi(anonymous, booleans, box_const, BinderInfo::Default);
        let mk_ty = kernel.pi(anonymous, naturals, inner, BinderInfo::Default);
        kernel
            .add_inductive(box_name, &[], 0, type_, &[(box_mk, mk_ty)])
            .expect("a two-field non-recursive structure must be admissible");
    }

    // `theorem axeyum_wire_eta : ∀ b, Eq b (axeyum_wire_box.mk b.0 b.1)`.
    // `Eq.refl _ b` infers `Eq b b`, so admitting this REQUIRES structure eta
    // in `def_eq`; nothing else on this wire reaches that routine.
    {
        let binder = kernel.name_str(anonymous, "b");
        let subject = kernel.bvar(0);
        let first = kernel.proj(box_name, 0, subject);
        let second = kernel.proj(box_name, 1, subject);
        let make = kernel.const_(box_mk, vec![]);
        let rebuilt = kernel.app(make, first);
        let rebuilt = kernel.app(rebuilt, second);
        let statement = kernel.app(eq_one, box_const);
        let statement = kernel.app(statement, subject);
        let statement = kernel.app(statement, rebuilt);
        let ty = kernel.pi(binder, box_const, statement, BinderInfo::Default);
        let proof = kernel.app(refl_one, box_const);
        let proof = kernel.app(proof, subject);
        let value = kernel.lam(binder, box_const, proof, BinderInfo::Default);
        let name = kernel.name_str(anonymous, "axeyum_wire_eta");
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams: Vec::new(),
                ty,
                value,
            })
            .expect("structure eta must admit the reflexivity proof");
    }

    // `theorem axeyum_wire_lit : Eq (3 : Nat) (Nat.succ (Nat.succ (Nat.succ Nat.zero)))`
    // — the compact literal and the unary spelling are the same value only if a
    // kernel converts between them.
    {
        let literal = kernel.lit(Lit::Nat(
            NatLit::from_decimal("3").expect("a decimal literal"),
        ));
        let unary = kernel.app(successor, naught);
        let unary = kernel.app(successor, unary);
        let unary = kernel.app(successor, unary);
        let statement = kernel.app(eq_one, naturals);
        let statement = kernel.app(statement, literal);
        let statement = kernel.app(statement, unary);
        let proof = kernel.app(refl_one, naturals);
        let proof = kernel.app(proof, literal);
        let name = kernel.name_str(anonymous, "axeyum_wire_lit");
        kernel
            .add_declaration(Declaration::Theorem {
                name,
                uparams: Vec::new(),
                ty: statement,
                value: proof,
            })
            .expect("literal/constructor conversion must admit reflexivity");
    }

    // `inductive axeyum_wire_vec : Nat → Type` — one index, one recursive
    // constructor whose result index is `Nat.succ n`.
    {
        let vec_name = kernel.name_str(anonymous, "axeyum_wire_vec");
        let vnil = kernel.name_str(vec_name, "vnil");
        let vcons = kernel.name_str(vec_name, "vcons");
        let vec_ty = kernel.pi(anonymous, naturals, type_, BinderInfo::Default);
        let vec_const = kernel.const_(vec_name, vec![]);
        let vnil_ty = kernel.app(vec_const, naught);
        let here = kernel.bvar(0);
        let head = kernel.app(vec_const, here);
        let outer = kernel.bvar(1);
        let stepped = kernel.app(successor, outer);
        let tail = kernel.app(vec_const, stepped);
        let inner = kernel.pi(anonymous, head, tail, BinderInfo::Default);
        let vcons_ty = kernel.pi(anonymous, naturals, inner, BinderInfo::Default);
        kernel
            .add_inductive(
                vec_name,
                &[],
                0,
                vec_ty,
                &[(vnil, vnil_ty), (vcons, vcons_ty)],
            )
            .expect("an indexed family must be admissible");
    }

    // `inductive axeyum_wire_list (α : Type) : Type` — one parameter, one
    // recursive constructor. Also the container the nested group below nests in.
    let list_name = kernel.name_str(anonymous, "axeyum_wire_list");
    let list_const = kernel.const_(list_name, vec![]);
    {
        let list_nil = kernel.name_str(list_name, "nil");
        let list_cons = kernel.name_str(list_name, "cons");
        let alpha = kernel.name_str(anonymous, "a");
        let list_ty = kernel.pi(alpha, type_, type_, BinderInfo::Default);
        let here = kernel.bvar(0);
        let applied = kernel.app(list_const, here);
        let nil_ty = kernel.pi(alpha, type_, applied, BinderInfo::Default);
        let one_up = kernel.bvar(1);
        let two_up = kernel.bvar(2);
        let spine = kernel.app(list_const, one_up);
        let result = kernel.app(list_const, two_up);
        let rest = kernel.pi(anonymous, spine, result, BinderInfo::Default);
        let field = kernel.pi(anonymous, here, rest, BinderInfo::Default);
        let cons_ty = kernel.pi(alpha, type_, field, BinderInfo::Default);
        kernel
            .add_inductive(
                list_name,
                &[],
                1,
                list_ty,
                &[(list_nil, nil_ty), (list_cons, cons_ty)],
            )
            .expect("a parameterized recursive family must be admissible");
    }

    // A MUTUAL group: `tree.node : forest → tree`, `forest.fcons : tree → forest → forest`.
    {
        let tree = kernel.name_str(anonymous, "axeyum_wire_tree");
        let forest = kernel.name_str(anonymous, "axeyum_wire_forest");
        let tree_node = kernel.name_str(tree, "node");
        let forest_nil = kernel.name_str(forest, "nil");
        let forest_cons = kernel.name_str(forest, "cons");
        let branch = kernel.const_(tree, vec![]);
        let grove = kernel.const_(forest, vec![]);
        let node_ty = kernel.pi(anonymous, grove, branch, BinderInfo::Default);
        let cons_rest = kernel.pi(anonymous, grove, grove, BinderInfo::Default);
        let cons_ty = kernel.pi(anonymous, branch, cons_rest, BinderInfo::Default);
        kernel
            .add_mutual_inductive(
                &[],
                0,
                &[
                    InductiveFamilySpec::new(tree, type_, vec![(tree_node, node_ty)]),
                    InductiveFamilySpec::new(
                        forest,
                        type_,
                        vec![(forest_nil, grove), (forest_cons, cons_ty)],
                    ),
                ],
            )
            .expect("a mutual group must be admissible");
    }

    // A NESTED group: `inductive axeyum_wire_rose | node : axeyum_wire_list
    // axeyum_wire_rose -> axeyum_wire_rose`. This is the fourth admission gate,
    // `Kernel::restore_nested_inductive_group`, and reaching it is the point of
    // the whole declaration.
    //
    // Round 3 tried this and backed out, because the UNDAMAGED stream failed:
    // the replay script reported `axeyum_wire_rose.rec_1` — the auxiliary
    // recursor of the nested expansion — as a constant "Lean's kernel generated
    // no such constant" for. The conclusion drawn was that Lean's kernel nests
    // internally and only the frontend publishes the auxiliary constant, so
    // every field of an auxiliary recursor is a byte Lean never reads.
    //
    // That conclusion was wrong, and the instrument was what lied. Lean's
    // KERNEL does build `Rose.rec_1`; `Environment.find?` — which the replay
    // script was using — is the *elaborator's* view, and `addDeclCore`
    // republishes only `Declaration.getNames`, whose own docstring says it
    // "does not include ... auxiliary recursors computed by the kernel for
    // nested inductive types". Measured 2026-08-18 on the pinned 4.30.0:
    // `env.find? `…rec_1`` is `none` while `env.constants.find? `…rec_1`` is a
    // recursor with two motives, three minors and both ι-rules. The replay
    // script now looks constants up in `env.toKernelEnv`, all three official
    // nested fixtures replay clean, and every field of the auxiliary recursor
    // is compared against Lean's own regeneration — no exemption, no residue.
    // `the_official_nested_fixtures_reach_the_auxiliary_recursor` below is the
    // test that fails if that stops holding.
    {
        let rose_name = kernel.name_str(anonymous, "axeyum_wire_rose");
        let rose_node = kernel.name_str(rose_name, "node");
        let rose_const = kernel.const_(rose_name, vec![]);
        let container = kernel.app(list_const, rose_const);
        let node_ty = kernel.pi(anonymous, container, rose_const, BinderInfo::Default);
        kernel
            .add_inductive(rose_name, &[], 0, type_, &[(rose_node, node_ty)])
            .expect("a nested group must be admissible");
    }

    // The remaining two declaration kinds and the remaining two reducibility
    // hints. `decl.type` / `decl.value` / `decl.hints` claim to cover all four
    // kinds; without these they fire only on `thm` and `def`.
    {
        let name = kernel.name_str(anonymous, "axeyum_wire_axiom");
        kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: Vec::new(),
                ty: naturals,
            })
            .expect("an axiom over a checked type must be admissible");
        let name = kernel.name_str(anonymous, "axeyum_wire_opaque");
        kernel
            .add_declaration(Declaration::Opaque {
                name,
                uparams: Vec::new(),
                ty: naturals,
                value: naught,
            })
            .expect("an opaque over a checked value must be admissible");
        for (label, hint) in [
            ("axeyum_wire_abbrev", ReducibilityHint::Abbrev),
            ("axeyum_wire_hint_opaque", ReducibilityHint::Opaque),
        ] {
            let name = kernel.name_str(anonymous, label);
            kernel
                .add_declaration(Declaration::Definition {
                    name,
                    uparams: Vec::new(),
                    ty: naturals,
                    value: naught,
                    hint,
                })
                .expect("a hinted definition must be admissible");
        }
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
    /// The name table, resolved to dotted text.
    ///
    /// Nothing else here needs a name's *spelling* — indices are enough to
    /// rewire a field. The auxiliary-recursor split does: `axeyum_wire_rose.rec`
    /// is a recursor Lean's kernel names from the family, and
    /// `axeyum_wire_rose.rec_1` is one it derives for the nested expansion, and
    /// the only thing on the wire that distinguishes them is the name.
    names: Vec<String>,
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
        let mut name_text = vec![String::new()];
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
                let (parent, component) = record.get("str").map_or_else(
                    || {
                        let entry = &record["num"];
                        (
                            entry["pre"].as_u64().unwrap_or(0),
                            entry["i"].as_u64().unwrap_or(0).to_string(),
                        )
                    },
                    |entry| {
                        (
                            entry["pre"].as_u64().unwrap_or(0),
                            entry["str"].as_str().unwrap_or_default().to_owned(),
                        )
                    },
                );
                let prefix = &name_text[usize::try_from(parent).expect("name index fits")];
                name_text.push(if prefix.is_empty() {
                    component
                } else {
                    format!("{prefix}.{component}")
                });
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
            names: name_text,
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
        // One universe argument too FEW. `const-arity` only ever added one, and
        // a checker that reads the declared list positionally can fail in the
        // other direction as easily.
        if universes.len() > 1 {
            let mut narrowed = universes.clone();
            narrowed.pop();
            let mut m = record.clone();
            m["const"]["us"] = Value::from(narrowed);
            emit(
                wire,
                out,
                "expr.const-arity-short",
                "missing",
                &[(index, m)],
            );
        }
        // The universe arguments PERMUTED. Arity, every index and the whole
        // table are untouched, so nothing structural distinguishes it: only a
        // checker that substitutes the declared parameters positionally *and*
        // then re-checks the result can tell. This is the exact shape of the
        // defect round 2 found in `levelParams`, on the other side of the
        // substitution.
        if universes.len() > 1 && universes[0] != universes[1] {
            let mut swapped = universes.clone();
            swapped.swap(0, 1);
            let mut m = record.clone();
            m["const"]["us"] = Value::from(swapped);
            emit(wire, out, "expr.const-universe-swap", "01", &[(index, m)]);
        }
    }
    // A compact `Nat` literal. Nothing else on the wire carries one, and the
    // routines that convert between `Lit::Nat` and `Nat.succ`/`Nat.zero`
    // (`nat_offset`, `nat_literal_to_constructor`) are reachable no other way.
    if let Some(literal) = record.get("natVal").and_then(Value::as_str) {
        let value: u64 = literal.parse().unwrap_or(0);
        for (next, detail) in [(value + 1, "+1"), (0, "zero")] {
            if next == value {
                continue;
            }
            let mut m = record.clone();
            m["natVal"] = Value::from(next.to_string());
            emit(wire, out, "expr.lit-nat", detail, &[(index, m)]);
        }
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
        // `nondep` is Lean 4.30 frontend metadata that neither kernel types,
        // and our importer reads it and discards it. Like `expr.binder-info`
        // this family earns its place by being EXPECTED to agree: a suite in
        // which every family disagrees is comparing the wrong axis.
        let nondep = binding["nondep"].as_bool().unwrap_or(false);
        let mut m = record.clone();
        m["letE"]["nondep"] = Value::from(!nondep);
        emit(wire, out, "expr.let-nondep", "flip", &[(index, m)]);
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
    // The universe parameters PERMUTED at the binding site. Every name stays
    // bound, so the "must be bound" fix round 2 landed does not see it; what
    // changes is which parameter each POSITION of a `Const` reference feeds.
    if let Some(uparams) = record[kind].get("levelParams").and_then(Value::as_array)
        && uparams.len() > 1
        && uparams[0] != uparams[1]
    {
        let mut swapped = uparams.clone();
        swapped.swap(0, 1);
        let mut m = record.clone();
        m[kind]["levelParams"] = Value::from(swapped);
        emit(wire, out, "decl.universe-param-swap", kind, &[(index, m)]);
    }
    // `all` is the mutual-definition group this declaration belongs to. The
    // importer validates that the names resolve; whether it validates that they
    // describe THIS declaration is the question.
    if let Some(all) = record[kind].get("all").and_then(Value::as_array)
        && let Some(first) = all.first().and_then(Value::as_u64)
        && let Some(next) = retarget(first, 1, wire.names_before[index])
    {
        let mut m = record.clone();
        m[kind]["all"][0] = Value::from(next);
        emit(wire, out, "decl.all", kind, &[(index, m)]);
    }
    // The reducibility hint drives lazy-delta unfolding order. `opaque` claims
    // the definition never unfolds and `abbrev` that it unfolds first; a kernel
    // that believes a wrong hint can stop unfolding a definition it must
    // unfold, or unfold one it must not.
    if let Some(hints) = record[kind].get("hints").cloned() {
        for (detail, replacement) in [
            ("opaque", Value::from("opaque")),
            ("abbrev", Value::from("abbrev")),
        ] {
            if hints == replacement {
                continue;
            }
            let mut m = record.clone();
            m[kind]["hints"] = replacement;
            emit(wire, out, "decl.hints", detail, &[(index, m)]);
        }
        if let Some(height) = hints.get("regular").and_then(Value::as_u64) {
            let mut m = record.clone();
            m[kind]["hints"]["regular"] = Value::from(height + 7);
            emit(wire, out, "decl.hints", "height", &[(index, m)]);
        }
    }
}

/// Name a recursor mutation family, splitting the auxiliary recursors out.
///
/// A nested group publishes one recursor per source family — `X.rec` — plus one
/// `X.rec_N` per auxiliary family the nested expansion introduced, and the
/// second kind exists only because `Kernel::restore_nested_inductive_group`,
/// the fourth admission gate, republished it. Damaging it under the same family
/// name as `X.rec` would leave the stratifier free to sample only main
/// recursors, and the gate would read as covered while nothing had touched it.
/// A separate family means the corpus is *required* to carry one of each (the
/// exhaustive list in `the_mutator_is_derived_from_the_stream_and_changes_bytes`)
/// and the stratifier is required to sample it.
fn recursor_family(is_auxiliary: bool, base: &str) -> String {
    if is_auxiliary {
        base.replacen("ind.", "ind.aux-", 1)
    } else {
        base.to_owned()
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
        if let Some(first) = family["levelParams"]
            .as_array()
            .and_then(|list| list.first())
            .and_then(Value::as_u64)
            && let Some(next) = retarget(first, 1, names)
        {
            let mut m = record.clone();
            m["inductive"]["types"][position]["levelParams"][0] = Value::from(next);
            emit(
                wire,
                out,
                "ind.family-uparams",
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
        if let Some(first) = family["all"]
            .as_array()
            .and_then(|list| list.first())
            .and_then(Value::as_u64)
            && let Some(next) = retarget(first, 1, names)
        {
            let mut m = record.clone();
            m["inductive"]["types"][position]["all"][0] = Value::from(next);
            emit(
                wire,
                out,
                "ind.family-all",
                &format!("{position}+1"),
                &[(index, m)],
            );
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
        if let Some(first) = constructor["levelParams"]
            .as_array()
            .and_then(|list| list.first())
            .and_then(Value::as_u64)
            && let Some(next) = retarget(first, 1, names)
        {
            let mut m = record.clone();
            m["inductive"]["ctors"][position]["levelParams"][0] = Value::from(next);
            emit(
                wire,
                out,
                "ind.ctor-uparams",
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

    // Which recursors this group's *source* families own. Everything else in
    // `recs` is an auxiliary recursor of a nested expansion, republished by the
    // fourth admission gate rather than generated for a declared family.
    let main_recursor_names: std::collections::BTreeSet<String> = group["types"]
        .as_array()
        .map(|families| {
            families
                .iter()
                .filter_map(|family| family["name"].as_u64())
                .map(|name| format!("{}.rec", wire.names[usize::try_from(name).expect("fits")]))
                .collect()
        })
        .unwrap_or_default();

    for (position, recursor) in group["recs"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .enumerate()
    {
        let is_auxiliary = recursor["name"]
            .as_u64()
            .and_then(|name| wire.names.get(usize::try_from(name).expect("fits")))
            .is_some_and(|name| !main_recursor_names.contains(name));
        if let Some(current) = recursor["type"].as_u64()
            && let Some(next) = retarget(current, 1, exprs)
        {
            let mut m = record.clone();
            m["inductive"]["recs"][position]["type"] = Value::from(next);
            emit(
                wire,
                out,
                &recursor_family(is_auxiliary, "ind.rec-type"),
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
                &recursor_family(is_auxiliary, family_name),
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
            &recursor_family(is_auxiliary, "ind.rec-k"),
            &format!("{position}flip"),
            &[(index, m)],
        );
        // A recursor's `levelParams` carry the motive universe as well as the
        // family's, so this is where a positional universe substitution has the
        // most to get wrong.
        let rec_uparams = recursor["levelParams"]
            .as_array()
            .cloned()
            .unwrap_or_default();
        if let Some(first) = rec_uparams.first().and_then(Value::as_u64)
            && let Some(next) = retarget(first, 1, names)
        {
            let mut m = record.clone();
            m["inductive"]["recs"][position]["levelParams"][0] = Value::from(next);
            emit(
                wire,
                out,
                &recursor_family(is_auxiliary, "ind.rec-uparams"),
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
        if rec_uparams.len() > 1 && rec_uparams[0] != rec_uparams[1] {
            let mut swapped = rec_uparams.clone();
            swapped.swap(0, 1);
            let mut m = record.clone();
            m["inductive"]["recs"][position]["levelParams"] = Value::from(swapped);
            emit(
                wire,
                out,
                &recursor_family(is_auxiliary, "ind.rec-uparams-swap"),
                &format!("{position}01"),
                &[(index, m)],
            );
        }
        if let Some(first) = recursor["all"]
            .as_array()
            .and_then(|list| list.first())
            .and_then(Value::as_u64)
            && let Some(next) = retarget(first, 1, names)
        {
            let mut m = record.clone();
            m["inductive"]["recs"][position]["all"][0] = Value::from(next);
            emit(
                wire,
                out,
                &recursor_family(is_auxiliary, "ind.rec-all"),
                &format!("{position}+1"),
                &[(index, m)],
            );
        }
        // The ι-rules of ONE recursor exchange right-hand sides while keeping
        // their constructor names. Every index stays in range and both rules
        // stay well formed; what changes is that `Nat.rec` on `Nat.zero` now
        // computes the successor branch. `ind.rule-rhs` retargets to an
        // arbitrary expression, which is far cruder — this is the mistake a
        // generator could actually make.
        let rules = recursor["rules"].as_array().cloned().unwrap_or_default();
        if rules.len() > 1
            && let (Some(left), Some(right)) = (rules[0]["rhs"].as_u64(), rules[1]["rhs"].as_u64())
            && left != right
        {
            let mut m = record.clone();
            m["inductive"]["recs"][position]["rules"][0]["rhs"] = Value::from(right);
            m["inductive"]["recs"][position]["rules"][1]["rhs"] = Value::from(left);
            emit(
                wire,
                out,
                &recursor_family(is_auxiliary, "ind.rule-rhs-swap"),
                &format!("{position}01"),
                &[(index, m)],
            );
        }
        // The rules PERMUTED as whole objects: the export lists them in
        // constructor order and a recursor that dispatches by position rather
        // than by name cannot tell.
        if rules.len() > 1 {
            let mut permuted = rules.clone();
            permuted.swap(0, 1);
            let mut m = record.clone();
            m["inductive"]["recs"][position]["rules"] = Value::from(permuted);
            emit(
                wire,
                out,
                &recursor_family(is_auxiliary, "ind.rule-order"),
                &format!("{position}01"),
                &[(index, m)],
            );
        }
        if let Some(current) = recursor["name"].as_u64()
            && let Some(next) = retarget(current, 1, names)
        {
            let mut m = record.clone();
            m["inductive"]["recs"][position]["name"] = Value::from(next);
            emit(
                wire,
                out,
                &recursor_family(is_auxiliary, "ind.rec-name"),
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
                    &recursor_family(is_auxiliary, "ind.rule-rhs"),
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
                &recursor_family(is_auxiliary, "ind.rule-nfields"),
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
                    &recursor_family(is_auxiliary, "ind.rule-ctor"),
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

/// Distinct mutants to check, spread across every family.
///
/// Measured on the development host 2026-08-18, and the cost is linear in the
/// mutant count because essentially all of it is the `lean --run` subprocess:
/// 51 mutants in 62 s, 126 in 126 s, 444 in 433 s — **0.98 s per mutant**. The
/// full corpus this development generates is 4,747 mutants, so an exhaustive
/// sweep is about **80 minutes**: a thing to run deliberately
/// (`AXEYUM_WIRE_MUTANTS=99999`), not a thing to put in an aggregate gate. The
/// default is the largest sweep that keeps `scripts/check-lean-gate.sh` inside
/// ten minutes; it was 144 through round 2, which checked 134.
///
/// The stratified sample IS the binding constraint on what a round finds, and
/// round 3 measured that directly: with the `ind.rec-uparams` fix reverted, a
/// 66-mutant sweep (one per family) passed clean while a 126-mutant sweep found
/// the defect twice. So a clean sweep is evidence in proportion to its budget,
/// and this suite is a DISCOVERY instrument — the ratchet that keeps a found
/// defect fixed is the dedicated regression test each one gets.
fn budget() -> usize {
    std::env::var("AXEYUM_WIRE_MUTANTS")
        .ok()
        .and_then(|value| value.parse().ok())
        .unwrap_or(396)
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
    lean_probe::assert_pinned_version("wire-differential", &version);
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
    // The fourth admission gate's own tally, kept apart from the aggregate:
    // damage confined to a nested group's auxiliary recursor is the one class
    // that was believed unreachable, so "the sweep was clean" must not be able
    // to mean "those mutants were never looked at".
    let mut auxiliary_seen = 0_usize;
    let mut auxiliary_discriminated = 0_usize;
    let mut auxiliary_accepted = Vec::new();

    for (position, mutant) in corpus.iter().enumerate() {
        let admitted = ours(&mutant.stream).is_ok();
        let (verdict, report) = theirs(&lean, &directory, &mutant.stream, &format!("m{position}"));
        recorded.push((mutant.id.clone(), verdict));
        if !admitted {
            ours_declined += 1;
        }
        if mutant.family.starts_with("ind.aux-") {
            auxiliary_seen += 1;
            if verdict == Theirs::Accepted {
                auxiliary_accepted.push(mutant.id.clone());
            } else {
                auxiliary_discriminated += 1;
            }
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
         stricter_than_lean={}|aux_recursor_checked={}|aux_recursor_discriminated={}|\
         violations={}",
        all.len(),
        corpus.len(),
        families.len(),
        kernel_rejections,
        regeneration_mismatches,
        malformed,
        corpus.len() - kernel_rejections - regeneration_mismatches - malformed,
        ours_declined,
        stricter_than_lean.len(),
        auxiliary_seen,
        auxiliary_discriminated,
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
    if !auxiliary_accepted.is_empty() {
        println!("  auxiliary-recursor damage Lean accepted: {auxiliary_accepted:?}");
    }
    assert!(
        auxiliary_discriminated >= MIN_AUX_RECURSOR_DISCRIMINATED,
        "Lean's kernel discriminated only {auxiliary_discriminated} of \
         {auxiliary_seen} mutants confined to a nested group's AUXILIARY \
         recursor (floor {MIN_AUX_RECURSOR_DISCRIMINATED}). That is the only \
         evidence `restore_nested_inductive_group` — the fourth admission gate \
         — is covered at all; without it the nested group is on the wire but \
         nothing on Lean's side reads the half of it that gate republishes"
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

/// The official `lean4export` nested fixtures, and the auxiliary recursor in
/// each of them, put through the real Lean kernel.
///
/// This is the test that fails if the argument behind the nested coverage stops
/// holding, and it fails in both directions:
///
/// * **undamaged fixture rejected** — the replay script stopped being able to
///   see `X.rec_1`. That is what `Environment.find?` does (it consults the
///   elaborator's async constant map, which `addDeclCore` populates only from
///   `Declaration.getNames`, and that list excludes auxiliary recursors by
///   documented design). Under it these three fixtures each failed with exactly
///   one disagreement.
/// * **damaged auxiliary recursor accepted** — the comparison started skipping
///   a constant it could not find, or stopped reading the auxiliary recursor's
///   fields. Either would restore the blind spot with the count still looking
///   healthy.
///
/// These are official bytes, not ours: they were produced by `lean4export` from
/// a development Lean itself elaborated, so the auxiliary recursor here is the
/// shape the reference toolchain publishes rather than the shape our exporter
/// happens to render.
#[test]
fn the_official_nested_fixtures_reach_the_auxiliary_recursor() {
    let Some(lean) = pinned_lean() else {
        assert!(!lean_probe::lean_required(), "AXEYUM_REQUIRE_LEAN=1");
        println!(
            "{} nested-auxiliary-fixtures not_checked=unknown reason=pinned-toolchain-missing",
            lean_probe::SKIPPED_MARKER
        );
        return;
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../docs/plan/fixtures");
    let directory = std::env::temp_dir().join(format!("axeyum_wire_aux_{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("create mutant directory");

    let mut checked = 0_usize;
    for fixture in [
        "lean4export-v4.30-construct-matrix-nested.ndjson",
        "lean4export-v4.30-nested-aux-computation.ndjson",
        "lean4export-v4.30-nested-indexed-computation.ndjson",
    ] {
        let base = std::fs::read_to_string(root.join(fixture)).expect("official fixture");
        let (verdict, report) = theirs(&lean, &directory, &base, "base");
        assert_eq!(
            verdict,
            Theirs::Accepted,
            "{fixture}: the real Lean kernel rejected an UNDAMAGED official \
             stream. The auxiliary recursor of a nested group is the only \
             construct here that `Environment.find?` cannot see, so a lookup \
             that regressed to it reports exactly this:\n{report}"
        );
        checked += 1;

        let auxiliary: Vec<&Mutant> = mutants(&base)
            .leak()
            .iter()
            .filter(|mutant| mutant.family.starts_with("ind.aux-"))
            .collect();
        assert!(
            auxiliary.len() >= 8,
            "{fixture}: only {} auxiliary-recursor mutants were generated; a \
             fixture whose nested group stopped being recognised as nested \
             would make every assertion below vacuous",
            auxiliary.len()
        );
        for mutant in auxiliary {
            let admitted = ours(&mutant.stream).is_ok();
            let (verdict, report) = theirs(&lean, &directory, &mutant.stream, "aux");
            assert_ne!(
                verdict,
                Theirs::Accepted,
                "{fixture} {}: Lean's kernel accepted a stream whose AUXILIARY \
                 recursor was damaged. Those bytes are republished by \
                 `restore_nested_inductive_group` and by nothing else, so if \
                 Lean does not read them the fourth admission gate has no \
                 independent check at all:\n{report}",
                mutant.id
            );
            assert!(
                violation(&mutant.id, admitted, verdict).is_none(),
                "{fixture}: our kernel admitted auxiliary-recursor damage the \
                 real Lean kernel refused:\n{report}"
            );
            checked += 1;
        }
    }
    lean_probe::report_checked("nested-auxiliary-fixtures", checked);
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

#[allow(clippy::too_many_lines)]
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
        "decl.all",
        "decl.hints",
        "decl.type",
        "decl.universe-param",
        "decl.universe-param-swap",
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
        "expr.const-arity-short",
        "expr.const-name",
        "expr.const-universe",
        "expr.const-universe-swap",
        "expr.let-body",
        "expr.let-nondep",
        "expr.let-type",
        "expr.let-type-value-swap",
        "expr.let-value",
        "expr.lit-nat",
        "expr.proj-index",
        "expr.proj-struct",
        "expr.proj-type",
        "expr.sort",
        "ind.ctor-cidx",
        "ind.ctor-induct",
        "ind.ctor-num-fields",
        "ind.ctor-num-params",
        "ind.ctor-type",
        "ind.ctor-uparams",
        "ind.family-all",
        "ind.family-ctors",
        "ind.family-is-rec",
        "ind.family-num-indices",
        "ind.family-num-nested",
        "ind.family-num-params",
        "ind.family-type",
        "ind.family-uparams",
        "ind.aux-rec-all",
        "ind.aux-rec-k",
        "ind.aux-rec-name",
        "ind.aux-rec-num-indices",
        "ind.aux-rec-num-minors",
        "ind.aux-rec-num-motives",
        "ind.aux-rec-num-params",
        "ind.aux-rec-type",
        "ind.aux-rec-uparams",
        "ind.aux-rule-ctor",
        "ind.aux-rule-nfields",
        "ind.aux-rule-order",
        "ind.aux-rule-rhs",
        "ind.aux-rule-rhs-swap",
        "ind.rec-all",
        "ind.rec-k",
        "ind.rec-name",
        "ind.rec-num-indices",
        "ind.rec-num-minors",
        "ind.rec-num-motives",
        "ind.rec-num-params",
        "ind.rec-type",
        "ind.rec-uparams",
        "ind.rec-uparams-swap",
        "ind.rule-ctor",
        "ind.rule-nfields",
        "ind.rule-order",
        "ind.rule-rhs",
        "ind.rule-rhs-swap",
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
