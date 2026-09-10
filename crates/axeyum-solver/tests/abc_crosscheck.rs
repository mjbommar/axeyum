//! Third-party cross-check of axeyum's AIG bit-blasting layer by **ABC**
//! (Berkeley's combinational/sequential synthesis and verification system),
//! per `docs/solver-comparison-2026-09/11-roadmap-and-plan.md` item 2.4.
//!
//! `docs/solver-comparison-2026-09/09-abc-and-aiger.md` established that
//! axeyum's AIG export (`Aig::to_aiger_ascii`, `crates/axeyum-aig/src/
//! lib.rs:628`) writes ASCII AIGER, while ABC's readers accept binary AIGER
//! only (`references/abc/src/aig/gia/giaAiger.c:1980`), and that the AIGER
//! project's own `aigtoaig` converts ASCII to binary in one hop. This suite
//! is that hop, wired to a real check: two INDEPENDENTLY CONSTRUCTED circuits
//! for the same Boolean function (never sharing gate-building code with each
//! other) are exported, converted, and handed to ABC's `&cec` (combinational
//! equivalence checker) to confirm they agree -- a cross-check of
//! `axeyum-aig`'s own AND/OR/XOR/MUX primitives that shares no code with
//! `axeyum-aig` itself, `axeyum-bv`, or `axeyum-cnf`.
//!
//! Both ABC and `aigtoaig` live in the gitignored `references/` tree (or on
//! `PATH`) and are NOT assumed present: every test here still runs its
//! **semantic** check (brute-force `Aig::eval` over every input, no external
//! tool) unconditionally, and additionally runs the ABC-backed check only
//! when both binaries resolve. Point `AXEYUM_ABC_BIN`/`AXEYUM_AIGTOAIG_BIN`
//! at binaries, or build them:
//!
//! ```sh
//! # aigtoaig -- tiny, two C files, safe to build from source:
//! git clone --depth 1 https://github.com/arminbiere/aiger references/aiger
//! cc -O2 -o references/aiger/aigtoaig references/aiger/aigtoaig.c references/aiger/aiger.c
//!
//! # abc -- LARGE (56 MB, 1.1M LOC). Do NOT build it as part of this gate.
//! # Either point AXEYUM_ABC_BIN at a system/CI-provisioned binary, or accept
//! # that the ABC-backed half of this suite is unexercised (see
//! # scripts/check-abc-crosscheck.sh).
//! ```
//!
//! **A skipping suite is a suite that has never been shown to fail** (the
//! lesson `scripts/check-carcara-gate.sh` documents at length after Carcara
//! sat unused for weeks). This suite avoids that trap two ways: (1) the
//! semantic check never skips -- it needs no external tool and is real
//! evidence on every run; (2) `AXEYUM_REQUIRE_ABC=1` turns an absent
//! `abc`/`aigtoaig` into a panic instead of a quiet pass, for the gate script
//! to set on a host that is supposed to have them.
//!
//! ABC's own verdict is read from **text**, never from its exit status:
//! `Abc_RealMain` (`references/abc/src/base/main/mainReal.c:389`) returns `0`
//! whether `&cec` found the networks equivalent, inequivalent, or undecided
//! -- the same shape of trap as Carcara's `holey` exiting 0. See
//! [`abc_verdict`] for the exact strings, measured from the ABC clone at
//! `fbaae01487b05982739a5636df30687f41a10a2d` on 2026-09-09.
// `and_ab`/`and_ac`/`and_bc`/`and_xc` deliberately mirror the textbook
// full-adder carry-formula variable names (the terms of `(a&b)|(a&c)|(b&c)`
// and `(a&b)|((a^b)&c)`) so the code reads against the identities cited in
// the doc comments above each formula; renaming them to widen the edit
// distance would make the correspondence harder to audit, not easier -- the
// same tradeoff `carcara_crosscheck.rs` makes for `fa_abs`/`fb_abs`/`ga_abs`.
#![allow(clippy::similar_names)]

use std::env;
use std::path::{Path, PathBuf};
use std::process::Command;

use axeyum_aig::{Aig, AigLit};

/// Bit width used by every curated circuit pair in this suite. Small enough
/// that the semantic check (`brute_force_diff`) exhaustively covers all
/// `2^(2*WIDTH)` input pairs in well under a second.
const WIDTH: usize = 4;

// ---------------------------------------------------------------------------
// Circuit builders. Each pair below computes the SAME Boolean function via
// deliberately different gate sequences, so that agreement is evidence about
// the underlying primitives (`Aig::and`/`or`/`xor`) rather than about shared
// code.
// ---------------------------------------------------------------------------

/// XOR built from `Aig::and`/`Aig::or`/negation only -- i.e. WITHOUT calling
/// `Aig::xor` -- so a circuit using this differs structurally from one built
/// with the native XOR gate, even though both compute the same relation:
/// `(a | b) & !(a & b)`.
fn xor_via_and_or(aig: &mut Aig, a: AigLit, b: AigLit) -> AigLit {
    let or_ab = aig.or(a, b);
    let and_ab = aig.and(a, b);
    aig.and(or_ab, and_ab.negated())
}

/// Which carry formula [`build_adder`] uses. `Majority` and `Distributive`
/// are the two textbook full-adder carry identities (provably equal);
/// `Broken` is a deliberate bug -- see [`mislowered_adder_is_rejected`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CarryKind {
    /// `carry_out = maj(a, b, cin) = (a&b) | (a&cin) | (b&cin)`, sum built
    /// with the native `Aig::xor` gate.
    Majority,
    /// `carry_out = (a&b) | ((a^b)&cin)`, sum and the `a^b` term both built
    /// via [`xor_via_and_or`] instead of `Aig::xor` -- a genuinely different
    /// gate sequence computing the same function as `Majority`.
    Distributive,
    /// DELIBERATE BUG: drops the `a&b` term from the `Distributive` carry
    /// formula (`carry_out = (a^b)&cin` only). Bit 0 of the sum is still
    /// correct (there is no incoming carry to lose), but bit 1 onward
    /// computes something other than addition whenever a lower bit position
    /// had both operand bits set. This is the negative control.
    Broken,
}

/// Builds a `width`-bit ripple-carry adder using `kind`'s carry formula.
/// Returns `(aig, a_inputs, b_inputs, sum_outputs)`; inputs are created
/// `a0..a{width-1}, b0..b{width-1}` (LSB-first), so two adders built with
/// different `kind`s share input POSITION even though they are otherwise
/// unrelated graphs -- required both for [`brute_force_diff`] (same input
/// vector drives both) and for ABC's `&cec` (which pairs primary inputs by
/// position across the two AIGER files).
fn build_adder(width: usize, kind: CarryKind) -> (Aig, Vec<AigLit>, Vec<AigLit>, Vec<AigLit>) {
    let mut aig = Aig::new();
    let a_inputs: Vec<AigLit> = (0..width).map(|i| aig.input(format!("a{i}"))).collect();
    let b_inputs: Vec<AigLit> = (0..width).map(|i| aig.input(format!("b{i}"))).collect();
    let mut carry = AigLit::FALSE;
    let mut sums = Vec::with_capacity(width);
    for i in 0..width {
        let a = a_inputs[i];
        let b = b_inputs[i];
        let a_xor_b = match kind {
            CarryKind::Majority => aig.xor(a, b),
            CarryKind::Distributive | CarryKind::Broken => xor_via_and_or(&mut aig, a, b),
        };
        let sum = match kind {
            CarryKind::Majority => aig.xor(a_xor_b, carry),
            CarryKind::Distributive | CarryKind::Broken => xor_via_and_or(&mut aig, a_xor_b, carry),
        };
        let next_carry = match kind {
            CarryKind::Majority => {
                let and_ab = aig.and(a, b);
                let and_ac = aig.and(a, carry);
                let and_bc = aig.and(b, carry);
                let t = aig.or(and_ab, and_ac);
                aig.or(t, and_bc)
            }
            CarryKind::Distributive => {
                let and_ab = aig.and(a, b);
                let and_xc = aig.and(a_xor_b, carry);
                aig.or(and_ab, and_xc)
            }
            CarryKind::Broken => aig.and(a_xor_b, carry),
        };
        carry = next_carry;
        sums.push(sum);
    }
    (aig, a_inputs, b_inputs, sums)
}

/// `width`-bit bitwise equality via `Aig::xor` (native gate) + AND-reduce.
fn build_eq_native(width: usize) -> (Aig, Vec<AigLit>, Vec<AigLit>, Vec<AigLit>) {
    let mut aig = Aig::new();
    let a_inputs: Vec<AigLit> = (0..width).map(|i| aig.input(format!("a{i}"))).collect();
    let b_inputs: Vec<AigLit> = (0..width).map(|i| aig.input(format!("b{i}"))).collect();
    let mut acc = AigLit::TRUE;
    for i in 0..width {
        let bit_xor = aig.xor(a_inputs[i], b_inputs[i]);
        let bit_eq = bit_xor.negated();
        acc = aig.and(acc, bit_eq);
    }
    (aig, a_inputs, b_inputs, vec![acc])
}

/// `width`-bit bitwise equality built two different ways from
/// [`build_eq_native`]: per-bit XNOR via `(¬a∨b)∧(a∨¬b)` (no `Aig::xor`
/// call), AND-reduced by De Morgan (`AND(x_i) = ¬OR(¬x_i)`) instead of
/// direct `Aig::and` folding.
fn build_eq_demorgan(width: usize) -> (Aig, Vec<AigLit>, Vec<AigLit>, Vec<AigLit>) {
    let mut aig = Aig::new();
    let a_inputs: Vec<AigLit> = (0..width).map(|i| aig.input(format!("a{i}"))).collect();
    let b_inputs: Vec<AigLit> = (0..width).map(|i| aig.input(format!("b{i}"))).collect();
    let mut not_eqs: Vec<AigLit> = Vec::with_capacity(width);
    for i in 0..width {
        let a = a_inputs[i];
        let b = b_inputs[i];
        let t1 = aig.or(a.negated(), b);
        let t2 = aig.or(a, b.negated());
        let bit_eq = aig.and(t1, t2);
        not_eqs.push(bit_eq.negated());
    }
    let mut or_not = not_eqs[0];
    for &n in &not_eqs[1..] {
        or_not = aig.or(or_not, n);
    }
    (aig, a_inputs, b_inputs, vec![or_not.negated()])
}

// ---------------------------------------------------------------------------
// The always-available semantic check: brute-force `Aig::eval` over every
// `(a, b)` pair. Needs no external tool, so it is the check this suite can
// never skip.
// ---------------------------------------------------------------------------

/// Exhaustively compares `aig1`/`outs1` against `aig2`/`outs2` over every
/// `width`-bit `(a, b)` input pair. Returns the first differing input and
/// both output vectors, or `None` if the circuits agree everywhere.
fn brute_force_diff(
    aig1: &Aig,
    outs1: &[AigLit],
    aig2: &Aig,
    outs2: &[AigLit],
    width: usize,
) -> Option<(usize, usize, Vec<bool>, Vec<bool>)> {
    for a in 0..(1usize << width) {
        for b in 0..(1usize << width) {
            let mut inputs = Vec::with_capacity(2 * width);
            for i in 0..width {
                inputs.push((a >> i) & 1 == 1);
            }
            for i in 0..width {
                inputs.push((b >> i) & 1 == 1);
            }
            let o1 = aig1.eval_many(outs1, &inputs).expect("eval circuit 1");
            let o2 = aig2.eval_many(outs2, &inputs).expect("eval circuit 2");
            if o1 != o2 {
                return Some((a, b, o1, o2));
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// External-tool resolution -- mirrors `carcara_crosscheck.rs`'s pattern.
// ---------------------------------------------------------------------------

/// Whether `AXEYUM_REQUIRE_ABC=1` is set: an absent `abc` or `aigtoaig` is
/// then a FAILURE rather than a skip. `scripts/check-abc-crosscheck.sh` sets
/// it on a host that is supposed to have both.
fn abc_required() -> bool {
    env::var("AXEYUM_REQUIRE_ABC").unwrap_or_default() == "1"
}

fn which_on_path(name: &str) -> Option<PathBuf> {
    let path_var = env::var_os("PATH")?;
    env::split_paths(&path_var)
        .map(|dir| dir.join(name))
        .find(|candidate| candidate.is_file())
}

fn abc_banner(bin: &Path) {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| println!("AXEYUM-ABC-BIN bin={}", bin.display()));
}

fn aigtoaig_banner(bin: &Path) {
    static ONCE: std::sync::Once = std::sync::Once::new();
    ONCE.call_once(|| println!("AXEYUM-AIGTOAIG-BIN bin={}", bin.display()));
}

/// Resolves the `abc` binary: `AXEYUM_ABC_BIN`, then the conventional
/// reference-clone build path, then `PATH`. Returns `None` (-> the ABC-backed
/// half of the calling test is skipped) unless `AXEYUM_REQUIRE_ABC=1`, in
/// which case absence panics. **Do NOT build ABC from source here or in the
/// gate script** -- it is a 56 MB, 1.1M-line clone; see the module doc.
fn resolve_abc() -> Option<PathBuf> {
    if let Ok(p) = env::var("AXEYUM_ABC_BIN") {
        let path = PathBuf::from(p);
        if path.is_file() {
            abc_banner(&path);
            return Some(path);
        }
    }
    let vendored = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../references/abc/abc");
    if vendored.is_file() {
        abc_banner(&vendored);
        return Some(vendored);
    }
    if let Some(path) = which_on_path("abc") {
        abc_banner(&path);
        return Some(path);
    }
    assert!(
        !abc_required(),
        "AXEYUM_REQUIRE_ABC=1 but no `abc` binary was found. Set AXEYUM_ABC_BIN, or place a \
         binary at references/abc/abc, or put `abc` on PATH. Do not build ABC from source as \
         part of this gate -- see the module doc for why."
    );
    println!("AXEYUM-ABC-SKIPPED no abc binary");
    None
}

/// Resolves the `aigtoaig` binary the same way as [`resolve_abc`], except it
/// is small and safe to build from a `references/aiger` clone -- see the
/// module doc for the one-line build command. Not built automatically here;
/// `scripts/check-abc-crosscheck.sh` does that when the source is present.
fn resolve_aigtoaig() -> Option<PathBuf> {
    if let Ok(p) = env::var("AXEYUM_AIGTOAIG_BIN") {
        let path = PathBuf::from(p);
        if path.is_file() {
            aigtoaig_banner(&path);
            return Some(path);
        }
    }
    let vendored =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../references/aiger/aigtoaig");
    if vendored.is_file() {
        aigtoaig_banner(&vendored);
        return Some(vendored);
    }
    if let Some(path) = which_on_path("aigtoaig") {
        aigtoaig_banner(&path);
        return Some(path);
    }
    assert!(
        !abc_required(),
        "AXEYUM_REQUIRE_ABC=1 but no `aigtoaig` binary was found (needed to convert axeyum's \
         ASCII AIGER export to the binary format ABC's readers require). Set \
         AXEYUM_AIGTOAIG_BIN, or build one: see the module doc."
    );
    println!("AXEYUM-AIGTOAIG-SKIPPED no aigtoaig binary -- binary-AIGER conversion untested");
    None
}

fn scratch_dir(tag: &str) -> PathBuf {
    let dir = env::temp_dir().join(format!("axeyum_abc_crosscheck_{tag}"));
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn export_ascii(aig: &Aig, outputs: &[AigLit], dir: &Path, tag: &str) -> PathBuf {
    let path = dir.join(format!("{tag}.aag"));
    std::fs::write(&path, aig.to_aiger_ascii(outputs)).expect("write ascii aiger");
    path
}

/// Converts `aag` (ASCII AIGER) to binary AIGER via `aigtoaig` and confirms
/// the result actually begins with the binary AIGER magic (`aig ` per
/// `references/aiger/FORMAT`) rather than silently re-emitting ASCII.
fn convert_to_binary(aigtoaig: &Path, aag: &Path) -> PathBuf {
    let bin_path = aag.with_extension("aig");
    let status = Command::new(aigtoaig)
        .arg(aag)
        .arg(&bin_path)
        .status()
        .expect("run aigtoaig");
    assert!(
        status.success(),
        "aigtoaig failed converting {}",
        aag.display()
    );
    let bytes = std::fs::read(&bin_path).expect("read converted aiger");
    assert!(
        bytes.starts_with(b"aig "),
        "{} does not start with the binary AIGER magic 'aig ' -- got {:?}",
        bin_path.display(),
        &bytes[..bytes.len().min(16)]
    );
    bin_path
}

// ---------------------------------------------------------------------------
// ABC `&cec` invocation and verdict parsing.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AbcVerdict {
    Equivalent,
    NotEquivalent,
    Undecided,
    Unparsed,
}

/// Parses ABC's `&cec` verdict from its combined stdout/stderr.
///
/// `&cec f1 f2` (`Abc_CommandAbc9Cec`, `references/abc/src/base/abci/
/// abc.c:43767`, registered at `abc.c:1366`) calls `Cec_ManVerify`
/// (`references/abc/src/proof/cec/cecCec.c:431`), which prints exactly one
/// of three fixed lines -- measured against clone
/// `fbaae01487b05982739a5636df30687f41a10a2d` on 2026-09-09:
///
///   `"Networks are equivalent.  "`      (`cecCec.c:190`, via the
///                                        `Cec_ManVerifyOld` fallback)
///   `"Networks are NOT EQUIVALENT.  "`  (`cecCec.c:198` / `:488`)
///   `"Networks are UNDECIDED.  "`       (`cecCec.c:225`, verbose-only path)
///
/// `Abc_RealMain` (`mainReal.c:389`) `return`s `0` unconditionally after
/// running a batch command, REGARDLESS of which line fired -- so, exactly as
/// with Carcara's `holey` (`scripts/check-carcara-gate.sh`), the verdict is
/// the TEXT, never `$?`. Matched by a distinguishing substring rather than a
/// whole-line match, because ABC pads the line with a trailing `Time = ...`
/// report on the same line. `"NOT EQUIVALENT"` (upper case) can never be
/// mistaken for `"Networks are equivalent."` (lower case) -- the two do not
/// share a substring -- but the NOT-case is still checked first, defensively,
/// and pinned by `abc_verdict_parses_measured_strings` below.
fn abc_verdict(output: &str) -> AbcVerdict {
    let mut verdict = AbcVerdict::Unparsed;
    for line in output.lines() {
        if line.contains("NOT EQUIVALENT") {
            verdict = AbcVerdict::NotEquivalent;
        } else if line.contains("UNDECIDED") {
            verdict = AbcVerdict::Undecided;
        } else if line.contains("Networks are equivalent.") {
            verdict = AbcVerdict::Equivalent;
        }
    }
    verdict
}

/// Runs `abc -q "&cec f1 f2"` and returns its combined stdout/stderr, printing
/// the marker `scripts/check-abc-crosscheck.sh` counts.
///
/// `-q "<cmd>"` is ABC's `BATCH_QUIET` mode (`mainReal.c:169-174`): it runs
/// `<cmd>` and exits without echoing the command line first. `-c` and `-q`
/// must not both be passed -- each independently APPENDS to the command
/// buffer (`mainReal.c:158-175`), so combining them runs two commands
/// separated by `;` rather than one.
fn run_cec(abc: &Path, f1: &Path, f2: &Path, tag: &str) -> String {
    let script = format!("&cec {} {}", f1.display(), f2.display());
    let out = Command::new(abc)
        .arg("-q")
        .arg(&script)
        .output()
        .expect("run abc");
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    println!(
        "AXEYUM-ABC-CHECKED {tag} verdict={:?}",
        abc_verdict(&combined)
    );
    combined
}

// ---------------------------------------------------------------------------
// Shared check bodies.
// ---------------------------------------------------------------------------

/// Asserts `(aig1, outs1)` and `(aig2, outs2)` agree everywhere: always via
/// brute-force `Aig::eval`, and additionally via ABC's `&cec` when both
/// external binaries resolve.
fn check_pair_equivalent(
    tag: &str,
    aig1: &Aig,
    outs1: &[AigLit],
    aig2: &Aig,
    outs2: &[AigLit],
    width: usize,
) {
    if let Some((a, b, o1, o2)) = brute_force_diff(aig1, outs1, aig2, outs2, width) {
        panic!("{tag}: circuits differ at a={a} b={b}: {o1:?} vs {o2:?}");
    }
    println!(
        "AXEYUM-ABC-SEMANTIC-CHECK {tag} brute-force equivalent over {} input pairs",
        (1usize << width) * (1usize << width)
    );

    let Some(aigtoaig) = resolve_aigtoaig() else {
        return;
    };
    let Some(abc) = resolve_abc() else {
        return;
    };
    let dir = scratch_dir(tag);
    let ascii1 = export_ascii(aig1, outs1, &dir, &format!("{tag}_a"));
    let ascii2 = export_ascii(aig2, outs2, &dir, &format!("{tag}_b"));
    let bin1 = convert_to_binary(&aigtoaig, &ascii1);
    let bin2 = convert_to_binary(&aigtoaig, &ascii2);
    let out = run_cec(&abc, &bin1, &bin2, tag);
    assert_eq!(
        abc_verdict(&out),
        AbcVerdict::Equivalent,
        "{tag}: abc &cec did not confirm equivalence:\n{out}"
    );
}

/// Asserts `(aig1, outs1)` and `(aig2, outs2)` DIFFER: always via brute-force
/// `Aig::eval`, and additionally via ABC's `&cec` when both external binaries
/// resolve. Used only by the negative control.
fn check_pair_not_equivalent(
    tag: &str,
    aig1: &Aig,
    outs1: &[AigLit],
    aig2: &Aig,
    outs2: &[AigLit],
    width: usize,
) {
    let diff = brute_force_diff(aig1, outs1, aig2, outs2, width);
    let (a, b, o1, o2) = diff.unwrap_or_else(|| {
        panic!(
            "{tag}: negative control circuits are semantically IDENTICAL -- the deliberate bug \
             did not change behavior; this negative control is vacuous and must be fixed"
        )
    });
    println!(
        "AXEYUM-ABC-SEMANTIC-CHECK {tag} brute-force confirms a real difference at a={a} b={b}: \
         {o1:?} vs {o2:?}"
    );

    let Some(aigtoaig) = resolve_aigtoaig() else {
        return;
    };
    let Some(abc) = resolve_abc() else {
        return;
    };
    let dir = scratch_dir(tag);
    let ascii1 = export_ascii(aig1, outs1, &dir, &format!("{tag}_a"));
    let ascii2 = export_ascii(aig2, outs2, &dir, &format!("{tag}_b"));
    let bin1 = convert_to_binary(&aigtoaig, &ascii1);
    let bin2 = convert_to_binary(&aigtoaig, &ascii2);
    let out = run_cec(&abc, &bin1, &bin2, tag);
    assert_eq!(
        abc_verdict(&out),
        AbcVerdict::NotEquivalent,
        "{tag}: abc &cec did not flag the deliberately mis-lowered pair as inequivalent:\n{out}"
    );
}

// ---------------------------------------------------------------------------
// Tests.
// ---------------------------------------------------------------------------

/// Curated instance 1: two independently-built 4-bit adders (textbook
/// majority-gate vs. distributive carry formula; the sum bit is built with
/// the native `Aig::xor` gate in one and hand-expanded AND/OR/NOT in the
/// other). Expected: equivalent.
#[test]
fn adder_majority_vs_distributive_are_equivalent() {
    let (aig1, _a1, _b1, outs1) = build_adder(WIDTH, CarryKind::Majority);
    let (aig2, _a2, _b2, outs2) = build_adder(WIDTH, CarryKind::Distributive);
    check_pair_equivalent(
        "adder_majority_vs_distributive",
        &aig1,
        &outs1,
        &aig2,
        &outs2,
        WIDTH,
    );
}

/// Curated instance 2: two independently-built 4-bit bitwise-equality
/// circuits (native XOR + AND-reduce vs. hand-expanded XNOR + De Morgan
/// OR-reduce). Expected: equivalent.
#[test]
fn eq_native_vs_eq_demorgan_are_equivalent() {
    let (aig1, _a1, _b1, outs1) = build_eq_native(WIDTH);
    let (aig2, _a2, _b2, outs2) = build_eq_demorgan(WIDTH);
    check_pair_equivalent(
        "eq_native_vs_eq_demorgan",
        &aig1,
        &outs1,
        &aig2,
        &outs2,
        WIDTH,
    );
}

/// THE NEGATIVE CONTROL. `build_adder(_, CarryKind::Broken)` deliberately
/// drops the `a & b` term from the carry formula -- a real, plausible
/// bit-blaster bug class (CLAUDE.md's Hard Rule on underspecified-operator
/// fuzz coverage exists for exactly this shape of defect: a wrong-unsat once
/// shipped from a folded convention a fuzz structurally could not reach).
/// This test asserts the cross-check DETECTS the bug, both at the
/// always-available semantic layer (`Aig::eval`, no external tool -- this is
/// the part that ran in THIS environment, `abc` not being installed) and, when
/// ABC is present, via `&cec` reporting `NOT EQUIVALENT`.
///
/// To reproduce "the gate fails on a deliberately mis-lowered operator"
/// directly: change `CarryKind::Broken`'s arm in [`build_adder`] to compute
/// the SAME formula as `CarryKind::Distributive` (i.e. silently "fix" the
/// bug this test exists to catch) -- `check_pair_not_equivalent`'s
/// `diff.unwrap_or_else` panics because the brute-force search no longer
/// finds a difference, and this is the one test in the suite that dies.
#[test]
fn mislowered_adder_is_rejected() {
    let (aig1, _a1, _b1, outs1) = build_adder(WIDTH, CarryKind::Majority);
    let (aig2, _a2, _b2, outs2) = build_adder(WIDTH, CarryKind::Broken);
    check_pair_not_equivalent(
        "adder_majority_vs_broken",
        &aig1,
        &outs1,
        &aig2,
        &outs2,
        WIDTH,
    );
}

/// Pins [`abc_verdict`] against the literal strings ABC prints (see the
/// citations on that function), so a change in ABC's wording -- or a
/// substring-matching bug like Carcara's `"invalid".contains("valid")` trap
/// -- is caught here first rather than by a false pass elsewhere. Needs no
/// external binary.
#[test]
fn abc_verdict_parses_measured_strings() {
    assert_eq!(
        abc_verdict("Networks are equivalent.  Time = 0.00 sec\n"),
        AbcVerdict::Equivalent
    );
    assert_eq!(
        abc_verdict("Networks are NOT EQUIVALENT.  Time = 0.00 sec\n"),
        AbcVerdict::NotEquivalent
    );
    assert_eq!(
        abc_verdict("Networks are UNDECIDED.  Time = 0.00 sec\n"),
        AbcVerdict::Undecided
    );
    assert_eq!(
        abc_verdict("garbage, no verdict line at all\n"),
        AbcVerdict::Unparsed
    );
    // The substring trap this function must not fall into: a line reporting
    // inequivalence must never be read as reporting equivalence.
    assert_ne!(
        abc_verdict("Networks are NOT EQUIVALENT.  Time = 0.00 sec\n"),
        AbcVerdict::Equivalent
    );
    // Last verdict line wins, mirroring `carcara_verdict`'s convention.
    assert_eq!(
        abc_verdict("Networks are UNDECIDED.  \nNetworks are equivalent.  \n"),
        AbcVerdict::Equivalent
    );
}

/// Demonstrates the pipeline up to the point ABC would be invoked, and
/// confirms the exported ASCII AIGER is well-formed, independent of whether
/// `abc` itself is available. This is the half of the cross-check that CAN
/// run on a host with `aigtoaig` but no `abc`.
#[test]
fn aiger_export_and_binary_conversion_round_trip() {
    let (aig, _a, _b, outs) = build_adder(WIDTH, CarryKind::Majority);
    let dir = scratch_dir("roundtrip");
    let aag = export_ascii(&aig, &outs, &dir, "roundtrip");
    let ascii = std::fs::read_to_string(&aag).expect("read ascii aiger");
    let header_line = ascii.lines().next().expect("ascii aiger has a header line");
    let header: Vec<&str> = header_line.split_whitespace().collect();
    assert_eq!(
        header.first().copied(),
        Some("aag"),
        "not an ASCII AIGER header: {header_line}"
    );
    assert_eq!(header.len(), 6, "aag M I L O A header: {header_line}");
    let inputs: usize = header[2].parse().expect("I field");
    let latches: usize = header[3].parse().expect("L field");
    let outputs: usize = header[4].parse().expect("O field");
    assert_eq!(inputs, 2 * WIDTH, "input count");
    assert_eq!(
        latches, 0,
        "axeyum-aig is purely combinational -- no latches"
    );
    assert_eq!(outputs, outs.len(), "output count");

    let Some(aigtoaig) = resolve_aigtoaig() else {
        println!(
            "AXEYUM-ABC-CROSSCHECK: aigtoaig unavailable -- binary AIGER conversion NOT \
             exercised this run (ASCII header well-formedness was still checked above)"
        );
        return;
    };
    let bin = convert_to_binary(&aigtoaig, &aag);
    println!(
        "AXEYUM-ABC-CROSSCHECK: exported ASCII AIGER converted to a magic-checked binary AIGER \
         at {}",
        bin.display()
    );
}
