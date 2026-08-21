//! What `Kernel::set_render_proofs_as_def` costs and buys, measured on the
//! artefacts this repository actually ships (ADR-0518).
//!
//! # The question
//!
//! Lean has two checkers and they disagree about a proof's opacity (ADR-0517).
//! Lean's *kernel* unfolds anything carrying a value and accepts the whole
//! constructed-real carrier; Lean's *elaborator* refuses to unfold a `theorem`
//! while reducing, so four `CReal` declarations whose type-checking must compute
//! through `Nat.gcd` are refused from `.lean` source. ADR-0517 measured that
//! re-spelling every `theorem` as `def` closes that gap and deliberately did not
//! take the change. This example renders both spellings of every artefact so the
//! cost and the benefit can be read off the same run.
//!
//! # What it emits
//!
//! Under `--emit <dir>`, six modules in two subdirectories, `thm/` (the default
//! rendering — the bytes that ship today) and `def/`:
//!
//! * `FrontDoor.lean` — the shipped single-file front door, one refutation over
//!   the constructed reals, self-contained.
//! * `AxeyumShared.lean` — the shared half of the split layout (ADR-0511),
//!   rooted at what this family of queries REACHES.
//! * `AxeyumCarrier.lean` — the WHOLE carrier, every declaration of the
//!   constructed-real context with no reachability filter. This is the module
//!   Lean's elaborator refuses today and its kernel accepts.
//!
//! Time each pair with the pinned `lean` to get the elaboration cost; the byte
//! sizes are printed here.
//!
//! # The invariant it checks itself
//!
//! `--require-keyword-only` makes the exit status depend on the finding: the
//! `def` rendering must equal the default rendering under a rewrite that
//! replaces the leading `theorem ` of a line by `def `, and nothing else. If the
//! switch ever moves a term, a share name, a binder or a banner byte, that
//! comparison fails. The module's ROOT theorem is excluded from the rewrite
//! because the switch deliberately leaves it a `theorem`.
//!
//! # Usage
//!
//! ```text
//! cargo run -p axeyum-solver --features full --example proof_keyword_cost
//! cargo run -p axeyum-solver --features full --example proof_keyword_cost -- --emit /data0/pk
//! cargo run -p axeyum-solver --features full --example proof_keyword_cost -- --require-keyword-only
//! ```

use std::collections::BTreeSet;

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_lean_kernel::{ExprId, Kernel, NameId};
use axeyum_solver::{LraReconstructCtx, reconstruct_lra_proof};

/// The theorem name the emitted module states, matching the front door's.
const THEOREM: &str = "axeyum_refutation";

/// `x < 0 ∧ 0 ≤ x` — the two-row strict conflict the front door ships.
fn strict_bound_conflict(arena: &mut TermArena) -> Vec<TermId> {
    let x = arena.real_var("x").unwrap();
    let zero = arena.real_const(Rational::integer(0));
    let a1 = arena.real_lt(x, zero).unwrap();
    let a2 = arena.real_le(zero, x).unwrap();
    vec![a1, a2]
}

/// The default rendering, rewritten by replacing the keyword that opens an
/// environment theorem — and nothing else.
///
/// The root `theorem <THEOREM> : …` line is left alone: the switch does not
/// re-spell it, because nothing reduces through a module's root.
fn theorems_as_defs(source: &str) -> String {
    let root = format!("theorem {THEOREM} ");
    source
        .lines()
        .map(|line| match line.strip_prefix("theorem ") {
            Some(rest) if !line.starts_with(&root) => format!("def {rest}\n"),
            _ => format!("{line}\n"),
        })
        .collect()
}

/// How many lines open an environment theorem.
fn theorem_lines(source: &str) -> usize {
    let root = format!("theorem {THEOREM} ");
    source
        .lines()
        .filter(|line| line.starts_with("theorem ") && !line.starts_with(&root))
        .count()
}

/// One artefact, rendered both ways.
struct Pair {
    stem: &'static str,
    what: &'static str,
    thm: String,
    def_: String,
}

impl Pair {
    fn keyword_only(&self) -> bool {
        theorems_as_defs(&self.thm) == self.def_
    }
}

fn render_all() -> Result<(Vec<Pair>, usize, usize), String> {
    let mut arena = TermArena::new();
    let assertions = strict_bound_conflict(&mut arena);
    let mut ctx = LraReconstructCtx::try_new_over_constructed_reals()
        .map_err(|e| format!("the CReal carrier did not build: {e:?}"))?;
    let carrier: Vec<NameId> = ctx.kernel().environment().iter().map(|(n, _)| *n).collect();
    let proof = reconstruct_lra_proof(&mut ctx, &arena, &assertions)
        .map_err(|e| format!("CReal reconstruction failed: {e:?}"))?;
    let goal: ExprId = {
        let f = ctx.arith().logic.false_;
        ctx.kernel_mut().const_(f, vec![])
    };
    let reached: BTreeSet<NameId> = ctx
        .kernel()
        .declarations_reached(&[goal, proof])
        .into_iter()
        .collect();
    let shared_roots: Vec<NameId> = carrier
        .iter()
        .copied()
        .filter(|n| reached.contains(n))
        .collect();

    // Render every artefact with the switch OFF, then with it ON. Same kernel,
    // same terms, same order -- so a byte that moves is the switch's doing.
    let render = |kernel: &Kernel| {
        (
            kernel.render_lean_module_compact(THEOREM, goal, proof),
            kernel
                .render_lean_prelude_module("AxeyumShared", &shared_roots)
                .source()
                .to_owned(),
            kernel
                .render_lean_prelude_module("AxeyumCarrier", &carrier)
                .source()
                .to_owned(),
        )
    };
    let (front_thm, shared_thm, carrier_thm) = render(ctx.kernel());
    ctx.kernel_mut().set_render_proofs_as_def(true);
    let (front_def, shared_def, carrier_def) = render(ctx.kernel());
    ctx.kernel_mut().set_render_proofs_as_def(false);
    // The default must be exactly recoverable: the switch is an option, not a
    // one-way door.
    let (front_again, _, _) = render(ctx.kernel());
    if front_again != front_thm {
        return Err("turning the switch off did not restore the default bytes".to_owned());
    }

    Ok((
        vec![
            Pair {
                stem: "FrontDoor",
                what: "shipped single-file front door (one refutation, self-contained)",
                thm: front_thm,
                def_: front_def,
            },
            Pair {
                stem: "AxeyumShared",
                what: "shared half of the split layout, rooted at the REACHED carrier",
                thm: shared_thm,
                def_: shared_def,
            },
            Pair {
                stem: "AxeyumCarrier",
                what: "the WHOLE carrier, no reachability filter",
                thm: carrier_thm,
                def_: carrier_def,
            },
        ],
        carrier.len(),
        shared_roots.len(),
    ))
}

fn main() {
    let arguments: Vec<String> = std::env::args().collect();
    let require = arguments.iter().any(|a| a == "--require-keyword-only");
    let emit = arguments
        .iter()
        .position(|a| a == "--emit")
        .and_then(|i| arguments.get(i + 1))
        .cloned();

    let (pairs, carrier_len, reached_len) = match render_all() {
        Ok(rendered) => rendered,
        Err(message) => {
            eprintln!("FAIL: {message}");
            std::process::exit(1);
        }
    };

    println!("=== `theorem` vs `def`: what the render option moves");
    println!("    carrier declarations: {carrier_len}; reached by this family: {reached_len}\n");
    let mut keyword_only = true;
    for pair in &pairs {
        let ok = pair.keyword_only();
        keyword_only &= ok;
        let thm = pair.thm.len();
        let def_ = pair.def_.len();
        let lines = theorem_lines(&pair.thm);
        println!("  --- {} ({})", pair.stem, pair.what);
        println!("    theorem spelling : {thm:>9} B");
        println!(
            "    def spelling     : {def_:>9} B  (-{} B = 4 B x {lines} theorem lines)",
            thm.saturating_sub(def_)
        );
        println!("    environment theorem lines : {lines}");
        println!("    differs ONLY by the keyword: {ok}");
    }

    if let Some(directory) = emit {
        for (sub, pick) in [("thm", true), ("def", false)] {
            let path = std::path::Path::new(&directory).join(sub);
            if let Err(e) = std::fs::create_dir_all(&path) {
                eprintln!("FAIL: cannot create {}: {e}", path.display());
                std::process::exit(1);
            }
            for pair in &pairs {
                let file = path.join(format!("{}.lean", pair.stem));
                let body = if pick { &pair.thm } else { &pair.def_ };
                if let Err(e) = std::fs::write(&file, body) {
                    eprintln!("FAIL: cannot write {}: {e}", file.display());
                    std::process::exit(1);
                }
            }
            println!(
                "\nwrote {}/{{FrontDoor,AxeyumShared,AxeyumCarrier}}.lean",
                path.display()
            );
        }
    }

    println!("\nthe def rendering differs from the default ONLY by the keyword: {keyword_only}");
    if require && !keyword_only {
        eprintln!(
            "FAIL: --require-keyword-only: the render option moved something other than the \
             keyword that opens an environment theorem."
        );
        std::process::exit(1);
    }
}
