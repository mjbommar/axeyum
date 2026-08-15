//! Reduce a `TypeMismatch` decline to the **smallest pair of terms** the kernel
//! refuses to identify, inside the very staging environment that refused them.
//!
//! Written for `Nat.bitwise._unary`, the top declined root in both the
//! `Init`+`Std` and the Mathlib scale censuses (236 of 500 and 186 of 400
//! sampled streams; its own stream admits 301 of 302 records and refuses only
//! the declaration). It is the well-founded-recursion unary helper shape —
//! `WellFounded.Nat.fix` over a `PSigma`-packed argument, an `InvImage`
//! relation, and a dependent `PSigma.casesOn` motive — and
//! `Nat.Linear.Poly.denote_reverse`, `Nat.Linear.ExprCnstr.denote_toNormPoly`
//! and the `Std.DTreeMap.Internal.*.eq_def` roots are the same family.
//!
//! `lean4export_census` reports the decline as
//! `TypeMismatch { expected: ExprId(61873), got: ExprId(61879) }`. Two arena
//! indices are not a diagnosis: they cannot be printed after the fact, because
//! the staging kernel is dropped with the census. This runs the same records
//! through the same gate via [`probe_first_decline`], which hands the failing
//! kernel to an inspector, and then walks *down* the two terms — whnf, spine,
//! congruence, binders — printing the first pair at each depth that the kernel
//! itself says are not definitionally equal.
//!
//! Nothing here admits anything. The refused declaration is absent from the
//! kernel the inspector sees, and no `Kernel` escapes the call.
//!
//! # The one thing this probe cannot see, and it cost a detour
//!
//! `KernelError` carries two `ExprId`s and nothing else, so the inspector
//! reduces them in a **fresh, empty** `LocalContext`. Every free variable in the
//! pair is therefore typeless *and valueless* here, while the checker that
//! refused them had a context. Concretely: a variable bound by a local `let` has
//! a value in the real context and reduces; in this probe it is inert, so the
//! descent can stop on a bare `_fvar.N` that the kernel would have reduced
//! further. That is exactly what happened on `Nat.bitwise._unary` — the printed
//! stop was `_fvar.34` against a `Nat.div` reduct, and `_fvar.34` turned out to
//! be `let n' := n / 2`. Read a bare `_fvar` in the output as *"ask the local
//! context"*, not as *"the kernel is stuck here"*.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-import --example wf_recursion_decline_probe -- \
//!     Nat.bitwise._unary.ndjson
//! ```
//!
//! On a fixed root the probe prints `PROBE|no kernel decline` — which is what
//! `Nat.bitwise._unary` does since ζ moved into `whnf_core`. Point it at
//! `Nat.Linear.Poly.denote_reverse` for a stream that still declines.

use std::fs::File;
use std::io::BufReader;

use axeyum_lean_import::{ImportLimits, probe_first_decline};
use axeyum_lean_kernel::{ExprId, ExprNode, Kernel, KernelError};

/// Reduction on a real `Init`+`Std` closure recurses on term structure; the
/// census example runs on 512 MB for the same reason.
const PROBE_STACK_BYTES: usize = 512 * 1024 * 1024;

/// How far `narrow` descends before it stops. A missing def-eq rule shows up in
/// the first few levels; past that the output stops being readable.
const MAX_DEPTH: usize = 24;

/// Longest rendered term printed in full. Beyond this the probe prints a head
/// summary instead, so one 200 kB `WellFounded.fix` body cannot bury the pair
/// the run exists to exhibit.
const MAX_RENDER: usize = 4000;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let worker = std::thread::Builder::new()
        .name("wf-probe".to_owned())
        .stack_size(PROBE_STACK_BYTES)
        .spawn(|| probe().map_err(|error| error.to_string()))?;
    match worker.join() {
        Ok(Ok(())) => Ok(()),
        Ok(Err(error)) => Err(error.into()),
        Err(_) => Err("probe thread panicked".into()),
    }
}

fn probe() -> Result<(), Box<dyn std::error::Error>> {
    let path = std::env::args_os()
        .nth(1)
        .ok_or("usage: wf_recursion_decline_probe <export.ndjson>")?;
    let reader = BufReader::new(File::open(&path)?);

    let mut limits = ImportLimits::default();
    if let Ok(v) = std::env::var("AXEYUM_PROBE_MAX_RECORDS") {
        limits.max_records = v.parse()?;
    }

    let probed = probe_first_decline(reader, limits, |kernel, error| {
        let KernelError::TypeMismatch { expected, got } = *error else {
            println!("DECLINE is not a TypeMismatch; nothing to narrow");
            return None;
        };
        println!("EXPECTED (declared type)");
        println!("  {}", render(kernel, expected));
        println!("GOT (inferred type of the value)");
        println!("  {}", render(kernel, got));
        println!();
        println!("--- narrowing ---");
        let mut trail = Vec::new();
        narrow(kernel, expected, got, 0, &mut trail);
        Some(trail)
    })?;

    match probed {
        None => {
            println!("PROBE|no kernel decline; the stream imports cleanly");
        }
        Some(decline) => {
            println!();
            println!(
                "PROBE|line={}|declaration={}|code={}|detail={}|narrowed_depth={}",
                decline.line,
                decline.declaration,
                decline.code,
                decline.detail,
                decline.inspected.as_ref().map_or(0, Vec::len),
            );
        }
    }
    Ok(())
}

/// One step of the descent, kept so the caller can report how deep it got.
#[derive(Debug, Clone, PartialEq, Eq)]
struct NarrowStep {
    depth: usize,
    reason: String,
}

fn render(kernel: &Kernel, e: ExprId) -> String {
    let text = kernel.render_lean(e);
    if text.len() <= MAX_RENDER {
        return text;
    }
    let mut cut = MAX_RENDER;
    while cut > 0 && !text.is_char_boundary(cut) {
        cut -= 1;
    }
    format!("{}... <{} bytes total>", &text[..cut], text.len())
}

/// Split an application spine into its head and arguments, outermost-last.
fn spine(kernel: &Kernel, mut e: ExprId) -> (ExprId, Vec<ExprId>) {
    let mut args = Vec::new();
    while let ExprNode::App(fun, arg) = *kernel.expr_node(e) {
        args.push(arg);
        e = fun;
    }
    args.reverse();
    (e, args)
}

/// Walk down to the smallest pair the checker refuses.
///
/// The invariant is that `x` and `y` entering this function are already known
/// **not** definitionally equal. Each level reduces both to weak head normal
/// form and asks which sub-obligation of the congruence failed; the first one
/// that is itself not def-eq is the one recursed into. The last line printed is
/// therefore a pair the kernel refuses whose immediate sub-obligations it
/// accepts — the actual missing rule.
fn narrow(kernel: &mut Kernel, x: ExprId, y: ExprId, depth: usize, trail: &mut Vec<NarrowStep>) {
    let pad = "  ".repeat(depth);
    if depth > MAX_DEPTH {
        println!("{pad}(depth limit {MAX_DEPTH})");
        return;
    }
    let xw = kernel.whnf(x);
    let yw = kernel.whnf(y);

    // Binders first: a `Pi`/`Pi` or `Lam`/`Lam` pair is compared by domain and
    // then by body under one shared local, which is what the kernel does and
    // what keeps the printed pair small.
    let xn = kernel.expr_node(xw).clone();
    let yn = kernel.expr_node(yw).clone();
    match (&xn, &yn) {
        (ExprNode::Pi(_, xd, xb, _), ExprNode::Pi(_, yd, yb, _))
        | (ExprNode::Lam(_, xd, xb, _), ExprNode::Lam(_, yd, yb, _)) => {
            let binder = if matches!(xn, ExprNode::Pi(..)) {
                "Pi"
            } else {
                "Lam"
            };
            let (xd, yd, xb, yb) = (*xd, *yd, *xb, *yb);
            if !kernel.def_eq(xd, yd) {
                let reason = format!("{binder} DOMAIN differs");
                println!("{pad}depth={depth} {reason}");
                trail.push(NarrowStep {
                    depth,
                    reason: reason.clone(),
                });
                narrow(kernel, xd, yd, depth + 1, trail);
                return;
            }
            let fvar = kernel.fvar(1_000_000 + depth as u64);
            let xb = kernel.instantiate(xb, &[fvar]);
            let yb = kernel.instantiate(yb, &[fvar]);
            let reason = format!("{binder} BODY differs (domains agree)");
            println!("{pad}depth={depth} {reason}");
            trail.push(NarrowStep {
                depth,
                reason: reason.clone(),
            });
            narrow(kernel, xb, yb, depth + 1, trail);
            return;
        }
        _ => {}
    }

    let (xf, xargs) = spine(kernel, xw);
    let (yf, yargs) = spine(kernel, yw);
    let head_x = render(kernel, xf);
    let head_y = render(kernel, yf);
    println!(
        "{pad}depth={depth} lhs_head={head_x} ({} args)  rhs_head={head_y} ({} args)",
        xargs.len(),
        yargs.len()
    );

    if xargs.len() != yargs.len() || !kernel.def_eq(xf, yf) {
        // Stuck: the two sides are not the same congruence obligation at all.
        // This is the pair, and it is as small as the descent can make it.
        let reason = if xargs.len() == yargs.len() {
            "HEADS not def-eq".to_owned()
        } else {
            "ARITY differs".to_owned()
        };
        println!("{pad}  STOP: {reason}");
        println!("{pad}  lhs = {}", render(kernel, xw));
        println!("{pad}  rhs = {}", render(kernel, yw));
        trail.push(NarrowStep { depth, reason });
        return;
    }

    for (index, (&xa, &ya)) in xargs.iter().zip(yargs.iter()).enumerate() {
        if !kernel.def_eq(xa, ya) {
            let reason = format!("ARG {index} of {head_x} differs");
            println!("{pad}  {reason}");
            trail.push(NarrowStep {
                depth,
                reason: reason.clone(),
            });
            narrow(kernel, xa, ya, depth + 1, trail);
            return;
        }
    }

    // Every sub-obligation the congruence rule generates is accepted, yet the
    // whole is refused. That is a def-eq rule the kernel does not have, applied
    // at exactly this pair.
    println!("{pad}  STOP: head and every argument are def-eq, but the pair is NOT");
    println!("{pad}  lhs = {}", render(kernel, xw));
    println!("{pad}  rhs = {}", render(kernel, yw));
    trail.push(NarrowStep {
        depth,
        reason: "congruence holds pointwise but the pair is refused".to_owned(),
    });
}
