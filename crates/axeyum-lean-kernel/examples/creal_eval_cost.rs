//! **The exact-real evaluation cost envelope** (roadmap W1-12,
//! `docs/math-department/11-applied-and-computational.md`'s reviewer
//! question: *what does it cost to evaluate π to a stated precision through
//! this representation?*).
//!
//! `CReal` is a regular sequence of rationals: `x : Nat -> Rat` with
//! `|x_m - x_n| <= 1/(m+1) + 1/(n+1)` (`creal.rs`'s own convention). This
//! measures the wall-clock cost of computing `CReal.seq x n` -- the `n`th
//! rational sample -- for `x` in `{pi, e, sqrt 2, exp 1}`, at increasing `n`,
//! through the kernel's OWN reduction machinery (`Kernel::whnf`, the same
//! engine that checks every proof in this repository). No new kernel
//! declaration is added; every term built here is transient and discarded.
//!
//! ## Method
//!
//! 1. Build the `creal` prelude (`build_creal_prelude`), exactly as every
//!    other `CReal` example and test does.
//! 2. Build the query index `n` **two ways**: as a `Nat` LITERAL
//!    (`Lit::Nat`, the kernel's accelerated bignum representation -- see
//!    `reduce_nat_binop`/`reduce_nat_succ` in `tc.rs`) and as a genuine
//!    UNARY `Nat` (`Nat.succ (Nat.succ (... Nat.zero))`, built exactly the
//!    way `linarith/generic.rs::nat_num_ctx` and this development's own
//!    internal numerals are built -- see `creal/pi.rs`'s module doc: "every
//!    numeral this prelude builds is unary and the kernel's binary-literal
//!    fast path never fires"). Both encode the SAME mathematical value.
//! 3. Apply `CReal.seq` to the target value and to `n`, then take the
//!    `Rat.num`/`Rat.den` projections and fully normalize each with a
//!    hand-rolled deep normalizer (`deep_nf`, below) built only from public
//!    `Kernel::whnf`/`Kernel::expr_node` calls -- the same primitives
//!    `Kernel::add_declaration` uses to check a proof's definitional
//!    equality obligations. This is deliberately the SAME mechanism the
//!    kernel already uses when it checks e.g. `CReal.threeLePi`; nothing
//!    kernel-internal is bypassed or approximated.
//! 4. Time each `(target, encoding, n)` cell's normalization wall-clock,
//!    and read off the resulting numerator/denominator digit counts.
//!
//! Every run is wrapped in `on_a_deep_stack` (`stack.rs`): `deep_nf`
//! recurses one Rust stack frame per unary `Nat.succ` layer while reading
//! back a unary result, which for the magnitudes this file finds is deep
//! enough to need it.
//!
//! ## What this does NOT measure
//!
//! The reported digit counts are the FINAL, gcd-reduced numerator and
//! denominator. `Rat.add`/`Rat.mul`'s naive pre-normalization numerator is
//! at least as large (`Rat.add`'s numerator before `gcd`-division is
//! `a.num*b.den + b.num*a.den`), so the true peak magnitude formed mid
//! computation is >= the reported final one, not measured here -- doing
//! that honestly needs an instrumented kernel build, which this
//! measurement-only lane does not touch. The final magnitude is the number
//! the reader can independently reproduce from this file, which is why it
//! is what gets reported.
//!
//! ## Run
//!
//! ```sh
//! scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example creal_eval_cost
//! # then, for TIMING, run the prebuilt binary directly (never under the
//! # cargo-serialized.sh flock, which measures the queue, not the work):
//! ./target/release/examples/creal_eval_cost --max-n 6
//! ```

use std::env;
use std::io::Write as _;
use std::time::Instant;

use axeyum_lean_kernel::{
    CRealPrelude, ExprId, ExprNode, Kernel, Lit, NameId, build_creal_prelude, on_a_deep_stack,
};
use num_bigint::{BigInt, BigUint};

#[derive(Clone, Copy, Debug)]
enum Encoding {
    /// The kernel's accelerated bignum `Lit::Nat` representation.
    Literal,
    /// `Nat.succ (Nat.succ (... Nat.zero))`, exactly as this development's
    /// own internal numerals are built (`linarith/generic.rs::nat_num_ctx`).
    Unary,
}

impl Encoding {
    fn label(self) -> &'static str {
        match self {
            Encoding::Literal => "literal",
            Encoding::Unary => "unary",
        }
    }
}

/// The handful of names `deep_nf`/`read_nat`/`read_int` need to recognize
/// `Nat`/`Int` normal forms. Everything else is opaque to them.
struct Consts {
    nat_zero: NameId,
    nat_succ: NameId,
    int_of_nat: NameId,
    int_neg_succ: NameId,
}

/// Build the `Nat` value `n` as a literal `Lit::Nat` bignum -- the
/// accelerated representation `reduce_nat_binop`/`reduce_nat_succ` (`tc.rs`)
/// recognize directly.
fn unary_zero_succ(kernel: &mut Kernel, c: &Consts, n: u64) -> ExprId {
    let mut e = kernel.const_(c.nat_zero, vec![]);
    for _ in 0..n {
        let s = kernel.const_(c.nat_succ, vec![]);
        e = kernel.app(s, e);
    }
    e
}

fn literal_nat(kernel: &mut Kernel, n: u64) -> ExprId {
    kernel.lit(Lit::nat(n))
}

/// Full (deep) normal form, built only from public `Kernel::whnf` /
/// `Kernel::expr_node` / `Kernel::app` calls -- the same primitives
/// `Kernel::add_declaration`'s definitional-equality check uses internally.
/// `Kernel::whnf` reduces the head redex chain only; this recurses into
/// application arguments too, and re-checks the rebuilt application for a
/// further head reduction, to a fixed point (detected by `ExprId` equality:
/// the interner hash-conses, so two structurally-identical rebuilds compare
/// equal in O(1) without a second traversal).
static DEEP_NF_STEPS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

fn deep_nf(kernel: &mut Kernel, e: ExprId) -> ExprId {
    let step = DEEP_NF_STEPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if step.is_multiple_of(50_000) {
        eprintln!("# deep_nf step {step} (about to whnf ExprId {})", e.index());
    }
    let t0 = std::time::Instant::now();
    let cur = kernel.whnf(e);
    let dt = t0.elapsed();
    if dt.as_millis() > 200 || step.is_multiple_of(50_000) {
        eprintln!("#   whnf({}) -> {} took {:?}", e.index(), cur.index(), dt);
    }
    let node = kernel.expr_node(cur).clone();
    if let ExprNode::App(f, a) = node {
        let f2 = deep_nf(kernel, f);
        let a2 = deep_nf(kernel, a);
        let next = kernel.app(f2, a2);
        if next != cur {
            return deep_nf(kernel, next);
        }
        return next;
    }
    cur
}

/// Read a fully-normalized `Nat` value: either a `Lit::Nat` bignum (the
/// accelerated path fired) or a canonical `Nat.succ (... Nat.zero)`
/// constructor chain (it never fired) -- counted iteratively, never
/// recursively, so this reader itself cannot be the stack-depth bottleneck.
fn read_nat_from_normal(
    kernel: &mut Kernel,
    c: &Consts,
    mut cur: ExprId,
) -> Result<BigUint, String> {
    let mut extra_succs: u64 = 0;
    loop {
        let node = kernel.expr_node(cur).clone();
        match node {
            ExprNode::Lit(Lit::Nat(value)) => {
                let base: BigUint = value
                    .to_string()
                    .parse()
                    .map_err(|err| format!("unreadable Nat literal: {err}"))?;
                return Ok(base + BigUint::from(extra_succs));
            }
            ExprNode::Const(name, _) if name == c.nat_zero => {
                return Ok(BigUint::from(extra_succs));
            }
            ExprNode::App(f, a) => {
                let f_node = kernel.expr_node(f).clone();
                match f_node {
                    ExprNode::Const(name, _) if name == c.nat_succ => {
                        extra_succs = extra_succs
                            .checked_add(1)
                            .ok_or_else(|| "Nat succ-chain overflowed u64 count".to_string())?;
                        cur = a;
                    }
                    _ => return Err("stuck Nat normal form (App head is not Nat.succ)".into()),
                }
            }
            other => return Err(format!("stuck Nat normal form: {other:?}")),
        }
    }
}

fn read_nat(kernel: &mut Kernel, c: &Consts, e: ExprId) -> Result<BigUint, String> {
    let normal = deep_nf(kernel, e);
    read_nat_from_normal(kernel, c, normal)
}

#[allow(clippy::many_single_char_names)]
fn read_int(kernel: &mut Kernel, c: &Consts, e: ExprId) -> Result<BigInt, String> {
    let normal = deep_nf(kernel, e);
    let node = kernel.expr_node(normal).clone();
    let ExprNode::App(f, a) = node else {
        return Err("stuck Int normal form (not an application)".into());
    };
    let f_node = kernel.expr_node(f).clone();
    let ExprNode::Const(name, _) = f_node else {
        return Err("stuck Int normal form (head is not a constant)".into());
    };
    if name == c.int_of_nat {
        let n = read_nat(kernel, c, a)?;
        Ok(BigInt::from(n))
    } else if name == c.int_neg_succ {
        let n = read_nat(kernel, c, a)?;
        Ok(-(BigInt::from(n) + BigInt::from(1u8)))
    } else {
        Err("stuck Int normal form (head is neither Int.ofNat nor Int.negSucc)".into())
    }
}

struct Target {
    name: &'static str,
    value: ExprId,
    reference: f64,
}

fn build_targets(kernel: &mut Kernel, p: &CRealPrelude) -> Vec<Target> {
    let one = kernel.const_(p.one, vec![]);
    let add = kernel.const_(p.add, vec![]);
    let add_one = kernel.app(add, one);
    let two = kernel.app(add_one, one);

    let pi_val = kernel.const_(p.pi.pi, vec![]);
    let e_val = kernel.const_(p.e, vec![]);
    let sqrt_fn = kernel.const_(p.sqrt, vec![]);
    let sqrt2_val = kernel.app(sqrt_fn, two);
    let exp_fn = kernel.const_(p.exp_fn.exp_fn, vec![]);
    let exp1_val = kernel.app(exp_fn, one);

    vec![
        Target {
            name: "zero",
            value: kernel.const_(p.zero, vec![]),
            reference: 0.0,
        },
        Target {
            name: "one",
            value: one,
            reference: 1.0,
        },
        Target {
            name: "two",
            value: two,
            reference: 2.0,
        },
        Target {
            name: "pi",
            value: pi_val,
            reference: std::f64::consts::PI,
        },
        Target {
            name: "e",
            value: e_val,
            reference: std::f64::consts::E,
        },
        Target {
            name: "sqrt2",
            value: sqrt2_val,
            reference: std::f64::consts::SQRT_2,
        },
        Target {
            name: "exp1",
            value: exp1_val,
            reference: std::f64::consts::E,
        },
    ]
}

fn run() {
    let max_n: u64 = env::args()
        .skip(1)
        .find_map(|arg| arg.strip_prefix("--max-n=").map(str::to_owned))
        .or_else(|| {
            let mut it = env::args().skip(1);
            while let Some(a) = it.next() {
                if a == "--max-n" {
                    return it.next();
                }
            }
            None
        })
        .and_then(|s| s.parse().ok())
        .unwrap_or(4);
    let only: Option<String> = env::args()
        .skip(1)
        .find_map(|arg| arg.strip_prefix("--only=").map(str::to_owned));

    let build_start = Instant::now();
    let mut kernel = Kernel::new();
    let p = build_creal_prelude(&mut kernel).expect("the CReal development must build");
    eprintln!(
        "# creal prelude built in {:.3}s",
        build_start.elapsed().as_secs_f64()
    );

    let c = Consts {
        nat_zero: p.rat.int.nat.zero,
        nat_succ: p.rat.int.nat.succ,
        int_of_nat: p.rat.int.of_nat,
        int_neg_succ: p.rat.int.neg_succ,
    };
    let seq = kernel.const_(p.seq, vec![]);
    let rat_num = p.rat.int.rat_num;
    let rat_den = p.rat.int.rat_den;

    let targets = build_targets(&mut kernel, &p);

    println!(
        "target\tencoding\tn\twall_ms\tnum_digits\tden_digits\tapprox\tabs_error_vs_f64\tstatus"
    );
    std::io::stdout().flush().ok();

    for target in &targets {
        if let Some(only) = &only
            && target.name != only
        {
            continue;
        }
        for encoding in [Encoding::Literal, Encoding::Unary] {
            for n in 0..=max_n {
                let n_expr = match encoding {
                    Encoding::Literal => literal_nat(&mut kernel, n),
                    Encoding::Unary => unary_zero_succ(&mut kernel, &c, n),
                };
                let seq_at_value = kernel.app(seq, target.value);
                let applied = kernel.app(seq_at_value, n_expr);
                let num_const = kernel.const_(rat_num, vec![]);
                let den_const = kernel.const_(rat_den, vec![]);
                let num_expr = kernel.app(num_const, applied);
                let den_expr = kernel.app(den_const, applied);

                let start = Instant::now();
                let num_res = read_int(&mut kernel, &c, num_expr);
                let den_res = read_nat(&mut kernel, &c, den_expr);
                let wall_ms = start.elapsed().as_secs_f64() * 1000.0;

                match (num_res, den_res) {
                    (Ok(num), Ok(den)) if den != BigUint::from(0u8) => {
                        let num_digits = num.to_string().trim_start_matches('-').len();
                        let den_digits = den.to_string().len();
                        let approx = num.to_string().parse::<f64>().unwrap_or(f64::NAN)
                            / den.to_string().parse::<f64>().unwrap_or(f64::NAN);
                        let abs_error = (approx - target.reference).abs();
                        println!(
                            "{}\t{}\t{n}\t{wall_ms:.1}\t{num_digits}\t{den_digits}\t{approx:.12}\t{abs_error:.3e}\tok",
                            target.name,
                            encoding.label(),
                        );
                    }
                    (num_res, den_res) => {
                        let reason = num_res
                            .err()
                            .or(den_res.err())
                            .unwrap_or_else(|| "denominator was zero".to_string());
                        println!(
                            "{}\t{}\t{n}\t{wall_ms:.1}\tNA\tNA\tNA\tNA\terror: {reason}",
                            target.name,
                            encoding.label(),
                        );
                    }
                }
                std::io::stdout().flush().ok();
            }
        }
    }
}

fn main() {
    on_a_deep_stack(run);
}
