//! Build ONE prelude on a thread of an EXACT, caller-given stack size, and let
//! the exit status say whether that much stack was enough.
//!
//! This exists so that "how much stack does the kernel need?" is a measurement
//! rather than folklore. It is the probe `scripts/check-kernel-stack-envelope.sh`
//! bisects with; on its own it answers one question, once.
//!
//! ```sh
//! cargo run --release -p axeyum-lean-kernel --example kernel_stack_envelope \
//!   -- --prelude cpoint --stack-bytes 1048576
//! ```
//!
//! # The exit status is the answer, and it has three values
//!
//! - **0** — the build completed on that stack. Prints `ok <prelude> <bytes>`.
//! - **134** (SIGABRT) — the stack was **not** enough. The Rust runtime prints
//!   `fatal runtime error: stack overflow` and aborts the process; nothing in
//!   this file runs after that, which is exactly why the caller has to be a
//!   separate process. This is a resource limit, not a proof bug.
//! - **2** — bad usage (unknown prelude, unparseable size). Deliberately
//!   distinct from both of the above so a typo cannot be read as a measurement.
//!
//! # Why the size is an argument and not `RUST_MIN_STACK`
//!
//! A test that passes only under an ambient environment variable is a gate on
//! one shell — this repository has already been burned by a lane that had
//! `RUST_MIN_STACK` exported from an earlier hand-bisect and reported a suite
//! green that SIGABRTs in a clean shell. The size here is positional, explicit,
//! and echoed back in the output line so a log records what was actually asked.
//!
//! # Why the prelude cache must be OFF
//!
//! `AXEYUM_PRELUDE_CACHE` (ADR-0464) serves a pristine build from a
//! process-wide template. A cached build does no type checking at all, so it
//! would report a stack requirement near zero — a green measurement of nothing,
//! and green is the direction that gets believed. `unsafe_code` is denied
//! workspace-wide so this cannot set the variable itself; instead it **refuses
//! to run** (exit 2) unless the cache is off, which is fail-closed. The caller
//! passes `AXEYUM_PRELUDE_CACHE=0`.

use std::process::ExitCode;

use axeyum_lean_kernel::{
    Kernel, build_arith_prelude, build_complex_prelude, build_cpoint_prelude, build_creal_prelude,
    build_int_prelude, build_logic_prelude, build_nat_prelude, build_rat_prelude,
    build_string_prelude,
};

/// A prelude's name and the function that builds it into a fresh kernel.
type PreludeEntry = (&'static str, fn(&mut Kernel));

/// Every prelude this probe can build, in dependency order. Kept as data so
/// `--list` and the dispatch cannot disagree.
const PRELUDES: &[PreludeEntry] = &[
    ("logic", |k| {
        build_logic_prelude(k).expect("logic prelude must build");
    }),
    ("nat", |k| {
        build_nat_prelude(k).expect("nat prelude must build");
    }),
    ("integer", |k| {
        build_int_prelude(k).expect("integer prelude must build");
    }),
    ("axreal", |k| {
        build_arith_prelude(k).expect("axreal prelude must build");
    }),
    ("rat", |k| {
        build_rat_prelude(k).expect("rat prelude must build");
    }),
    ("creal", |k| {
        build_creal_prelude(k).expect("creal prelude must build");
    }),
    ("cpoint", |k| {
        build_cpoint_prelude(k).expect("cpoint prelude must build");
    }),
    ("complex", |k| {
        build_complex_prelude(k).expect("complex prelude must build");
    }),
    ("string", |k| {
        let logic = build_logic_prelude(k).expect("logic prelude must build");
        build_string_prelude(k, logic, 2).expect("string prelude must build");
    }),
];

const USAGE: &str = "usage: kernel_stack_envelope --prelude <name> --stack-bytes <n>\n       kernel_stack_envelope --list";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--list") {
        for (name, _) in PRELUDES {
            println!("{name}");
        }
        return ExitCode::SUCCESS;
    }

    let mut prelude: Option<String> = None;
    let mut stack_bytes: Option<usize> = None;
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--prelude" => {
                prelude = args.get(i + 1).cloned();
                i += 2;
            }
            "--stack-bytes" => {
                stack_bytes = args.get(i + 1).and_then(|raw| raw.parse().ok());
                i += 2;
            }
            other => {
                eprintln!("unknown argument {other}\n{USAGE}");
                return ExitCode::from(2);
            }
        }
    }

    let (Some(prelude), Some(stack_bytes)) = (prelude, stack_bytes) else {
        eprintln!("{USAGE}");
        return ExitCode::from(2);
    };
    if stack_bytes == 0 {
        eprintln!("--stack-bytes must be positive\n{USAGE}");
        return ExitCode::from(2);
    }
    let Some((name, build)) = PRELUDES.iter().find(|(n, _)| *n == prelude) else {
        eprintln!("unknown prelude {prelude:?}; --list names the ones that exist");
        return ExitCode::from(2);
    };
    let (name, build) = (*name, *build);

    // Checked AFTER argument parsing so `--list` and a usage error still work,
    // and checked at all because a cache hit type-checks nothing: the run would
    // succeed on a tiny stack and report a requirement that is not the kernel's.
    if axeyum_lean_kernel::prelude_cache::enabled() {
        eprintln!(
            "refusing to measure with the prelude cache ON: a cache hit type-checks nothing, so the answer would be a stack requirement of ~0. Re-run with AXEYUM_PRELUDE_CACHE=0."
        );
        return ExitCode::from(2);
    }

    let Ok(handle) = std::thread::Builder::new()
        .stack_size(stack_bytes)
        .spawn(move || {
            let mut kernel = Kernel::new();
            build(&mut kernel);
            // Read something out of the finished environment so the build
            // cannot be optimized away and so an empty environment cannot be
            // mistaken for a cheap success.
            kernel.environment().iter().count()
        })
    else {
        eprintln!("could not spawn a {stack_bytes}-byte thread");
        return ExitCode::from(2);
    };

    match handle.join() {
        Ok(declarations) if declarations > 0 => {
            println!("ok\t{name}\t{stack_bytes}\t{declarations}");
            ExitCode::SUCCESS
        }
        Ok(_) => {
            eprintln!("{name} built an EMPTY environment; that is not a measurement");
            ExitCode::FAILURE
        }
        Err(_) => {
            eprintln!("{name} panicked at {stack_bytes} bytes");
            ExitCode::FAILURE
        }
    }
}
