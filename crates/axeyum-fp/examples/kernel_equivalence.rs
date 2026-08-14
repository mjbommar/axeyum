//! Exhaustive, solver-free settlement of floating-point kernel-equivalence
//! claims — the **independent route** for the `F:fp-*` facts.
//!
//! # Why this exists
//!
//! The `F:fp-*` facts in `artifacts/facts/` are established through axeyum's
//! SMT front door (`fp.*` operators lowered to bit-vectors, then decided).
//! One route asserting is not evidence in this repository. This binary is the
//! second, structurally independent route: it enumerates **every** bit pattern
//! of the narrow formats and evaluates each claim with
//! [`rustc_apfloat`] — LLVM's `APFloat`, a correctly-rounded IEEE-754 software
//! implementation that shares no line of code with axeyum's bit-blaster,
//! its CNF encoder, or its SAT core (ADR-0028 already admits it as the
//! dev-only reference oracle for the wide formats).
//!
//! The two routes agreeing is the strongest evidence this repository
//! recognises. Where they disagree, that is a finding and this binary exits
//! non-zero.
//!
//! # Semantics actually asserted
//!
//! * **Rounding mode is explicit in every claim.** `roundNearestTiesToEven`
//!   (`RNE`) unless the claim says otherwise; `--all-modes` re-runs the
//!   applicable claims under all five SMT-LIB modes.
//! * **Equality is SMT-LIB `=` on the FP sort, not `fp.eq`.** SMT-LIB's
//!   `FloatingPoint` sort has exactly one NaN, `+0` and `-0` are distinct
//!   values, and `=` is identity on values. `APFloat` distinguishes NaN
//!   payloads, so every comparison here goes through [`Class::of`], which
//!   collapses all NaN encodings to one class and keeps the two zeros apart.
//!   Using raw bits would make a true claim look false; using `fp.eq` would
//!   make a false claim look true (`fp.eq NaN NaN` is `false`, and
//!   `fp.eq +0 -0` is `true`).
//! * **Formats.** `fp8` here means the IEEE-754-conformant OCP **E5M2**
//!   layout, SMT-LIB `(_ FloatingPoint 5 3)`. E4M3 is deliberately absent: it
//!   has no infinities and an all-ones NaN, so it is not an IEEE format and
//!   axeyum's arithmetic gate refuses it.
//!
//! # Usage
//!
//! ```text
//! cargo run --release -p axeyum-fp --example kernel_equivalence -- <claim>...
//! ```
//!
//! Claims: `doubling`, `assoc`, `roundtrip-fp32`, `roundtrip-bf16`,
//! `monotone`, or `all` (the default). Each corresponds to a fact:
//!
//! | claim | fact | cost |
//! | --- | --- | --- |
//! | `doubling` | `F:fp16-doubling-add-equals-mul-two` | 2^16, instant |
//! | `doubling-fp32` | `F:fp32-doubling-add-equals-mul-two` | 2^32, ~1 min |
//! | `assoc` | `F:fp8-add-not-associative` | 2^24, ~3 s |
//! | `roundtrip-fp32` | `F:fp16-fp32-roundtrip-identity` | 2^16, instant |
//! | `roundtrip-bf16` | `F:fp16-bf16-roundtrip-not-identity` | 2^16, instant |
//! | `monotone` | `F:fp8-add-monotone-rne` | 2^24, ~3 s |
//!
//! `doubling-fp32` is **not** in `all`: it is minutes where everything else is
//! seconds, so it is opt-in and shards across
//! `std::thread::available_parallelism()` threads (override with
//! `--threads=N`).
//!
//! Exit status is the gate: `0` only if every enumerated claim matched what the
//! ledger records, `1` on any disagreement, `2` on an unrecognised claim name.
//! A claim expected to hold that examined **zero** points reports `VACUOUS` and
//! fails, because that is what every inert gate this repository has shipped
//! looked like from the outside.

use rustc_apfloat::ieee::{BFloat, Float8E5M2, Half, Single};
use rustc_apfloat::{Float, Round, Status};

/// A value of the SMT-LIB `FloatingPoint` sort, as distinguished by `=`.
///
/// This is the quotient `APFloat` bit patterns must be taken through before
/// they can answer a question about SMT-LIB `=`: every NaN encoding is one
/// value, and everything else is its bit pattern (so `+0` and `-0` stay
/// distinct, which `PartialEq` on the float would not).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Class {
    /// The single SMT-LIB NaN.
    Nan,
    /// A non-NaN value, by its encoding.
    Bits(u128),
}

impl Class {
    /// The SMT-LIB value denoted by an `APFloat`.
    fn of<F: Float>(x: F) -> Self {
        if x.is_nan() {
            Self::Nan
        } else {
            Self::Bits(x.to_bits())
        }
    }
}

/// The five SMT-LIB rounding modes, with their SMT-LIB spellings.
const MODES: [(&str, Round); 5] = [
    ("RNE", Round::NearestTiesToEven),
    ("RNA", Round::NearestTiesToAway),
    ("RTP", Round::TowardPositive),
    ("RTN", Round::TowardNegative),
    ("RTZ", Round::TowardZero),
];

/// Outcome of one claim: how many points were examined and how many failed,
/// plus the first failing witness in enumeration order.
struct Outcome {
    /// Total input points enumerated.
    examined: u64,
    /// Points at which the claim does not hold.
    failures: u64,
    /// The first failure encountered, already rendered.
    first_witness: Option<String>,
}

impl Outcome {
    /// A fresh, so-far-unfalsified outcome.
    fn new() -> Self {
        Self {
            examined: 0,
            failures: 0,
            first_witness: None,
        }
    }

    /// Records one examined point; `witness` is `Some` iff the claim failed.
    fn record(&mut self, witness: Option<String>) {
        self.examined += 1;
        if let Some(w) = witness {
            self.failures += 1;
            if self.first_witness.is_none() {
                self.first_witness = Some(w);
            }
        }
    }
}

/// Decodes an `APFloat` to a human-readable value, for witness rendering.
fn show<F: Float>(bits: u128, width: u32, x: F) -> String {
    let hex_digits = width.div_ceil(4) as usize;
    format!("0x{bits:0hex_digits$x}={x}")
}

// ---------------------------------------------------------------------------
// Claim 1: doubling.  fp.add RM x x  =  fp.mul RM 2 x
// ---------------------------------------------------------------------------

/// The FP value `2.0` in a format with `exp_bits` exponent bits and
/// `sig_bits` significand bits (hidden bit included), as an encoding.
///
/// `2.0 = 1.0 x 2^1`, so the biased exponent is `bias + 1 = 2^(eb-1)` and the
/// stored fraction is zero.
const fn two_bits(exp_bits: u32, sig_bits: u32) -> u128 {
    (1u128 << (exp_bits - 1)) << (sig_bits - 1)
}

/// `fp.add RM x x = fp.mul RM 2 x` over every encoding of `F`.
fn doubling<F: Float>(width: u32, exp_bits: u32, sig_bits: u32, round: Round) -> Outcome {
    let two = F::from_bits(two_bits(exp_bits, sig_bits));
    let mut out = Outcome::new();
    for bits in 0..(1u128 << width) {
        let x = F::from_bits(bits);
        let sum = x.add_r(x, round).value;
        let prod = two.mul_r(x, round).value;
        let witness = if Class::of(sum) == Class::of(prod) {
            None
        } else {
            Some(format!(
                "x={} : x+x={} but 2*x={}",
                show(bits, width, x),
                show(sum.to_bits(), width, sum),
                show(prod.to_bits(), width, prod)
            ))
        };
        out.record(witness);
    }
    out
}

/// `fp.add RNE x x = fp.mul RNE 2 x` over **all 2^32 binary32 encodings**,
/// sharded across `threads` OS threads.
///
/// Deliberately not part of `all`: it is minutes of work, where every other
/// claim here is seconds. It exists because the binary32 instance of the
/// doubling claim is the one place in this ledger where a claim settled
/// symbolically by the solver can ALSO be settled by brute force, so the two
/// can be compared rather than asserted to agree.
fn doubling_fp32_exhaustive(threads: u32) -> Outcome {
    let two = two_bits(8, 24);
    let shard = 1u64 << 32;
    let per = shard / u64::from(threads) + 1;
    let results: Vec<Outcome> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..u64::from(threads))
            .map(|t| {
                scope.spawn(move || {
                    let two = Single::from_bits(two);
                    let mut out = Outcome::new();
                    let lo = t * per;
                    let hi = ((t + 1) * per).min(shard);
                    for bits in lo..hi {
                        let x = Single::from_bits(u128::from(bits));
                        let sum = x.add_r(x, Round::NearestTiesToEven).value;
                        let prod = two.mul_r(x, Round::NearestTiesToEven).value;
                        let witness = if Class::of(sum) == Class::of(prod) {
                            None
                        } else {
                            Some(format!(
                                "x={} : x+x={} but 2*x={}",
                                show(u128::from(bits), 32, x),
                                show(sum.to_bits(), 32, sum),
                                show(prod.to_bits(), 32, prod)
                            ))
                        };
                        out.record(witness);
                    }
                    out
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut merged = Outcome::new();
    for r in results {
        merged.examined += r.examined;
        merged.failures += r.failures;
        if merged.first_witness.is_none() {
            merged.first_witness = r.first_witness;
        }
    }
    merged
}

// ---------------------------------------------------------------------------
// Claim 2: associativity of fp.add
// ---------------------------------------------------------------------------

/// `(a+b)+c = a+(b+c)` over every triple of `fp8` E5M2 encodings.
///
/// 2^24 triples: exhaustive, and small enough to run in seconds.
fn assoc_fp8(round: Round) -> Outcome {
    let mut out = Outcome::new();
    for ab in 0..256u128 {
        let a = Float8E5M2::from_bits(ab);
        for bb in 0..256u128 {
            let b = Float8E5M2::from_bits(bb);
            let ab_sum = a.add_r(b, round).value;
            for cb in 0..256u128 {
                let c = Float8E5M2::from_bits(cb);
                let left = ab_sum.add_r(c, round).value;
                let right = a.add_r(b.add_r(c, round).value, round).value;
                let witness = if Class::of(left) == Class::of(right) {
                    None
                } else {
                    Some(format!(
                        "a={} b={} c={} : (a+b)+c={} a+(b+c)={}",
                        show(ab, 8, a),
                        show(bb, 8, b),
                        show(cb, 8, c),
                        show(left.to_bits(), 8, left),
                        show(right.to_bits(), 8, right)
                    ))
                };
                out.record(witness);
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Claim 3 / 4: round trips
// ---------------------------------------------------------------------------

/// `narrow -> wide -> narrow` is the identity over every encoding of `N`.
///
/// Conversion is `((_ to_fp eb sb) RM x)` in SMT-LIB; `RM` is irrelevant on
/// the widening leg (it is exact) and is the claim's mode on the narrowing
/// leg.
fn roundtrip<N, W>(width: u32, round: Round) -> Outcome
where
    N: Float + rustc_apfloat::FloatConvert<W>,
    W: Float + rustc_apfloat::FloatConvert<N>,
{
    let mut out = Outcome::new();
    for bits in 0..(1u128 << width) {
        let x = N::from_bits(bits);
        let mut lost = false;
        let wide: W = x.convert_r(round, &mut lost).value;
        let mut lost_back = false;
        let back: N = wide.convert_r(round, &mut lost_back).value;
        let witness = if Class::of(x) == Class::of(back) {
            None
        } else {
            Some(format!(
                "x={} : round trip gives {}",
                show(bits, width, x),
                show(back.to_bits(), width, back)
            ))
        };
        out.record(witness);
    }
    out
}

// ---------------------------------------------------------------------------
// Claim 5: monotonicity of rounded addition
// ---------------------------------------------------------------------------

/// `a <= b  =>  a+c <= b+c` over every `fp8` E5M2 triple, guarded so that no
/// operand or result is NaN.
///
/// `<=` is SMT-LIB `fp.leq`, i.e. the ordering `APFloat`'s `PartialOrd` gives
/// (NaN unordered, `+0 == -0`). This is the property that licenses interval
/// propagation through a rounded-addition kernel.
fn monotone_fp8(round: Round) -> Outcome {
    let mut out = Outcome::new();
    for ab in 0..256u128 {
        let a = Float8E5M2::from_bits(ab);
        for bb in 0..256u128 {
            let b = Float8E5M2::from_bits(bb);
            // SMT-LIB `fp.leq`: NaN is unordered, so a `None` comparison
            // fails the antecedent, exactly as `fp.leq` would.
            if !matches!(
                a.partial_cmp(&b),
                Some(std::cmp::Ordering::Less | std::cmp::Ordering::Equal)
            ) {
                continue;
            }
            for cb in 0..256u128 {
                let c = Float8E5M2::from_bits(cb);
                let ac = a.add_r(c, round).value;
                let bc = b.add_r(c, round).value;
                if ac.is_nan() || bc.is_nan() {
                    continue;
                }
                let witness = if ac <= bc {
                    None
                } else {
                    Some(format!(
                        "a={} b={} c={} : a<=b but a+c={} > b+c={}",
                        show(ab, 8, a),
                        show(bb, 8, b),
                        show(cb, 8, c),
                        show(ac.to_bits(), 8, ac),
                        show(bc.to_bits(), 8, bc)
                    ))
                };
                out.record(witness);
            }
        }
    }
    out
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

/// Whether a claim is asserted to hold everywhere or to fail somewhere.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Expect {
    /// The claim must hold at every enumerated point.
    Holds,
    /// The claim must fail at at least one enumerated point.
    Fails,
}

/// Prints one claim's outcome and returns whether it matched `expect`.
///
/// A claim expected to HOLD reports agreement only if it also examined
/// something: "zero failures out of zero points" is what every inert gate this
/// repository has shipped looked like from the outside, and it must not be
/// spellable here.
fn report(label: &str, expect: Expect, out: &Outcome) -> bool {
    let verdict = match (expect, out.failures, out.examined) {
        (Expect::Holds, 0, 1..) | (Expect::Fails, 1.., _) => "AGREES",
        (Expect::Holds, 0, 0) => "VACUOUS",
        _ => "MISMATCH",
    };
    println!(
        "  {verdict:9} {label:<52} examined={} failures={}",
        out.examined, out.failures
    );
    if let Some(w) = &out.first_witness {
        println!("            first witness: {w}");
    }
    verdict == "AGREES"
}

/// Exhaustive-enumeration driver.
#[allow(clippy::too_many_lines)] // one straight-line list of claims; splitting it hides the list
fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let all_modes = args.iter().any(|a| a == "--all-modes");
    let wanted: Vec<&str> = args
        .iter()
        .filter(|a| !a.starts_with("--"))
        .map(String::as_str)
        .collect();
    let want = |name: &str| wanted.is_empty() || wanted.contains(&"all") || wanted.contains(&name);

    let modes: &[(&str, Round)] = if all_modes { &MODES } else { &MODES[..1] };
    let mut ok = true;

    if want("doubling") {
        println!("claim: fp.add RM x x = fp.mul RM 2 x   [equality is SMT-LIB `=`]");
        for (name, round) in modes {
            ok &= report(
                &format!("fp8 E5M2 (5,3) {name}, exhaustive 2^8"),
                Expect::Holds,
                &doubling::<Float8E5M2>(8, 5, 3, *round),
            );
            ok &= report(
                &format!("fp16 (5,11) {name}, exhaustive 2^16"),
                Expect::Holds,
                &doubling::<Half>(16, 5, 11, *round),
            );
            ok &= report(
                &format!("bf16 (8,8) {name}, exhaustive 2^16"),
                Expect::Holds,
                &doubling::<BFloat>(16, 8, 8, *round),
            );
        }
    }

    // Opt-in only: minutes, not seconds, so it is never part of `all`.
    if wanted.contains(&"doubling-fp32") {
        let threads = args
            .iter()
            .find_map(|a| a.strip_prefix("--threads="))
            .and_then(|n| n.parse::<u32>().ok())
            .unwrap_or_else(|| {
                std::thread::available_parallelism()
                    .map_or(4, |n| u32::try_from(n.get()).unwrap_or(4))
            });
        println!("claim: fp.add RNE x x = fp.mul RNE 2 x   [binary32, brute force]");
        ok &= report(
            &format!("fp32 (8,24) RNE, exhaustive 2^32, threads={threads}"),
            Expect::Holds,
            &doubling_fp32_exhaustive(threads),
        );
    }

    if want("assoc") {
        println!("claim: (a+b)+c = a+(b+c)              [expected to FAIL]");
        for (name, round) in modes {
            ok &= report(
                &format!("fp8 E5M2 (5,3) {name}, exhaustive 2^24 triples"),
                Expect::Fails,
                &assoc_fp8(*round),
            );
        }
    }

    if want("roundtrip-fp32") {
        println!("claim: narrow -> fp32 -> narrow is the identity");
        ok &= report(
            "fp16 -> fp32 -> fp16 RNE, exhaustive 2^16",
            Expect::Holds,
            &roundtrip::<Half, Single>(16, Round::NearestTiesToEven),
        );
        ok &= report(
            "bf16 -> fp32 -> bf16 RNE, exhaustive 2^16",
            Expect::Holds,
            &roundtrip::<BFloat, Single>(16, Round::NearestTiesToEven),
        );
        ok &= report(
            "fp8 E5M2 -> fp32 -> fp8 E5M2 RNE, exhaustive 2^8",
            Expect::Holds,
            &roundtrip::<Float8E5M2, Single>(8, Round::NearestTiesToEven),
        );
    }

    if want("roundtrip-bf16") {
        println!("claim: fp16 -> bf16 -> fp16 is the identity   [expected to FAIL]");
        ok &= report(
            "fp16 -> bf16 -> fp16 RNE, exhaustive 2^16",
            Expect::Fails,
            &roundtrip::<Half, BFloat>(16, Round::NearestTiesToEven),
        );
    }

    if want("monotone") {
        println!("claim: a<=b => a+c <= b+c (non-NaN results)");
        for (name, round) in modes {
            ok &= report(
                &format!("fp8 E5M2 (5,3) {name}, exhaustive over ordered triples"),
                Expect::Holds,
                &monotone_fp8(*round),
            );
        }
    }

    // A run that enumerated nothing is a failure, not a pass: this repository
    // has shipped several gates that exited 0 over zero work.
    if wanted.iter().any(|w| {
        !matches!(
            *w,
            "all"
                | "doubling"
                | "doubling-fp32"
                | "assoc"
                | "roundtrip-fp32"
                | "roundtrip-bf16"
                | "monotone"
        )
    }) {
        eprintln!("kernel_equivalence: unknown claim name in {wanted:?}");
        std::process::exit(2);
    }

    // Silence the unused-import warning for `Status` while keeping the type in
    // scope for readers checking that inexactness is deliberately ignored:
    // these claims are about the ROUNDED RESULT, not the exception flags.
    let _ = Status::OK;

    if ok {
        println!("kernel_equivalence: all enumerated claims agree with the ledger");
    } else {
        eprintln!("kernel_equivalence: MISMATCH — a claim disagrees with the ledger");
        std::process::exit(1);
    }
}
