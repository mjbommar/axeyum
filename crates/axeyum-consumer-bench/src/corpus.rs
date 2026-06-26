//! The construction-known bounded-property corpus.
//!
//! Each [`Case`] is authored so its true status is known **by construction** —
//! we hand-pick provable identities ([`Status::ShouldProve`]) and properties with
//! a deliberate, named counterexample ([`Status::ShouldFindCounterexample`]). No
//! external oracle is consulted; the corpus *is* its own ground truth.
//!
//! Mix (by design): overflow-safe-under-precondition (prove), `abs ≥ 0` (prove),
//! De Morgan / bit identities (prove), an unguarded overflow (counterexample), an
//! off-by-one bound (counterexample), and a few signed/unsigned subtleties.

use std::fmt;

use axeyum_property::{Bounded, Bv, BvArray, Ctx, Int, Outcome, SolverError, Symbolic, property};

use crate::harness::{RunOutcome, Verdict};

/// A derived 3-field struct input (exercises `#[derive(Symbolic)]` beyond the
/// arity-3 *tuple* ceiling — and lifts a counterexample into `Triple3Concrete`).
#[derive(Symbolic, Clone, Copy)]
struct Triple3<'c> {
    a: Bv<'c, 8>,
    b: Bv<'c, 8>,
    c: Bv<'c, 8>,
}

/// The construction-known true status of a corpus property.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Status {
    /// The property is universally true under its precondition — axeyum should
    /// `Prove` it (or honestly return `Unknown`, never a counterexample).
    ShouldProve,
    /// The property is false — there is a concrete counterexample under the
    /// precondition, so axeyum should find a `Counterexample` (or `Unknown`).
    ShouldFindCounterexample,
}

impl Status {
    /// A short, stable label for the scoreboard.
    #[must_use]
    pub fn label(self) -> &'static str {
        match self {
            Status::ShouldProve => "should-prove",
            Status::ShouldFindCounterexample => "should-find-ce",
        }
    }
}

impl fmt::Display for Status {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.label())
    }
}

/// One corpus entry: a stable name, a one-line description, the construction-known
/// status, and the closure that decides the property through the SDK.
pub struct Case {
    /// Stable, unique case name (drives deterministic ordering).
    pub name: &'static str,
    /// One-line human description.
    pub description: &'static str,
    /// The construction-known true status.
    pub status: Status,
    /// Runs the property through [`axeyum_property`] and collapses the outcome.
    pub run: fn() -> RunOutcome,
}

/// Collapse an SDK [`Outcome`] into a [`RunOutcome`], recording certificate facts
/// for a `Proved` result.
///
/// On a `Proved` we *independently re-verify* the certificate via
/// [`axeyum_property::Certificate::verify`] and check whether a standalone Lean
/// module was produced — the two facts the scoreboard's differentiator counts.
fn collapse<T>(outcome: Outcome<T>) -> RunOutcome {
    match outcome {
        Outcome::Proved(cert) => {
            let verified = cert
                .verify()
                .expect("certificate re-verification self-check must not error");
            let lean = cert.to_lean_module().is_some();
            RunOutcome {
                verdict: Verdict::Proved,
                cert_verified: Some(verified),
                lean_module: Some(lean),
            }
        }
        Outcome::Counterexample(_) => RunOutcome {
            verdict: Verdict::Counterexample,
            cert_verified: None,
            lean_module: None,
        },
        Outcome::Unknown(_) => RunOutcome {
            verdict: Verdict::Unknown,
            cert_verified: None,
            lean_module: None,
        },
    }
}

/// Shorthand: run a property over a fresh [`Ctx`] and collapse the outcome.
///
/// `f` builds and decides the property, returning the SDK's
/// `Result<Outcome<T>, SolverError>`. A `SolverError` is an engine self-check
/// failure (a soundness alarm), so the harness panics rather than masking it as
/// `Unknown`.
fn check<T>(f: impl FnOnce(&Ctx) -> Result<Outcome<T>, SolverError>) -> RunOutcome {
    let ctx = Ctx::new();
    let outcome = f(&ctx).expect("property check must not fail an internal self-check");
    collapse(outcome)
}

/// The committed construction-known corpus, in deterministic order.
// A flat data table of property cases; the length is inherent, not complexity.
// `eq_op` fires on the *intentional* `a ^ a` / `a & a` identity properties below.
#[allow(clippy::too_many_lines, clippy::eq_op)]
#[must_use]
pub fn corpus() -> Vec<Case> {
    vec![
        // ---- ShouldProve: arithmetic / overflow-safe under precondition ----
        Case {
            name: "bv32-add-no-wrap-guarded",
            description: "for a,b < 2^31 (Bv<32>): a + b >= a (sum never wraps below a)",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<32>, Bv<32>)>(ctx)
                        .assuming(|(a, b)| {
                            a.ult(Bv::lit(ctx, 1 << 31)) & b.ult(Bv::lit(ctx, 1 << 31))
                        })
                        .check(|(a, b)| (a + b).uge(a))
                })
            },
        },
        Case {
            name: "bv8-no-overflow-guarded",
            description: "for a,b with !uaddo(a,b) (Bv<8>): a + b >= a",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<8>, Bv<8>)>(ctx)
                        .assuming(|(a, b)| a.add_overflows(b).negate())
                        .check(|(a, b)| (a + b).uge(a))
                })
            },
        },
        Case {
            name: "int-abs-nonneg",
            description: "for x in [-1000,1000] (Int): |x| >= 0",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Int>(ctx)
                        .assuming(|x| x.ge(Int::lit(ctx, -1000)) & x.le(Int::lit(ctx, 1000)))
                        .check(|x| x.abs().ge(Int::lit(ctx, 0)))
                })
            },
        },
        Case {
            name: "int-abs-ge-self",
            description: "for x in [-1000,1000] (Int): |x| >= x",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Int>(ctx)
                        .assuming(|x| x.ge(Int::lit(ctx, -1000)) & x.le(Int::lit(ctx, 1000)))
                        .check(|x| x.abs().ge(x))
                })
            },
        },
        Case {
            name: "int-add-comm",
            description: "for a,b in [-100,100] (Int): a + b == b + a",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Int, Int)>(ctx)
                        .assuming(|(a, b)| {
                            a.ge(Int::lit(ctx, -100))
                                & a.le(Int::lit(ctx, 100))
                                & b.ge(Int::lit(ctx, -100))
                                & b.le(Int::lit(ctx, 100))
                        })
                        .check(|(a, b)| (a + b).equals(b + a))
                })
            },
        },
        // ---- ShouldProve: De Morgan / bit identities ----
        Case {
            name: "bv16-de-morgan-and",
            description: "De Morgan (Bv<16>): !(a & b) == (!a) | (!b)",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<16>, Bv<16>)>(ctx)
                        .check(|(a, b)| (!(a & b)).equals((!a) | (!b)))
                })
            },
        },
        Case {
            name: "bv16-de-morgan-or",
            description: "De Morgan (Bv<16>): !(a | b) == (!a) & (!b)",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<16>, Bv<16>)>(ctx)
                        .check(|(a, b)| (!(a | b)).equals((!a) & (!b)))
                })
            },
        },
        Case {
            name: "bv8-xor-self-zero",
            description: "for a (Bv<8>): a ^ a == 0",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Bv<8>>(ctx)
                        .check(|a| (a ^ a).equals(Bv::lit(ctx, 0)))
                })
            },
        },
        Case {
            name: "bv8-and-idempotent",
            description: "for a (Bv<8>): a & a == a",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Bv<8>>(ctx)
                        .check(|a| (a & a).equals(a))
                })
            },
        },
        Case {
            name: "bv8-double-neg",
            description: "for a (Bv<8>): !!a == a (bitwise double complement)",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Bv<8>>(ctx)
                        .check(|a| (!(!a)).equals(a))
                })
            },
        },
        Case {
            name: "bool-de-morgan",
            description: "Boolean De Morgan: !(p & q) <-> (!p) | (!q)",
            status: Status::ShouldProve,
            run: || {
                use axeyum_property::Bool;
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bool, Bool)>(ctx)
                        .check(|(p, q)| (!(p & q)).equals((!p) | (!q)))
                })
            },
        },
        Case {
            name: "bv8-ule-refl",
            description: "for a (Bv<8>): a <=u a (reflexivity of unsigned <=)",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Bv<8>>(ctx)
                        .check(|a| a.ule(a))
                })
            },
        },
        // ---- ShouldFindCounterexample: deliberate bugs ----
        Case {
            name: "bv8-add-no-wrap-unguarded",
            description: "for ALL a,b (Bv<8>, no guard): a + b >= a  — wraps (e.g. a=1,b=255)",
            status: Status::ShouldFindCounterexample,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<8>, Bv<8>)>(ctx)
                        .check(|(a, b)| (a + b).uge(a))
                })
            },
        },
        Case {
            name: "int-off-by-one-bound",
            description: "for x in [0,10] (Int): x < 10  — fails at x=10 (off-by-one)",
            status: Status::ShouldFindCounterexample,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Int>(ctx)
                        .assuming(|x| x.ge(Int::lit(ctx, 0)) & x.le(Int::lit(ctx, 10)))
                        .check(|x| x.lt(Int::lit(ctx, 10)))
                })
            },
        },
        Case {
            name: "bv8-mul-no-overflow-unguarded",
            description: "for ALL a,b (Bv<8>): !umulo(a,b)  — false (e.g. a=16,b=16 overflows)",
            status: Status::ShouldFindCounterexample,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<8>, Bv<8>)>(ctx)
                        .check(|(a, b)| a.mul_overflows(b).negate())
                })
            },
        },
        Case {
            name: "int-add-pos-stays-pos",
            description: "for a,b in [-5,5] (Int): a + b > 0  — false (e.g. a=-5,b=-5)",
            status: Status::ShouldFindCounterexample,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Int, Int)>(ctx)
                        .assuming(|(a, b)| {
                            a.ge(Int::lit(ctx, -5))
                                & a.le(Int::lit(ctx, 5))
                                & b.ge(Int::lit(ctx, -5))
                                & b.le(Int::lit(ctx, 5))
                        })
                        .check(|(a, b)| (a + b).gt(Int::lit(ctx, 0)))
                })
            },
        },
        Case {
            name: "bv8-sub-no-borrow-unguarded",
            description: "for ALL a,b (Bv<8>): a - b <=u a  — false when b > a (e.g. a=0,b=1)",
            status: Status::ShouldFindCounterexample,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<8>, Bv<8>)>(ctx)
                        .check(|(a, b)| (a - b).ule(a))
                })
            },
        },
        // ---- v1: #[derive(Symbolic)] (structs beyond arity-3 tuples) ----
        Case {
            name: "derive-triple-xor-rearrange",
            description: "derive(Symbolic) Triple3: (a^b)^c == a^(b^c) (XOR assoc), 8-bit",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Triple3>(ctx)
                        .check(|t| ((t.a ^ t.b) ^ t.c).equals(t.a ^ (t.b ^ t.c)))
                })
            },
        },
        Case {
            name: "derive-triple-sum-zero-unguarded",
            description: "derive(Symbolic) Triple3: a+b+c == 0 (no guard) — false, typed CE",
            status: Status::ShouldFindCounterexample,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Triple3>(ctx)
                        .check(|t| (t.a + t.b + t.c).equals(Bv::lit(ctx, 0)))
                })
            },
        },
        // ---- v1: Bounded<LO, HI> (auto-emitted range assume, no manual pre) ----
        Case {
            name: "bounded-abs-nonneg",
            description: "Bounded<-1000,1000>: |x| >= 0 (range assume emitted automatically)",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Bounded<-1000, 1000>>(ctx)
                        .check(|x| x.value().abs().ge(Int::lit(ctx, 0)))
                })
            },
        },
        Case {
            name: "bounded-succ-gt-self",
            description: "Bounded<0,100>: x + 1 > x (Sort::Int, no overflow)",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Bounded<0, 100>>(ctx)
                        .check(|x| (x.value() + Int::lit(ctx, 1)).gt(x.value()))
                })
            },
        },
        Case {
            name: "bounded-off-by-one",
            description: "Bounded<0,10>: x < 10 — false at the auto-assumed boundary x=10",
            status: Status::ShouldFindCounterexample,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<Bounded<0, 10>>(ctx)
                        .check(|x| x.value().lt(Int::lit(ctx, 10)))
                })
            },
        },
        // ---- v2: fixed BvArray<EW, N> (Sort::Array) + in-bounds indexing ----
        Case {
            name: "array-store-select-roundtrip",
            description: "BvArray<8,4>: select(store(arr,i,v),i) == v (read-over-write)",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(BvArray<8, 4>, Bv<32>, Bv<8>)>(ctx)
                        .check(|(arr, i, v)| arr.store(i, v).select(i).equals(v))
                })
            },
        },
        Case {
            name: "array-store-other-unchanged",
            description: "BvArray<8,4>: i!=j => select(store(arr,i,v),j) == select(arr,j)",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(BvArray<8, 4>, Bv<32>, Bv<32>, Bv<8>)>(ctx)
                        .assuming(|(_arr, i, j, _v)| i.equals(j).negate())
                        .check(|(arr, i, j, v)| arr.store(i, v).select(j).equals(arr.select(j)))
                })
            },
        },
        Case {
            name: "array-elem0-eq-elem1-unguarded",
            description: "BvArray<8,4>: arr[0] == arr[1] (no guard) — false, lifts to [u128;4]",
            status: Status::ShouldFindCounterexample,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<BvArray<8, 4>>(ctx)
                        .check(|arr| arr.get(0).equals(arr.get(1)))
                })
            },
        },
        // ---- Lean-cert frontier: QF_BV comparison theorems in the
        // reconstructable shape (separate top-level conjuncts) ----
        Case {
            name: "bv4-ult-not-symmetric",
            description: "Bv<4>: not(a <u b and b <u a) — emits a Lean module",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<4>, Bv<4>)>(ctx)
                        .check(|(a, b)| (a.ult(b) & b.ult(a)).negate())
                })
            },
        },
        Case {
            name: "bv4-ule-ult-exclusive",
            description: "Bv<4>: not(a <=u b and b <u a) — emits a Lean module",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<4>, Bv<4>)>(ctx)
                        .check(|(a, b)| (a.ule(b) & b.ult(a)).negate())
                })
            },
        },
        Case {
            name: "bv4-slt-not-symmetric",
            description: "Bv<4>: not(a <s b and b <s a) (signed) — emits a Lean module",
            status: Status::ShouldProve,
            run: || {
                check(|ctx| {
                    property()
                        .certificate(true)
                        .forall::<(Bv<4>, Bv<4>)>(ctx)
                        .check(|(a, b)| (a.slt(b) & b.slt(a)).negate())
                })
            },
        },
    ]
}
