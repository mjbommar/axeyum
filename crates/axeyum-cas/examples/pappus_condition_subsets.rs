//! Which non-degeneracy condition subsets of Pappus's hexagon theorem admit a
//! **refuting configuration** — decided exhaustively over `F_p`.
//!
//! A certificate proves that its condition set *suffices*. Nothing in it proves
//! the set is *minimal*: that needs, for each proper subset `S`, a configuration
//! satisfying every hypothesis, keeping every condition of `S` nonzero, and
//! falsifying the conclusion. Over ℚ we can only ever exhibit such configurations
//! one at a time, so failing to find one is not evidence of anything. Over a
//! finite field the question is finite, and this example settles it.
//!
//! The answer, stable across every prime tried: the **only** zero/nonzero pattern
//! of `(c₁, c₂, c₃)` admitting a refuting configuration is the one with all three
//! zero. So no singleton is refutable — each condition alone suffices — while the
//! empty set is refuted, which is exactly what the committed counterexample says.
//! That is the measurement behind `pappus-hexagon` using one condition rather
//! than the three it states.
//!
//! # Two things that make this evidence rather than a re-derivation
//!
//! **The polynomials are the committed ones.** Every hypothesis, condition and
//! conclusion is read out of [`geometry_corpus`] and reduced mod `p` term by
//! term. Nothing is transcribed into finite-field arithmetic by hand, so the
//! example cannot agree with a formula the corpus does not hold.
//!
//! **The first carrier triple ranges over affine orbits, not points.** Every
//! predicate here is affine-covariant — an invertible affine map preserves each
//! collinearity and multiplies each condition by the nonzero linear determinant —
//! so a configuration and its affine image share both the zero/nonzero pattern
//! and the conclusion. Representatives are therefore exhaustive, and they are
//! what makes `p = 23` reachable at all. Pass `--full` to enumerate every first
//! triple instead and confirm the two agree.
//!
//! Run from the repository root:
//! `cargo run -p axeyum-cas --release --example pappus_condition_subsets -- 5 7 11`

use std::collections::BTreeMap;

use axeyum_cas::geometry_certify::GeometryProblem;
use axeyum_cas::geometry_corpus::corpus;
use axeyum_cas::mvpoly::MvPoly;

type Point = (i64, i64);

/// An exact `i128` coefficient reduced into `0..p`. The remainder is smaller
/// than `p`, so it fits `i64` by construction rather than by a truncating cast.
fn reduce(value: i128, p: i64) -> i64 {
    let residue = value % i128::from(p);
    md(i64::try_from(residue).expect("a residue mod p fits i64"), p)
}

/// A nonnegative residue as a table index. Panics on a negative input, which
/// would be a bug in `md` rather than a condition to handle.
fn idx(value: i64) -> usize {
    usize::try_from(value).expect("residues are nonnegative")
}

/// `a mod p`, in `0..p`.
fn md(a: i64, p: i64) -> i64 {
    let r = a % p;
    if r < 0 { r + p } else { r }
}

fn inverses(p: i64) -> Vec<i64> {
    let mut table = vec![0i64; idx(p)];
    for a in 1..p {
        for b in 1..p {
            if a * b % p == 1 {
                table[idx(a)] = b;
            }
        }
    }
    table
}

/// Evaluate a **committed** `MvPoly` at a point of `F_p^n`, reducing each
/// rational coefficient mod `p`. `None` when a denominator is divisible by `p`,
/// which is the only way the reduction can fail to make sense.
fn eval_mod(
    poly: &MvPoly,
    assignment: &BTreeMap<String, i64>,
    p: i64,
    inverse: &[i64],
) -> Option<i64> {
    let mut total = 0i64;
    for (mono, coefficient) in poly.terms() {
        let denominator = reduce(coefficient.denominator(), p);
        if denominator == 0 {
            return None;
        }
        let numerator = reduce(coefficient.numerator(), p);
        let mut term = numerator * inverse[idx(denominator)] % p;
        for (name, exponent) in mono.powers() {
            let value = *assignment.get(name)?;
            for _ in 0..exponent {
                term = term * value % p;
            }
        }
        total = (total + term) % p;
    }
    Some(md(total, p))
}

/// The solution set of the two hypotheses that pin one cross point, as an affine
/// subspace of `F_p^2`.
///
/// The 2×2 system is *read off the committed polynomials* by evaluating each at
/// `(0,0)`, `(1,0)` and `(0,1)` — they are affine in the cross point, so those
/// three values determine the row and its right-hand side exactly.
#[derive(Clone, Copy)]
enum Solutions {
    Empty,
    Point(Point),
    Line(Point, Point),
    Plane,
}

fn solve(rows: [(i64, i64, i64); 2], p: i64, inverse: &[i64]) -> Solutions {
    let [(a11, a12, b1), (a21, a22, b2)] = rows;
    let determinant = md(a11 * a22 - a12 * a21, p);
    if determinant != 0 {
        let d = inverse[idx(determinant)];
        return Solutions::Point((
            md((b1 * a22 - a12 * b2) % p * d, p),
            md((a11 * b2 - b1 * a21) % p * d, p),
        ));
    }
    let first_zero = a11 == 0 && a12 == 0;
    let second_zero = a21 == 0 && a22 == 0;
    if first_zero && second_zero {
        return if b1 == 0 && b2 == 0 {
            Solutions::Plane
        } else {
            Solutions::Empty
        };
    }
    if first_zero {
        return if b1 == 0 {
            line(a21, a22, b2, p, inverse)
        } else {
            Solutions::Empty
        };
    }
    if second_zero {
        return if b2 == 0 {
            line(a11, a12, b1, p, inverse)
        } else {
            Solutions::Empty
        };
    }
    let ratio = if a11 != 0 {
        md(a21 * inverse[idx(a11)], p)
    } else {
        md(a22 * inverse[idx(a12)], p)
    };
    if md(b2 - ratio * b1, p) != 0 {
        return Solutions::Empty;
    }
    line(a11, a12, b1, p, inverse)
}

fn line(a1: i64, a2: i64, b: i64, p: i64, inverse: &[i64]) -> Solutions {
    let direction = (md(-a2, p), a1);
    let base = if a1 != 0 {
        (md(b * inverse[idx(a1)], p), 0)
    } else {
        (0, md(b * inverse[idx(a2)], p))
    };
    Solutions::Line(base, direction)
}

fn enumerate(set: Solutions, p: i64, out: &mut Vec<Point>) {
    out.clear();
    match set {
        Solutions::Empty => {}
        Solutions::Point(q) => out.push(q),
        Solutions::Line(base, direction) => {
            for step in 0..p {
                out.push((
                    md(base.0 + step * direction.0, p),
                    md(base.1 + step * direction.1, p),
                ));
            }
        }
        Solutions::Plane => {
            for x in 0..p {
                for y in 0..p {
                    out.push((x, y));
                }
            }
        }
    }
}

/// The `(row, right-hand side)` pair of one hypothesis, affine in `(vx, vy)`.
fn affine_row(
    poly: &MvPoly,
    base: &BTreeMap<String, i64>,
    vx: &str,
    vy: &str,
    p: i64,
    inverse: &[i64],
) -> (i64, i64, i64) {
    let mut at = base.clone();
    at.insert(vx.to_string(), 0);
    at.insert(vy.to_string(), 0);
    let constant = eval_mod(poly, &at, p, inverse).expect("no p in a denominator");
    at.insert(vx.to_string(), 1);
    let along_x = eval_mod(poly, &at, p, inverse).expect("evaluable");
    at.insert(vx.to_string(), 0);
    at.insert(vy.to_string(), 1);
    let along_y = eval_mod(poly, &at, p, inverse).expect("evaluable");
    (
        md(along_x - constant, p),
        md(along_y - constant, p),
        md(-constant, p),
    )
}

/// Every collinear triple of `F_p^2`, decided by the corpus's own
/// `abc-collinear` polynomial rather than by a re-derived formula.
fn collinear_triples(carrier: &MvPoly, p: i64, inverse: &[i64]) -> Vec<[Point; 3]> {
    let mut triples = Vec::new();
    for ax in 0..p {
        for ay in 0..p {
            for bx in 0..p {
                for by in 0..p {
                    for cx in 0..p {
                        for cy in 0..p {
                            let at: BTreeMap<String, i64> = [
                                ("ax", ax),
                                ("ay", ay),
                                ("bx", bx),
                                ("by", by),
                                ("cx", cx),
                                ("cy", cy),
                            ]
                            .into_iter()
                            .map(|(name, value)| (name.to_string(), value))
                            .collect();
                            if eval_mod(carrier, &at, p, inverse) == Some(0) {
                                triples.push([(ax, ay), (bx, by), (cx, cy)]);
                            }
                        }
                    }
                }
            }
        }
    }
    triples
}

/// One representative of each `Aff(2,p)` orbit of collinear triples: all three
/// points equal, each of the three ways exactly two coincide, and `(0,0)`,
/// `(1,0)`, `(t,0)` for the `p−2` admissible `t`.
fn orbit_representatives(p: i64) -> Vec<[Point; 3]> {
    let mut first = vec![
        [(0, 0), (0, 0), (0, 0)],
        [(0, 0), (0, 0), (1, 0)],
        [(0, 0), (1, 0), (0, 0)],
        [(0, 0), (1, 0), (1, 0)],
    ];
    for t in 0..p {
        if t != 0 && t != 1 {
            first.push([(0, 0), (1, 0), (t, 0)]);
        }
    }
    first
}

/// The six coordinates of one carrier-line pair, as an assignment.
fn carrier_assignment(first: &[Point; 3], second: &[Point; 3]) -> BTreeMap<String, i64> {
    let mut at = BTreeMap::new();
    for (name, point) in [
        ("a", first[0]),
        ("b", first[1]),
        ("c", first[2]),
        ("d", second[0]),
        ("e", second[1]),
        ("f", second[2]),
    ] {
        at.insert(format!("{name}x"), point.0);
        at.insert(format!("{name}y"), point.1);
    }
    at
}

/// The outcome of one prime: a refuting configuration per zero/nonzero pattern
/// of the three conditions, and how many configurations had all three nonzero.
struct Decision {
    witness: Vec<Option<String>>,
    all_nonzero: u64,
}

fn decide(
    problem: &GeometryProblem,
    carriers: [&MvPoly; 2],
    crosses: &[(&str, [&MvPoly; 2]); 3],
    first: &[[Point; 3]],
    triples: &[[Point; 3]],
    p: i64,
    inverse: &[i64],
) -> Decision {
    let mut witness: Vec<Option<String>> = vec![None; 8];
    let mut all_nonzero = 0u64;
    let mut sets = [Vec::new(), Vec::new(), Vec::new()];
    for carrier_one in first {
        for carrier_two in triples {
            let at = carrier_assignment(carrier_one, carrier_two);
            if eval_mod(carriers[1], &at, p, inverse) != Some(0) {
                continue;
            }
            let mut probe = at.clone();
            for name in ["xx", "xy", "yx", "yy", "zx", "zy"] {
                probe.insert(name.to_string(), 0);
            }
            let mut mask = 0usize;
            for (slot, condition) in problem.nondegeneracy.iter().enumerate() {
                if eval_mod(&condition.poly, &probe, p, inverse) != Some(0) {
                    mask |= 1 << slot;
                }
            }
            if mask == 0b111 {
                all_nonzero += 1;
            }
            if witness[mask].is_some() {
                continue;
            }
            let mut empty = false;
            for (slot, (name, polys)) in crosses.iter().enumerate() {
                let vx = format!("{name}x");
                let vy = format!("{name}y");
                let rows = [
                    affine_row(polys[0], &at, &vx, &vy, p, inverse),
                    affine_row(polys[1], &at, &vx, &vy, p, inverse),
                ];
                enumerate(solve(rows, p, inverse), p, &mut sets[slot]);
                empty |= sets[slot].is_empty();
            }
            if empty {
                continue;
            }
            witness[mask] = refuting(problem, &at, &sets, p, inverse);
        }
    }
    Decision {
        witness,
        all_nonzero,
    }
}

/// A choice of `X`, `Y`, `Z` from their solution sets that falsifies the
/// conclusion, if the sets admit one.
fn refuting(
    problem: &GeometryProblem,
    at: &BTreeMap<String, i64>,
    sets: &[Vec<Point>; 3],
    p: i64,
    inverse: &[i64],
) -> Option<String> {
    for &x in &sets[0] {
        for &y in &sets[1] {
            for &z in &sets[2] {
                let mut probe = at.clone();
                for (name, point) in [("x", x), ("y", y), ("z", z)] {
                    probe.insert(format!("{name}x"), point.0);
                    probe.insert(format!("{name}y"), point.1);
                }
                if eval_mod(&problem.conclusions[0].poly, &probe, p, inverse) != Some(0) {
                    return Some(format!("{probe:?}"));
                }
            }
        }
    }
    None
}

fn report(problem: &GeometryProblem, decision: &Decision, p: i64, full: bool) {
    println!(
        "\n=== p = {p}{} ===",
        if full {
            " (every first triple)"
        } else {
            " (affine orbits)"
        }
    );
    println!(
        "  configurations with all three conditions nonzero: {}",
        decision.all_nonzero
    );
    for mask in 0..8usize {
        let label = format!(
            "c1{} c2{} c3{}",
            if mask & 1 != 0 { "≠0" } else { "=0" },
            if mask & 2 != 0 { "≠0" } else { "=0" },
            if mask & 4 != 0 { "≠0" } else { "=0" },
        );
        println!(
            "  [{label}] {}",
            if decision.witness[mask].is_some() {
                "a refuting configuration EXISTS"
            } else {
                "no refuting configuration"
            }
        );
    }
    println!("  subset verdicts:");
    for subset in 0..8usize {
        let refuted =
            (0..8usize).any(|mask| decision.witness[mask].is_some() && mask & subset == subset);
        let named: Vec<&str> = (0..3)
            .filter(|slot| subset & (1 << slot) != 0)
            .map(|slot| problem.nondegeneracy[slot].id.as_str())
            .collect();
        println!(
            "    {{{}}}: {}",
            named.join(", "),
            if refuted {
                "REFUTED — insufficient"
            } else {
                "no refutation — sufficient over this field"
            }
        );
    }
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let full = arguments.iter().any(|argument| argument == "--full");
    let mut primes: Vec<i64> = arguments
        .iter()
        .filter_map(|argument| argument.parse().ok())
        .collect();
    if primes.is_empty() {
        primes = vec![5, 7, 11];
    }

    let problem: GeometryProblem = corpus()
        .into_iter()
        .find(|problem| problem.id == "pappus-hexagon")
        .expect("pappus-hexagon is in the corpus");
    // Hypotheses 0 and 1 are the two carrier collinearities; 2..8 come in pairs,
    // one pair per cross point, in the order X, Y, Z.
    let carriers = [&problem.hypotheses[0].poly, &problem.hypotheses[1].poly];
    let crosses = [
        (
            "x",
            [&problem.hypotheses[2].poly, &problem.hypotheses[3].poly],
        ),
        (
            "y",
            [&problem.hypotheses[4].poly, &problem.hypotheses[5].poly],
        ),
        (
            "z",
            [&problem.hypotheses[6].poly, &problem.hypotheses[7].poly],
        ),
    ];
    println!(
        "pappus-hexagon: {} hypotheses, {} conditions, conclusion `{}`",
        problem.hypotheses.len(),
        problem.nondegeneracy.len(),
        problem.conclusions[0].id
    );

    for p in primes {
        let inverse = inverses(p);
        let triples = collinear_triples(carriers[0], p, &inverse);
        let first = if full {
            triples.clone()
        } else {
            orbit_representatives(p)
        };
        let decision = decide(&problem, carriers, &crosses, &first, &triples, p, &inverse);
        report(&problem, &decision, p, full);
    }
}
