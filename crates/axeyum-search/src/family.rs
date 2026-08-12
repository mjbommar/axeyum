//! Instance families: parameterised generators of [`ColouringProblem`]s.
//!
//! A family owns two *deliberately different* implementations of the same
//! mathematics:
//!
//! * [`ColouringFamily::constraints`] — the fast parameterised enumeration the
//!   encoder consumes;
//! * [`ColouringFamily::first_violation`] — a brute-force enumerator, written
//!   from the defining equation rather than from the parameterisation, used to
//!   check witnesses.
//!
//! The duplication is the point. A witness accepted by the same enumeration
//! that built the formula proves only that the two agree; a witness accepted by
//! an independent pass over the defining equation proves the colouring is real.
//! The scratch tooling this crate replaces caught a search bug that way, and the
//! `SEARCH LIED` path exists because it fired.
//!
//! Adding a family means implementing three short methods. Everything
//! downstream — the encoder, the cover harness, the ledger, the certification
//! pass, the local search — is family-agnostic and needs no change.

use crate::SearchError;
use crate::colouring::{ColouringProblem, Witness};

/// A parameterised family of colouring instances.
pub trait ColouringFamily: Sync {
    /// Short machine-readable family name, e.g. `rado`.
    fn name(&self) -> &'static str;

    /// Human-readable identity of this family instance, e.g. `R_4(3(x-y)=2z)`.
    fn label(&self) -> String;

    /// Number of colours, the `k` of the instance.
    fn colours(&self) -> usize;

    /// The forbidden sets over `1..=points`, in encoding order.
    ///
    /// This is the enumeration the CNF encoder consumes, so its order is part
    /// of the encoding contract.
    fn constraints(&self, points: usize) -> Vec<Vec<usize>>;

    /// The first violation of the family's defining relation in `colouring`,
    /// found by brute force over the relation itself.
    ///
    /// Implementations must **not** call [`ColouringFamily::constraints`]: the
    /// value of this method is that it shares no code with the encoder.
    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)>;

    /// Points to branch on for a cover of the given depth.
    ///
    /// The default skips point 1, whose colour the symmetry breaking already
    /// fixes, and takes every second point after it — the choice the Rado runs
    /// used.
    fn branch_points(&self, depth: usize) -> Vec<usize> {
        (1..=depth).map(|slot| 2 * slot).collect()
    }

    /// Builds the colouring problem for `points`.
    ///
    /// # Errors
    ///
    /// Returns whatever [`ColouringProblem::new`] rejects.
    fn problem(&self, points: usize) -> Result<ColouringProblem, SearchError> {
        ColouringProblem::new(points, self.colours(), self.constraints(points))
    }

    /// Checks a witness against the family's own relation.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::WitnessMonochromatic`] when the colouring
    /// contains a monochromatic set — the witness is not a witness — and
    /// [`SearchError::ColourOutOfRange`] when it uses a colour the family does
    /// not have.
    fn verify_witness(&self, witness: &Witness) -> Result<(), SearchError> {
        for &colour in witness.colouring() {
            if colour == 0 || colour > self.colours() {
                return Err(SearchError::ColourOutOfRange {
                    colour,
                    colours: self.colours(),
                });
            }
        }
        match self.first_violation(witness.colouring()) {
            None => Ok(()),
            Some((members, colour)) => Err(SearchError::WitnessMonochromatic { members, colour }),
        }
    }
}

/// Sorts and deduplicates a triple into a forbidden set.
fn member_set(a: usize, b: usize, c: usize) -> Vec<usize> {
    let mut set = vec![a, b, c];
    set.sort_unstable();
    set.dedup();
    set
}

/// The Rado family `a(x - y) = b z` over `1..=n`.
///
/// `R_k(a(x-y)=bz)` is the least `n` such that every `k`-colouring of `[1..n]`
/// has a monochromatic solution, so the instance for `n` is satisfiable exactly
/// when `R_k > n`. Published values this crate reproduces end to end:
/// `R_3(4(x-y)=3z) = 73` and `R_4(3(x-y)=2z) = 103`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rado {
    a: usize,
    b: usize,
    colours: usize,
}

impl Rado {
    /// Builds the family `a(x - y) = b z` with `colours` colours.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] if any parameter is zero.
    pub fn new(a: usize, b: usize, colours: usize) -> Result<Self, SearchError> {
        if a == 0 || b == 0 || colours == 0 {
            return Err(SearchError::InvalidParameter {
                what: format!("rado needs a,b,k >= 1, got a={a} b={b} k={colours}"),
            });
        }
        Ok(Self { a, b, colours })
    }

    /// The `a` coefficient.
    pub fn a(&self) -> usize {
        self.a
    }

    /// The `b` coefficient.
    pub fn b(&self) -> usize {
        self.b
    }
}

/// Greatest common divisor, iterative.
fn gcd(mut a: usize, mut b: usize) -> usize {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

impl ColouringFamily for Rado {
    fn name(&self) -> &'static str {
        "rado"
    }

    fn label(&self) -> String {
        format!("R_{}({}(x-y)={}z)", self.colours, self.a, self.b)
    }

    fn colours(&self) -> usize {
        self.colours
    }

    /// Solutions are enumerated as `x - y = b' t`, `z = a' t` for `t = 1, 2, …`
    /// with `g = gcd(a, b)`, `a' = a / g`, `b' = b / g`, inner loop over `y`
    /// ascending. This parameterisation and this order are the encoding
    /// contract shared with `scripts/gen-rado-instance.py`.
    fn constraints(&self, points: usize) -> Vec<Vec<usize>> {
        let divisor = gcd(self.a, self.b);
        let (step_z, step_x) = (self.a / divisor, self.b / divisor);
        let mut sets = Vec::new();
        let mut t = 1usize;
        while let (Some(z), Some(dx)) = (step_z.checked_mul(t), step_x.checked_mul(t)) {
            if z > points || dx + 1 > points {
                break;
            }
            for y in 1..=(points - dx) {
                sets.push(member_set(y + dx, y, z));
            }
            t += 1;
        }
        sets
    }

    /// Brute force straight off `a(x - y) = b z`, over all ordered pairs.
    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        let points = colouring.len();
        for x in 1..=points {
            for y in 1..x {
                let numerator = self.a * (x - y);
                if !numerator.is_multiple_of(self.b) {
                    continue;
                }
                let z = numerator / self.b;
                if z == 0 || z > points {
                    continue;
                }
                let colour = colouring[x - 1];
                if colouring[y - 1] == colour && colouring[z - 1] == colour {
                    return Some((member_set(x, y, z), colour));
                }
            }
        }
        None
    }
}

/// The Schur family `x + y = z` over `1..=n`, the second family.
///
/// Present to keep the abstraction honest: it exists so that "a second family
/// needs no change to the harness" is a fact the tests exercise rather than a
/// claim. Known values: a 2-colouring of `[1..4]` exists and none of `[1..5]`
/// does, so `R_2 = 5`; `R_3 = 14`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Schur {
    colours: usize,
}

impl Schur {
    /// Builds the family with `colours` colours.
    ///
    /// # Errors
    ///
    /// Returns [`SearchError::InvalidParameter`] if `colours` is zero.
    pub fn new(colours: usize) -> Result<Self, SearchError> {
        if colours == 0 {
            return Err(SearchError::InvalidParameter {
                what: "schur needs k >= 1".to_string(),
            });
        }
        Ok(Self { colours })
    }
}

impl ColouringFamily for Schur {
    fn name(&self) -> &'static str {
        "schur"
    }

    fn label(&self) -> String {
        format!("R_{}(x+y=z)", self.colours)
    }

    fn colours(&self) -> usize {
        self.colours
    }

    fn constraints(&self, points: usize) -> Vec<Vec<usize>> {
        let mut sets = Vec::new();
        for z in 2..=points {
            for x in 1..=(z / 2) {
                sets.push(member_set(x, z - x, z));
            }
        }
        sets
    }

    fn first_violation(&self, colouring: &[usize]) -> Option<(Vec<usize>, usize)> {
        let points = colouring.len();
        for x in 1..=points {
            for y in x..=points {
                let z = x + y;
                if z > points {
                    break;
                }
                let colour = colouring[x - 1];
                if colouring[y - 1] == colour && colouring[z - 1] == colour {
                    return Some((member_set(x, y, z), colour));
                }
            }
        }
        None
    }

    fn branch_points(&self, depth: usize) -> Vec<usize> {
        (1..=depth).map(|slot| slot + 1).collect()
    }
}

/// Parses a family specification such as `rado:a=3,b=2,k=4` or `schur:k=3`.
///
/// # Errors
///
/// Returns [`SearchError::InvalidParameter`] for an unknown family, a malformed
/// or unknown key, a missing required key, or a value that is not a number.
pub fn parse_family(spec: &str) -> Result<Box<dyn ColouringFamily>, SearchError> {
    let (name, rest) = spec.split_once(':').unwrap_or((spec, ""));
    let mut keys: Vec<(&str, usize)> = Vec::new();
    for field in rest.split(',').filter(|field| !field.trim().is_empty()) {
        let (key, value) = field
            .split_once('=')
            .ok_or_else(|| SearchError::InvalidParameter {
                what: format!("family field {field:?} is not key=value"),
            })?;
        let value = value
            .trim()
            .parse::<usize>()
            .map_err(|_| SearchError::InvalidParameter {
                what: format!("family field {field:?} has a non-numeric value"),
            })?;
        keys.push((key.trim(), value));
    }
    let get = |wanted: &str| keys.iter().find(|(key, _)| *key == wanted).map(|(_, v)| *v);
    let require = |wanted: &str| {
        get(wanted).ok_or_else(|| SearchError::InvalidParameter {
            what: format!("family {name:?} needs {wanted}=<number>"),
        })
    };
    let known: &[&str] = match name {
        "rado" => &["a", "b", "k"],
        "schur" => &["k"],
        _ => {
            return Err(SearchError::InvalidParameter {
                what: format!("unknown family {name:?}; known: rado, schur"),
            });
        }
    };
    if let Some((key, _)) = keys.iter().find(|(key, _)| !known.contains(key)) {
        return Err(SearchError::InvalidParameter {
            what: format!("family {name:?} has no parameter {key:?}"),
        });
    }
    match name {
        "rado" => Ok(Box::new(Rado::new(
            require("a")?,
            require("b")?,
            require("k")?,
        )?)),
        _ => Ok(Box::new(Schur::new(require("k")?)?)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rado_constraints_match_the_generator_parameterisation() {
        // a=3, b=2, n=8: g=1, so z = 3t and x - y = 2t.
        let family = Rado::new(3, 2, 4).expect("family");
        let sets = family.constraints(8);
        // t = 1: z = 3, dx = 2, y = 1..6 -> {1,3}, {2,3,4}, {3,5}, {3,4,6}, ...
        assert_eq!(sets[0], vec![1, 3]);
        assert_eq!(sets[1], vec![2, 3, 4]);
        assert_eq!(sets[2], vec![3, 5]);
        // t = 2: z = 6, dx = 4, y = 1..4.
        assert_eq!(sets[6], vec![1, 5, 6]);
    }

    #[test]
    fn rado_brute_force_finds_a_monochromatic_solution() {
        let family = Rado::new(3, 2, 2).expect("family");
        // 3(4-2) = 2*3, so {2,3,4} monochromatic is a violation.
        let violation = family.first_violation(&[1, 2, 2, 2, 1, 1]);
        assert_eq!(violation, Some((vec![2, 3, 4], 2)));
    }

    #[test]
    fn rado_brute_force_and_encoder_view_agree_on_random_colourings() {
        let family = Rado::new(4, 3, 3).expect("family");
        let problem = family.problem(24).expect("problem");
        let mut state = 0x2026_0812_u64;
        let mut compared = 0usize;
        for _ in 0..64 {
            let colouring: Vec<usize> = (0..24)
                .map(|_| {
                    state = state
                        .wrapping_mul(6_364_136_223_846_793_005)
                        .wrapping_add(1);
                    ((state >> 33) % 3) as usize + 1
                })
                .collect();
            assert_eq!(
                family.first_violation(&colouring).is_none(),
                problem.first_monochromatic(&colouring).is_none(),
                "independent and encoder views disagree on {colouring:?}"
            );
            compared += 1;
        }
        assert_eq!(compared, 64);
    }

    #[test]
    fn schur_brute_force_finds_a_monochromatic_sum() {
        let family = Schur::new(2).expect("family");
        assert_eq!(family.first_violation(&[1, 1, 1]), Some((vec![1, 2], 1)));
        assert_eq!(family.first_violation(&[1, 2, 2, 1]), None);
    }

    #[test]
    fn verify_witness_rejects_a_lying_search() {
        let family = Schur::new(2).expect("family");
        let witness = Witness::new(2, vec![1, 1, 1]).expect("witness");
        let error = family.verify_witness(&witness).expect_err("1+1=2 is mono");
        assert_eq!(
            error,
            SearchError::WitnessMonochromatic {
                members: vec![1, 2],
                colour: 1
            }
        );
    }

    #[test]
    fn family_specs_round_trip() {
        let rado = parse_family("rado:a=3,b=2,k=4").expect("rado spec");
        assert_eq!(rado.label(), "R_4(3(x-y)=2z)");
        let schur = parse_family("schur:k=3").expect("schur spec");
        assert_eq!(schur.label(), "R_3(x+y=z)");
    }

    #[test]
    fn family_specs_reject_unknown_families_and_keys() {
        assert!(parse_family("vdw:k=2").is_err());
        assert!(parse_family("rado:a=3,b=2,k=4,c=1").is_err());
        assert!(parse_family("rado:a=3,b=2").is_err());
        assert!(parse_family("rado:a=x,b=2,k=4").is_err());
    }
}
