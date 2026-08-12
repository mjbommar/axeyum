//! Min-conflicts local search for the satisfiable side of a threshold.
//!
//! Establishing `R` needs a colouring of `[R - 1]`, and a stochastic local
//! search finds one orders of magnitude faster than the CDCL core on the
//! instances this crate was built for. The search is **untrusted**: a returned
//! [`Witness`] has already been screened against
//! [`ColouringProblem::first_monochromatic`], but callers must still replay it
//! through [`ColouringFamily::first_violation`](crate::ColouringFamily), the
//! brute-force enumerator that shares no code with the encoder.
//!
//! Determinism is a public API promise: the walk is driven by an explicit
//! seed through a fixed xorshift generator, the budget is a move count rather
//! than wall-clock time, and identical inputs produce identical outputs on
//! every platform.

use crate::SearchError;
use crate::colouring::{ColouringProblem, Witness};

/// A fixed 64-bit xorshift generator. Not cryptographic and not meant to be:
/// it exists so the walk is reproducible from `seed` alone, with no OS
/// entropy anywhere.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        // Avoid the all-zero fixed point.
        Self(seed.wrapping_add(0x9e37_79b9_7f4a_7c15) | 1)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    /// A value in `0..bound`. `bound` must be non-zero.
    fn below(&mut self, bound: usize) -> usize {
        usize::try_from(self.next() % (bound as u64)).expect("bound fits usize")
    }
}

/// Tuning for [`min_conflicts`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MinConflictsOptions {
    /// Seed for the deterministic walk. Two calls with the same problem,
    /// start, and options return the same result.
    pub seed: u64,
    /// Maximum number of recolouring moves before giving up. A move touches
    /// one point, so the budget bounds work, not wall-clock time.
    pub max_moves: u64,
    /// Percent chance (`0..=100`) that a move recolours randomly instead of
    /// greedily — the WalkSAT-style noise that escapes local minima.
    pub noise_percent: u8,
    /// Percent chance (`0..=100`) that a tie between equally good colours is
    /// broken in favour of the later candidate.
    pub tie_percent: u8,
}

impl Default for MinConflictsOptions {
    fn default() -> Self {
        // The values the Rado runs used (15% noise, 30% tie randomness).
        Self {
            seed: 0,
            max_moves: 2_000_000,
            noise_percent: 15,
            tie_percent: 30,
        }
    }
}

/// Min-conflicts search for a colouring of `problem` with no monochromatic
/// forbidden set.
///
/// Starts from `start` when given (a warm start such as the valuation
/// colouring cuts the walk dramatically on Rado instances), otherwise from
/// the deterministic round-robin colouring. Each move picks a violated
/// forbidden set, picks a point in it, and recolours that point to minimise
/// the number of violated sets it touches, with bounded noise.
///
/// Returns `Ok(Some(witness))` only when the finished colouring ALSO passes
/// [`ColouringProblem::first_monochromatic`] — the search's own bookkeeping is
/// never the last word. Returns `Ok(None)` when the move budget runs out.
///
/// # Errors
///
/// Returns [`SearchError::InvalidParameter`] if `start` does not match the
/// problem's points/colours, or if the search's cleared conflict set
/// disagrees with the independent screen (an internal invariant violation).
pub fn min_conflicts(
    problem: &ColouringProblem,
    start: Option<&Witness>,
    options: &MinConflictsOptions,
) -> Result<Option<Witness>, SearchError> {
    let points = problem.points();
    let colours = problem.colours();
    let forbidden = problem.forbidden();

    // `colouring[j - 1]` is the colour of point `j`, in `1..=colours`.
    let mut colouring: Vec<usize> = match start {
        Some(witness) => {
            if witness.points() != points || witness.colours() != colours {
                return Err(SearchError::InvalidParameter {
                    what: format!(
                        "start witness colours {} points with {} colours; the problem has {points} \
                         points and {colours} colours",
                        witness.points(),
                        witness.colours()
                    ),
                });
            }
            witness.colouring().to_vec()
        }
        None => (0..points).map(|index| (index % colours) + 1).collect(),
    };

    // Incidence: which forbidden sets each point participates in.
    let mut incidence: Vec<Vec<usize>> = vec![Vec::new(); points];
    for (constraint, set) in forbidden.iter().enumerate() {
        for &point in set {
            incidence[point - 1].push(constraint);
        }
    }
    let monochromatic = |colouring: &[usize], set: &[usize]| {
        let first = colouring[set[0] - 1];
        set.iter().all(|&point| colouring[point - 1] == first)
    };

    // The violated set, as a vector with O(1) membership and swap-removal so
    // "pick a random violated constraint" stays cheap and deterministic.
    let mut violated: Vec<usize> = Vec::new();
    let mut position: Vec<Option<usize>> = vec![None; forbidden.len()];
    for (constraint, set) in forbidden.iter().enumerate() {
        if monochromatic(&colouring, set) {
            position[constraint] = Some(violated.len());
            violated.push(constraint);
        }
    }

    let mut rng = Rng::new(options.seed);
    let mut moves = 0u64;
    while !violated.is_empty() && moves < options.max_moves {
        moves += 1;
        let constraint = violated[rng.below(violated.len())];
        let set = &forbidden[constraint];
        let point = set[rng.below(set.len())];
        let current = colouring[point - 1];

        let chosen = if u64::from(options.noise_percent) > rng.next() % 100 {
            // Noise: any other colour, uniformly.
            let offset = 1 + rng.below(colours - 1);
            ((current - 1 + offset) % colours) + 1
        } else {
            // Greedy: the colour minimising violated sets through this point.
            let mut best_colour = current;
            let mut best_count = usize::MAX;
            for candidate in 1..=colours {
                if candidate == current {
                    continue;
                }
                colouring[point - 1] = candidate;
                let count = incidence[point - 1]
                    .iter()
                    .filter(|&&other| monochromatic(&colouring, &forbidden[other]))
                    .count();
                colouring[point - 1] = current;
                let tie = count == best_count && u64::from(options.tie_percent) > rng.next() % 100;
                if count < best_count || tie {
                    best_count = count;
                    best_colour = candidate;
                }
            }
            best_colour
        };

        colouring[point - 1] = chosen;
        for &other in &incidence[point - 1] {
            let now_violated = monochromatic(&colouring, &forbidden[other]);
            match (position[other], now_violated) {
                (None, true) => {
                    position[other] = Some(violated.len());
                    violated.push(other);
                }
                (Some(slot), false) => {
                    let last = violated.pop().expect("slot implies non-empty");
                    if slot < violated.len() {
                        violated[slot] = last;
                        position[last] = Some(slot);
                    }
                    position[other] = None;
                }
                _ => {}
            }
        }
    }

    if !violated.is_empty() {
        return Ok(None);
    }
    // The walk's own bookkeeping cleared; screen the result independently of
    // it before offering a witness. A disagreement is a bug, not a "no".
    if let Some((set, colour)) = problem.first_monochromatic(&colouring) {
        return Err(SearchError::InvalidParameter {
            what: format!(
                "internal: min-conflicts cleared its conflict set but {set:?} is monochromatic \
                 in colour {colour}"
            ),
        });
    }
    Ok(Some(Witness::new(colours, colouring)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::family::{ColouringFamily, Schur};

    #[test]
    fn finds_a_schur_colouring_below_the_threshold() {
        // S(2) = 5: [1, 4] has a sum-free 2-colouring, [1, 5] does not.
        let family = Schur::new(2).expect("family");
        let problem = family.problem(4).expect("problem");
        let witness = min_conflicts(&problem, None, &MinConflictsOptions::default())
            .expect("search")
            .expect("a witness exists at n = 4");
        // Replay through the enumerator that shares no code with the encoder.
        assert_eq!(family.first_violation(witness.colouring()), None);
    }

    #[test]
    fn gives_up_honestly_at_the_threshold() {
        let family = Schur::new(2).expect("family");
        let problem = family.problem(5).expect("problem");
        let options = MinConflictsOptions {
            max_moves: 20_000,
            ..MinConflictsOptions::default()
        };
        assert_eq!(
            min_conflicts(&problem, None, &options).expect("search"),
            None
        );
    }

    #[test]
    fn identical_seeds_walk_identically() {
        let family = Schur::new(2).expect("family");
        let problem = family.problem(4).expect("problem");
        let options = MinConflictsOptions {
            seed: 7,
            ..MinConflictsOptions::default()
        };
        let first = min_conflicts(&problem, None, &options).expect("search");
        let second = min_conflicts(&problem, None, &options).expect("search");
        assert_eq!(first, second);
    }

    #[test]
    fn a_mismatched_start_is_refused() {
        let family = Schur::new(2).expect("family");
        let problem = family.problem(4).expect("problem");
        let start = Witness::new(2, vec![1, 2]).expect("witness");
        assert!(matches!(
            min_conflicts(&problem, Some(&start), &MinConflictsOptions::default()),
            Err(SearchError::InvalidParameter { .. })
        ));
    }
}
