//! Reconstruct and check exact theta duals for two calibration graphs.

use axeyum_cas::sos::{
    psd_big::BigPsdLimits,
    theta::{NonedgeMultiplier, ThetaCliqueDual, ThetaDualCheck, check_theta_clique_dual},
};
use num_bigint::BigInt;
use num_rational::BigRational;

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn graph(order: usize, edges: &[(usize, usize)]) -> Vec<Vec<bool>> {
    let mut adjacency = vec![vec![false; order]; order];
    for &(u, v) in edges {
        adjacency[u][v] = true;
        adjacency[v][u] = true;
    }
    adjacency
}

fn verified(result: &ThetaDualCheck) -> bool {
    matches!(result, ThetaDualCheck::Verified { .. })
}

fn main() {
    let limits = BigPsdLimits::default();
    let k3 = graph(3, &[(0, 1), (0, 2), (1, 2)]);
    let k3_bound_three = ThetaCliqueDual {
        bound: integer(3),
        nonedge_multipliers: vec![],
    };
    let k3_false_bound_two = ThetaCliqueDual {
        bound: integer(2),
        nonedge_multipliers: vec![],
    };
    let empty3_bound_one = ThetaCliqueDual {
        bound: integer(1),
        nonedge_multipliers: vec![
            NonedgeMultiplier {
                u: 0,
                v: 1,
                value: integer(1),
            },
            NonedgeMultiplier {
                u: 0,
                v: 2,
                value: integer(1),
            },
            NonedgeMultiplier {
                u: 1,
                v: 2,
                value: integer(1),
            },
        ],
    };

    let positive_k3 = verified(&check_theta_clique_dual(&k3, &k3_bound_three, limits));
    let negative_k3 = !verified(&check_theta_clique_dual(&k3, &k3_false_bound_two, limits));
    let positive_empty = verified(&check_theta_clique_dual(
        &graph(3, &[]),
        &empty3_bound_one,
        limits,
    ));

    println!("theta-dual-format=v1");
    println!("k3-bound-3-verified={positive_k3}");
    println!("k3-bound-2-rejected={negative_k3}");
    println!("empty3-bound-1-verified={positive_empty}");
    if !(positive_k3 && negative_k3 && positive_empty) {
        std::process::exit(1);
    }
}
