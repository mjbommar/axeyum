//! Quantified BV front-door regressions.
//!
//! The measured cvc5-regress-clean quantified-BV batch now routes through the
//! full SMT-LIB front door without surfacing backend-unsupported errors.

use std::time::Duration;

use axeyum_solver::{SolverConfig, SolverError, solve_smtlib};

const INTERSECTION_ONELANE: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__intersection-example-onelane.proof-node22337.smt2"
);
const PSYCO_001_BV: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__psyco-001-bv.smt2"
);
const PSYCO_107_BV: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__psyco-107-bv.smt2"
);
const SMTCOMP_QBV_053118: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__smtcomp-qbv-053118.smt2"
);
const GN_WRONG_091018: &str = include_str!(
    "../../../corpus/public-curated/quantified/BV/cvc5-regress-clean/cli__regress2__quantifiers__gn-wrong-091018.smt2"
);

#[test]
fn remaining_quantified_bv_rows_are_not_unsupported() {
    let config = SolverConfig::new().with_timeout(Duration::from_secs(10));
    for (name, text) in [
        ("intersection-example-onelane", INTERSECTION_ONELANE),
        ("psyco-001-bv", PSYCO_001_BV),
        ("psyco-107-bv", PSYCO_107_BV),
        ("smtcomp-qbv-053118", SMTCOMP_QBV_053118),
        ("gn-wrong-091018", GN_WRONG_091018),
    ] {
        match solve_smtlib(text, &config) {
            Ok(outcome) => {
                eprintln!("{name}: {:?}", outcome.result);
            }
            Err(SolverError::Unsupported(error)) => {
                panic!("{name} regressed to unsupported: {error}");
            }
            Err(error) => {
                panic!("{name} produced an unexpected error: {error}");
            }
        }
    }
}
