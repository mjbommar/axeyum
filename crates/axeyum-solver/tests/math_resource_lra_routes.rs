//! Resource-backed `QF_LRA` proof-route regressions for math curriculum packs.
//!
//! These tests keep the educational resources tied to Axeyum's checked evidence
//! path: the pack-level replay remains useful, but an upgraded `unsat` row must
//! also produce independently rechecked Farkas evidence.

use axeyum_ir::{Rational, TermArena, TermId};
use axeyum_smtlib::parse_script;
use axeyum_solver::{
    CheckResult, Evidence, SolverConfig, TrustId, check_auto, produce_lra_evidence,
};

const LINEAR_ALGEBRA_SINGULAR_SYSTEM: &str = include_str!(
    "../../../artifacts/examples/math/linear-algebra-rational-v0/smt2/singular-system-inconsistent-farkas-conflict.smt2"
);
const LINEAR_ALGEBRA_BAD_LU_PRODUCT_ENTRY: &str = include_str!(
    "../../../artifacts/examples/math/linear-algebra-rational-v0/smt2/bad-lu-product-entry-farkas-conflict.smt2"
);
const FINITE_LU_DECOMPOSITION_BAD_MULTIPLIER: &str = include_str!(
    "../../../artifacts/examples/math/finite-lu-decomposition-v0/smt2/bad-lu-multiplier-farkas-conflict.smt2"
);
const FINITE_PIVOTED_LU_DECOMPOSITION_BAD_PIVOT_SIGN: &str = include_str!(
    "../../../artifacts/examples/math/finite-pivoted-lu-decomposition-v0/smt2/bad-pivot-sign-farkas-conflict.smt2"
);
const FINITE_LDLT_DECOMPOSITION_BAD_DIAGONAL: &str = include_str!(
    "../../../artifacts/examples/math/finite-ldlt-decomposition-v0/smt2/bad-ldlt-diagonal-farkas-conflict.smt2"
);
const LINEAR_ALGEBRA_BAD_NULLSPACE_COMPONENT: &str = include_str!(
    "../../../artifacts/examples/math/linear-algebra-rational-v0/smt2/bad-nullspace-component-farkas-conflict.smt2"
);
const FINITE_GAUSSIAN_ELIMINATION_BAD_RHS: &str = include_str!(
    "../../../artifacts/examples/math/finite-gaussian-elimination-v0/smt2/bad-eliminated-rhs-farkas-conflict.smt2"
);
const FINITE_QR_DECOMPOSITION_BAD_PRODUCT_ENTRY: &str = include_str!(
    "../../../artifacts/examples/math/finite-qr-decomposition-v0/smt2/bad-qr-product-entry-farkas-conflict.smt2"
);
const FINITE_GIVENS_ROTATION_BAD_SINE: &str = include_str!(
    "../../../artifacts/examples/math/finite-givens-rotation-v0/smt2/bad-givens-sine-farkas-conflict.smt2"
);
const FINITE_GRAM_SCHMIDT_BAD_R12: &str = include_str!(
    "../../../artifacts/examples/math/finite-gram-schmidt-v0/smt2/bad-gram-schmidt-r12-farkas-conflict.smt2"
);
const FINITE_HOUSEHOLDER_REFLECTION_BAD_ENTRY: &str = include_str!(
    "../../../artifacts/examples/math/finite-householder-reflection-v0/smt2/bad-householder-entry-farkas-conflict.smt2"
);
const FINITE_CHOLESKY_DECOMPOSITION_BAD_PRODUCT_ENTRY: &str = include_str!(
    "../../../artifacts/examples/math/finite-cholesky-decomposition-v0/smt2/bad-cholesky-product-entry-farkas-conflict.smt2"
);
const LINEAR_OPTIMIZATION_OBJECTIVE_THRESHOLD: &str = include_str!(
    "../../../artifacts/examples/math/linear-optimization-v0/smt2/objective-threshold-farkas-conflict.smt2"
);
const CONVEXITY_BAD_MIDPOINT: &str = include_str!(
    "../../../artifacts/examples/math/convexity-rational-v0/smt2/bad-midpoint-convexity-farkas-conflict.smt2"
);
const CONVEXITY_BAD_AFFINE_THRESHOLD: &str = include_str!(
    "../../../artifacts/examples/math/convexity-rational-v0/smt2/bad-affine-threshold-farkas-conflict.smt2"
);
const DESCRIPTIVE_STATS_BAD_VARIANCE: &str = include_str!(
    "../../../artifacts/examples/math/descriptive-statistics-v0/smt2/bad-variance-farkas-conflict.smt2"
);
const FINITE_COVARIANCE_MATRIX_BAD_ENTRY: &str = include_str!(
    "../../../artifacts/examples/math/finite-covariance-matrix-v0/smt2/bad-covariance-entry-farkas-conflict.smt2"
);
const FINITE_PRINCIPAL_COMPONENTS_BAD_EIGENVALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-principal-components-v0/smt2/bad-principal-eigenvalue-farkas-conflict.smt2"
);
const FINITE_K_MEANS_CLUSTERING_BAD_CENTROID: &str = include_str!(
    "../../../artifacts/examples/math/finite-k-means-clustering-v0/smt2/bad-centroid-x-farkas-conflict.smt2"
);
const FINITE_NAIVE_BAYES_CLASSIFIER_BAD_POSTERIOR: &str = include_str!(
    "../../../artifacts/examples/math/finite-naive-bayes-classifier-v0/smt2/bad-posterior-farkas-conflict.smt2"
);
const FINITE_CONFUSION_MATRIX_BAD_PRECISION: &str = include_str!(
    "../../../artifacts/examples/math/finite-confusion-matrix-v0/smt2/bad-precision-farkas-conflict.smt2"
);
const FINITE_ROC_AUC_BAD_AUC: &str = include_str!(
    "../../../artifacts/examples/math/finite-roc-auc-v0/smt2/bad-auc-farkas-conflict.smt2"
);
const LEAST_SQUARES_BAD_RSS_IMPROVEMENT: &str = include_str!(
    "../../../artifacts/examples/math/least-squares-regression-v0/smt2/bad-rss-improvement-farkas-conflict.smt2"
);
const LEAST_SQUARES_BAD_COEFFICIENTS: &str = include_str!(
    "../../../artifacts/examples/math/least-squares-regression-v0/smt2/bad-coefficients-farkas-conflict.smt2"
);
const FINITE_RIDGE_REGRESSION_BAD_BETA0: &str = include_str!(
    "../../../artifacts/examples/math/finite-ridge-regression-v0/smt2/bad-ridge-beta0-farkas-conflict.smt2"
);
const FINITE_LINEAR_DISCRIMINANT_BAD_DIRECTION: &str = include_str!(
    "../../../artifacts/examples/math/finite-linear-discriminant-v0/smt2/bad-fisher-direction-farkas-conflict.smt2"
);
const EXACT_STATS_BAD_FISHER_LEFT_TAIL: &str = include_str!(
    "../../../artifacts/examples/math/exact-statistical-tests-v0/smt2/bad-fisher-left-tail-farkas-conflict.smt2"
);
const EXACT_STATS_BAD_FISHER_TWO_SIDED: &str = include_str!(
    "../../../artifacts/examples/math/exact-statistical-tests-v0/smt2/bad-fisher-two-sided-farkas-conflict.smt2"
);
const EXACT_STATS_BAD_MULTINOMIAL_PVALUE: &str = include_str!(
    "../../../artifacts/examples/math/exact-statistical-tests-v0/smt2/bad-multinomial-pvalue-farkas-conflict.smt2"
);
const CALCULUS_RIEMANN_FALSE_INTEGRAL: &str = include_str!(
    "../../../artifacts/examples/math/calculus-riemann-sum-v0/smt2/false-integral-farkas-conflict.smt2"
);
const FINITE_SIMPSON_RULE_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-simpson-rule-v0/smt2/bad-simpson-value-farkas-conflict.smt2"
);
const FINITE_ROMBERG_EXTRAPOLATION_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-romberg-extrapolation-v0/smt2/bad-romberg-value-farkas-conflict.smt2"
);
const FINITE_DIVIDED_DIFFERENCES_BAD_INTERPOLATION_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-divided-differences-v0/smt2/bad-interpolation-value-farkas-conflict.smt2"
);
const FINITE_BARYCENTRIC_INTERPOLATION_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-barycentric-interpolation-v0/smt2/bad-barycentric-value-farkas-conflict.smt2"
);
const FINITE_DIFFERENCE_DERIVATIVES_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-difference-derivatives-v0/smt2/bad-finite-difference-value-farkas-conflict.smt2"
);
const FINITE_TAYLOR_POLYNOMIALS_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-taylor-polynomials-v0/smt2/bad-taylor-value-farkas-conflict.smt2"
);
const FINITE_CUBIC_HERMITE_INTERPOLATION_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-cubic-hermite-interpolation-v0/smt2/bad-hermite-value-farkas-conflict.smt2"
);
const FINITE_CUBIC_SPLINE_INTERPOLATION_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-cubic-spline-interpolation-v0/smt2/bad-spline-value-farkas-conflict.smt2"
);
const CALCULUS_ALGEBRAIC_FALSE_DERIVATIVE: &str = include_str!(
    "../../../artifacts/examples/math/calculus-algebraic-shadow-v0/smt2/false-derivative-farkas-conflict.smt2"
);
const POLYNOMIAL_FACTORIZATION_IRREDUCIBLE_QUADRATIC_DISCRIMINANT: &str = include_str!(
    "../../../artifacts/examples/math/polynomial-factorization-rational-v0/smt2/irreducible-quadratic-discriminant-farkas-conflict.smt2"
);
const REALS_RCF_NEGATIVE_DISCRIMINANT: &str = include_str!(
    "../../../artifacts/examples/math/reals-rcf-shadow-v0/smt2/negative-discriminant-farkas-conflict.smt2"
);
const METRIC_CONTINUITY_BAD_OPEN_BALL_PREIMAGE: &str = include_str!(
    "../../../artifacts/examples/math/metric-continuity-v0/smt2/bad-open-ball-preimage-farkas-conflict.smt2"
);
const COMPLEX_ALGEBRAIC_BAD_NORM_SQUARED: &str = include_str!(
    "../../../artifacts/examples/math/complex-algebraic-v0/smt2/bad-norm-squared-farkas-conflict.smt2"
);
const COMPLEX_ALGEBRAIC_BAD_PRODUCT_REAL_PART: &str = include_str!(
    "../../../artifacts/examples/math/complex-algebraic-v0/smt2/bad-product-real-part-farkas-conflict.smt2"
);
const COMPLEX_PLANE_BAD_UNIT_SQUARE_REAL_PART: &str = include_str!(
    "../../../artifacts/examples/math/complex-plane-transforms-v0/smt2/bad-unit-square-real-part-farkas-conflict.smt2"
);
const COMPLEX_PLANE_BAD_CONJUGATION_PRODUCT_IMAGINARY: &str = include_str!(
    "../../../artifacts/examples/math/complex-plane-transforms-v0/smt2/bad-conjugation-product-imaginary-farkas-conflict.smt2"
);
const FINITE_CAUCHY_RIEMANN_BAD_DERIVATIVE_REAL_PART: &str = include_str!(
    "../../../artifacts/examples/math/finite-cauchy-riemann-shadow-v0/smt2/bad-derivative-real-part-farkas-conflict.smt2"
);
const SEQUENCE_LIMIT_BOUNDED_CAUCHY: &str = include_str!(
    "../../../artifacts/examples/math/sequence-limit-shadow-v0/smt2/bounded-cauchy-tail-farkas-conflict.smt2"
);
const SEQUENCE_LIMIT_BAD_RECIPROCAL_TAIL_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/sequence-limit-shadow-v0/smt2/bad-reciprocal-tail-bound-farkas-conflict.smt2"
);
const RANDOM_MATRIX_BAD_EXPECTED_RANK: &str = include_str!(
    "../../../artifacts/examples/math/random-matrix-finite-v0/smt2/bad-expected-rank-farkas-conflict.smt2"
);
const RANDOM_MATRIX_BAD_TRACE_MOMENT: &str = include_str!(
    "../../../artifacts/examples/math/random-matrix-finite-v0/smt2/bad-trace-moment-farkas-conflict.smt2"
);
const BOUNDED_MONOTONE_SEQUENCE_BAD_UPPER_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/bounded-monotone-sequence-v0/smt2/bad-upper-bound-farkas-conflict.smt2"
);
const BOUNDED_MONOTONE_SEQUENCE_BAD_TAIL_GAP: &str = include_str!(
    "../../../artifacts/examples/math/bounded-monotone-sequence-v0/smt2/bad-tail-gap-farkas-conflict.smt2"
);
const FINITE_RECURRENCE_PREFIX_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-recurrence-prefix-v0/smt2/bad-fibonacci-value-farkas-conflict.smt2"
);
const FINITE_RECURRENCE_PREFIX_BAD_AFFINE_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-recurrence-prefix-v0/smt2/bad-affine-step-farkas-conflict.smt2"
);
const FINITE_ROOT_FINDING_BAD_NEWTON_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-root-finding-v0/smt2/bad-newton-step-farkas-conflict.smt2"
);
const FINITE_ROOT_FINDING_BAD_BISECTION_WIDTH: &str = include_str!(
    "../../../artifacts/examples/math/finite-root-finding-v0/smt2/bad-bisection-width-farkas-conflict.smt2"
);
const FINITE_SECANT_METHOD_BAD_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-secant-method-v0/smt2/bad-secant-step-farkas-conflict.smt2"
);
const FINITE_AITKEN_ACCELERATION_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-aitken-acceleration-v0/smt2/bad-aitken-value-farkas-conflict.smt2"
);
const FINITE_STEFFENSEN_METHOD_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-steffensen-method-v0/smt2/bad-steffensen-value-farkas-conflict.smt2"
);
const FINITE_FLOW_CUT_BAD_FLOW_VALUE_CUT_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/finite-flow-cut-v0/smt2/bad-flow-value-cut-bound-farkas-conflict.smt2"
);
const FINITE_SHORTEST_PATH_BAD_SHORTER_DISTANCE_POTENTIAL_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/finite-shortest-path-v0/smt2/bad-shorter-distance-potential-bound-farkas-conflict.smt2"
);
const FINITE_SEPARATION_BAD_SEPARATOR: &str = include_str!(
    "../../../artifacts/examples/math/finite-separation-v0/smt2/bad-separator-farkas-conflict.smt2"
);
const FINITE_SEPARATION_BAD_CONVEX_COMBINATION: &str = include_str!(
    "../../../artifacts/examples/math/finite-separation-v0/smt2/bad-convex-combination-point-farkas-conflict.smt2"
);
const FINITE_KKT_BAD_STATIONARITY: &str = include_str!(
    "../../../artifacts/examples/math/finite-kkt-v0/smt2/bad-stationarity-farkas-conflict.smt2"
);
const FINITE_KKT_BAD_COMPLEMENTARITY: &str = include_str!(
    "../../../artifacts/examples/math/finite-kkt-v0/smt2/bad-complementarity-farkas-conflict.smt2"
);
const FINITE_ACTIVE_SET_QP_BAD_FREE_GRADIENT: &str = include_str!(
    "../../../artifacts/examples/math/finite-active-set-qp-v0/smt2/bad-free-gradient-farkas-conflict.smt2"
);
const FINITE_ACTIVE_SET_QP_BAD_INACTIVE_SLACK: &str = include_str!(
    "../../../artifacts/examples/math/finite-active-set-qp-v0/smt2/bad-inactive-slack-farkas-conflict.smt2"
);
const FINITE_ACTIVE_SET_QP_BAD_DEGENERATE_MULTIPLIER: &str = include_str!(
    "../../../artifacts/examples/math/finite-active-set-qp-v0/smt2/bad-degenerate-multiplier-farkas-conflict.smt2"
);
const FINITE_SDP_BAD_OBJECTIVE: &str = include_str!(
    "../../../artifacts/examples/math/finite-sdp-v0/smt2/bad-objective-farkas-conflict.smt2"
);
const FINITE_SDP_BAD_DUALITY_GAP: &str = include_str!(
    "../../../artifacts/examples/math/finite-sdp-v0/smt2/bad-duality-gap-farkas-conflict.smt2"
);
const FINITE_SDP_BAD_SLACK_ENTRY: &str = include_str!(
    "../../../artifacts/examples/math/finite-sdp-v0/smt2/bad-slack-entry-farkas-conflict.smt2"
);
const FINITE_GRADIENT_DESCENT_BAD_DECREASE: &str = include_str!(
    "../../../artifacts/examples/math/finite-gradient-descent-v0/smt2/bad-decrease-farkas-conflict.smt2"
);
const FINITE_GRADIENT_DESCENT_BAD_STEP_COORDINATE: &str = include_str!(
    "../../../artifacts/examples/math/finite-gradient-descent-v0/smt2/bad-step-coordinate-farkas-conflict.smt2"
);
const FINITE_GRADIENT_DESCENT_BAD_DESCENT_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/finite-gradient-descent-v0/smt2/bad-descent-bound-farkas-conflict.smt2"
);
const FINITE_LINE_SEARCH_BAD_ARMIJO: &str = include_str!(
    "../../../artifacts/examples/math/finite-line-search-v0/smt2/bad-armijo-farkas-conflict.smt2"
);
const FINITE_LINE_SEARCH_BAD_DESCENT_DIRECTION: &str = include_str!(
    "../../../artifacts/examples/math/finite-line-search-v0/smt2/bad-descent-direction-farkas-conflict.smt2"
);
const FINITE_LINE_SEARCH_BAD_ACCEPTED_CANDIDATE: &str = include_str!(
    "../../../artifacts/examples/math/finite-line-search-v0/smt2/bad-accepted-candidate-farkas-conflict.smt2"
);
const FINITE_WOLFE_LINE_SEARCH_BAD_MINIMIZER: &str = include_str!(
    "../../../artifacts/examples/math/finite-wolfe-line-search-v0/smt2/bad-line-minimizer-farkas-conflict.smt2"
);
const FINITE_WOLFE_LINE_SEARCH_BAD_SUFFICIENT_DECREASE: &str = include_str!(
    "../../../artifacts/examples/math/finite-wolfe-line-search-v0/smt2/bad-wolfe-sufficient-decrease-farkas-conflict.smt2"
);
const FINITE_WOLFE_LINE_SEARCH_BAD_CURVATURE: &str = include_str!(
    "../../../artifacts/examples/math/finite-wolfe-line-search-v0/smt2/bad-wolfe-curvature-farkas-conflict.smt2"
);
const FINITE_PROJECTED_GRADIENT_BAD_PROJECTION: &str = include_str!(
    "../../../artifacts/examples/math/finite-projected-gradient-v0/smt2/bad-projection-farkas-conflict.smt2"
);
const FINITE_PROJECTED_GRADIENT_BAD_DECREASE: &str = include_str!(
    "../../../artifacts/examples/math/finite-projected-gradient-v0/smt2/bad-projected-decrease-farkas-conflict.smt2"
);
const INNER_PRODUCT_BAD_PROJECTION_ORTHOGONALITY: &str = include_str!(
    "../../../artifacts/examples/math/inner-product-spaces-rational-v0/smt2/bad-projection-orthogonality-farkas-conflict.smt2"
);
const FINITE_PROXIMAL_GRADIENT_BAD_PROXIMAL_POINT: &str = include_str!(
    "../../../artifacts/examples/math/finite-proximal-gradient-v0/smt2/bad-proximal-point-farkas-conflict.smt2"
);
const FINITE_PROXIMAL_GRADIENT_BAD_COMPOSITE_DECREASE: &str = include_str!(
    "../../../artifacts/examples/math/finite-proximal-gradient-v0/smt2/bad-composite-decrease-farkas-conflict.smt2"
);
const FINITE_PROXIMAL_GRADIENT_BAD_BOX_PROXIMAL_POINT: &str = include_str!(
    "../../../artifacts/examples/math/finite-proximal-gradient-v0/smt2/bad-box-proximal-point-farkas-conflict.smt2"
);
const MULTIVARIABLE_CALCULUS_BAD_GRADIENT: &str = include_str!(
    "../../../artifacts/examples/math/multivariable-calculus-rational-v0/smt2/bad-gradient-farkas-conflict.smt2"
);
const FINITE_NEWTON_STEP_BAD_COORDINATE: &str = include_str!(
    "../../../artifacts/examples/math/finite-newton-step-v0/smt2/bad-newton-coordinate-farkas-conflict.smt2"
);
const FINITE_CONDITION_NUMBER_BAD_CONDITION: &str = include_str!(
    "../../../artifacts/examples/math/finite-condition-number-v0/smt2/bad-condition-number-farkas-conflict.smt2"
);
const FINITE_ROUNDING_SHADOW_BAD_ROUNDED_DELTA: &str = include_str!(
    "../../../artifacts/examples/math/finite-rounding-shadow-v0/smt2/bad-rounded-delta-farkas-conflict.smt2"
);
const FINITE_INTERVAL_ARITHMETIC_BAD_PRODUCT_UPPER: &str = include_str!(
    "../../../artifacts/examples/math/finite-interval-arithmetic-shadow-v0/smt2/bad-product-upper-farkas-conflict.smt2"
);
const FINITE_SCHUR_COMPLEMENT_BAD_VALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-schur-complement-v0/smt2/bad-schur-complement-farkas-conflict.smt2"
);
const FINITE_SINGULAR_VALUE_SHADOW_BAD_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/finite-singular-value-shadow-v0/smt2/bad-singular-value-bound-farkas-conflict.smt2"
);
const FINITE_JORDAN_CHAIN_BAD_COMPONENT: &str = include_str!(
    "../../../artifacts/examples/math/finite-jordan-chain-v0/smt2/bad-jordan-chain-farkas-conflict.smt2"
);
const FINITE_MEASURE_BAD_COMPLEMENT: &str = include_str!(
    "../../../artifacts/examples/math/finite-measure-v0/smt2/bad-complement-measure-farkas-conflict.smt2"
);
const FINITE_MEASURE_MONOTONICITY_BAD_SUBSET_MEASURE: &str = include_str!(
    "../../../artifacts/examples/math/finite-measure-monotonicity-v0/smt2/bad-subset-measure-farkas-conflict.smt2"
);
const FINITE_MEASURE_MONOTONICITY_BAD_UNION_SUBADDITIVITY: &str = include_str!(
    "../../../artifacts/examples/math/finite-measure-monotonicity-v0/smt2/bad-union-subadditivity-farkas-conflict.smt2"
);
const COORDINATE_GEOMETRY_BAD_DISTANCE_SQUARED: &str = include_str!(
    "../../../artifacts/examples/math/coordinate-geometry-v0/smt2/bad-distance-squared-farkas-conflict.smt2"
);
const COORDINATE_GEOMETRY_BAD_MIDPOINT_X: &str = include_str!(
    "../../../artifacts/examples/math/coordinate-geometry-v0/smt2/bad-midpoint-x-farkas-conflict.smt2"
);
const FINITE_CIRCLE_GEOMETRY_BAD_RADIUS: &str = include_str!(
    "../../../artifacts/examples/math/finite-circle-geometry-v0/smt2/bad-radius-farkas-conflict.smt2"
);
const FINITE_CIRCLE_GEOMETRY_BAD_LINE_INTERSECTION: &str = include_str!(
    "../../../artifacts/examples/math/finite-circle-geometry-v0/smt2/bad-line-intersection-farkas-conflict.smt2"
);
const FINITE_INVERSION_GEOMETRY_BAD_INVERSE_X: &str = include_str!(
    "../../../artifacts/examples/math/finite-inversion-geometry-v0/smt2/bad-inversion-x-farkas-conflict.smt2"
);
const FINITE_INVERSION_GEOMETRY_BAD_INVERSE_DISTANCE_PRODUCT: &str = include_str!(
    "../../../artifacts/examples/math/finite-inversion-geometry-v0/smt2/bad-inverse-distance-product-farkas-conflict.smt2"
);
const FINITE_CYCLIC_GEOMETRY_BAD_DIAGONAL_INTERSECTION: &str = include_str!(
    "../../../artifacts/examples/math/finite-cyclic-geometry-v0/smt2/bad-diagonal-intersection-farkas-conflict.smt2"
);
const FINITE_CYCLIC_GEOMETRY_BAD_OPPOSITE_ANGLE: &str = include_str!(
    "../../../artifacts/examples/math/finite-cyclic-geometry-v0/smt2/bad-opposite-angle-farkas-conflict.smt2"
);
const FINITE_CYCLIC_GEOMETRY_BAD_PTOLEMY: &str = include_str!(
    "../../../artifacts/examples/math/finite-cyclic-geometry-v0/smt2/bad-ptolemy-farkas-conflict.smt2"
);
const INCIDENCE_GEOMETRY_BAD_POINT_ON_LINE: &str = include_str!(
    "../../../artifacts/examples/math/incidence-geometry-v0/smt2/bad-incidence-farkas-conflict.smt2"
);
const INCIDENCE_GEOMETRY_BAD_INTERSECTION_X: &str = include_str!(
    "../../../artifacts/examples/math/incidence-geometry-v0/smt2/bad-intersection-x-farkas-conflict.smt2"
);
const RIGID_CONFIGURATION_BAD_DISTANCE_TABLE: &str = include_str!(
    "../../../artifacts/examples/math/rigid-configuration-geometry-v0/smt2/bad-rigid-distance-table-farkas-conflict.smt2"
);
const RIGID_CONFIGURATION_BAD_TRANSLATION_IMAGE_X: &str = include_str!(
    "../../../artifacts/examples/math/rigid-configuration-geometry-v0/smt2/bad-translation-image-x-farkas-conflict.smt2"
);
const AFFINE_GEOMETRY_BAD_MIDPOINT_IMAGE_Y: &str = include_str!(
    "../../../artifacts/examples/math/affine-geometry-v0/smt2/bad-midpoint-image-y-farkas-conflict.smt2"
);
const AFFINE_GEOMETRY_BAD_COLLINEARITY_DETERMINANT: &str = include_str!(
    "../../../artifacts/examples/math/affine-geometry-v0/smt2/bad-collinearity-determinant-farkas-conflict.smt2"
);
const ORIENTATION_AREA_BAD_AFFINE_AREA_SCALING: &str = include_str!(
    "../../../artifacts/examples/math/orientation-area-geometry-v0/smt2/bad-affine-area-scaling-farkas-conflict.smt2"
);
const FINITE_OPERATOR_BAD_OPERATOR_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/finite-operator-v0/smt2/bad-operator-bound-farkas-conflict.smt2"
);
const FINITE_OPERATOR_BAD_L1_SUM_NORM: &str = include_str!(
    "../../../artifacts/examples/math/finite-operator-v0/smt2/bad-l1-sum-norm-farkas-conflict.smt2"
);
const FINITE_OPERATOR_BAD_CHEBYSHEV_T3: &str = include_str!(
    "../../../artifacts/examples/math/finite-operator-v0/smt2/bad-chebyshev-t3-farkas-conflict.smt2"
);
const MATRIX_INVARIANTS_BAD_TRACE: &str = include_str!(
    "../../../artifacts/examples/math/matrix-invariants-v0/smt2/bad-trace-invariant-farkas-conflict.smt2"
);
const MATRIX_INVARIANTS_BAD_CHARACTERISTIC_POLYNOMIAL: &str = include_str!(
    "../../../artifacts/examples/math/matrix-invariants-v0/smt2/bad-characteristic-polynomial-farkas-conflict.smt2"
);
const SPECTRAL_BAD_RAYLEIGH_QUOTIENT: &str = include_str!(
    "../../../artifacts/examples/math/spectral-linear-algebra-v0/smt2/bad-rayleigh-quotient-farkas-conflict.smt2"
);
const SPECTRAL_BAD_EIGENPAIR: &str = include_str!(
    "../../../artifacts/examples/math/spectral-linear-algebra-v0/smt2/bad-eigenpair-farkas-conflict.smt2"
);
const FINITE_ORTHOGONAL_DIAGONALIZATION_BAD_EIGENVALUE: &str = include_str!(
    "../../../artifacts/examples/math/finite-orthogonal-diagonalization-v0/smt2/bad-spectral-eigenvalue-farkas-conflict.smt2"
);
const FINITE_REAL_SCHUR_DECOMPOSITION_BAD_SUPERDIAGONAL: &str = include_str!(
    "../../../artifacts/examples/math/finite-real-schur-decomposition-v0/smt2/bad-schur-superdiagonal-farkas-conflict.smt2"
);
const FINITE_POLAR_DECOMPOSITION_BAD_DIAGONAL: &str = include_str!(
    "../../../artifacts/examples/math/finite-polar-decomposition-v0/smt2/bad-polar-diagonal-farkas-conflict.smt2"
);
const FINITE_QR_ITERATION_STEP_BAD_ENTRY: &str = include_str!(
    "../../../artifacts/examples/math/finite-qr-iteration-step-v0/smt2/bad-qr-step-entry-farkas-conflict.smt2"
);
const FINITE_SHIFTED_QR_STEP_BAD_ENTRY: &str = include_str!(
    "../../../artifacts/examples/math/finite-shifted-qr-step-v0/smt2/bad-shifted-qr-entry-farkas-conflict.smt2"
);
const FINITE_POWER_ITERATION_BAD_COORDINATE: &str = include_str!(
    "../../../artifacts/examples/math/finite-power-iteration-v0/smt2/bad-power-iterate-coordinate-farkas-conflict.smt2"
);
const FINITE_CONJUGATE_GRADIENT_BAD_ALPHA0: &str = include_str!(
    "../../../artifacts/examples/math/finite-conjugate-gradient-v0/smt2/bad-cg-alpha0-farkas-conflict.smt2"
);
const FINITE_GMRES_RESIDUAL_SHADOW_BAD_ALPHA: &str = include_str!(
    "../../../artifacts/examples/math/finite-gmres-residual-shadow-v0/smt2/bad-gmres-alpha-farkas-conflict.smt2"
);
const FINITE_ARNOLDI_ITERATION_BAD_H21: &str = include_str!(
    "../../../artifacts/examples/math/finite-arnoldi-iteration-v0/smt2/bad-arnoldi-h21-farkas-conflict.smt2"
);
const FINITE_LANCZOS_ITERATION_BAD_BETA1: &str = include_str!(
    "../../../artifacts/examples/math/finite-lanczos-iteration-v0/smt2/bad-lanczos-beta1-farkas-conflict.smt2"
);
const FINITE_WALSH_HADAMARD_BAD_TRANSFORM_COEFFICIENT: &str = include_str!(
    "../../../artifacts/examples/math/finite-walsh-hadamard-transform-v0/smt2/bad-transform-coefficient-farkas-conflict.smt2"
);
const FINITE_CHEBYSHEV_BAD_INTERPOLATION_SAMPLE: &str = include_str!(
    "../../../artifacts/examples/math/finite-chebyshev-systems-v0/smt2/bad-interpolation-sample-farkas-conflict.smt2"
);
const FINITE_CHEBYSHEV_BAD_ALTERNATING_RESIDUAL: &str = include_str!(
    "../../../artifacts/examples/math/finite-chebyshev-systems-v0/smt2/bad-alternating-residual-farkas-conflict.smt2"
);
const FINITE_CONCENTRATION_BAD_TAIL_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/finite-concentration-v0/smt2/bad-concentration-bound-farkas-conflict.smt2"
);
const FINITE_CONCENTRATION_BAD_UNION_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/finite-concentration-v0/smt2/bad-union-bound-farkas-conflict.smt2"
);
const BOUNDED_DYNAMICS_BAD_INVARIANT_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/bounded-dynamics-v0/smt2/bad-invariant-bound-farkas-conflict.smt2"
);
const BOUNDED_DYNAMICS_BAD_TRANSITION_STEP: &str = include_str!(
    "../../../artifacts/examples/math/bounded-dynamics-v0/smt2/bad-transition-step-farkas-conflict.smt2"
);
const BOUNDED_DYNAMICS_BAD_THRESHOLD_STEP: &str = include_str!(
    "../../../artifacts/examples/math/bounded-dynamics-v0/smt2/bad-threshold-step-farkas-conflict.smt2"
);
const FINITE_EULER_BAD_MAX_ERROR_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/finite-euler-method-v0/smt2/bad-max-error-bound-farkas-conflict.smt2"
);
const FINITE_EULER_BAD_TERMINAL_ERROR: &str = include_str!(
    "../../../artifacts/examples/math/finite-euler-method-v0/smt2/bad-terminal-error-farkas-conflict.smt2"
);
const FINITE_RUNGE_KUTTA_MIDPOINT_BAD_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-runge-kutta-midpoint-v0/smt2/bad-rk-midpoint-step-farkas-conflict.smt2"
);
const FINITE_HEUN_BAD_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-heun-method-v0/smt2/bad-heun-step-farkas-conflict.smt2"
);
const FINITE_BACKWARD_EULER_BAD_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-backward-euler-method-v0/smt2/bad-backward-euler-step-farkas-conflict.smt2"
);
const FINITE_CRANK_NICOLSON_BAD_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-crank-nicolson-method-v0/smt2/bad-crank-nicolson-step-farkas-conflict.smt2"
);
const FINITE_ADAMS_BASHFORTH_BAD_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-adams-bashforth-method-v0/smt2/bad-adams-bashforth-step-farkas-conflict.smt2"
);
const FINITE_BDF2_BAD_STEP: &str = include_str!(
    "../../../artifacts/examples/math/finite-bdf2-method-v0/smt2/bad-bdf2-step-farkas-conflict.smt2"
);
const NUMERICAL_LINEAR_ALGEBRA_BAD_JACOBI_ERROR_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/numerical-linear-algebra-v0/smt2/bad-jacobi-error-bound-farkas-conflict.smt2"
);
const NUMERICAL_LINEAR_ALGEBRA_BAD_RESIDUAL_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/numerical-linear-algebra-v0/smt2/bad-residual-bound-farkas-conflict.smt2"
);
const NUMERICAL_LINEAR_ALGEBRA_BAD_SOLUTION_BOX_UPPER_BOUND: &str = include_str!(
    "../../../artifacts/examples/math/numerical-linear-algebra-v0/smt2/bad-solution-box-upper-bound-farkas-conflict.smt2"
);
const FINITE_MARKOV_CHAIN_BAD_STOCHASTIC_ROW: &str = include_str!(
    "../../../artifacts/examples/math/finite-markov-chain-v0/smt2/bad-stochastic-row-farkas-conflict.smt2"
);
const FINITE_MARKOV_CHAIN_BAD_STATIONARY_DISTRIBUTION: &str = include_str!(
    "../../../artifacts/examples/math/finite-markov-chain-v0/smt2/bad-stationary-distribution-farkas-conflict.smt2"
);
const FINITE_PRODUCT_MEASURE_BAD_MARGINAL: &str = include_str!(
    "../../../artifacts/examples/math/finite-product-measure-v0/smt2/bad-product-marginal-farkas-conflict.smt2"
);
const FINITE_RANDOM_VARIABLES_BAD_EXPECTATION_THROUGH_PUSHFORWARD: &str = include_str!(
    "../../../artifacts/examples/math/finite-random-variables-v0/smt2/bad-expectation-through-pushforward-farkas-conflict.smt2"
);
const FINITE_CONDITIONAL_EXPECTATION_BAD_TOWER_PROPERTY: &str = include_str!(
    "../../../artifacts/examples/math/finite-conditional-expectation-v0/smt2/bad-tower-property-farkas-conflict.smt2"
);
const FINITE_CONDITIONAL_EXPECTATION_BAD_TOTAL_EXPECTATION: &str = include_str!(
    "../../../artifacts/examples/math/finite-conditional-expectation-v0/smt2/bad-total-expectation-farkas-conflict.smt2"
);
const FINITE_CONDITIONAL_EXPECTATION_BAD_VARIANCE_DECOMPOSITION: &str = include_str!(
    "../../../artifacts/examples/math/finite-conditional-expectation-v0/smt2/bad-variance-decomposition-farkas-conflict.smt2"
);
const FINITE_MARTINGALES_BAD_STOPPED_EXPECTATION: &str = include_str!(
    "../../../artifacts/examples/math/finite-martingales-v0/smt2/bad-stopped-expectation-farkas-conflict.smt2"
);
const FINITE_STOCHASTIC_KERNEL_BAD_ROW: &str = include_str!(
    "../../../artifacts/examples/math/finite-stochastic-kernels-v0/smt2/bad-kernel-row-farkas-conflict.smt2"
);
const FINITE_STOCHASTIC_KERNEL_BAD_COMPOSITION: &str = include_str!(
    "../../../artifacts/examples/math/finite-stochastic-kernels-v0/smt2/bad-composition-entry-farkas-conflict.smt2"
);
const FINITE_HITTING_TIMES_BAD_SURVIVAL_MASS: &str = include_str!(
    "../../../artifacts/examples/math/finite-hitting-times-v0/smt2/bad-survival-mass-farkas-conflict.smt2"
);
const FINITE_HITTING_TIMES_BAD_EXPECTED_TIME: &str = include_str!(
    "../../../artifacts/examples/math/finite-hitting-times-v0/smt2/bad-expected-time-farkas-conflict.smt2"
);
const FINITE_PROBABILITY_BAD_CONDITIONAL_PROBABILITY: &str = include_str!(
    "../../../artifacts/examples/math/finite-probability-v0/smt2/bad-conditional-probability-farkas-conflict.smt2"
);
const FINITE_PROBABILITY_BAD_INDEPENDENCE: &str = include_str!(
    "../../../artifacts/examples/math/finite-probability-v0/smt2/bad-independence-farkas-conflict.smt2"
);
const FINITE_PROBABILITY_BAD_TOTAL_VARIATION: &str = include_str!(
    "../../../artifacts/examples/math/finite-probability-v0/smt2/bad-total-variation-farkas-conflict.smt2"
);
const RATIONALS_TRICHOTOMY_NONLESS: &str = include_str!(
    "../../../artifacts/examples/math/rationals-lra-v0/smt2/trichotomy-nonless-farkas-conflict.smt2"
);
const RATIONALS_TRICHOTOMY_EQUALITY: &str = include_str!(
    "../../../artifacts/examples/math/rationals-lra-v0/smt2/trichotomy-equality-farkas-conflict.smt2"
);
const RATIONALS_TRICHOTOMY_GREATER: &str = include_str!(
    "../../../artifacts/examples/math/rationals-lra-v0/smt2/trichotomy-greater-farkas-conflict.smt2"
);
const RATIONALS_ORDER_TRANSITIVITY: &str = include_str!(
    "../../../artifacts/examples/math/rationals-lra-v0/smt2/order-transitivity-farkas-conflict.smt2"
);

fn real(arena: &mut TermArena, name: &str) -> TermId {
    arena.real_var(name).unwrap()
}

fn eq_ratio(arena: &mut TermArena, term: TermId, numerator: i128, denominator: i128) -> TermId {
    let value = arena.real_ratio(numerator, denominator);
    arena.eq(term, value).unwrap()
}

fn assert_farkas_checked(label: &str, arena: &TermArena, assertions: &[TermId]) {
    let report = produce_lra_evidence(arena, assertions).unwrap();
    assert!(
        matches!(&report.evidence, Evidence::UnsatFarkas(_)),
        "{label}: expected Farkas-certified unsat, got {:?}",
        report.evidence
    );
    assert!(report.evidence.is_certified(), "{label}: not certified");
    assert!(
        report.evidence.check(arena, assertions).unwrap(),
        "{label}: evidence failed independent recheck"
    );
    assert_eq!(
        report.provenance.backend, "lra-fourier-motzkin-farkas",
        "{label}: unexpected backend"
    );
    assert!(
        report
            .trusted_steps
            .iter()
            .any(|step| step.id == TrustId::Farkas && step.certified),
        "{label}: missing certified Farkas trust step"
    );
}

fn assert_resource_farkas(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: resource SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: resource obligation must be unsat"
    );
    assert_farkas_checked(label, &script.arena, &assertions);
}

fn assert_resource_farkas_rejects_tampered_certificate(label: &str, smt2: &str) {
    let mut script = parse_script(smt2)
        .unwrap_or_else(|error| panic!("{label}: resource SMT-LIB artifact parses: {error}"));
    let assertions = script.assertions.clone();

    assert_eq!(
        check_auto(&mut script.arena, &assertions, &SolverConfig::default()).unwrap(),
        CheckResult::Unsat,
        "{label}: resource obligation must be unsat before tampering"
    );

    let report = produce_lra_evidence(&script.arena, &assertions).unwrap();
    let Evidence::UnsatFarkas(mut certificate) = report.evidence else {
        panic!("{label}: expected Farkas-certified unsat");
    };
    assert!(
        certificate.verify(),
        "{label}: genuine certificate must verify before tampering"
    );
    assert!(
        Evidence::UnsatFarkas(certificate.clone())
            .check(&script.arena, &assertions)
            .unwrap(),
        "{label}: genuine evidence must independently check before tampering"
    );

    certificate.multipliers[0] = Rational::zero();
    let bogus = Evidence::UnsatFarkas(certificate);
    assert!(
        !bogus.check(&script.arena, &assertions).unwrap(),
        "{label}: tampering a Farkas multiplier must make evidence reject"
    );
}

#[test]
fn qf_lra_resource_route_rejects_tampered_farkas_certificate() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let zero = arena.real_ratio(0, 1);
    let one = arena.real_ratio(1, 1);
    let x_ge_one = arena.real_ge(x, one).unwrap();
    let x_le_zero = arena.real_le(x, zero).unwrap();
    let assertions = [x_ge_one, x_le_zero];

    let report = produce_lra_evidence(&arena, &assertions).unwrap();
    let Evidence::UnsatFarkas(mut certificate) = report.evidence else {
        panic!("expected Farkas-certified unsat");
    };
    assert!(certificate.verify());

    certificate.multipliers[0] = Rational::zero();
    let bogus = Evidence::UnsatFarkas(certificate);
    assert!(
        !bogus.check(&arena, &assertions).unwrap(),
        "tampering a Farkas multiplier must make evidence reject"
    );
}

#[test]
fn rationals_trichotomy_fixed_unsat_branches_emit_checked_farkas() {
    let mut arena = TermArena::new();
    let left = real(&mut arena, "left");
    let right = real(&mut arena, "right");
    let left_is_quarter = eq_ratio(&mut arena, left, 1, 4);
    let right_is_three_quarters = eq_ratio(&mut arena, right, 3, 4);

    // `1/4 < 3/4`, so every non-less/equality/greater branch of a fixed
    // trichotomy violation closes as an exact-rational Farkas contradiction.
    let not_less = arena.real_ge(left, right).unwrap();
    assert_farkas_checked(
        "rationals-lra-v0 trichotomy non-less branch",
        &arena,
        &[left_is_quarter, right_is_three_quarters, not_less],
    );

    let equal = arena.eq(left, right).unwrap();
    assert_farkas_checked(
        "rationals-lra-v0 trichotomy equality branch",
        &arena,
        &[left_is_quarter, right_is_three_quarters, equal],
    );

    let greater = arena.real_gt(left, right).unwrap();
    assert_farkas_checked(
        "rationals-lra-v0 trichotomy greater-than branch",
        &arena,
        &[left_is_quarter, right_is_three_quarters, greater],
    );
}

#[test]
fn rationals_trichotomy_source_artifacts_emit_checked_farkas() {
    for (label, smt2) in [
        (
            "rationals-lra-v0 trichotomy non-less SMT-LIB artifact",
            RATIONALS_TRICHOTOMY_NONLESS,
        ),
        (
            "rationals-lra-v0 trichotomy equality SMT-LIB artifact",
            RATIONALS_TRICHOTOMY_EQUALITY,
        ),
        (
            "rationals-lra-v0 trichotomy greater SMT-LIB artifact",
            RATIONALS_TRICHOTOMY_GREATER,
        ),
    ] {
        assert_resource_farkas(label, smt2);
    }
}

#[test]
fn rationals_order_transitivity_fixed_unsat_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let a = real(&mut arena, "a");
    let b = real(&mut arena, "b");
    let c = real(&mut arena, "c");
    let a_is_one_fifth = eq_ratio(&mut arena, a, 1, 5);
    let b_is_two_fifths = eq_ratio(&mut arena, b, 2, 5);
    let c_is_three_fifths = eq_ratio(&mut arena, c, 3, 5);
    let a_lt_b = arena.real_lt(a, b).unwrap();
    let b_lt_c = arena.real_lt(b, c).unwrap();
    let not_a_lt_c = arena.real_ge(a, c).unwrap();

    assert_farkas_checked(
        "rationals-lra-v0 order-transitivity violation",
        &arena,
        &[
            a_is_one_fifth,
            b_is_two_fifths,
            c_is_three_fifths,
            a_lt_b,
            b_lt_c,
            not_a_lt_c,
        ],
    );
}

#[test]
fn rationals_order_transitivity_source_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "rationals-lra-v0 order-transitivity SMT-LIB artifact",
        RATIONALS_ORDER_TRANSITIVITY,
    );
}

#[test]
fn linear_algebra_singular_system_inconsistent_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");

    let x_plus_y = arena.real_add(x, y).unwrap();
    let first_row = eq_ratio(&mut arena, x_plus_y, 1, 1);

    let two_x = arena.real_add(x, x).unwrap();
    let two_y = arena.real_add(y, y).unwrap();
    let two_x_plus_two_y = arena.real_add(two_x, two_y).unwrap();
    let second_row = eq_ratio(&mut arena, two_x_plus_two_y, 3, 1);

    assert_farkas_checked(
        "linear-algebra-rational-v0 singular-system-inconsistent",
        &arena,
        &[first_row, second_row],
    );
}

#[test]
fn linear_algebra_singular_system_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "linear-algebra-rational-v0 singular-system-inconsistent SMT-LIB artifact",
        LINEAR_ALGEBRA_SINGULAR_SYSTEM,
    );
}

#[test]
fn linear_algebra_bad_lu_product_entry_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "linear-algebra-rational-v0 bad-lu-product-entry SMT-LIB artifact",
        LINEAR_ALGEBRA_BAD_LU_PRODUCT_ENTRY,
    );
}

#[test]
fn finite_lu_decomposition_bad_multiplier_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-lu-decomposition-v0 bad-lu-multiplier SMT-LIB artifact",
        FINITE_LU_DECOMPOSITION_BAD_MULTIPLIER,
    );
}

#[test]
fn finite_pivoted_lu_decomposition_bad_pivot_sign_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-pivoted-lu-decomposition-v0 bad-pivot-sign SMT-LIB artifact",
        FINITE_PIVOTED_LU_DECOMPOSITION_BAD_PIVOT_SIGN,
    );
}

#[test]
fn finite_ldlt_decomposition_bad_diagonal_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-ldlt-decomposition-v0 bad-ldlt-diagonal SMT-LIB artifact",
        FINITE_LDLT_DECOMPOSITION_BAD_DIAGONAL,
    );
}

#[test]
fn linear_algebra_bad_nullspace_component_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "linear-algebra-rational-v0 bad-nullspace-component SMT-LIB artifact",
        LINEAR_ALGEBRA_BAD_NULLSPACE_COMPONENT,
    );
}

#[test]
fn finite_gaussian_elimination_bad_rhs_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-gaussian-elimination-v0 bad-eliminated-rhs SMT-LIB artifact",
        FINITE_GAUSSIAN_ELIMINATION_BAD_RHS,
    );
}

#[test]
fn finite_qr_decomposition_bad_product_entry_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-qr-decomposition-v0 bad-qr-product-entry SMT-LIB artifact",
        FINITE_QR_DECOMPOSITION_BAD_PRODUCT_ENTRY,
    );
}

#[test]
fn finite_givens_rotation_bad_sine_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-givens-rotation-v0 bad-givens-sine SMT-LIB artifact",
        FINITE_GIVENS_ROTATION_BAD_SINE,
    );
}

#[test]
fn finite_gram_schmidt_bad_r12_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-gram-schmidt-v0 bad-r12 SMT-LIB artifact",
        FINITE_GRAM_SCHMIDT_BAD_R12,
    );
}

#[test]
fn finite_householder_reflection_bad_entry_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-householder-reflection-v0 bad-householder-entry SMT-LIB artifact",
        FINITE_HOUSEHOLDER_REFLECTION_BAD_ENTRY,
    );
}

#[test]
fn finite_cholesky_decomposition_bad_product_entry_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-cholesky-decomposition-v0 bad-cholesky-product-entry SMT-LIB artifact",
        FINITE_CHOLESKY_DECOMPOSITION_BAD_PRODUCT_ENTRY,
    );
}

#[test]
fn linear_optimization_objective_threshold_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let x = real(&mut arena, "x");
    let y = real(&mut arena, "y");
    let x_plus_y = arena.real_add(x, y).unwrap();
    let four = arena.real_ratio(4, 1);
    let five = arena.real_ratio(5, 1);
    let budget = arena.real_le(x_plus_y, four).unwrap();
    let threshold = arena.real_ge(x_plus_y, five).unwrap();

    assert_farkas_checked(
        "linear-optimization-v0 objective-threshold-farkas-infeasible",
        &arena,
        &[budget, threshold],
    );
}

#[test]
fn linear_optimization_objective_threshold_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "linear-optimization-v0 objective-threshold SMT-LIB artifact",
        LINEAR_OPTIMIZATION_OBJECTIVE_THRESHOLD,
    );
}

#[test]
fn linear_optimization_objective_threshold_rejects_tampered_farkas_certificate() {
    assert_resource_farkas_rejects_tampered_certificate(
        "linear-optimization-v0 objective-threshold SMT-LIB artifact",
        LINEAR_OPTIMIZATION_OBJECTIVE_THRESHOLD,
    );
}

#[test]
fn convexity_bad_midpoint_claim_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let left_value = real(&mut arena, "left_value");
    let midpoint_value = real(&mut arena, "midpoint_value");
    let right_value = real(&mut arena, "right_value");
    let left_is_zero = eq_ratio(&mut arena, left_value, 0, 1);
    let midpoint_is_one = eq_ratio(&mut arena, midpoint_value, 1, 1);
    let right_is_zero = eq_ratio(&mut arena, right_value, 0, 1);

    // Midpoint convexity at weight 1/2 is checked in division-free form:
    // 2*f(midpoint) <= f(left) + f(right). For the bad row this says 2 <= 0.
    let twice_midpoint = arena.real_add(midpoint_value, midpoint_value).unwrap();
    let endpoint_sum = arena.real_add(left_value, right_value).unwrap();
    let midpoint_convexity_claim = arena.real_le(twice_midpoint, endpoint_sum).unwrap();

    assert_farkas_checked(
        "convexity-rational-v0 bad-midpoint-convexity-rejected",
        &arena,
        &[
            left_is_zero,
            midpoint_is_one,
            right_is_zero,
            midpoint_convexity_claim,
        ],
    );
}

#[test]
fn convexity_bad_midpoint_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "convexity-rational-v0 bad-midpoint SMT-LIB artifact",
        CONVEXITY_BAD_MIDPOINT,
    );
}

#[test]
fn convexity_bad_affine_threshold_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "convexity-rational-v0 bad-affine-threshold SMT-LIB artifact",
        CONVEXITY_BAD_AFFINE_THRESHOLD,
    );
}

#[test]
fn descriptive_stats_bad_variance_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "descriptive-statistics-v0 bad-variance SMT-LIB artifact",
        DESCRIPTIVE_STATS_BAD_VARIANCE,
    );
}

#[test]
fn finite_covariance_matrix_bad_entry_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-covariance-matrix-v0 bad-covariance-entry SMT-LIB artifact",
        FINITE_COVARIANCE_MATRIX_BAD_ENTRY,
    );
}

#[test]
fn finite_principal_components_bad_eigenvalue_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-principal-components-v0 bad-principal-eigenvalue SMT-LIB artifact",
        FINITE_PRINCIPAL_COMPONENTS_BAD_EIGENVALUE,
    );
}

#[test]
fn finite_k_means_clustering_bad_centroid_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-k-means-clustering-v0 bad-centroid-x SMT-LIB artifact",
        FINITE_K_MEANS_CLUSTERING_BAD_CENTROID,
    );
}

#[test]
fn finite_naive_bayes_classifier_bad_posterior_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-naive-bayes-classifier-v0 bad-posterior SMT-LIB artifact",
        FINITE_NAIVE_BAYES_CLASSIFIER_BAD_POSTERIOR,
    );
}

#[test]
fn finite_confusion_matrix_bad_precision_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-confusion-matrix-v0 bad-precision SMT-LIB artifact",
        FINITE_CONFUSION_MATRIX_BAD_PRECISION,
    );
}

#[test]
fn finite_roc_auc_bad_auc_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-roc-auc-v0 bad-AUC SMT-LIB artifact",
        FINITE_ROC_AUC_BAD_AUC,
    );
}

#[test]
fn exact_stats_bad_fisher_left_tail_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "exact-statistical-tests-v0 bad-Fisher-left-tail SMT-LIB artifact",
        EXACT_STATS_BAD_FISHER_LEFT_TAIL,
    );
}

#[test]
fn exact_stats_bad_fisher_two_sided_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "exact-statistical-tests-v0 bad-Fisher-two-sided SMT-LIB artifact",
        EXACT_STATS_BAD_FISHER_TWO_SIDED,
    );
}

#[test]
fn exact_stats_bad_multinomial_pvalue_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "exact-statistical-tests-v0 bad-multinomial-pvalue SMT-LIB artifact",
        EXACT_STATS_BAD_MULTINOMIAL_PVALUE,
    );
}

#[test]
fn calculus_riemann_sum_false_integral_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "calculus-riemann-sum-v0 false-integral SMT-LIB artifact",
        CALCULUS_RIEMANN_FALSE_INTEGRAL,
    );
}

#[test]
fn finite_simpson_rule_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-simpson-rule-v0 bad-simpson-value SMT-LIB artifact",
        FINITE_SIMPSON_RULE_BAD_VALUE,
    );
}

#[test]
fn finite_romberg_extrapolation_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-romberg-extrapolation-v0 bad-romberg-value SMT-LIB artifact",
        FINITE_ROMBERG_EXTRAPOLATION_BAD_VALUE,
    );
}

#[test]
fn finite_divided_differences_bad_interpolation_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-divided-differences-v0 bad-interpolation-value SMT-LIB artifact",
        FINITE_DIVIDED_DIFFERENCES_BAD_INTERPOLATION_VALUE,
    );
}

#[test]
fn finite_barycentric_interpolation_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-barycentric-interpolation-v0 bad-barycentric-value SMT-LIB artifact",
        FINITE_BARYCENTRIC_INTERPOLATION_BAD_VALUE,
    );
}

#[test]
fn finite_difference_derivatives_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-difference-derivatives-v0 bad-finite-difference-value SMT-LIB artifact",
        FINITE_DIFFERENCE_DERIVATIVES_BAD_VALUE,
    );
}

#[test]
fn finite_taylor_polynomials_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-taylor-polynomials-v0 bad-taylor-value SMT-LIB artifact",
        FINITE_TAYLOR_POLYNOMIALS_BAD_VALUE,
    );
}

#[test]
fn finite_cubic_hermite_interpolation_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-cubic-hermite-interpolation-v0 bad-hermite-value SMT-LIB artifact",
        FINITE_CUBIC_HERMITE_INTERPOLATION_BAD_VALUE,
    );
}

#[test]
fn finite_cubic_spline_interpolation_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-cubic-spline-interpolation-v0 bad-spline-value SMT-LIB artifact",
        FINITE_CUBIC_SPLINE_INTERPOLATION_BAD_VALUE,
    );
}

#[test]
fn calculus_algebraic_false_derivative_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "calculus-algebraic-shadow-v0 false-derivative SMT-LIB artifact",
        CALCULUS_ALGEBRAIC_FALSE_DERIVATIVE,
    );
}

#[test]
fn polynomial_factorization_irreducible_quadratic_discriminant_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "polynomial-factorization-rational-v0 irreducible quadratic discriminant SMT-LIB artifact",
        POLYNOMIAL_FACTORIZATION_IRREDUCIBLE_QUADRATIC_DISCRIMINANT,
    );
}

#[test]
fn reals_rcf_shadow_negative_discriminant_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "reals-rcf-shadow-v0 negative-discriminant SMT-LIB artifact",
        REALS_RCF_NEGATIVE_DISCRIMINANT,
    );
}

#[test]
fn complex_plane_bad_unit_square_real_part_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "complex-plane-transforms-v0 bad-unit-square-real-part SMT-LIB artifact",
        COMPLEX_PLANE_BAD_UNIT_SQUARE_REAL_PART,
    );
}

#[test]
fn complex_plane_bad_conjugation_product_imaginary_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "complex-plane-transforms-v0 bad-conjugation-product-imaginary SMT-LIB artifact",
        COMPLEX_PLANE_BAD_CONJUGATION_PRODUCT_IMAGINARY,
    );
}

#[test]
fn complex_algebraic_bad_norm_squared_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "complex-algebraic-v0 bad-norm-squared SMT-LIB artifact",
        COMPLEX_ALGEBRAIC_BAD_NORM_SQUARED,
    );
}

#[test]
fn complex_algebraic_bad_product_real_part_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "complex-algebraic-v0 bad-product-real-part SMT-LIB artifact",
        COMPLEX_ALGEBRAIC_BAD_PRODUCT_REAL_PART,
    );
}

#[test]
fn finite_cauchy_riemann_bad_derivative_real_part_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-cauchy-riemann-shadow-v0 bad-derivative-real-part SMT-LIB artifact",
        FINITE_CAUCHY_RIEMANN_BAD_DERIVATIVE_REAL_PART,
    );
}

#[test]
fn sequence_limit_bounded_cauchy_tail_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "sequence-limit-shadow-v0 bounded-Cauchy-tail SMT-LIB artifact",
        SEQUENCE_LIMIT_BOUNDED_CAUCHY,
    );
}

#[test]
fn sequence_limit_bad_reciprocal_tail_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "sequence-limit-shadow-v0 bad-reciprocal-tail-bound SMT-LIB artifact",
        SEQUENCE_LIMIT_BAD_RECIPROCAL_TAIL_BOUND,
    );
}

#[test]
fn bounded_monotone_sequence_bad_upper_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "bounded-monotone-sequence-v0 bad-upper-bound SMT-LIB artifact",
        BOUNDED_MONOTONE_SEQUENCE_BAD_UPPER_BOUND,
    );
}

#[test]
fn bounded_monotone_sequence_bad_tail_gap_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "bounded-monotone-sequence-v0 bad-tail-gap SMT-LIB artifact",
        BOUNDED_MONOTONE_SEQUENCE_BAD_TAIL_GAP,
    );
}

#[test]
fn finite_recurrence_prefix_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-recurrence-prefix-v0 bad-Fibonacci-value SMT-LIB artifact",
        FINITE_RECURRENCE_PREFIX_BAD_VALUE,
    );
}

#[test]
fn finite_recurrence_prefix_bad_affine_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-recurrence-prefix-v0 bad-affine-step SMT-LIB artifact",
        FINITE_RECURRENCE_PREFIX_BAD_AFFINE_STEP,
    );
}

#[test]
fn finite_root_finding_bad_newton_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-root-finding-v0 bad-Newton-step SMT-LIB artifact",
        FINITE_ROOT_FINDING_BAD_NEWTON_STEP,
    );
}

#[test]
fn finite_root_finding_bad_bisection_width_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-root-finding-v0 bad-bisection-width SMT-LIB artifact",
        FINITE_ROOT_FINDING_BAD_BISECTION_WIDTH,
    );
}

#[test]
fn finite_secant_method_bad_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-secant-method-v0 bad-secant-step SMT-LIB artifact",
        FINITE_SECANT_METHOD_BAD_STEP,
    );
}

#[test]
fn finite_aitken_acceleration_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-aitken-acceleration-v0 bad-aitken-value SMT-LIB artifact",
        FINITE_AITKEN_ACCELERATION_BAD_VALUE,
    );
}

#[test]
fn finite_steffensen_method_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-steffensen-method-v0 bad-steffensen-value SMT-LIB artifact",
        FINITE_STEFFENSEN_METHOD_BAD_VALUE,
    );
}

#[test]
fn finite_flow_cut_bad_flow_value_cut_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-flow-cut-v0 qf-lra-bad-flow-value-cut-bound SMT-LIB artifact",
        FINITE_FLOW_CUT_BAD_FLOW_VALUE_CUT_BOUND,
    );
}

#[test]
fn finite_shortest_path_bad_shorter_distance_potential_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-shortest-path-v0 qf-lra-bad-shorter-distance-potential-bound SMT-LIB artifact",
        FINITE_SHORTEST_PATH_BAD_SHORTER_DISTANCE_POTENTIAL_BOUND,
    );
}

#[test]
fn finite_separation_bad_separator_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-separation-v0 bad-separator SMT-LIB artifact",
        FINITE_SEPARATION_BAD_SEPARATOR,
    );
}

#[test]
fn finite_separation_bad_convex_combination_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-separation-v0 bad-convex-combination SMT-LIB artifact",
        FINITE_SEPARATION_BAD_CONVEX_COMBINATION,
    );
}

#[test]
fn finite_kkt_bad_stationarity_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-kkt-v0 bad-stationarity SMT-LIB artifact",
        FINITE_KKT_BAD_STATIONARITY,
    );
}

#[test]
fn finite_kkt_bad_complementarity_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-kkt-v0 bad-complementarity SMT-LIB artifact",
        FINITE_KKT_BAD_COMPLEMENTARITY,
    );
}

#[test]
fn finite_active_set_qp_bad_free_gradient_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-active-set-qp-v0 bad-free-gradient SMT-LIB artifact",
        FINITE_ACTIVE_SET_QP_BAD_FREE_GRADIENT,
    );
}

#[test]
fn finite_active_set_qp_bad_inactive_slack_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-active-set-qp-v0 bad-inactive-slack SMT-LIB artifact",
        FINITE_ACTIVE_SET_QP_BAD_INACTIVE_SLACK,
    );
}

#[test]
fn finite_active_set_qp_bad_degenerate_multiplier_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-active-set-qp-v0 bad-degenerate-multiplier SMT-LIB artifact",
        FINITE_ACTIVE_SET_QP_BAD_DEGENERATE_MULTIPLIER,
    );
}

#[test]
fn finite_sdp_bad_objective_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-sdp-v0 bad-objective SMT-LIB artifact",
        FINITE_SDP_BAD_OBJECTIVE,
    );
}

#[test]
fn finite_sdp_bad_duality_gap_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-sdp-v0 bad-duality-gap SMT-LIB artifact",
        FINITE_SDP_BAD_DUALITY_GAP,
    );
}

#[test]
fn finite_sdp_bad_slack_entry_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-sdp-v0 bad-slack-entry SMT-LIB artifact",
        FINITE_SDP_BAD_SLACK_ENTRY,
    );
}

#[test]
fn finite_gradient_descent_bad_decrease_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-gradient-descent-v0 bad-decrease SMT-LIB artifact",
        FINITE_GRADIENT_DESCENT_BAD_DECREASE,
    );
}

#[test]
fn finite_gradient_descent_bad_step_coordinate_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-gradient-descent-v0 bad-step-coordinate SMT-LIB artifact",
        FINITE_GRADIENT_DESCENT_BAD_STEP_COORDINATE,
    );
}

#[test]
fn finite_gradient_descent_bad_descent_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-gradient-descent-v0 bad-descent-bound SMT-LIB artifact",
        FINITE_GRADIENT_DESCENT_BAD_DESCENT_BOUND,
    );
}

#[test]
fn finite_line_search_bad_armijo_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-line-search-v0 bad-Armijo SMT-LIB artifact",
        FINITE_LINE_SEARCH_BAD_ARMIJO,
    );
}

#[test]
fn finite_line_search_bad_descent_direction_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-line-search-v0 bad-descent-direction SMT-LIB artifact",
        FINITE_LINE_SEARCH_BAD_DESCENT_DIRECTION,
    );
}

#[test]
fn finite_line_search_bad_accepted_candidate_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-line-search-v0 bad-accepted-candidate SMT-LIB artifact",
        FINITE_LINE_SEARCH_BAD_ACCEPTED_CANDIDATE,
    );
}

#[test]
fn finite_wolfe_line_search_bad_minimizer_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-wolfe-line-search-v0 bad-line-minimizer SMT-LIB artifact",
        FINITE_WOLFE_LINE_SEARCH_BAD_MINIMIZER,
    );
}

#[test]
fn finite_wolfe_line_search_bad_sufficient_decrease_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-wolfe-line-search-v0 bad-sufficient-decrease SMT-LIB artifact",
        FINITE_WOLFE_LINE_SEARCH_BAD_SUFFICIENT_DECREASE,
    );
}

#[test]
fn finite_wolfe_line_search_bad_curvature_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-wolfe-line-search-v0 bad-Wolfe-curvature SMT-LIB artifact",
        FINITE_WOLFE_LINE_SEARCH_BAD_CURVATURE,
    );
}

#[test]
fn finite_projected_gradient_bad_projection_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-projected-gradient-v0 bad-projection SMT-LIB artifact",
        FINITE_PROJECTED_GRADIENT_BAD_PROJECTION,
    );
}

#[test]
fn finite_projected_gradient_bad_decrease_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-projected-gradient-v0 bad-decrease SMT-LIB artifact",
        FINITE_PROJECTED_GRADIENT_BAD_DECREASE,
    );
}

#[test]
fn finite_proximal_gradient_bad_proximal_point_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-proximal-gradient-v0 bad-proximal-point SMT-LIB artifact",
        FINITE_PROXIMAL_GRADIENT_BAD_PROXIMAL_POINT,
    );
}

#[test]
fn finite_proximal_gradient_bad_composite_decrease_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-proximal-gradient-v0 bad-composite-decrease SMT-LIB artifact",
        FINITE_PROXIMAL_GRADIENT_BAD_COMPOSITE_DECREASE,
    );
}

#[test]
fn finite_proximal_gradient_bad_box_proximal_point_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-proximal-gradient-v0 bad-box-proximal-point SMT-LIB artifact",
        FINITE_PROXIMAL_GRADIENT_BAD_BOX_PROXIMAL_POINT,
    );
}

#[test]
fn multivariable_calculus_bad_gradient_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "multivariable-calculus-rational-v0 bad-gradient SMT-LIB artifact",
        MULTIVARIABLE_CALCULUS_BAD_GRADIENT,
    );
}

#[test]
fn finite_newton_step_bad_coordinate_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-newton-step-v0 bad-coordinate SMT-LIB artifact",
        FINITE_NEWTON_STEP_BAD_COORDINATE,
    );
}

#[test]
fn finite_condition_number_bad_condition_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-condition-number-v0 bad-condition-number SMT-LIB artifact",
        FINITE_CONDITION_NUMBER_BAD_CONDITION,
    );
}

#[test]
fn finite_rounding_shadow_bad_rounded_delta_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-rounding-shadow-v0 bad-rounded-delta SMT-LIB artifact",
        FINITE_ROUNDING_SHADOW_BAD_ROUNDED_DELTA,
    );
}

#[test]
fn finite_interval_arithmetic_bad_product_upper_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-interval-arithmetic-shadow-v0 bad-product-upper SMT-LIB artifact",
        FINITE_INTERVAL_ARITHMETIC_BAD_PRODUCT_UPPER,
    );
}

#[test]
fn finite_schur_complement_bad_value_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-schur-complement-v0 bad-value SMT-LIB artifact",
        FINITE_SCHUR_COMPLEMENT_BAD_VALUE,
    );
}

#[test]
fn finite_singular_value_shadow_bad_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-singular-value-shadow-v0 bad-singular-value-bound SMT-LIB artifact",
        FINITE_SINGULAR_VALUE_SHADOW_BAD_BOUND,
    );
}

#[test]
fn finite_jordan_chain_bad_component_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-jordan-chain-v0 bad-component SMT-LIB artifact",
        FINITE_JORDAN_CHAIN_BAD_COMPONENT,
    );
}

#[test]
fn coordinate_geometry_bad_distance_squared_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "coordinate-geometry-v0 bad-distance-squared SMT-LIB artifact",
        COORDINATE_GEOMETRY_BAD_DISTANCE_SQUARED,
    );
}

#[test]
fn coordinate_geometry_bad_midpoint_x_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "coordinate-geometry-v0 bad-midpoint-x SMT-LIB artifact",
        COORDINATE_GEOMETRY_BAD_MIDPOINT_X,
    );
}

#[test]
fn finite_circle_geometry_bad_radius_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-circle-geometry-v0 bad-radius SMT-LIB artifact",
        FINITE_CIRCLE_GEOMETRY_BAD_RADIUS,
    );
}

#[test]
fn finite_circle_geometry_bad_line_intersection_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-circle-geometry-v0 bad-line-intersection SMT-LIB artifact",
        FINITE_CIRCLE_GEOMETRY_BAD_LINE_INTERSECTION,
    );
}

#[test]
fn finite_inversion_geometry_bad_inverse_x_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-inversion-geometry-v0 bad-inversion-x SMT-LIB artifact",
        FINITE_INVERSION_GEOMETRY_BAD_INVERSE_X,
    );
}

#[test]
fn finite_inversion_geometry_bad_inverse_distance_product_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-inversion-geometry-v0 bad-inverse-distance-product SMT-LIB artifact",
        FINITE_INVERSION_GEOMETRY_BAD_INVERSE_DISTANCE_PRODUCT,
    );
}

#[test]
fn finite_cyclic_geometry_bad_diagonal_intersection_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-cyclic-geometry-v0 bad-diagonal-intersection SMT-LIB artifact",
        FINITE_CYCLIC_GEOMETRY_BAD_DIAGONAL_INTERSECTION,
    );
}

#[test]
fn finite_cyclic_geometry_bad_opposite_angle_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-cyclic-geometry-v0 bad-opposite-angle SMT-LIB artifact",
        FINITE_CYCLIC_GEOMETRY_BAD_OPPOSITE_ANGLE,
    );
}

#[test]
fn finite_cyclic_geometry_bad_ptolemy_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-cyclic-geometry-v0 bad-ptolemy SMT-LIB artifact",
        FINITE_CYCLIC_GEOMETRY_BAD_PTOLEMY,
    );
}

#[test]
fn incidence_geometry_bad_point_on_line_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "incidence-geometry-v0 bad-incidence SMT-LIB artifact",
        INCIDENCE_GEOMETRY_BAD_POINT_ON_LINE,
    );
}

#[test]
fn incidence_geometry_bad_intersection_x_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "incidence-geometry-v0 bad-intersection-x SMT-LIB artifact",
        INCIDENCE_GEOMETRY_BAD_INTERSECTION_X,
    );
}

#[test]
fn rigid_configuration_bad_distance_table_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "rigid-configuration-geometry-v0 bad-distance-table SMT-LIB artifact",
        RIGID_CONFIGURATION_BAD_DISTANCE_TABLE,
    );
}

#[test]
fn rigid_configuration_bad_translation_image_x_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "rigid-configuration-geometry-v0 bad-translation-image-x SMT-LIB artifact",
        RIGID_CONFIGURATION_BAD_TRANSLATION_IMAGE_X,
    );
}

#[test]
fn finite_operator_bad_l1_sum_norm_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-operator-v0 bad-l1-sum-norm SMT-LIB artifact",
        FINITE_OPERATOR_BAD_L1_SUM_NORM,
    );
}

#[test]
fn finite_operator_bad_operator_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-operator-v0 bad-operator-bound SMT-LIB artifact",
        FINITE_OPERATOR_BAD_OPERATOR_BOUND,
    );
}

#[test]
fn finite_operator_bad_chebyshev_t3_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-operator-v0 bad-chebyshev-t3 SMT-LIB artifact",
        FINITE_OPERATOR_BAD_CHEBYSHEV_T3,
    );
}

#[test]
fn finite_concentration_bad_tail_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-concentration-v0 bad-concentration-bound SMT-LIB artifact",
        FINITE_CONCENTRATION_BAD_TAIL_BOUND,
    );
}

#[test]
fn finite_concentration_bad_union_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-concentration-v0 bad-union-bound SMT-LIB artifact",
        FINITE_CONCENTRATION_BAD_UNION_BOUND,
    );
}

#[test]
fn finite_chebyshev_duplicate_node_grid_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let determinant = real(&mut arena, "determinant");
    let determinant_is_zero = eq_ratio(&mut arena, determinant, 0, 1);
    let false_nonzero_determinant = eq_ratio(&mut arena, determinant, 1, 1);

    assert_farkas_checked(
        "finite-chebyshev-systems-v0 bad-duplicate-node-grid-rejected",
        &arena,
        &[determinant_is_zero, false_nonzero_determinant],
    );
}

#[test]
fn finite_chebyshev_bad_interpolation_sample_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-chebyshev-systems-v0 bad-interpolation-sample SMT-LIB artifact",
        FINITE_CHEBYSHEV_BAD_INTERPOLATION_SAMPLE,
    );
}

#[test]
fn finite_chebyshev_bad_alternating_residual_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-chebyshev-systems-v0 bad-alternating-residual SMT-LIB artifact",
        FINITE_CHEBYSHEV_BAD_ALTERNATING_RESIDUAL,
    );
}

#[test]
fn finite_probability_bad_normalization_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let heads = real(&mut arena, "heads");
    let tails = real(&mut arena, "tails");
    let total = real(&mut arena, "total");
    let heads_is_half = eq_ratio(&mut arena, heads, 1, 2);
    let tails_is_half = eq_ratio(&mut arena, tails, 1, 2);
    let mass_sum = arena.real_add(heads, tails).unwrap();
    let total_matches_sum = arena.eq(total, mass_sum).unwrap();
    let total_is_three_halves = eq_ratio(&mut arena, total, 3, 2);

    assert_farkas_checked(
        "finite-probability-v0 bad-normalization-rejected",
        &arena,
        &[
            heads_is_half,
            tails_is_half,
            total_matches_sum,
            total_is_three_halves,
        ],
    );
}

#[test]
fn finite_probability_bad_bayes_posterior_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let posterior = real(&mut arena, "posterior");

    // For prior=1/100, sensitivity=9/10, and false_positive_rate=1/20:
    // P(disease and positive)=9/1000 and P(positive)=117/2000. Bayes requires
    // (117/2000)*posterior = 9/1000. The bad row claims posterior=1/5.
    let evidence_probability = arena.real_ratio(117, 2000);
    let weighted_posterior = arena.real_mul(evidence_probability, posterior).unwrap();
    let bayes_equation = eq_ratio(&mut arena, weighted_posterior, 9, 1000);
    let false_posterior = eq_ratio(&mut arena, posterior, 1, 5);

    assert_farkas_checked(
        "finite-probability-v0 bad-bayes-posterior-rejected",
        &arena,
        &[bayes_equation, false_posterior],
    );
}

#[test]
fn finite_probability_bad_conditional_probability_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-probability-v0 bad-conditional-probability SMT-LIB artifact",
        FINITE_PROBABILITY_BAD_CONDITIONAL_PROBABILITY,
    );
}

#[test]
fn finite_probability_bad_independence_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-probability-v0 bad-independence SMT-LIB artifact",
        FINITE_PROBABILITY_BAD_INDEPENDENCE,
    );
}

#[test]
fn finite_probability_bad_total_variation_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-probability-v0 bad-total-variation SMT-LIB artifact",
        FINITE_PROBABILITY_BAD_TOTAL_VARIATION,
    );
}

#[test]
fn finite_product_measure_bad_probability_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let product_probability = real(&mut arena, "product_probability");
    let replay_computed_mass = eq_ratio(&mut arena, product_probability, 1, 6);
    let false_claimed_mass = eq_ratio(&mut arena, product_probability, 1, 5);

    assert_farkas_checked(
        "finite-product-measure-v0 bad-product-measure-rejected",
        &arena,
        &[replay_computed_mass, false_claimed_mass],
    );
}

#[test]
fn finite_product_measure_bad_marginal_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-product-measure-v0 bad-product-marginal SMT-LIB artifact",
        FINITE_PRODUCT_MEASURE_BAD_MARGINAL,
    );
}

#[test]
fn finite_measure_bad_complement_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-measure-v0 bad-complement SMT-LIB artifact",
        FINITE_MEASURE_BAD_COMPLEMENT,
    );
}

#[test]
fn finite_measure_monotonicity_bad_subset_measure_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-measure-monotonicity-v0 bad-subset-measure SMT-LIB artifact",
        FINITE_MEASURE_MONOTONICITY_BAD_SUBSET_MEASURE,
    );
}

#[test]
fn finite_measure_monotonicity_bad_union_subadditivity_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-measure-monotonicity-v0 bad-union-subadditivity SMT-LIB artifact",
        FINITE_MEASURE_MONOTONICITY_BAD_UNION_SUBADDITIVITY,
    );
}

#[test]
fn finite_random_variables_bad_pushforward_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let long_probability = real(&mut arena, "long_probability");
    let replay_computed_mass = eq_ratio(&mut arena, long_probability, 1, 4);
    let false_claimed_mass = eq_ratio(&mut arena, long_probability, 1, 2);

    assert_farkas_checked(
        "finite-random-variables-v0 qf-lra-bad-pushforward",
        &arena,
        &[replay_computed_mass, false_claimed_mass],
    );
}

#[test]
fn finite_random_variables_bad_expectation_through_pushforward_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-random-variables-v0 qf-lra-bad-expectation-through-pushforward SMT-LIB artifact",
        FINITE_RANDOM_VARIABLES_BAD_EXPECTATION_THROUGH_PUSHFORWARD,
    );
}

#[test]
fn finite_integration_bad_expectation_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let integral_value = real(&mut arena, "integral_value");
    let replay_computed_integral = eq_ratio(&mut arena, integral_value, 5, 2);
    let false_claimed_integral = eq_ratio(&mut arena, integral_value, 3, 1);

    assert_farkas_checked(
        "finite-integration-v0 qf-lra-bad-expectation",
        &arena,
        &[replay_computed_integral, false_claimed_integral],
    );
}

#[test]
fn finite_martingales_bad_stopped_expectation_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-martingales-v0 qf-lra-bad-stopped-expectation SMT-LIB artifact",
        FINITE_MARTINGALES_BAD_STOPPED_EXPECTATION,
    );
}

#[test]
fn finite_martingales_bad_conditional_expectation_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let up_block_conditional_expectation = real(&mut arena, "up_block_conditional_expectation");
    let replay_computed_expectation = eq_ratio(&mut arena, up_block_conditional_expectation, 3, 2);
    let false_martingale_equality = eq_ratio(&mut arena, up_block_conditional_expectation, 1, 1);

    assert_farkas_checked(
        "finite-martingales-v0 qf-lra-bad-martingale",
        &arena,
        &[replay_computed_expectation, false_martingale_equality],
    );
}

#[test]
fn finite_markov_chain_bad_stochastic_row_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-markov-chain-v0 bad-stochastic-row SMT-LIB artifact",
        FINITE_MARKOV_CHAIN_BAD_STOCHASTIC_ROW,
    );
}

#[test]
fn finite_markov_chain_bad_stationary_distribution_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-markov-chain-v0 bad-stationary-distribution SMT-LIB artifact",
        FINITE_MARKOV_CHAIN_BAD_STATIONARY_DISTRIBUTION,
    );
}

#[test]
fn finite_hitting_times_bad_survival_mass_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-hitting-times-v0 qf-lra-bad-survival-mass SMT-LIB artifact",
        FINITE_HITTING_TIMES_BAD_SURVIVAL_MASS,
    );
}

#[test]
fn finite_hitting_times_bad_expected_time_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-hitting-times-v0 qf-lra-bad-expected-time SMT-LIB artifact",
        FINITE_HITTING_TIMES_BAD_EXPECTED_TIME,
    );
}

#[test]
fn least_squares_bad_coefficients_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "least-squares-regression-v0 bad-regression-coefficients SMT-LIB artifact",
        LEAST_SQUARES_BAD_COEFFICIENTS,
    );
}

#[test]
fn least_squares_bad_rss_improvement_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "least-squares-regression-v0 bad-rss-improvement SMT-LIB artifact",
        LEAST_SQUARES_BAD_RSS_IMPROVEMENT,
    );
}

#[test]
fn finite_ridge_regression_bad_beta0_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-ridge-regression-v0 qf-lra-bad-ridge-beta0 SMT-LIB artifact",
        FINITE_RIDGE_REGRESSION_BAD_BETA0,
    );
}

#[test]
fn finite_linear_discriminant_bad_direction_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-linear-discriminant-v0 qf-lra-bad-fisher-direction SMT-LIB artifact",
        FINITE_LINEAR_DISCRIMINANT_BAD_DIRECTION,
    );
}

#[test]
fn real_analysis_bad_linear_delta_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let output_distance = real(&mut arena, "output_distance");
    let output_distance_is_four_thirds = eq_ratio(&mut arena, output_distance, 4, 3);
    let epsilon = arena.real_ratio(1, 1);
    let false_output_bound = arena.real_lt(output_distance, epsilon).unwrap();

    assert_farkas_checked(
        "real-analysis-rational-v0 bad-linear-delta-rejected",
        &arena,
        &[output_distance_is_four_thirds, false_output_bound],
    );
}

#[test]
fn metric_continuity_bad_delta_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let output_distance = real(&mut arena, "output_distance");
    let output_distance_is_epsilon = eq_ratio(&mut arena, output_distance, 1, 1);
    let epsilon = arena.real_ratio(1, 1);
    let false_output_bound = arena.real_lt(output_distance, epsilon).unwrap();

    assert_farkas_checked(
        "metric-continuity-v0 bad-delta-rejected",
        &arena,
        &[output_distance_is_epsilon, false_output_bound],
    );
}

#[test]
fn metric_continuity_bad_open_ball_preimage_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "metric-continuity-v0 bad-open-ball-preimage SMT-LIB artifact",
        METRIC_CONTINUITY_BAD_OPEN_BALL_PREIMAGE,
    );
}

#[test]
fn finite_conditional_expectation_bad_table_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let high_block_expectation = real(&mut arena, "high_block_expectation");
    let half = arena.real_ratio(1, 2);
    let weighted_expectation = arena.real_mul(half, high_block_expectation).unwrap();
    let block_average_equation = eq_ratio(&mut arena, weighted_expectation, 3, 1);
    let false_claim = eq_ratio(&mut arena, high_block_expectation, 5, 1);

    assert_farkas_checked(
        "finite-conditional-expectation-v0 bad-conditional-expectation-rejected",
        &arena,
        &[block_average_equation, false_claim],
    );
}

#[test]
fn finite_conditional_expectation_bad_total_expectation_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-conditional-expectation-v0 bad-total-expectation SMT-LIB artifact",
        FINITE_CONDITIONAL_EXPECTATION_BAD_TOTAL_EXPECTATION,
    );
}

#[test]
fn finite_conditional_expectation_bad_tower_property_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-conditional-expectation-v0 bad-tower-property SMT-LIB artifact",
        FINITE_CONDITIONAL_EXPECTATION_BAD_TOWER_PROPERTY,
    );
}

#[test]
fn finite_conditional_expectation_bad_variance_decomposition_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-conditional-expectation-v0 bad-variance-decomposition SMT-LIB artifact",
        FINITE_CONDITIONAL_EXPECTATION_BAD_VARIANCE_DECOMPOSITION,
    );
}

#[test]
fn finite_stochastic_kernel_bad_row_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-stochastic-kernels-v0 bad-kernel-row SMT-LIB artifact",
        FINITE_STOCHASTIC_KERNEL_BAD_ROW,
    );
}

#[test]
fn finite_stochastic_kernel_bad_composition_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-stochastic-kernels-v0 bad-composition-entry SMT-LIB artifact",
        FINITE_STOCHASTIC_KERNEL_BAD_COMPOSITION,
    );
}

#[test]
fn finite_euler_bad_step_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let state = real(&mut arena, "state");
    let derivative = real(&mut arena, "derivative");
    let next_state = real(&mut arena, "next_state");
    let state_is_one = eq_ratio(&mut arena, state, 1, 1);
    let derivative_is_minus_one = eq_ratio(&mut arena, derivative, -1, 1);

    // Fixed explicit-Euler transition for y' = -y after derivative replay:
    // next_state = state + (1/2)*derivative. The bad row claims 3/4, while the
    // transition forces 1/2.
    let half = arena.real_ratio(1, 2);
    let half_derivative = arena.real_mul(half, derivative).unwrap();
    let transition_rhs = arena.real_add(state, half_derivative).unwrap();
    let euler_step = arena.eq(next_state, transition_rhs).unwrap();
    let false_next_state = eq_ratio(&mut arena, next_state, 3, 4);

    assert_farkas_checked(
        "finite-euler-method-v0 bad-euler-step-rejected",
        &arena,
        &[
            state_is_one,
            derivative_is_minus_one,
            euler_step,
            false_next_state,
        ],
    );
}

#[test]
fn finite_euler_bad_max_error_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-euler-method-v0 bad-max-error-bound SMT-LIB artifact",
        FINITE_EULER_BAD_MAX_ERROR_BOUND,
    );
}

#[test]
fn finite_euler_bad_terminal_error_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-euler-method-v0 bad-terminal-error SMT-LIB artifact",
        FINITE_EULER_BAD_TERMINAL_ERROR,
    );
}

#[test]
fn finite_runge_kutta_midpoint_bad_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-runge-kutta-midpoint-v0 bad-rk-midpoint-step SMT-LIB artifact",
        FINITE_RUNGE_KUTTA_MIDPOINT_BAD_STEP,
    );
}

#[test]
fn finite_heun_bad_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-heun-method-v0 bad-heun-step SMT-LIB artifact",
        FINITE_HEUN_BAD_STEP,
    );
}

#[test]
fn finite_backward_euler_bad_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-backward-euler-method-v0 bad-backward-euler-step SMT-LIB artifact",
        FINITE_BACKWARD_EULER_BAD_STEP,
    );
}

#[test]
fn finite_crank_nicolson_bad_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-crank-nicolson-method-v0 bad-crank-nicolson-step SMT-LIB artifact",
        FINITE_CRANK_NICOLSON_BAD_STEP,
    );
}

#[test]
fn finite_adams_bashforth_bad_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-adams-bashforth-method-v0 bad-adams-bashforth-step SMT-LIB artifact",
        FINITE_ADAMS_BASHFORTH_BAD_STEP,
    );
}

#[test]
fn finite_bdf2_bad_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-bdf2-method-v0 bad-bdf2-step SMT-LIB artifact",
        FINITE_BDF2_BAD_STEP,
    );
}

#[test]
fn bounded_dynamics_bad_invariant_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "bounded-dynamics-v0 bad-invariant-bound SMT-LIB artifact",
        BOUNDED_DYNAMICS_BAD_INVARIANT_BOUND,
    );
}

#[test]
fn bounded_dynamics_bad_transition_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "bounded-dynamics-v0 bad-transition-step SMT-LIB artifact",
        BOUNDED_DYNAMICS_BAD_TRANSITION_STEP,
    );
}

#[test]
fn bounded_dynamics_bad_threshold_step_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "bounded-dynamics-v0 bad-threshold-step SMT-LIB artifact",
        BOUNDED_DYNAMICS_BAD_THRESHOLD_STEP,
    );
}

#[test]
fn orientation_area_bad_orientation_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let signed_double_area = real(&mut arena, "signed_double_area");
    let area_is_negative_one = eq_ratio(&mut arena, signed_double_area, -1, 1);
    let zero = arena.real_ratio(0, 1);
    let false_ccw_claim = arena.real_gt(signed_double_area, zero).unwrap();

    assert_farkas_checked(
        "orientation-area-geometry-v0 bad-orientation-rejected",
        &arena,
        &[area_is_negative_one, false_ccw_claim],
    );
}

#[test]
fn orientation_area_bad_affine_area_scaling_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "orientation-area-geometry-v0 bad-affine-area-scaling SMT-LIB artifact",
        ORIENTATION_AREA_BAD_AFFINE_AREA_SCALING,
    );
}

#[test]
fn numerical_linear_algebra_bad_residual_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "numerical-linear-algebra-v0 bad-residual-bound SMT-LIB artifact",
        NUMERICAL_LINEAR_ALGEBRA_BAD_RESIDUAL_BOUND,
    );
}

#[test]
fn numerical_linear_algebra_bad_jacobi_error_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "numerical-linear-algebra-v0 bad-jacobi-error-bound SMT-LIB artifact",
        NUMERICAL_LINEAR_ALGEBRA_BAD_JACOBI_ERROR_BOUND,
    );
}

#[test]
fn numerical_linear_algebra_bad_solution_box_upper_bound_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "numerical-linear-algebra-v0 bad-solution-box-upper-bound SMT-LIB artifact",
        NUMERICAL_LINEAR_ALGEBRA_BAD_SOLUTION_BOX_UPPER_BOUND,
    );
}

#[test]
fn random_matrix_bad_trace_moment_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "random-matrix-finite-v0 bad-trace-moment SMT-LIB artifact",
        RANDOM_MATRIX_BAD_TRACE_MOMENT,
    );
}

#[test]
fn random_matrix_bad_expected_rank_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "random-matrix-finite-v0 bad-expected-rank SMT-LIB artifact",
        RANDOM_MATRIX_BAD_EXPECTED_RANK,
    );
}

#[test]
fn affine_geometry_bad_distance_preservation_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let original_distance_squared = real(&mut arena, "original_distance_squared");
    let transformed_distance_squared = real(&mut arena, "transformed_distance_squared");
    let original_is_one = eq_ratio(&mut arena, original_distance_squared, 1, 1);
    let transformed_is_five = eq_ratio(&mut arena, transformed_distance_squared, 5, 1);
    let false_preservation = arena
        .eq(original_distance_squared, transformed_distance_squared)
        .unwrap();

    assert_farkas_checked(
        "affine-geometry-v0 bad-distance-preservation-rejected",
        &arena,
        &[original_is_one, transformed_is_five, false_preservation],
    );
}

#[test]
fn affine_geometry_bad_midpoint_image_y_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "affine-geometry-v0 bad-midpoint-image-y SMT-LIB artifact",
        AFFINE_GEOMETRY_BAD_MIDPOINT_IMAGE_Y,
    );
}

#[test]
fn affine_geometry_bad_collinearity_determinant_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "affine-geometry-v0 bad-collinearity-determinant SMT-LIB artifact",
        AFFINE_GEOMETRY_BAD_COLLINEARITY_DETERMINANT,
    );
}

#[test]
fn inner_product_bad_projection_orthogonality_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "inner-product-spaces-rational-v0 bad-projection-orthogonality SMT-LIB artifact",
        INNER_PRODUCT_BAD_PROJECTION_ORTHOGONALITY,
    );
}

#[test]
fn inner_product_bad_norm_square_emits_checked_farkas() {
    let mut arena = TermArena::new();
    let norm_square = real(&mut arena, "norm_square");
    let norm_is_negative_one = eq_ratio(&mut arena, norm_square, -1, 1);
    let zero = arena.real_ratio(0, 1);
    let positivity_for_nonzero_vector = arena.real_gt(norm_square, zero).unwrap();

    assert_farkas_checked(
        "inner-product-spaces-rational-v0 bad-inner-product-rejected",
        &arena,
        &[norm_is_negative_one, positivity_for_nonzero_vector],
    );
}

#[test]
fn spectral_bad_rayleigh_quotient_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "spectral-linear-algebra-v0 bad-rayleigh-quotient SMT-LIB artifact",
        SPECTRAL_BAD_RAYLEIGH_QUOTIENT,
    );
}

#[test]
fn spectral_bad_eigenpair_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "spectral-linear-algebra-v0 bad-eigenpair SMT-LIB artifact",
        SPECTRAL_BAD_EIGENPAIR,
    );
}

#[test]
fn finite_orthogonal_diagonalization_bad_eigenvalue_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-orthogonal-diagonalization-v0 bad-eigenvalue SMT-LIB artifact",
        FINITE_ORTHOGONAL_DIAGONALIZATION_BAD_EIGENVALUE,
    );
}

#[test]
fn finite_real_schur_decomposition_bad_superdiagonal_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-real-schur-decomposition-v0 bad-superdiagonal SMT-LIB artifact",
        FINITE_REAL_SCHUR_DECOMPOSITION_BAD_SUPERDIAGONAL,
    );
}

#[test]
fn finite_polar_decomposition_bad_diagonal_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-polar-decomposition-v0 bad-diagonal SMT-LIB artifact",
        FINITE_POLAR_DECOMPOSITION_BAD_DIAGONAL,
    );
}

#[test]
fn finite_qr_iteration_step_bad_entry_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-qr-iteration-step-v0 bad-entry SMT-LIB artifact",
        FINITE_QR_ITERATION_STEP_BAD_ENTRY,
    );
}

#[test]
fn finite_shifted_qr_step_bad_entry_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-shifted-qr-step-v0 bad-entry SMT-LIB artifact",
        FINITE_SHIFTED_QR_STEP_BAD_ENTRY,
    );
}

#[test]
fn finite_power_iteration_bad_coordinate_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-power-iteration-v0 bad-power-iterate-coordinate SMT-LIB artifact",
        FINITE_POWER_ITERATION_BAD_COORDINATE,
    );
}

#[test]
fn finite_conjugate_gradient_bad_alpha0_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-conjugate-gradient-v0 bad-cg-alpha0 SMT-LIB artifact",
        FINITE_CONJUGATE_GRADIENT_BAD_ALPHA0,
    );
}

#[test]
fn finite_gmres_residual_shadow_bad_alpha_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-gmres-residual-shadow-v0 bad-gmres-alpha SMT-LIB artifact",
        FINITE_GMRES_RESIDUAL_SHADOW_BAD_ALPHA,
    );
}

#[test]
fn finite_arnoldi_iteration_bad_h21_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-arnoldi-iteration-v0 bad-arnoldi-h21 SMT-LIB artifact",
        FINITE_ARNOLDI_ITERATION_BAD_H21,
    );
}

#[test]
fn finite_lanczos_iteration_bad_beta1_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-lanczos-iteration-v0 bad-lanczos-beta1 SMT-LIB artifact",
        FINITE_LANCZOS_ITERATION_BAD_BETA1,
    );
}

#[test]
fn finite_walsh_hadamard_bad_transform_coefficient_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "finite-walsh-hadamard-transform-v0 bad-transform-coefficient SMT-LIB artifact",
        FINITE_WALSH_HADAMARD_BAD_TRANSFORM_COEFFICIENT,
    );
}

#[test]
fn matrix_invariants_bad_characteristic_polynomial_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "matrix-invariants-v0 bad-characteristic-polynomial SMT-LIB artifact",
        MATRIX_INVARIANTS_BAD_CHARACTERISTIC_POLYNOMIAL,
    );
}

#[test]
fn matrix_invariants_bad_trace_artifact_emits_checked_farkas() {
    assert_resource_farkas(
        "matrix-invariants-v0 bad-trace-invariant SMT-LIB artifact",
        MATRIX_INVARIANTS_BAD_TRACE,
    );
}
