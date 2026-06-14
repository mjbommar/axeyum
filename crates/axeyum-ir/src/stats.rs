//! Term-shape metrics for admission control and blowup diagnosis.
//!
//! The key discriminator (query-cost-control note): `dag_nodes` small but
//! `tree_nodes` astronomical means any non-memoized downstream pass will
//! exhibit representational blowup; both small with slow solving means
//! genuine search hardness.

use std::collections::{HashMap, HashSet};

use crate::arena::TermArena;
use crate::term::{Op, TermId, TermNode};

/// Shape metrics for one or more root terms, computed in a single memoized
/// pass over the shared DAG.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct TermStats {
    /// Unique DAG nodes reachable from the roots.
    pub dag_nodes: u64,
    /// Nodes of the fully unfolded tree, saturating at `u64::MAX`
    /// ("astronomical" — any tree-shaped pass will blow up).
    pub tree_nodes: u64,
    /// Longest root-to-leaf path.
    pub max_depth: u64,
    /// Distinct symbols (free variables) referenced.
    pub distinct_symbols: u64,
    /// `Ite` applications (path-merging density signal).
    pub ite_count: u64,
    /// Multiplication/division/remainder applications (bit-blast cost
    /// signal).
    pub mul_div_count: u64,
}

impl TermStats {
    /// Computes metrics for everything reachable from `roots`.
    ///
    /// # Panics
    ///
    /// Panics if any root does not belong to `arena`.
    pub fn compute(arena: &TermArena, roots: &[TermId]) -> Self {
        // Per-node (tree_size, depth), memoized; iterative post-order.
        let mut memo: HashMap<TermId, (u64, u64)> = HashMap::new();
        let mut symbols: HashSet<u32> = HashSet::new();
        let mut stats = TermStats::default();
        let mut stack: Vec<(TermId, bool)> = roots.iter().map(|&r| (r, false)).collect();

        while let Some((t, children_ready)) = stack.pop() {
            if memo.contains_key(&t) {
                continue;
            }
            match arena.node(t) {
                TermNode::BoolConst(_)
                | TermNode::BvConst { .. }
                | TermNode::WideBvConst(_)
                | TermNode::IntConst(_)
                | TermNode::RealConst(_) => {
                    stats.dag_nodes += 1;
                    memo.insert(t, (1, 1));
                }
                TermNode::Symbol(s) => {
                    stats.dag_nodes += 1;
                    symbols.insert(u32::try_from(s.index()).expect("symbol index fits u32"));
                    memo.insert(t, (1, 1));
                }
                TermNode::App { op, args } => {
                    if children_ready {
                        let mut tree: u64 = 1;
                        let mut depth: u64 = 0;
                        for a in args {
                            let (ts, d) = memo[a];
                            tree = tree.saturating_add(ts);
                            depth = depth.max(d);
                        }
                        stats.dag_nodes += 1;
                        match op {
                            Op::Ite => stats.ite_count += 1,
                            Op::BvMul
                            | Op::BvUdiv
                            | Op::BvUrem
                            | Op::BvSdiv
                            | Op::BvSrem
                            | Op::BvSmod => stats.mul_div_count += 1,
                            _ => {}
                        }
                        memo.insert(t, (tree, depth + 1));
                    } else {
                        stack.push((t, true));
                        for &a in &**args {
                            stack.push((a, false));
                        }
                    }
                }
            }
        }

        let mut tree_total: u64 = 0;
        for &r in roots {
            let (ts, d) = memo[&r];
            tree_total = tree_total.saturating_add(ts);
            stats.max_depth = stats.max_depth.max(d);
        }
        stats.tree_nodes = tree_total;
        stats.distinct_symbols = symbols.len() as u64;
        stats
    }

    /// Sharing ratio `tree_nodes / dag_nodes`; saturated tree counts yield
    /// `f64::INFINITY` semantics naturally (huge ratio).
    pub fn sharing_ratio(&self) -> f64 {
        #[allow(clippy::cast_precision_loss)]
        if self.dag_nodes == 0 {
            0.0
        } else {
            self.tree_nodes as f64 / self.dag_nodes as f64
        }
    }
}
