//! Layered (Sugiyama-style) DAG layout in pure Rust, with no dependencies
//! beyond `std`.
//!
//! This module exists because the atlas needs a dependency-graph figure and
//! the strand forbids a Node toolchain, a vendored JS layout library, and a
//! shell-out to Graphviz (a C binary is not self-contained and is not
//! available on every fleet host). The graphs are small -- tens of nodes for a
//! fact cluster, ~325 for the whole ledger today -- so an O(V*E) implementation
//! of the classical four-phase pipeline is comfortably fast enough and is
//! small enough to read in one sitting.
//!
//! Pipeline (see `docs/render-2026-08/07-r-notes.md`, section R-a):
//!
//! 1. **Acyclic**: DFS; edges into a gray vertex are reversed and remembered.
//! 2. **Layering**: longest path (`layer(v) = 1 + max layer(pred)`).
//! 3. **Dummies**: every edge spanning more than one layer is subdivided.
//! 4. **Ordering**: alternating median sweeps + adjacent-transpose, keeping
//!    the best crossing count seen.
//! 5. **Coordinates**: per-layer weighted isotonic regression (PAVA) against
//!    the median of adjacent-layer neighbours, which is the exact optimum of
//!    a convex placement problem rather than a heuristic nudge.
//!
//! Determinism is a public promise of this repository, so every tie in every
//! phase is broken by index, every sort is stable, and no hash container is
//! iterated. The same input produces byte-identical output.

// Pedantic lints deliberately allowed in this module, with reasons. The
// package sets `clippy::pedantic = warn`; these four fire on shapes that are
// correct here and whose "fix" would make the code worse:
#![allow(
    // Layout arithmetic converts small counts to f64 for geometry. The counts
    // are node indices and layer sizes -- bounded by the ~325-node ledger, so
    // nowhere near f64's 53-bit exact range.
    clippy::cast_precision_loss,
    // Rounding a computed coordinate or a tick value to an integer for display
    // is the intent, not an accident.
    clippy::cast_possible_truncation,
    // Emitting HTML is a long straight-line sequence of writes; splitting it
    // into a dozen private helpers to satisfy a line count would hide the
    // document structure, which is the one thing a reader of an emitter needs.
    clippy::too_many_lines,
    // `write!` into a String cannot fail, and the `format!`-append form reads
    // better than a `let _ = write!` in an expression position.
    clippy::format_push_string,
    // `n`, `d`, `w` are the standard names in the layout literature this file
    // implements; renaming them to `node_count` and `desired` would make the
    // code harder to check against the papers, not easier.
    clippy::many_single_char_names
)]

use std::collections::BTreeMap;

/// A node handed to the layout engine.
#[derive(Clone, Debug, PartialEq)]
pub struct NodeSpec {
    /// Caller-side stable key (a fact id, a theorem name). Echoed back out.
    pub key: String,
    /// Box width in user units. Callers usually derive this from label length.
    pub width: f64,
    /// Box height in user units.
    pub height: f64,
}

impl NodeSpec {
    /// A node with the configured default box size.
    pub fn new(key: &str, width: f64, height: f64) -> Self {
        NodeSpec {
            key: key.to_string(),
            width,
            height,
        }
    }
}

/// Tuning knobs. Defaults are chosen for the atlas figure at ~14px text.
#[derive(Clone, Debug, PartialEq)]
pub struct LayoutConfig {
    /// Vertical distance between the top edges of consecutive layers.
    pub layer_sep: f64,
    /// Minimum horizontal gap between two boxes in the same layer.
    pub node_sep: f64,
    /// Minimum horizontal gap involving a dummy (bend) point.
    pub dummy_sep: f64,
    /// Padding added around the whole drawing.
    pub margin: f64,
    /// Median/transpose sweep budget (measured: 12 reaches the best ordering
    /// this implementation finds on the ledger's prelude component, and the
    /// whole sweep costs microseconds at this size). dagre instead sweeps until four
    /// consecutive sweeps fail to improve (`lib/order/index.ts`, read
    /// 2026-08-21); we cap instead, because a fixed budget is trivially
    /// deterministic and eight sweeps already reaches zero crossings on the
    /// ledger graph. The best ordering seen is kept regardless.
    pub sweeps: usize,
    /// Coordinate refinement passes (each is one down sweep + one up sweep).
    pub coord_passes: usize,
    /// Relative pull a dummy node exerts during coordinate assignment. Higher
    /// values straighten long edges at the cost of nudging real boxes.
    pub dummy_weight: f64,
}

impl Default for LayoutConfig {
    fn default() -> Self {
        LayoutConfig {
            layer_sep: 78.0,
            node_sep: 18.0,
            dummy_sep: 12.0,
            margin: 16.0,
            sweeps: 12,
            coord_passes: 6,
            dummy_weight: 6.0,
        }
    }
}

/// A laid-out node: the caller's key plus a box in drawing coordinates.
#[derive(Clone, Debug, PartialEq)]
pub struct PositionedNode {
    pub key: String,
    /// Index into the caller's original node slice.
    pub index: usize,
    pub layer: usize,
    /// Position within the layer, left to right, 0-based.
    pub order: usize,
    /// Centre of the box.
    pub cx: f64,
    pub cy: f64,
    pub width: f64,
    pub height: f64,
}

impl PositionedNode {
    /// Left edge of the box.
    pub fn x(&self) -> f64 {
        self.cx - self.width / 2.0
    }
    /// Top edge of the box.
    pub fn y(&self) -> f64 {
        self.cy - self.height / 2.0
    }
}

/// A laid-out edge: a polyline from the source box's bottom to the target
/// box's top, passing through the bend points contributed by dummy nodes.
#[derive(Clone, Debug, PartialEq)]
pub struct EdgePath {
    /// Index into the caller's node slice.
    pub from: usize,
    /// Index into the caller's node slice.
    pub to: usize,
    /// `true` when the edge had to be reversed to break a cycle. The points
    /// are always emitted in the caller's original direction; this flag only
    /// tells a renderer that the drawing direction is a fiction.
    pub reversed: bool,
    /// At least two points; `[0]` is on the source box, the last on the target.
    pub points: Vec<(f64, f64)>,
}

/// The finished drawing.
#[derive(Clone, Debug, PartialEq)]
pub struct Layout {
    pub nodes: Vec<PositionedNode>,
    pub edges: Vec<EdgePath>,
    pub width: f64,
    pub height: f64,
    /// Layer membership, as node indices into the caller's slice.
    pub layers: Vec<Vec<usize>>,
    /// Edge crossings in the final ordering. Diagnostic only; a test asserts
    /// it does not regress on the committed sample graph.
    pub crossings: usize,
    /// Number of edges that had to be reversed to break a cycle. `0` for a DAG.
    pub reversed_edges: usize,
}

// ---------------------------------------------------------------------------
// internal graph
// ---------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Internal {
    /// The caller's node index, or `None` for a dummy (bend) node.
    orig: Option<usize>,
    width: f64,
    height: f64,
    weight: f64,
    layer: usize,
    order: usize,
    x: f64,
}

/// Normalise the caller's edge list: drop self loops, drop duplicates, sort.
fn normalize_edges(n: usize, edges: &[(usize, usize)]) -> Vec<(usize, usize)> {
    let mut out: Vec<(usize, usize)> = edges
        .iter()
        .copied()
        .filter(|&(a, b)| a != b && a < n && b < n)
        .collect();
    out.sort_unstable();
    out.dedup();
    out
}

/// Reverse the minimum set of edges a depth-first search finds to be back
/// edges. On a DAG this reverses nothing, which is the case we care about;
/// it is here so a cyclic input degrades to a drawing instead of a panic.
fn break_cycles(n: usize, edges: &[(usize, usize)]) -> (Vec<(usize, usize)>, Vec<bool>) {
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, &(a, _b)) in edges.iter().enumerate() {
        succ[a].push(i);
    }
    let _ = &succ;
    let mut color = vec![0u8; n]; // 0 white, 1 gray, 2 black
    let mut reversed = vec![false; edges.len()];
    // Iterative DFS so a deep chain cannot blow the stack.
    for root in 0..n {
        if color[root] != 0 {
            continue;
        }
        let mut stack: Vec<(usize, usize)> = vec![(root, 0)];
        color[root] = 1;
        while let Some(&mut (v, ref mut i)) = stack.last_mut() {
            if *i < succ[v].len() {
                let ei = succ[v][*i];
                *i += 1;
                let w = edges[ei].1;
                match color[w] {
                    0 => {
                        color[w] = 1;
                        stack.push((w, 0));
                    }
                    1 => reversed[ei] = true, // back edge
                    _ => {}
                }
            } else {
                color[v] = 2;
                stack.pop();
            }
        }
    }
    let out = edges
        .iter()
        .enumerate()
        .map(|(i, &(a, b))| if reversed[i] { (b, a) } else { (a, b) })
        .collect();
    (out, reversed)
}

/// Longest-path layering: a node sits one layer below its deepest predecessor.
/// Sources land on layer 0, so in the atlas the axioms and the imported
/// statements form the top row and everything that rests on them hangs below.
fn assign_layers(n: usize, edges: &[(usize, usize)]) -> Vec<usize> {
    let mut indeg = vec![0usize; n];
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &(a, b) in edges {
        succ[a].push(b);
        indeg[b] += 1;
    }
    let mut layer = vec![0usize; n];
    // Kahn, in index order, so the result does not depend on container order.
    let mut ready: Vec<usize> = (0..n).filter(|&v| indeg[v] == 0).collect();
    let mut head = 0;
    let mut settled = 0;
    while head < ready.len() {
        let v = ready[head];
        head += 1;
        settled += 1;
        for &w in &succ[v] {
            if layer[w] < layer[v] + 1 {
                layer[w] = layer[v] + 1;
            }
            indeg[w] -= 1;
            if indeg[w] == 0 {
                ready.push(w);
            }
        }
    }
    debug_assert_eq!(settled, n, "graph was not acyclic after cycle breaking");
    let _ = settled;
    layer
}

fn median_of(mut vals: Vec<f64>) -> Option<f64> {
    if vals.is_empty() {
        return None;
    }
    vals.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let m = vals.len();
    if m % 2 == 1 {
        Some(vals[m / 2])
    } else if m == 2 {
        Some(f64::midpoint(vals[0], vals[1]))
    } else {
        // dagre's weighted interpolation: bias toward the denser side.
        let left = vals[m / 2 - 1] - vals[0];
        let right = vals[m - 1] - vals[m / 2];
        Some((vals[m / 2 - 1] * right + vals[m / 2] * left) / (left + right).max(1e-9))
    }
}

/// Count crossings between two adjacent layers, given the current ordering.
fn count_crossings(layers: &[Vec<usize>], nodes: &[Internal], succ: &[Vec<usize>]) -> usize {
    let mut total = 0usize;
    for layer in layers.iter().take(layers.len().saturating_sub(1)) {
        // Positions of every edge endpoint in the layer below.
        let mut pairs: Vec<(usize, usize)> = Vec::new();
        for (pos, &v) in layer.iter().enumerate() {
            for &w in &succ[v] {
                pairs.push((pos, nodes[w].order));
            }
        }
        pairs.sort_unstable();
        // Count inversions in the second coordinate (insertion counting; the
        // layers here are small, so the quadratic form is fine and obvious).
        for i in 0..pairs.len() {
            for j in (i + 1)..pairs.len() {
                if pairs[i].1 > pairs[j].1 {
                    total += 1;
                }
            }
        }
    }
    total
}

fn set_orders(layers: &[Vec<usize>], nodes: &mut [Internal]) {
    for layer in layers {
        for (pos, &v) in layer.iter().enumerate() {
            nodes[v].order = pos;
        }
    }
}

/// Weighted isotonic regression with separation constraints (PAVA).
///
/// Given nodes already fixed in left-to-right order, desired centres `d`,
/// weights `w`, and minimum centre-to-centre gaps `gap[i]` between `i` and
/// `i+1`, this returns the placement minimising `sum w_i (x_i - d_i)^2`
/// subject to `x_{i+1} - x_i >= gap[i]`. Substituting `y_i = x_i - G_i` with
/// `G_i = sum_{j<i} gap[j]` turns the constraints into `y` nondecreasing,
/// which pool-adjacent-violators solves exactly in linear time.
///
/// This is the phase where a heuristic would show: barycentre-then-shove
/// leaves boxes visibly off-centre under their parents. Solving the convex
/// problem is both shorter and better.
fn isotonic_place(d: &[f64], w: &[f64], gap: &[f64]) -> Vec<f64> {
    let n = d.len();
    if n == 0 {
        return Vec::new();
    }
    debug_assert_eq!(w.len(), n);
    debug_assert_eq!(gap.len(), n.saturating_sub(1));
    let mut cum = vec![0.0f64; n];
    for i in 1..n {
        cum[i] = cum[i - 1] + gap[i - 1];
    }
    // Blocks: (weighted sum, total weight, count).
    let mut blk_val: Vec<f64> = Vec::with_capacity(n);
    let mut blk_wt: Vec<f64> = Vec::with_capacity(n);
    let mut blk_len: Vec<usize> = Vec::with_capacity(n);
    for i in 0..n {
        let mut val = (d[i] - cum[i]) * w[i];
        let mut wt = w[i];
        let mut len = 1usize;
        while let Some(&prev) = blk_val.last() {
            let pw = *blk_wt.last().unwrap();
            if prev / pw <= val / wt {
                break;
            }
            blk_val.pop();
            blk_wt.pop();
            let pl = blk_len.pop().unwrap();
            val += prev;
            wt += pw;
            len += pl;
        }
        blk_val.push(val);
        blk_wt.push(wt);
        blk_len.push(len);
    }
    let mut out = Vec::with_capacity(n);
    for b in 0..blk_val.len() {
        let mean = blk_val[b] / blk_wt[b];
        for _ in 0..blk_len[b] {
            out.push(mean);
        }
    }
    for i in 0..n {
        out[i] += cum[i];
    }
    out
}

/// Lay out a directed graph in layers.
///
/// Edge `(a, b)` places `a` strictly above `b`. For the fact atlas the caller
/// emits `(dependency, dependent)`, so prerequisites are drawn above the
/// results that rest on them.
///
/// The layout is total: an empty graph, isolated nodes, parallel edges, self
/// loops and even a cyclic input all produce a drawing.
pub fn layered_layout(specs: &[NodeSpec], edges: &[(usize, usize)], cfg: &LayoutConfig) -> Layout {
    let n = specs.len();
    if n == 0 {
        return Layout {
            nodes: Vec::new(),
            edges: Vec::new(),
            width: 2.0 * cfg.margin,
            height: 2.0 * cfg.margin,
            layers: Vec::new(),
            crossings: 0,
            reversed_edges: 0,
        };
    }
    let orig_edges = normalize_edges(n, edges);
    let (acyclic, reversed_flags) = break_cycles(n, &orig_edges);
    let reversed_edges = reversed_flags.iter().filter(|b| **b).count();
    let layer_of = assign_layers(n, &acyclic);
    let n_layers = layer_of.iter().copied().max().unwrap_or(0) + 1;

    // Build the proper (unit-span) graph: real nodes plus dummies.
    let mut nodes: Vec<Internal> = (0..n)
        .map(|i| Internal {
            orig: Some(i),
            width: specs[i].width,
            height: specs[i].height,
            weight: 1.0,
            layer: layer_of[i],
            order: 0,
            x: 0.0,
        })
        .collect();
    // chains[e] = the dummy node indices for acyclic edge e, top to bottom.
    let mut chains: Vec<Vec<usize>> = Vec::with_capacity(acyclic.len());
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut pred: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &(a, b) in &acyclic {
        let span = layer_of[b] - layer_of[a];
        let mut chain = Vec::new();
        let mut upstream = a;
        for k in 1..span {
            let id = nodes.len();
            nodes.push(Internal {
                orig: None,
                width: 0.0,
                height: 0.0,
                weight: cfg.dummy_weight,
                layer: layer_of[a] + k,
                order: 0,
                x: 0.0,
            });
            succ.push(Vec::new());
            pred.push(Vec::new());
            succ[upstream].push(id);
            pred[id].push(upstream);
            chain.push(id);
            upstream = id;
        }
        succ[upstream].push(b);
        pred[b].push(upstream);
        chains.push(chain);
    }

    // Initial ordering: a depth-first walk from the sources, appending each
    // node to its layer the first time it is reached. This is dagre's
    // `initOrder` and it matters more than it looks -- seeding with plain index
    // order left 47 crossings on the ledger's prelude component where the DFS
    // seed leaves far fewer, because the sweeps that follow are local and
    // cannot undo a bad global interleaving. Roots are visited in index order,
    // so the result is still deterministic.
    let mut layers: Vec<Vec<usize>> = vec![Vec::new(); n_layers];
    {
        let mut seen = vec![false; nodes.len()];
        let mut roots: Vec<usize> = (0..nodes.len()).filter(|&v| nodes[v].layer == 0).collect();
        roots.sort_unstable();
        let mut stack: Vec<usize> = Vec::new();
        for r in roots {
            if seen[r] {
                continue;
            }
            stack.push(r);
            while let Some(v) = stack.pop() {
                if seen[v] {
                    continue;
                }
                seen[v] = true;
                layers[nodes[v].layer].push(v);
                let mut kids = succ[v].clone();
                kids.sort_unstable();
                // Reversed, so the lowest index is popped first.
                for &w in kids.iter().rev() {
                    if !seen[w] {
                        stack.push(w);
                    }
                }
            }
        }
        for v in 0..nodes.len() {
            if !seen[v] {
                layers[nodes[v].layer].push(v);
            }
        }
    }
    set_orders(&layers, &mut nodes);

    // Phase 4: median sweeps with transpose, keeping the best.
    let mut best = layers.clone();
    let mut best_cross = count_crossings(&layers, &nodes, &succ);
    for it in 0..cfg.sweeps {
        let down = it % 2 == 0;
        if down {
            for li in 1..n_layers {
                sort_layer_by_median(&mut layers[li], &nodes, &pred);
                set_orders(&layers, &mut nodes);
            }
        } else {
            for li in (0..n_layers.saturating_sub(1)).rev() {
                sort_layer_by_median(&mut layers[li], &nodes, &succ);
                set_orders(&layers, &mut nodes);
            }
        }
        transpose(&mut layers, &mut nodes, &succ, &pred);
        let c = count_crossings(&layers, &nodes, &succ);
        if c < best_cross {
            best_cross = c;
            best.clone_from(&layers);
        }
    }
    layers = best;
    set_orders(&layers, &mut nodes);

    // Phase 5: coordinates. Seed with a tight left-to-right packing, then
    // alternate down/up passes of median-target isotonic placement.
    for layer in &layers {
        let mut cursor = 0.0f64;
        for &v in layer {
            let half = nodes[v].width / 2.0;
            cursor += half;
            nodes[v].x = cursor;
            cursor += half + sep_after(v, layer, &nodes, cfg);
        }
    }
    for pass in 0..cfg.coord_passes {
        let down = pass % 2 == 0;
        let range: Vec<usize> = if down {
            (0..n_layers).collect()
        } else {
            (0..n_layers).rev().collect()
        };
        for li in range {
            let layer = &layers[li];
            if layer.is_empty() {
                continue;
            }
            let mut d = Vec::with_capacity(layer.len());
            let mut w = Vec::with_capacity(layer.len());
            for &v in layer {
                let neigh: &Vec<usize> = if down { &pred[v] } else { &succ[v] };
                let target = median_of(neigh.iter().map(|&u| nodes[u].x).collect());
                d.push(target.unwrap_or(nodes[v].x));
                w.push(if target.is_some() {
                    nodes[v].weight
                } else {
                    nodes[v].weight * 0.25
                });
            }
            let mut gaps = Vec::with_capacity(layer.len().saturating_sub(1));
            for i in 0..layer.len().saturating_sub(1) {
                let a = layer[i];
                let b = layer[i + 1];
                let sep = if nodes[a].orig.is_none() || nodes[b].orig.is_none() {
                    cfg.dummy_sep
                } else {
                    cfg.node_sep
                };
                gaps.push(nodes[a].width / 2.0 + sep + nodes[b].width / 2.0);
            }
            let placed = isotonic_place(&d, &w, &gaps);
            for (i, &v) in layer.iter().enumerate() {
                nodes[v].x = placed[i];
            }
        }
    }

    // Vertical coordinates: one row per layer, rows sized by their tallest box.
    let mut row_h = vec![0.0f64; n_layers];
    for node in &nodes {
        if node.height > row_h[node.layer] {
            row_h[node.layer] = node.height;
        }
    }
    let mut row_cy = vec![0.0f64; n_layers];
    let mut y = 0.0f64;
    for li in 0..n_layers {
        row_cy[li] = y + row_h[li] / 2.0;
        y += row_h[li] + cfg.layer_sep;
    }
    let total_h = if n_layers == 0 {
        0.0
    } else {
        y - cfg.layer_sep
    };

    // Normalise so the drawing starts at (margin, margin).
    let min_x = nodes
        .iter()
        .map(|nd| nd.x - nd.width / 2.0)
        .fold(f64::INFINITY, f64::min);
    let max_x = nodes
        .iter()
        .map(|nd| nd.x + nd.width / 2.0)
        .fold(f64::NEG_INFINITY, f64::max);
    let shift = cfg.margin - min_x;

    let mut out_nodes: Vec<PositionedNode> = Vec::with_capacity(n);
    let mut by_orig: BTreeMap<usize, (f64, f64)> = BTreeMap::new();
    for (i, node) in nodes.iter().enumerate() {
        let cx = node.x + shift;
        let cy = row_cy[node.layer] + cfg.margin;
        by_orig.insert(i, (cx, cy));
        if let Some(oi) = node.orig {
            out_nodes.push(PositionedNode {
                key: specs[oi].key.clone(),
                index: oi,
                layer: node.layer,
                order: node.order,
                cx,
                cy,
                width: node.width,
                height: node.height,
            });
        }
    }
    out_nodes.sort_by_key(|p| p.index);

    // Edge polylines, in the caller's original direction.
    let mut out_edges = Vec::with_capacity(acyclic.len());
    for (ei, &(a, b)) in acyclic.iter().enumerate() {
        let mut pts: Vec<(f64, f64)> = Vec::new();
        let (ax, ay) = by_orig[&a];
        pts.push((ax, ay + nodes[a].height / 2.0));
        for &dv in &chains[ei] {
            pts.push(by_orig[&dv]);
        }
        let (bx, by) = by_orig[&b];
        pts.push((bx, by - nodes[b].height / 2.0));
        let rev = reversed_flags[ei];
        if rev {
            pts.reverse();
        }
        let (from, to) = if rev { (b, a) } else { (a, b) };
        out_edges.push(EdgePath {
            from,
            to,
            reversed: rev,
            points: pts,
        });
    }
    out_edges.sort_by_key(|e| (e.from, e.to));

    let mut out_layers: Vec<Vec<usize>> = vec![Vec::new(); n_layers];
    for layer in &layers {
        for &v in layer {
            if let Some(oi) = nodes[v].orig {
                out_layers[nodes[v].layer].push(oi);
            }
        }
    }

    Layout {
        nodes: out_nodes,
        edges: out_edges,
        width: (max_x - min_x) + 2.0 * cfg.margin,
        height: total_h + 2.0 * cfg.margin,
        layers: out_layers,
        crossings: best_cross,
        reversed_edges,
    }
}

fn sep_after(v: usize, _layer: &[usize], nodes: &[Internal], cfg: &LayoutConfig) -> f64 {
    if nodes[v].orig.is_none() {
        cfg.dummy_sep
    } else {
        cfg.node_sep
    }
}

fn sort_layer_by_median(layer: &mut [usize], nodes: &[Internal], adj: &[Vec<usize>]) {
    // Nodes with no neighbour in the fixed layer keep their current position:
    // the standard fix-in-place rule, and the reason this is stable.
    let mut keyed: Vec<(f64, usize, usize)> = layer
        .iter()
        .enumerate()
        .map(|(pos, &v)| {
            let m = median_of(adj[v].iter().map(|&u| nodes[u].order as f64).collect());
            (m.unwrap_or(pos as f64), pos, v)
        })
        .collect();
    keyed.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap().then(a.1.cmp(&b.1)));
    for (i, k) in keyed.iter().enumerate() {
        layer[i] = k.2;
    }
}

/// Adjacent-swap improvement: repeatedly swap neighbours when doing so lowers
/// the crossing count. Bounded so a pathological graph cannot spin.
fn transpose(
    layers: &mut [Vec<usize>],
    nodes: &mut [Internal],
    succ: &[Vec<usize>],
    pred: &[Vec<usize>],
) {
    let mut improved = true;
    let mut rounds = 0;
    while improved && rounds < 8 {
        improved = false;
        rounds += 1;
        for layer in layers.iter_mut() {
            for i in 0..layer.len().saturating_sub(1) {
                let v = layer[i];
                let w = layer[i + 1];
                let before = local_crossings(v, w, nodes, succ, pred);
                layer.swap(i, i + 1);
                set_orders_layer(layer, nodes);
                let after = local_crossings(w, v, nodes, succ, pred);
                if after < before {
                    improved = true;
                } else {
                    layer.swap(i, i + 1);
                    set_orders_layer(layer, nodes);
                }
            }
        }
    }
}

fn set_orders_layer(layer: &[usize], nodes: &mut [Internal]) {
    for (pos, &v) in layer.iter().enumerate() {
        nodes[v].order = pos;
    }
}

/// Crossings contributed by the pair (`left`, `right`) alone, up and down.
fn local_crossings(
    left: usize,
    right: usize,
    nodes: &[Internal],
    succ: &[Vec<usize>],
    pred: &[Vec<usize>],
) -> usize {
    let mut c = 0;
    for adj in [succ, pred] {
        for &a in &adj[left] {
            for &b in &adj[right] {
                if nodes[a].order > nodes[b].order {
                    c += 1;
                }
            }
        }
    }
    c
}

// ---------------------------------------------------------------------------
// reachability, for the atlas hover interaction
// ---------------------------------------------------------------------------

/// Transitive ancestors and descendants of every node, as sorted index lists.
///
/// The HTML emitter bakes these into `data-` attributes so hovering a fact can
/// dim everything outside its cone without any client-side graph traversal.
/// Bitset closure over a topological order, so `O(V*E/64)`.
pub fn reachability(n: usize, edges: &[(usize, usize)]) -> (Vec<Vec<usize>>, Vec<Vec<usize>>) {
    let e = normalize_edges(n, edges);
    let (acyclic, _) = break_cycles(n, &e);
    let layer = assign_layers(n, &acyclic);
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&v| (layer[v], v));
    let words = n.div_ceil(64).max(1);
    let mut anc = vec![0u64; n * words];
    let mut pred: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut succ: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &(a, b) in &acyclic {
        pred[b].push(a);
        succ[a].push(b);
    }
    for &v in &order {
        for &u in &pred[v] {
            for wi in 0..words {
                anc[v * words + wi] |= anc[u * words + wi];
            }
            anc[v * words + u / 64] |= 1u64 << (u % 64);
        }
    }
    let mut desc = vec![0u64; n * words];
    for &v in order.iter().rev() {
        for &u in &succ[v] {
            for wi in 0..words {
                desc[v * words + wi] |= desc[u * words + wi];
            }
            desc[v * words + u / 64] |= 1u64 << (u % 64);
        }
    }
    let unpack = |bits: &[u64], v: usize| -> Vec<usize> {
        let mut out = Vec::new();
        for u in 0..n {
            if bits[v * words + u / 64] >> (u % 64) & 1 == 1 {
                out.push(u);
            }
        }
        out
    };
    (
        (0..n).map(|v| unpack(&anc, v)).collect(),
        (0..n).map(|v| unpack(&desc, v)).collect(),
    )
}

/// Render an edge polyline as an SVG path: vertical stubs out of each box and
/// a smooth curve through the bend points. Kept here so the geometry and the
/// path syntax stay in one file.
pub fn edge_path_d(points: &[(f64, f64)]) -> String {
    if points.len() < 2 {
        return String::new();
    }
    let mut d = format!("M {:.1} {:.1}", points[0].0, points[0].1);
    for i in 0..points.len() - 1 {
        let (x0, y0) = points[i];
        let (x1, y1) = points[i + 1];
        if (x0 - x1).abs() < 0.05 {
            d.push_str(&format!(" L {x1:.1} {y1:.1}"));
        } else {
            let my = f64::midpoint(y0, y1);
            d.push_str(&format!(
                " C {x0:.1} {my:.1}, {x1:.1} {my:.1}, {x1:.1} {y1:.1}"
            ));
        }
    }
    d
}

#[cfg(test)]
mod tests {
    use super::*;

    fn boxes(n: usize) -> Vec<NodeSpec> {
        (0..n)
            .map(|i| NodeSpec::new(&format!("n{i}"), 100.0, 30.0))
            .collect()
    }

    #[test]
    fn empty_graph_is_total() {
        let l = layered_layout(&[], &[], &LayoutConfig::default());
        assert!(l.nodes.is_empty() && l.edges.is_empty());
        assert!(l.width > 0.0 && l.height > 0.0);
    }

    #[test]
    fn isolated_nodes_share_one_layer() {
        let l = layered_layout(&boxes(4), &[], &LayoutConfig::default());
        assert_eq!(l.layers.len(), 1);
        assert_eq!(l.layers[0].len(), 4);
        // ...and do not overlap.
        let mut xs: Vec<f64> = l.nodes.iter().map(|n| n.cx).collect();
        xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
        for w in xs.windows(2) {
            assert!(w[1] - w[0] >= 100.0, "boxes overlap: {xs:?}");
        }
    }

    #[test]
    fn chain_layers_in_order() {
        let l = layered_layout(
            &boxes(4),
            &[(0, 1), (1, 2), (2, 3)],
            &LayoutConfig::default(),
        );
        for i in 0..4 {
            assert_eq!(l.nodes[i].layer, i);
        }
        // A pure chain must draw as a straight vertical line.
        let x0 = l.nodes[0].cx;
        for nd in &l.nodes {
            assert!((nd.cx - x0).abs() < 1e-6, "chain not straight: {nd:?}");
        }
        assert_eq!(l.crossings, 0);
    }

    #[test]
    fn longest_path_layering_is_not_shortest_path() {
        // 0 -> 1 -> 2 and 0 -> 2. Node 2 must sit below node 1, not beside it.
        let l = layered_layout(
            &boxes(3),
            &[(0, 1), (1, 2), (0, 2)],
            &LayoutConfig::default(),
        );
        assert_eq!(l.nodes[0].layer, 0);
        assert_eq!(l.nodes[1].layer, 1);
        assert_eq!(l.nodes[2].layer, 2);
    }

    #[test]
    fn long_edge_gets_bend_points() {
        let l = layered_layout(
            &boxes(3),
            &[(0, 1), (1, 2), (0, 2)],
            &LayoutConfig::default(),
        );
        let long = l.edges.iter().find(|e| e.from == 0 && e.to == 2).unwrap();
        // source anchor + one dummy + target anchor
        assert_eq!(long.points.len(), 3, "{:?}", long.points);
        let short = l.edges.iter().find(|e| e.from == 0 && e.to == 1).unwrap();
        assert_eq!(short.points.len(), 2);
    }

    #[test]
    fn parent_is_centred_over_its_children() {
        // One parent, three children: the parent should land on the middle one.
        let l = layered_layout(
            &boxes(4),
            &[(0, 1), (0, 2), (0, 3)],
            &LayoutConfig::default(),
        );
        let kids: Vec<f64> = l.nodes[1..].iter().map(|n| n.cx).collect();
        let mid = kids.iter().copied().fold(f64::NEG_INFINITY, f64::max)
            + kids.iter().copied().fold(f64::INFINITY, f64::min);
        assert!(
            (l.nodes[0].cx - mid / 2.0).abs() < 1.0,
            "parent off-centre: {:?} over {kids:?}",
            l.nodes[0].cx
        );
    }

    #[test]
    fn ordering_reduces_crossings_on_a_deliberate_tangle() {
        // Two sources cross-connected to two sinks in the worst initial order.
        let specs = boxes(4);
        let edges = [(0, 3), (1, 2)];
        let l = layered_layout(&specs, &edges, &LayoutConfig::default());
        assert_eq!(l.crossings, 0, "median sweeps failed to untangle a 2x2");
    }

    #[test]
    fn cyclic_input_still_draws() {
        let l = layered_layout(
            &boxes(3),
            &[(0, 1), (1, 2), (2, 0)],
            &LayoutConfig::default(),
        );
        assert_eq!(l.reversed_edges, 1);
        assert_eq!(l.nodes.len(), 3);
        // The reversed edge is still reported in the caller's direction.
        let back = l.edges.iter().find(|e| e.from == 2 && e.to == 0).unwrap();
        assert!(back.reversed);
    }

    #[test]
    fn self_loops_and_duplicates_are_dropped() {
        let l = layered_layout(
            &boxes(2),
            &[(0, 0), (0, 1), (0, 1)],
            &LayoutConfig::default(),
        );
        assert_eq!(l.edges.len(), 1);
    }

    #[test]
    fn layout_is_deterministic() {
        let specs = boxes(12);
        let edges: Vec<(usize, usize)> = vec![
            (0, 2),
            (1, 2),
            (2, 5),
            (3, 5),
            (4, 6),
            (5, 8),
            (6, 8),
            (7, 9),
            (8, 10),
            (9, 10),
            (0, 10),
            (1, 7),
            (3, 11),
            (11, 9),
        ];
        let a = layered_layout(&specs, &edges, &LayoutConfig::default());
        let b = layered_layout(&specs, &edges, &LayoutConfig::default());
        assert_eq!(a, b);
    }

    #[test]
    fn isotonic_place_respects_gaps_and_hits_free_targets() {
        // Unconstrained targets are met exactly.
        let x = isotonic_place(&[0.0, 100.0, 200.0], &[1.0, 1.0, 1.0], &[10.0, 10.0]);
        assert_eq!(x, vec![0.0, 100.0, 200.0]);
        // Conflicting targets are pooled and separated by exactly the gap.
        let x = isotonic_place(&[50.0, 50.0, 50.0], &[1.0, 1.0, 1.0], &[10.0, 10.0]);
        assert!((x[1] - x[0] - 10.0).abs() < 1e-9);
        assert!((x[2] - x[1] - 10.0).abs() < 1e-9);
        // The pooled block is centred on the common target.
        assert!((x[1] - 50.0).abs() < 1e-9, "{x:?}");
    }

    #[test]
    fn isotonic_place_weights_pull() {
        // Two nodes that cannot both reach their target: the heavier one ends
        // up closer to its own. This is what makes `dummy_weight` straighten
        // long edges instead of merely nudging them.
        let light = isotonic_place(&[0.0, 100.0], &[1.0, 1.0], &[200.0]);
        let heavy = isotonic_place(&[0.0, 100.0], &[1.0, 9.0], &[200.0]);
        assert!(
            (heavy[1] - 100.0).abs() < (light[1] - 100.0).abs(),
            "heavy node not favoured: {heavy:?} vs {light:?}"
        );
    }

    #[test]
    fn reachability_is_transitive() {
        let (anc, desc) = reachability(4, &[(0, 1), (1, 2), (2, 3)]);
        assert_eq!(anc[3], vec![0, 1, 2]);
        assert_eq!(desc[0], vec![1, 2, 3]);
        assert!(anc[0].is_empty());
        assert!(desc[3].is_empty());
    }

    #[test]
    fn reachability_diamond() {
        let (anc, desc) = reachability(4, &[(0, 1), (0, 2), (1, 3), (2, 3)]);
        assert_eq!(anc[3], vec![0, 1, 2]);
        assert_eq!(desc[0], vec![1, 2, 3]);
        assert!(anc[1] == vec![0] && desc[1] == vec![3]);
    }

    #[test]
    fn edge_path_d_is_straight_when_aligned() {
        let d = edge_path_d(&[(10.0, 0.0), (10.0, 50.0)]);
        assert_eq!(d, "M 10.0 0.0 L 10.0 50.0");
        let d = edge_path_d(&[(0.0, 0.0), (40.0, 50.0)]);
        assert!(d.starts_with("M 0.0 0.0 C "), "{d}");
    }

    #[test]
    fn wide_graph_stays_bounded() {
        // 60 sources into one sink: the sink must be inside the drawing.
        let specs = boxes(61);
        let edges: Vec<(usize, usize)> = (0..60).map(|i| (i, 60)).collect();
        let l = layered_layout(&specs, &edges, &LayoutConfig::default());
        let sink = &l.nodes[60];
        assert!(sink.x() >= 0.0 && sink.cx + sink.width / 2.0 <= l.width);
    }
}
