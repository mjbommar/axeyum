//! Throwaway probe: how big is the whole `creal` carrier rendered as Lean
//! source, and does pinned Lean accept it? Deleted before the lane commits.
use std::collections::BTreeSet;

use axeyum_lean_kernel::{
    Declaration, ExprId, ExprNode, Kernel, LevelNode, NameId, build_creal_prelude, on_a_deep_stack,
};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let out_dir = args.get(1).cloned().expect("out dir");
    let as_def = args.iter().any(|a| a == "--def");
    on_a_deep_stack(move || {
        let t0 = std::time::Instant::now();
        let mut kernel = Kernel::new();
        build_creal_prelude(&mut kernel).expect("creal builds");
        eprintln!("build: {:.1}s", t0.elapsed().as_secs_f64());
        let roots: Vec<NameId> = kernel.environment().iter().map(|(n, _)| *n).collect();
        eprintln!("declarations={}", roots.len());
        let thms: Vec<(NameId, ExprId)> = kernel
            .environment()
            .iter()
            .filter_map(|(n, d)| match d {
                Declaration::Theorem { ty, .. } => Some((*n, *ty)),
                _ => None,
            })
            .collect();
        let mut type_valued: BTreeSet<String> = BTreeSet::new();
        for (n, ty) in thms {
            let ok = kernel
                .infer(ty)
                .ok()
                .map(|s| {
                    let s = kernel.whnf(s);
                    match kernel.expr_node(s) {
                        ExprNode::Sort(l) => matches!(kernel.level_node(*l), LevelNode::Zero),
                        _ => false,
                    }
                })
                .unwrap_or(false);
            if !ok {
                type_valued.insert(kernel.display_name(n).to_string());
            }
        }
        eprintln!("type_valued={}", type_valued.len());
        kernel.set_render_proofs_as_def(as_def);
        let t1 = std::time::Instant::now();
        let m = kernel.render_lean_prelude_module("AxeyumCrealProbe", &roots);
        eprintln!(
            "render: {:.1}s bytes={} provided={}",
            t1.elapsed().as_secs_f64(),
            m.source().len(),
            m.provided_len()
        );
        std::fs::create_dir_all(&out_dir).unwrap();
        std::fs::write(format!("{out_dir}/{}", m.file_name()), m.source()).unwrap();
        eprintln!("wrote {out_dir}/{}", m.file_name());
    });
}
