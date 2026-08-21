//! Every link between pages of the emitted site resolves.
//!
//! WHY THIS TEST IS THE PRICE OF THE LINKS EXISTING. Until 2026-08-21 a fact
//! atlas node carrying `href: "cards/F-x.doc.json"` was slugged into an in-page
//! anchor that no page contained, so 152 boxes on the atlas looked clickable and
//! did nothing -- the reader review's gripe 3, and a dead link that looks live is
//! exactly the class of quiet lie this strand exists to stop. Making them real
//! links means the self-containment lint now accepts a relative `.html` href,
//! which is a hole unless SOMETHING checks the other end. This is that something.
//!
//! It works on the EMITTED BYTES, like the self-containment lint and the
//! `<merror>` scan, because that catches every producer and every call site at
//! once instead of one convention at a time.
//!
//! What it asserts, over the whole real corpus (the atlas, both pilots, and all
//! 324 fact cards):
//!
//! 1. every relative `href` resolves to a file that was emitted;
//! 2. every `#fragment` on such an href names an `id` that exists in the target
//!    page (a card's "up" link points at the atlas figure for its own connected
//!    component, and that numbering is recomputed in the producer -- if the two
//!    ever drift, the fragment stops resolving);
//! 3. the sweep saw a nonzero number of links, so a corpus that stopped emitting
//!    them cannot pass by checking nothing;
//! 4. the DEP-GRAPH nodes specifically link out: a page whose graph lost its
//!    anchors would still satisfy (1)-(3) trivially.
//!
//! And it demonstrates it can fail: `a_dangling_card_link_is_caught` points one
//! node at a card that does not exist and requires the scan to report it.

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use axeyum_render::assemble::{AssembleOptions, Assembler};
use axeyum_render::{Emitter, emit_html::HtmlEmitter};

/// `render/examples-input/facts`.
fn facts_input() -> PathBuf {
    common::package_root().join("examples-input/facts")
}

/// Render one manifest to HTML, named after its SOURCE file -- the naming rule
/// that makes cross-references resolve (see `NameBy` in `main.rs`).
fn render_to(manifest: &Path, out_dir: &Path) -> String {
    let mut opts = AssembleOptions::new(
        common::repo_root(),
        manifest
            .parent()
            .expect("manifest has a parent")
            .to_path_buf(),
    );
    opts.facts_dir = common::repo_root().join("artifacts/facts");
    let doc = Assembler::new(opts)
        .assemble_path(manifest)
        .unwrap_or_else(|e| panic!("{} does not assemble: {e}", manifest.display()));
    let stem = manifest
        .file_name()
        .and_then(|f| f.to_str())
        .and_then(|f| f.strip_suffix(".doc.json"))
        .expect("a *.doc.json manifest");
    std::fs::create_dir_all(out_dir).expect("out dir creatable");
    let path = out_dir.join(format!("{stem}.html"));
    let html = HtmlEmitter.emit(&doc).primary;
    std::fs::write(&path, &html).expect("page writable");
    html
}

/// Render the whole facts site into `root`, laid out the way
/// `render/build-outputs.sh` lays out `render/out/`.
///
/// Returns the number of pages written.
fn render_site(root: &Path) -> usize {
    let input = facts_input();
    let mut n = 0usize;
    for name in [
        "facts-atlas.doc.json",
        "facts-pilot.doc.json",
        "facts-pilot-arith.doc.json",
    ] {
        render_to(&input.join(name), root);
        n += 1;
    }
    let cards_in = input.join("cards");
    let cards_out = root.join("cards");
    let mut manifests: Vec<PathBuf> = std::fs::read_dir(&cards_in)
        .expect("cards directory readable")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.file_name()
                .and_then(|f| f.to_str())
                .is_some_and(|f| f.ends_with(".doc.json"))
        })
        .collect();
    manifests.sort();
    assert!(
        manifests.len() > 300,
        "expected the whole card corpus, found {}",
        manifests.len()
    );
    for m in &manifests {
        render_to(m, &cards_out);
        n += 1;
    }
    n
}

/// Every `href` in a page that is neither a fragment, a `data:` URI, nor an
/// absolute URL -- i.e. every link to another page of the site.
fn relative_hrefs(html: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = html;
    while let Some(at) = rest.find(" href=\"") {
        rest = &rest[at + 7..];
        let Some(end) = rest.find('"') else { break };
        let value = &rest[..end];
        rest = &rest[end..];
        if value.is_empty()
            || value.starts_with('#')
            || value.starts_with("data:")
            || value.starts_with("mailto:")
            || value.starts_with("http://")
            || value.starts_with("https://")
        {
            continue;
        }
        out.push(value.to_string());
    }
    out
}

/// The `id` attributes a page defines.
fn ids(html: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut rest = html;
    while let Some(at) = rest.find("id=\"") {
        rest = &rest[at + 4..];
        let Some(end) = rest.find('"') else { break };
        out.insert(rest[..end].to_string());
        rest = &rest[end..];
    }
    out
}

/// Resolve `href` against the page it appears on, without touching the disk.
///
/// Deliberately hand-rolled rather than `Path::join` + `canonicalize`: the
/// point is to resolve the link the way a BROWSER would, from the page's own
/// directory, and `canonicalize` would silently follow whatever exists.
fn resolve(page: &Path, href: &str) -> Option<(PathBuf, Option<String>)> {
    let (path, fragment) = match href.split_once('#') {
        Some((p, f)) => (p, Some(f.to_string())),
        None => (href, None),
    };
    let mut here = page.parent()?.to_path_buf();
    for part in path.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                here.pop();
            }
            other => here.push(other),
        }
    }
    Some((here, fragment))
}

/// One finding: a link that does not resolve.
#[derive(Debug)]
struct Broken {
    /// Read through `Debug` in the failure message, which the dead-code pass
    /// does not follow. Kept because a finding without the page it is on is
    /// not actionable over a 328-page site.
    #[allow(dead_code)]
    page: String,
    href: String,
    why: &'static str,
}

/// The whole sweep. Returns `(findings, links seen, pages seen)`.
fn sweep(root: &Path) -> (Vec<Broken>, usize, usize) {
    let mut pages: Vec<PathBuf> = Vec::new();
    collect_html(root, &mut pages);
    pages.sort();
    let mut cache: BTreeMap<PathBuf, BTreeSet<String>> = BTreeMap::new();
    let mut findings = Vec::new();
    let mut links = 0usize;
    for page in &pages {
        let html = std::fs::read_to_string(page).expect("page readable");
        for href in relative_hrefs(&html) {
            links += 1;
            let Some((target, fragment)) = resolve(page, &href) else {
                findings.push(Broken {
                    page: page.display().to_string(),
                    href,
                    why: "href does not resolve to a path",
                });
                continue;
            };
            if !target.is_file() {
                findings.push(Broken {
                    page: page.display().to_string(),
                    href,
                    why: "target file was not emitted",
                });
                continue;
            }
            if let Some(f) = fragment {
                let known = cache.entry(target.clone()).or_insert_with(|| {
                    ids(&std::fs::read_to_string(&target).expect("target readable"))
                });
                if !known.contains(&f) {
                    findings.push(Broken {
                        page: page.display().to_string(),
                        href,
                        why: "target page has no element with that id",
                    });
                }
            }
        }
    }
    (findings, links, pages.len())
}

fn collect_html(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect_html(&p, out);
        } else if p.extension().is_some_and(|x| x == "html") {
            out.push(p);
        }
    }
}

#[test]
fn every_link_in_the_emitted_site_resolves() {
    let root = common::scratch("link-integrity");
    let pages = render_site(&root);
    let (findings, links, seen) = sweep(&root);
    assert_eq!(seen, pages, "every emitted page was swept");
    // A sweep that found no links is a sweep that proves nothing. The atlas
    // alone carries one per node plus one per index row.
    assert!(
        links > 1000,
        "only {links} relative link(s) over {pages} pages -- the corpus stopped emitting them"
    );
    assert!(
        findings.is_empty(),
        "{} broken link(s) of {links}: {:#?}",
        findings.len(),
        &findings[..findings.len().min(10)]
    );
}

#[test]
fn dep_graph_nodes_link_out_of_the_page() {
    // (1)-(3) above are satisfiable by a site whose GRAPHS link nowhere and
    // whose only links are in tables, which is exactly the state gripe 3
    // described. So the graph's own anchors are asserted separately.
    let root = common::scratch("link-integrity-graph");
    render_to(&facts_input().join("facts-atlas.doc.json"), &root);
    let html = std::fs::read_to_string(root.join("facts-atlas.html")).expect("atlas readable");
    let anchored = html
        .matches("<a class=\"gnode-link\" href=\"cards/")
        .count();
    assert!(
        anchored > 100,
        "only {anchored} dep-graph node(s) link to a card; the atlas has 151 in components"
    );
    // ...and none of them left the old dead in-page form behind.
    assert!(
        !html.contains("data-href=\"cards-"),
        "a node href was slugged into an in-page anchor that no page contains"
    );
}

#[test]
fn a_dangling_card_link_is_caught() {
    // THE PROOF THAT THE SWEEP CAN FAIL. One node of one card is pointed at a
    // document that does not exist; nothing else changes. A copy is mutated in
    // a scratch directory, never the shared checkout.
    let root = common::scratch("link-integrity-negative");
    let src = facts_input().join("cards/F-nat-add-comm.doc.json");
    let mut doc: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&src).expect("card readable")).expect("card parses");
    let mut mutated = false;
    for b in doc["blocks"].as_array_mut().expect("blocks") {
        if b["kind"]["type"] == "figure"
            && let Some(nodes) = b["kind"]["spec"]["nodes"].as_array_mut()
        {
            nodes[0]["href"] = serde_json::json!("F-there-is-no-such-fact.doc.json");
            mutated = true;
        }
    }
    assert!(mutated, "the card fixture has no dep-graph node to point");

    let cards = root.join("cards");
    std::fs::create_dir_all(&cards).expect("scratch cards");
    let manifest = cards.join("F-nat-add-comm.doc.json");
    common::write_json(&manifest, &doc);
    render_to(&manifest, &cards);

    let (findings, links, _) = sweep(&root);
    assert!(links > 0, "the mutated page emitted no links at all");
    assert!(
        findings
            .iter()
            .any(|f| f.href.contains("F-there-is-no-such-fact")
                && f.why == "target file was not emitted"),
        "the sweep did not report the dangling link: {findings:#?}"
    );
}

#[test]
fn a_dangling_fragment_is_caught() {
    // The second half of the control: the FILE exists and the anchor inside it
    // does not. Without this, a card's "up" link could point at a component
    // figure the atlas stopped numbering that way and nothing would notice.
    let root = common::scratch("link-integrity-fragment");
    let src = facts_input().join("cards/F-nat-add-comm.doc.json");
    let mut doc: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&src).expect("card readable")).expect("card parses");
    doc["meta"]["nav"] = serde_json::json!([
        { "label": "Fact atlas", "href": "../facts-atlas.doc.json#dep-graph-c99", "rel": "up" }
    ]);
    render_to(&facts_input().join("facts-atlas.doc.json"), &root);
    let cards = root.join("cards");
    std::fs::create_dir_all(&cards).expect("scratch cards");
    let manifest = cards.join("F-nat-add-comm.doc.json");
    common::write_json(&manifest, &doc);
    render_to(&manifest, &cards);

    let (findings, _, _) = sweep(&root);
    assert!(
        findings
            .iter()
            .any(|f| f.why == "target page has no element with that id"),
        "the sweep did not report the dangling fragment: {findings:#?}"
    );
}

#[test]
fn an_emitted_card_is_still_self_contained() {
    // THE WIDENED LINT, EXERCISED ON REAL BYTES. `is_sibling_page` in
    // `emit_html.rs` is what lets a page carry `href="F-nat-succ-add.html"`;
    // delete it and this test dies, which is the point of asserting it over an
    // emitted card rather than over a hand-written fragment.
    let root = common::scratch("link-integrity-lint");
    let html = render_to(
        &facts_input().join("cards/F-nat-add-comm.doc.json"),
        &root.join("cards"),
    );
    assert!(
        html.contains(".html\""),
        "the card carries no sibling-page link, so this test would pass vacuously"
    );
    let findings = axeyum_render::emit_html::lint_self_contained(&html);
    assert!(findings.is_empty(), "{findings:#?}");

    // ...and the rule it was widened from still bites. One external image, one
    // finding: accepting a relative page link must not have accepted a fetch.
    let tampered = html.replace("<main", "<img src=\"https://evil.example/x.png\"><main");
    assert!(
        !axeyum_render::emit_html::lint_self_contained(&tampered).is_empty(),
        "the lint accepted an external image on a page that carries sibling links"
    );
}
