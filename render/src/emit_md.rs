//! The Markdown emitter: CommonMark plus the `<details>` fold GitHub renders.
//!
//! Total and dumb, per the contract in the crate documentation. Everything this
//! file does is string formatting; it reads no file, computes no status and has
//! no error path.
//!
//! Verbosity: `Essential` renders in the body, `Detail` renders inside
//! `<details><summary>`, `Archive` renders as a one-line link and its content
//! does not appear. Badges are the plain uppercase token in square brackets --
//! `[CHECKED]` -- because plain text survives every Markdown consumer that
//! matters here (GitHub, a pager, a diff) and because
//! `render/tests/cross_format.rs` recovers claims from these bytes.

use std::fmt::Write as _;

use crate::assemble::{
    ResolvedBlock, ResolvedDocument, ResolvedEvidence, ResolvedFormal, ResolvedKind, ResolvedStep,
};
use crate::ir::{FigureSpec, RenderHint, RichText, StatementField, Verbosity};
use crate::{EmitOutput, Emitter};

/// Renders a resolved document as CommonMark.
#[derive(Debug, Clone, Copy, Default)]
pub struct MarkdownEmitter;

impl Emitter for MarkdownEmitter {
    fn format_name(&self) -> &'static str {
        "md"
    }

    fn primary_extension(&self) -> &'static str {
        "md"
    }

    fn emit(&self, doc: &ResolvedDocument) -> EmitOutput {
        let mut out = EmitOutput::default();
        let mut s = String::new();

        let _ = writeln!(s, "# {}", doc.title);
        s.push('\n');
        if let Some(sub) = &doc.subtitle {
            let _ = writeln!(s, "*{sub}*\n");
        }
        if !doc.authors.is_empty() {
            let _ = writeln!(s, "Authors: {}\n", doc.authors.join(", "));
        }
        if let Some(a) = &doc.abstract_text {
            for line in a.text.lines() {
                let _ = writeln!(s, "> {line}");
            }
            s.push('\n');
        }

        for block in &doc.blocks {
            let body = render_block(doc, block, &mut out);
            match block.tag {
                Verbosity::Essential => {
                    s.push_str(&body);
                }
                Verbosity::Detail => {
                    let _ = writeln!(s, "<details>");
                    let _ = writeln!(s, "<summary>{}</summary>\n", fold_summary(block));
                    s.push_str(&body);
                    let _ = writeln!(s, "</details>\n");
                }
                Verbosity::Archive => {
                    let target = archive_target(block);
                    match target {
                        Some(path) => {
                            let _ = writeln!(
                                s,
                                "*Archived -- [{}]({}) (not shown here).*\n",
                                fold_summary(block),
                                link(doc, &path)
                            );
                        }
                        None => {
                            let _ = writeln!(
                                s,
                                "*Archived -- {} (not shown here).*\n",
                                fold_summary(block)
                            );
                        }
                    }
                }
            }
        }

        let _ = writeln!(s, "---\n");
        let _ = writeln!(
            s,
            "Rendered from Doc-IR by `axeyum-render`. Epoch {} ({}, source `{}`){}.",
            doc.epoch_unix,
            iso_utc(doc.epoch_unix),
            doc.epoch_source,
            match &doc.commit {
                Some(c) => format!(", commit `{c}`"),
                None => String::new(),
            }
        );

        out.primary = s;
        out
    }
}

#[allow(clippy::too_many_lines)] // one arm per block kind; splitting hides the totality
fn render_block(doc: &ResolvedDocument, block: &ResolvedBlock, out: &mut EmitOutput) -> String {
    let mut s = String::new();
    match &block.kind {
        ResolvedKind::Prose {
            text,
            heading_level,
            ..
        } => match heading_level {
            Some(level) => {
                let hashes = "#".repeat((*level).clamp(1, 6) as usize);
                let _ = writeln!(s, "{hashes} {}\n", text.text);
            }
            None => {
                let _ = writeln!(s, "{}\n", text.text);
            }
        },
        ResolvedKind::Claim {
            label,
            statement,
            status,
            evidence,
            note,
            ..
        } => {
            // The cross-format anchor line. `render/tests/cross_format.rs`
            // parses exactly this shape out of the emitted bytes.
            let _ = writeln!(s, "**Claim -- {label}** [{}]\n", status.badge());
            let _ = writeln!(s, "{}\n", statement.text);
            if let Some(from) = &statement.from_ref {
                let _ = writeln!(s, "Statement of record: `{from}`\n");
            }
            for e in evidence {
                s.push_str(&evidence_line(e));
            }
            s.push('\n');
            if let Some(n) = note {
                let _ = writeln!(s, "{}\n", n.text);
            }
        }
        ResolvedKind::Statement { show, formal, note } => {
            s.push_str(&statement_block(show, formal));
            if let Some(n) = note {
                let _ = writeln!(s, "{}\n", n.text);
            }
        }
        ResolvedKind::Steps { caption, steps } => {
            if let Some(c) = caption {
                let _ = writeln!(s, "{}\n", c.text);
            }
            for step in steps {
                s.push_str(&step_line(step));
            }
            s.push('\n');
        }
        ResolvedKind::Table {
            caption,
            columns,
            rows,
            source,
        } => {
            if let Some(c) = caption {
                let _ = writeln!(s, "{}\n", c.text);
            }
            let headers: Vec<String> = columns.iter().map(|c| cell(&c.header)).collect();
            let _ = writeln!(s, "| {} |", headers.join(" | "));
            let rules: Vec<&str> = columns
                .iter()
                .map(|c| match c.align {
                    Some(crate::ir::Align::Right) => "---:",
                    Some(crate::ir::Align::Center) => ":---:",
                    _ => "---",
                })
                .collect();
            let _ = writeln!(s, "| {} |", rules.join(" | "));
            for row in rows {
                let cells: Vec<String> = row.iter().map(|c| cell(c)).collect();
                let _ = writeln!(s, "| {} |", cells.join(" | "));
            }
            let _ = writeln!(
                s,
                "\nSource: `{}` (exit {}), {} input(s) hashed.\n",
                source.command,
                source.exit_status,
                source.inputs.len()
            );
        }
        ResolvedKind::Certificate {
            cert_kind,
            summary,
            artifact_refs,
            replay,
            evidence,
        } => {
            let _ = writeln!(s, "**Certificate -- {}**\n", cert_kind.label());
            let _ = writeln!(s, "{}\n", summary.text);
            if !artifact_refs.is_empty() {
                let _ = writeln!(s, "Artifacts:\n");
                for a in artifact_refs {
                    let label = a.label.clone().unwrap_or_else(|| a.path.clone());
                    let _ = writeln!(s, "- [{}]({})", label, link(doc, &a.path));
                }
                s.push('\n');
            }
            let _ = writeln!(s, "Replay:\n");
            let _ = writeln!(s, "```sh\n{}\n```\n", replay.line);
            for e in evidence {
                s.push_str(&evidence_line(e));
            }
            if !evidence.is_empty() {
                s.push('\n');
            }
        }
        ResolvedKind::Figure { caption, alt, spec } => {
            let alt = alt.clone().unwrap_or_else(|| "figure".to_string());
            match spec {
                FigureSpec::Svg { svg, src, .. } => {
                    if let Some(src) = src {
                        let _ = writeln!(s, "![{alt}]({})\n", link(doc, src));
                    } else if let Some(svg) = svg {
                        // Markdown consumers strip inline SVG, so it becomes a
                        // side file and a link -- the same bytes, still one
                        // source of truth.
                        let name = format!("{}-{}.svg", doc.doc_id, block.id);
                        out.aux.insert(name.clone(), svg.clone());
                        let _ = writeln!(s, "![{alt}]({name})\n");
                    }
                }
                other => {
                    // No layout engine lives in this emitter (that is DESIGN's
                    // `layout.rs`), so a data figure renders as its data. Honest
                    // and total; never an apology.
                    let _ = writeln!(s, "*Figure ({alt}) -- data:*\n");
                    let _ = writeln!(s, "```json\n{}\n```\n", figure_data(other));
                }
            }
            if let Some(c) = caption {
                let _ = writeln!(s, "*{}*\n", c.text);
            }
        }
        ResolvedKind::Include {
            path,
            render_hint,
            language,
            caption,
            inline,
            bytes,
        } => {
            if let Some(c) = caption {
                let _ = writeln!(s, "{}\n", c.text);
            }
            match (render_hint, inline) {
                (RenderHint::Image, _) => {
                    let _ = writeln!(s, "![{path}]({})\n", link(doc, path));
                }
                (RenderHint::Code | RenderHint::Json, Some(body)) => {
                    let lang = match render_hint {
                        RenderHint::Json => "json",
                        _ => language.as_deref().unwrap_or(""),
                    };
                    let _ = writeln!(s, "```{lang}\n{}\n```\n", body.trim_end());
                }
                (RenderHint::Text, Some(body)) => {
                    let _ = writeln!(s, "```\n{}\n```\n", body.trim_end());
                }
                _ => {
                    let _ = writeln!(s, "- [{path}]({}) ({bytes} bytes)\n", link(doc, path));
                }
            }
        }
    }
    s
}

fn statement_block(show: &[StatementField], f: &ResolvedFormal) -> String {
    let mut s = String::new();
    for field in show {
        match field {
            StatementField::Title => {
                let _ = writeln!(s, "**{}** (`{}`)\n", f.title, f.key);
            }
            StatementField::Prose => {
                let _ = writeln!(s, "{}\n", f.prose);
            }
            StatementField::Formal => {
                let _ = writeln!(s, "```{}\n{}\n```\n", f.language, f.formal);
            }
            StatementField::Status => {
                let _ = writeln!(
                    s,
                    "Status: established here `{}`; externally `{}`.\n",
                    f.epistemic_status,
                    f.external_status
                        .clone()
                        .unwrap_or_else(|| "not recorded".to_string())
                );
            }
            StatementField::AxiomFootprint => match &f.axiom_footprint {
                Some(list) if list.is_empty() => {
                    let _ = writeln!(s, "Axiom footprint: empty (axiom-free on this route).\n");
                }
                Some(list) => {
                    let _ = writeln!(s, "Axiom footprint ({}):\n", list.len());
                    for a in list {
                        let _ = writeln!(s, "- `{a}`");
                    }
                    s.push('\n');
                }
                None => {
                    let _ = writeln!(s, "Axiom footprint: not recorded.\n");
                }
            },
            StatementField::ProofRoute => {
                let _ = writeln!(
                    s,
                    "Proof route: `{}`.\n",
                    f.proof_route.clone().unwrap_or_else(|| "none".to_string())
                );
            }
            StatementField::DependsOn => {
                if f.depends_on.is_empty() {
                    let _ = writeln!(s, "Depends on: nothing (foundational).\n");
                } else {
                    let joined: Vec<String> =
                        f.depends_on.iter().map(|d| format!("`{d}`")).collect();
                    let _ = writeln!(s, "Depends on: {}.\n", joined.join(", "));
                }
            }
            StatementField::EvidenceCount => {
                let _ = writeln!(s, "Evidence rows in the ledger: {}.\n", f.evidence_count);
            }
        }
    }
    s
}

fn evidence_line(e: &ResolvedEvidence) -> String {
    let mut s = String::new();
    let _ = writeln!(
        s,
        "- Evidence `{}` ({}): {} -- `{}` exited {}, {} input(s) re-hashed.",
        e.record_id,
        e.role.label(),
        e.summary,
        e.command,
        e.exit_status,
        e.inputs_verified
    );
    if let (Some(key), Some(st)) = (&e.claim_key, &e.claim_status) {
        let _ = writeln!(
            s,
            "  - run claim `{key}` [{}]: {}",
            st.badge(),
            e.claim_statement.clone().unwrap_or_default()
        );
    }
    if let Some(r) = &e.replay {
        let _ = writeln!(s, "  - replay: `{}`", r.line);
    }
    s
}

fn step_line(step: &ResolvedStep) -> String {
    let mut s = String::new();
    let _ = writeln!(s, "{}. **{}**", step.index, step.op);
    if let Some(i) = &step.input {
        let _ = writeln!(s, "   - in: {}", i.text);
    }
    let _ = writeln!(s, "   - out: {}", step.output.text);
    if let Some(j) = &step.justification {
        let _ = writeln!(s, "   - by: `{}` ({})", j.key, j.title);
    }
    if let Some(n) = &step.note {
        let _ = writeln!(s, "   - note: {}", n.text);
    }
    s
}

fn fold_summary(block: &ResolvedBlock) -> String {
    if let Some(t) = &block.title {
        return t.clone();
    }
    match &block.kind {
        ResolvedKind::Claim { label, .. } => format!("Claim -- {label}"),
        ResolvedKind::Statement { formal, .. } => format!("Statement -- {}", formal.title),
        ResolvedKind::Steps { .. } => "Derivation".to_string(),
        ResolvedKind::Table { .. } => "Table".to_string(),
        ResolvedKind::Certificate { cert_kind, .. } => {
            format!("Certificate -- {}", cert_kind.label())
        }
        ResolvedKind::Figure { .. } => "Figure".to_string(),
        ResolvedKind::Include { path, .. } => path.clone(),
        ResolvedKind::Prose { .. } => "Detail".to_string(),
    }
}

/// The file an `archive`-tier block links to, when it has one.
fn archive_target(block: &ResolvedBlock) -> Option<String> {
    match &block.kind {
        ResolvedKind::Include { path, .. } => Some(path.clone()),
        ResolvedKind::Figure {
            spec: FigureSpec::Svg { src: Some(src), .. },
            ..
        } => Some(src.clone()),
        ResolvedKind::Certificate { artifact_refs, .. } => {
            artifact_refs.first().map(|a| a.path.clone())
        }
        _ => block
            .provenance
            .as_ref()
            .and_then(|p| p.inputs.first())
            .map(|i| i.path.clone()),
    }
}

/// A link to a repository path, pinned to the commit when one is recorded.
fn link(doc: &ResolvedDocument, path: &str) -> String {
    match (&doc.repo_url, &doc.commit) {
        (Some(url), Some(commit)) => format!("{}/blob/{commit}/{path}", url.trim_end_matches('/')),
        _ => path.to_string(),
    }
}

/// Escape the one character that breaks a GFM table row.
fn cell(s: &str) -> String {
    s.replace('|', "\\|")
}

/// A figure's data, as deterministic JSON.
fn figure_data(spec: &FigureSpec) -> String {
    serde_json::to_string_pretty(&serde_json::to_value(spec).unwrap_or(serde_json::Value::Null))
        .unwrap_or_else(|_| "{}".to_string())
}

/// `RichText` is rendered from `text` in this emitter; the helper exists so the
/// choice is stated once rather than assumed at nine call sites.
#[allow(dead_code)]
fn rich(r: &RichText) -> &str {
    &r.text
}

/// ISO-8601 UTC from a Unix timestamp, without a date library and without a
/// clock. Civil-from-days after Howard Hinnant's `chrono`-compatible algorithm.
fn iso_utc(unix: i64) -> String {
    let days = unix.div_euclid(86_400);
    let secs = unix.rem_euclid(86_400);
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!(
        "{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}Z",
        secs / 3_600,
        (secs % 3_600) / 60,
        secs % 60
    )
}

#[cfg(test)]
mod tests {
    use super::iso_utc;

    #[test]
    fn iso_utc_matches_known_instants() {
        assert_eq!(iso_utc(0), "1970-01-01T00:00:00Z");
        assert_eq!(iso_utc(1_000_000_000), "2001-09-09T01:46:40Z");
        // 2026-08-21T12:00:00Z, cross-checked against `date -u -d @1787313600`.
        assert_eq!(iso_utc(1_787_313_600), "2026-08-21T12:00:00Z");
    }
}
