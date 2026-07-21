use super::{
    ArrayDefs, Assignment, CheckResult, HashSet, Instant, LastExtReplay, MAX_DIFF_SKOLEMS,
    MAX_ROW_ROUNDS, ReplayTargets, RowCtx, RowKind, SolverBackend, SolverConfig, SolverError,
    SymbolId, TermArena, TermId, UnknownReason, Value, check_row_cegar, check_scalar_abstraction,
    complete_assignment, config_with_remaining_deadline, ext_unknown, indices_equal, past_deadline,
    project_replay_ext, read_indices_for, read_terms_differ, replay_last_ext_candidate,
    results_differ, row_axiom_lemma, row_violated, select_congruence_lemma,
};

#[derive(Clone, Copy)]
struct ExtProgress<'a> {
    round: usize,
    ctx: &'a RowCtx,
    row_lemmas: usize,
    cong_lemmas: usize,
    diff_skolems: usize,
    working_assertions: usize,
}

impl ExtProgress<'_> {
    fn fields(self) -> String {
        format!(
            "round={}, sites={}, array_eq_atoms={}, row_lemmas={}, cong_lemmas={}, \
             diff_skolems={}, working_assertions={}",
            self.round,
            self.ctx.sites.len(),
            self.ctx.eq_atoms.len(),
            self.row_lemmas,
            self.cong_lemmas,
            self.diff_skolems,
            self.working_assertions
        )
    }
}

fn ext_unknown_with_progress_note(
    detail: &str,
    progress: ExtProgress<'_>,
    note: Option<String>,
) -> CheckResult {
    let fields = match note {
        Some(note) => format!("{}, {note}", progress.fields()),
        None => progress.fields(),
    };
    ext_unknown(format!("{detail} ({fields})"))
}

fn ext_contextual_unknown_note(
    context: &str,
    progress: ExtProgress<'_>,
    reason: &UnknownReason,
    note: Option<String>,
) -> CheckResult {
    let fields = match note {
        Some(note) => format!("{}, {note}", progress.fields()),
        None => progress.fields(),
    };
    CheckResult::Unknown(UnknownReason {
        kind: reason.kind,
        detail: format!("{context} ({fields}): {}", reason.detail),
    })
}

/// Decides a `QF_ABV` query carrying a **true array (dis)equality** — an array
/// equality `a = b` (or its negation) between two array terms *neither* of which
/// is an inlinable variable definition — via **lazy extensionality** (CEGAR):
///
/// * Each array `Op::Eq` atom `a = b` is abstracted to a fresh `Bool` flag.
///   Every `select(…)` is abstracted to a fresh `BitVec` site exactly as in the
///   lazy-ROW path, so ROW / read-over-read congruence are still enforced.
/// * On a candidate model, for each atom: when the flag is **true**, the
///   select-congruence lemma `flag => select(a,i) = select(b,i)` is added for any
///   already-materialised read index `i` that the model leaves inconsistent; when
///   the flag is **false** (`a != b`), a fresh **diff-skolem** index `k` is
///   introduced once and the witness lemma `!flag => select(a,k) != select(b,k)`
///   is added (a concrete index where the arrays differ).
/// * The relaxation's `unsat` transfers (strictly fewer constraints); a
///   refinement-consistent candidate is **projected and replayed** against the
///   *original* assertions — including the array (dis)equalities, re-derived
///   extensionally from the reconstructed array values — and accepted only if it
///   genuinely satisfies them, else `unknown`.
///
/// Strictly additive: any query the eager / lazy-ROW paths already decide reaches
/// this function only after they refuse, so it never changes a decided verdict.
/// Bounded by `MAX_ROW_ROUNDS`, `MAX_ROW_SITES`, `MAX_DIFF_SKOLEMS`, and the
/// optional deadline; a blow-up degrades to `unknown`.
///
/// # Errors
///
/// Returns [`SolverError`] from the backend. A `sat` candidate that fails to
/// replay against the originals declines to `unknown`, never a wrong `sat`.
pub(super) fn check_qf_abv_lazy_ext<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let mut ctx = RowCtx::default();

    // Abstract: array-eq atoms -> fresh Bool flags, selects -> fresh BV sites.
    let mut working: Vec<TermId> = Vec::with_capacity(assertions.len());
    for &assertion in assertions {
        match ctx.abstract_with_array_eq(arena, assertion)? {
            Some(t) => working.push(t),
            None => {
                return Ok(ext_unknown(
                    "lazy-extensionality declines: an array read/term is outside the modelled \
                     store/variable/const-array fragment"
                        .to_owned(),
                ));
            }
        }
    }

    // No array-eq atom survived abstraction: this is a pure-ROW query the ROW
    // path's own abstraction handles — delegate (it re-abstracts from the
    // originals) rather than duplicate it.
    if ctx.eq_atoms.is_empty() {
        let defs = ArrayDefs::new();
        let replay = ReplayTargets {
            originals: assertions,
            defs: &defs,
        };
        return check_row_cegar(backend, arena, assertions, &replay, config, deadline);
    }

    add_const_lemmas(arena, &ctx, &mut working)?;
    ext_cegar_loop(
        backend, arena, &mut ctx, working, assertions, config, deadline,
    )
}

/// Asserts the unconditional `select((as const _) v, j) = v` facts for every
/// const-array site (shared with the lazy-ROW path).
fn add_const_lemmas(
    arena: &mut TermArena,
    ctx: &RowCtx,
    working: &mut Vec<TermId>,
) -> Result<(), SolverError> {
    let const_lemmas: Vec<(SymbolId, TermId)> = ctx
        .sites
        .iter()
        .filter_map(|site| match &site.kind {
            RowKind::Const { value } => Some((site.fresh, *value)),
            _ => None,
        })
        .collect();
    for (fresh, value) in const_lemmas {
        let var = arena.var(fresh);
        let eqc = arena
            .eq(var, value)
            .map_err(|e| SolverError::Backend(format!("lazy-ext const lemma failed: {e}")))?;
        working.push(eqc);
    }
    Ok(())
}

/// The CEGAR loop for the lazy-extensionality path: solve the abstraction, add any
/// violated ROW / congruence / extensionality lemma, repeat to convergence or the
/// bound.
#[allow(clippy::too_many_arguments)]
fn ext_cegar_loop<B: SolverBackend>(
    backend: &mut B,
    arena: &mut TermArena,
    ctx: &mut RowCtx,
    mut working: Vec<TermId>,
    originals: &[TermId],
    config: &SolverConfig,
    deadline: Option<Instant>,
) -> Result<CheckResult, SolverError> {
    let mut added_row: HashSet<usize> = HashSet::new();
    let mut added_cong: HashSet<(usize, usize)> = HashSet::new();
    let mut diff_skolems = 0usize;
    let mut last_candidate: Option<Assignment> = None;

    for round in 0..MAX_ROW_ROUNDS {
        if past_deadline(deadline) {
            let replay = replay_last_ext_candidate(arena, ctx, originals, last_candidate.as_ref());
            let replay_note = match replay {
                LastExtReplay::Sat(model) => return Ok(CheckResult::Sat(model)),
                other => other.note(),
            };
            return Ok(ext_unknown_with_progress_note(
                "lazy-extensionality deadline exceeded before refinement converged",
                ExtProgress {
                    round,
                    ctx,
                    row_lemmas: added_row.len(),
                    cong_lemmas: added_cong.len(),
                    diff_skolems,
                    working_assertions: working.len(),
                },
                replay_note,
            ));
        }
        let round_config = config_with_remaining_deadline(config, deadline);
        let assignment = match check_scalar_abstraction(backend, arena, &working, &round_config)? {
            CheckResult::Unsat => return Ok(CheckResult::Unsat),
            CheckResult::Unknown(reason) => {
                let replay =
                    replay_last_ext_candidate(arena, ctx, originals, last_candidate.as_ref());
                let replay_note = match replay {
                    LastExtReplay::Sat(model) => return Ok(CheckResult::Sat(model)),
                    other => other.note(),
                };
                return Ok(ext_contextual_unknown_note(
                    "lazy-extensionality scalar backend declined",
                    ExtProgress {
                        round,
                        ctx,
                        row_lemmas: added_row.len(),
                        cong_lemmas: added_cong.len(),
                        diff_skolems,
                        working_assertions: working.len(),
                    },
                    &reason,
                    replay_note,
                ));
            }
            CheckResult::Sat(model) => complete_assignment(arena, &model.to_assignment()),
        };
        last_candidate = Some(assignment.clone());

        let mut progressed = false;

        // 1. ROW + read-over-read congruence on the materialised sites.
        progressed |= refine_row_and_congruence(
            arena,
            ctx,
            &assignment,
            &mut working,
            &mut added_row,
            &mut added_cong,
        )?;

        // 2. Extensionality on the array-eq atoms (congruence when the flag is
        //    true, a fresh diff-skolem witness when it is false).
        progressed |=
            refine_extensionality(arena, ctx, &assignment, &mut working, &mut diff_skolems)?;

        if !progressed {
            return project_replay_ext(arena, ctx, originals, &assignment);
        }
    }

    let replay = replay_last_ext_candidate(arena, ctx, originals, last_candidate.as_ref());
    let replay_note = match replay {
        LastExtReplay::Sat(model) => return Ok(CheckResult::Sat(model)),
        other => other.note(),
    };
    Ok(ext_unknown_with_progress_note(
        &format!("lazy-extensionality refinement did not converge within {MAX_ROW_ROUNDS} rounds"),
        ExtProgress {
            round: MAX_ROW_ROUNDS,
            ctx,
            row_lemmas: added_row.len(),
            cong_lemmas: added_cong.len(),
            diff_skolems,
            working_assertions: working.len(),
        },
        replay_note,
    ))
}

/// Adds every ROW / read-over-read-congruence lemma the candidate violates,
/// returning whether any lemma was added. Shared shape with the lazy-ROW loop.
fn refine_row_and_congruence(
    arena: &mut TermArena,
    ctx: &RowCtx,
    assignment: &Assignment,
    working: &mut Vec<TermId>,
    added_row: &mut HashSet<usize>,
    added_cong: &mut HashSet<(usize, usize)>,
) -> Result<bool, SolverError> {
    let mut new_row: Vec<usize> = Vec::new();
    for (idx, site) in ctx.sites.iter().enumerate() {
        if added_row.contains(&idx) {
            continue;
        }
        if let RowKind::Store { .. } = site.kind
            && row_violated(arena, ctx, idx, assignment)?
        {
            new_row.push(idx);
        }
    }
    let mut new_cong: Vec<(usize, usize)> = Vec::new();
    for a in 0..ctx.sites.len() {
        for b in (a + 1)..ctx.sites.len() {
            if added_cong.contains(&(a, b)) {
                continue;
            }
            if let (RowKind::Var { array: va }, RowKind::Var { array: vb }) =
                (&ctx.sites[a].kind, &ctx.sites[b].kind)
                && va == vb
                && indices_equal(arena, ctx.sites[a].index, ctx.sites[b].index, assignment)?
                && results_differ(assignment, ctx.sites[a].fresh, ctx.sites[b].fresh)
            {
                new_cong.push((a, b));
            }
        }
    }

    let progressed = !new_row.is_empty() || !new_cong.is_empty();
    for idx in new_row {
        let lemma = row_axiom_lemma(arena, ctx, idx)?;
        working.push(lemma);
        added_row.insert(idx);
    }
    for (a, b) in new_cong {
        let lemma = select_congruence_lemma(
            arena,
            ctx.sites[a].index,
            ctx.sites[b].index,
            ctx.sites[a].fresh,
            ctx.sites[b].fresh,
        )?;
        working.push(lemma);
        added_cong.insert((a, b));
    }
    Ok(progressed)
}

/// Refines the array (dis)equality atoms against extensionality, returning whether
/// any lemma was added.
///
/// For each atom `a = b` with flag `f` under `assignment`:
/// * `f` **true** but some already-materialised read index `i` has
///   `select(a,i) != select(b,i)` in the model: add `f => select(a,i)=select(b,i)`.
/// * `f` **false** and no diff-witness yet: introduce a fresh diff-skolem `k` and
///   add `!f => select(a,k) != select(b,k)`.
fn refine_extensionality(
    arena: &mut TermArena,
    ctx: &mut RowCtx,
    assignment: &Assignment,
    working: &mut Vec<TermId>,
    diff_skolems: &mut usize,
) -> Result<bool, SolverError> {
    let mut progressed = false;
    for atom_idx in 0..ctx.eq_atoms.len() {
        let flag = ctx.eq_atoms[atom_idx].flag;
        let flag_true = matches!(assignment.get(flag), Some(Value::Bool(true)));
        if flag_true {
            progressed |= refine_eq_congruence(arena, ctx, atom_idx, assignment, working)?;
        } else if !ctx.eq_atoms[atom_idx].diff_materialised {
            if *diff_skolems >= MAX_DIFF_SKOLEMS {
                continue;
            }
            refine_diff_skolem(arena, ctx, atom_idx, working)?;
            *diff_skolems += 1;
            progressed = true;
        }
    }
    Ok(progressed)
}

/// For a *true*-flagged atom `a = b`, adds `flag => select(a,i)=select(b,i)` for
/// every read index `i` (already materialised on either operand) the model leaves
/// inconsistent. Returns whether any lemma was added.
fn refine_eq_congruence(
    arena: &mut TermArena,
    ctx: &mut RowCtx,
    atom_idx: usize,
    assignment: &Assignment,
    working: &mut Vec<TermId>,
) -> Result<bool, SolverError> {
    // Gather the distinct index terms already read on either operand.
    let (lhs, rhs, flag) = {
        let atom = &ctx.eq_atoms[atom_idx];
        (atom.lhs, atom.rhs, atom.flag)
    };
    let indices = read_indices_for(arena, ctx, lhs, rhs);
    let mut progressed = false;
    for index in indices {
        let Some(read_a) = ctx.resolve_select(arena, lhs, index)? else {
            continue;
        };
        let Some(read_b) = ctx.resolve_select(arena, rhs, index)? else {
            continue;
        };
        // `resolve_select` can materialize a fresh read symbol after the scalar
        // assignment was completed. Complete again before evaluating the read
        // terms so an unassigned fresh does not turn a candidate into a backend
        // error; the eventual projected model is still replay-gated.
        let completed = complete_assignment(arena, assignment);
        if read_terms_differ(arena, read_a, read_b, &completed)? {
            let var_flag = arena.var(flag);
            let eqr = arena
                .eq(read_a, read_b)
                .map_err(|e| SolverError::Backend(format!("lazy-ext cong build failed: {e}")))?;
            let lemma = arena
                .implies(var_flag, eqr)
                .map_err(|e| SolverError::Backend(format!("lazy-ext cong build failed: {e}")))?;
            working.push(lemma);
            progressed = true;
        }
    }
    Ok(progressed)
}

/// For a *false*-flagged atom `a != b`, introduces a fresh diff-skolem index `k`
/// and adds the witness lemma `!flag => select(a,k) != select(b,k)`, materialising
/// the two read sites at `k`.
fn refine_diff_skolem(
    arena: &mut TermArena,
    ctx: &mut RowCtx,
    atom_idx: usize,
    working: &mut Vec<TermId>,
) -> Result<(), SolverError> {
    let (lhs, rhs, flag) = {
        let atom = &ctx.eq_atoms[atom_idx];
        (atom.lhs, atom.rhs, atom.flag)
    };
    let Some((index_sort, _)) = arena.sort_of(lhs).array_sorts() else {
        return Ok(());
    };
    let name = format!("!ext_diff_{}", ctx.fresh_counter);
    ctx.fresh_counter += 1;
    let k_sym = arena
        .declare_internal(&name, index_sort)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff-skolem declare failed: {e}")))?;
    let k = arena.var(k_sym);

    let Some(read_a) = ctx.resolve_select(arena, lhs, k)? else {
        return Ok(());
    };
    let Some(read_b) = ctx.resolve_select(arena, rhs, k)? else {
        return Ok(());
    };
    let var_flag = arena.var(flag);
    let not_flag = arena
        .not(var_flag)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff build failed: {e}")))?;
    let eqr = arena
        .eq(read_a, read_b)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff build failed: {e}")))?;
    let ner = arena
        .not(eqr)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff build failed: {e}")))?;
    let lemma = arena
        .implies(not_flag, ner)
        .map_err(|e| SolverError::Backend(format!("lazy-ext diff build failed: {e}")))?;
    working.push(lemma);
    ctx.eq_atoms[atom_idx].diff_materialised = true;
    Ok(())
}
