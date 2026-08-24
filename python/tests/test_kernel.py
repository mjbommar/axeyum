"""`axeyum.kernel` -- handles, preludes, footprints, and the trusted gate.

Two differentials here run against **example binaries built from this tree**:
`nat_theorem_inventory` and `theorem_axiom_footprint`, under
`target/release/examples/`. Build them with

    cargo build --release -p axeyum-lean-kernel \\
        --example nat_theorem_inventory --example theorem_axiom_footprint

A binary that is *absent* skips (with the command above in the message). A
binary that is *present and disagrees* FAILS -- it is either stale or the
binding is wrong, and both need a human. Measured 2026-08-24: the copies in the
main checkout were three days old and reported 139 Nat theorems where this tree
has 235, so "compare against whatever binary is lying around" is not a check.
"""

from __future__ import annotations

import subprocess
from pathlib import Path

import pytest

from axeyum.kernel import (
    BinderInfo,
    Declaration,
    EpochError,
    Kernel,
    KernelError,
    Lit,
    identity,
    prelude_cache_enabled,
    prelude_cache_stats,
    theorem_inventory,
)

REPO_ROOT = Path(__file__).resolve().parents[2]
EXAMPLES = REPO_ROOT / "target" / "release" / "examples"
BUILD_HINT = (
    "cargo build --release -p axeyum-lean-kernel "
    "--example nat_theorem_inventory --example theorem_axiom_footprint"
)


KERNEL_SOURCES = REPO_ROOT / "crates" / "axeyum-lean-kernel" / "src"


def run_example(name: str, *args: str) -> subprocess.CompletedProcess[str]:
    """Runs a prebuilt example binary, skipping when it is absent OR STALE.

    A binary older than the newest kernel source is a differential against
    the wrong subject: it reported 139 theorems where the source had 235, and
    a merge that adds theorems makes it wrong again. Failing there reads as a
    binding defect; the honest answer is "not looked at", with the rebuild
    command -- the same distinction the inventory examples themselves draw.
    """
    binary = EXAMPLES / name
    if not binary.exists():
        pytest.skip(f"{binary} not built; run: {BUILD_HINT}")
    newest_source = max(path.stat().st_mtime for path in KERNEL_SOURCES.rglob("*.rs"))
    if binary.stat().st_mtime < newest_source:
        pytest.skip(f"{binary} is older than the kernel sources; run: {BUILD_HINT}")
    return subprocess.run(
        [str(binary), *args], capture_output=True, text=True, timeout=600, check=False
    )


@pytest.fixture(scope="module")
def nat_kernel() -> Kernel:
    """A kernel carrying the computational `Nat` prelude."""
    kernel = Kernel()
    kernel.build_nat_prelude()
    return kernel


@pytest.fixture(scope="module")
def arith_kernel() -> Kernel:
    """A kernel carrying the AXIOMATIZED ordered field (`axreal`, 30 axioms)."""
    kernel = Kernel()
    kernel.build_arith_prelude()
    return kernel


def theorem_names(kernel: Kernel) -> list[str]:
    """Every `theorem`-kind declaration name in the environment."""
    return [name for name, decl in kernel.declarations() if decl.kind == "theorem"]


# --------------------------------------------------------------------------
# Construction, epochs, forks
# --------------------------------------------------------------------------


def test_new_kernel_is_empty() -> None:
    kernel = Kernel()
    assert kernel.declaration_count() == 0
    assert kernel.declarations() == []


def test_each_kernel_gets_its_own_epoch() -> None:
    first, second = Kernel(), Kernel()
    assert first.epoch != second.epoch
    assert first.anon().epoch == first.epoch


def test_handles_carry_the_producing_epoch(nat_kernel: Kernel) -> None:
    name = nat_kernel.name("Nat.add_comm", must_exist=True)
    assert name.epoch == nat_kernel.epoch
    assert name.raw >= 0


def test_cross_kernel_name_handle_raises_epoch_error(nat_kernel: Kernel) -> None:
    other = Kernel()
    foreign = other.anon()
    with pytest.raises(EpochError) as raised:
        nat_kernel.display_name(foreign)
    assert str(other.epoch) in str(raised.value)


def test_cross_kernel_expr_handle_raises_epoch_error(nat_kernel: Kernel) -> None:
    other = Kernel()
    foreign = other.sort_zero()
    with pytest.raises(EpochError):
        nat_kernel.render_lean(foreign)


def test_fork_rejects_the_parent_handles(nat_kernel: Kernel) -> None:
    # The two kernels agree on every id at the instant of the fork, so accepting
    # a parent handle would work until either side interned anything -- after
    # which the same id denotes two different terms, silently.
    forked = nat_kernel.fork()
    assert forked.epoch != nat_kernel.epoch
    parent_name = nat_kernel.name("Nat.add_comm", must_exist=True)
    with pytest.raises(EpochError):
        forked.axiom_footprint(parent_name)
    # Re-resolving by string is the supported route across a fork.
    assert forked.axiom_footprint("Nat.add_comm") == []


def test_fork_is_an_independent_snapshot(nat_kernel: Kernel) -> None:
    forked = nat_kernel.fork()
    before = nat_kernel.declaration_count()
    assert forked.declaration_count() == before
    name = forked.name("Fork.only")
    forked.add_declaration(Declaration.axiom(name, [], forked.sort_zero()))
    assert forked.declaration_count() == before + 1
    assert nat_kernel.declaration_count() == before


# --------------------------------------------------------------------------
# Preludes and the process cache
# --------------------------------------------------------------------------


def test_nat_prelude_declares_a_nonempty_environment(nat_kernel: Kernel) -> None:
    assert nat_kernel.declaration_count() > 0
    assert len(theorem_names(nat_kernel)) > 0


def test_prelude_package_exposes_its_fields(nat_kernel: Kernel) -> None:
    kernel = Kernel()
    nat = kernel.build_nat_prelude()
    assert nat.kind == "nat"
    assert len(nat) == 244
    assert "add_comm" in nat
    assert kernel.display_name(nat.add_comm) == "Nat.add_comm"
    assert len(nat.to_dict()) == len(nat)


def test_prelude_package_missing_field_raises_attribute_error(nat_kernel: Kernel) -> None:
    kernel = Kernel()
    nat = kernel.build_nat_prelude()
    with pytest.raises(AttributeError):
        _ = nat.no_such_theorem
    with pytest.raises(KeyError):
        _ = nat["no_such_theorem"]


def test_prelude_package_carries_its_subpackages() -> None:
    kernel = Kernel()
    nat = kernel.build_nat_prelude()
    assert nat.package_names == ["logic"]
    assert nat.logic.kind == "logic"
    assert kernel.display_name(nat.logic.eq_refl) == "Eq.refl"


def test_arith_prelude_is_labelled_axreal_not_real(arith_kernel: Kernel) -> None:
    kernel = Kernel()
    package = kernel.build_arith_prelude()
    # `axreal`, never `real`: the label contradicting its contents is exactly the
    # confusion ADR-0522's rename existed to prevent.
    assert package.kind == "axreal"
    assert arith_kernel.declaration_count() > 0


def test_creal_prelude_is_a_different_package_from_axreal() -> None:
    kernel = Kernel()
    package = kernel.build_creal_prelude()
    assert package.kind == "creal"
    assert kernel.declaration_count() > 0


def test_string_prelude_needs_the_logic_package() -> None:
    kernel = Kernel()
    logic = kernel.build_logic_prelude()
    string = kernel.build_string_prelude(logic, 2)
    assert string.kind == "string"
    assert len(string.char_ctors) == 2


def test_string_prelude_rejects_a_non_logic_package() -> None:
    kernel = Kernel()
    nat = kernel.build_nat_prelude()
    with pytest.raises(ValueError, match="build_logic_prelude"):
        kernel.build_string_prelude(nat, 2)


def test_prelude_cache_hits_increase_on_a_second_build() -> None:
    assert prelude_cache_enabled(), "AXEYUM_PRELUDE_CACHE=0 disables the cache under test"
    Kernel().build_nat_prelude()  # ensure a template exists
    before = prelude_cache_stats().hits
    Kernel().build_nat_prelude()
    after = prelude_cache_stats().hits
    assert after > before, "process-wide prelude reuse did not run"


def test_prelude_cache_stats_fields_are_monotone() -> None:
    stats = prelude_cache_stats()
    assert stats.hits >= 0
    assert stats.templates_built >= 1
    assert "hits=" in repr(stats)


# --------------------------------------------------------------------------
# The inventory differentials
# --------------------------------------------------------------------------


def test_theorem_count_matches_nat_theorem_inventory(nat_kernel: Kernel) -> None:
    counted = len(theorem_names(nat_kernel))
    assert counted > 0, "an empty inventory is a failed check, not an empty report"
    # `--expect-count` makes the BINARY's exit status depend on our number: it
    # fails on drift in either direction.
    result = run_example("nat_theorem_inventory", "--expect-count", str(counted))
    assert result.returncode == 0, (
        f"python counted {counted} Nat theorems; the example disagrees:\n"
        f"{result.stderr}\nIf the binary predates this tree, rebuild it: {BUILD_HINT}"
    )


def test_theorem_inventory_rows_match_the_example(nat_kernel: Kernel) -> None:
    rows = theorem_inventory(nat_kernel)
    assert len(rows) > 0
    result = run_example("nat_theorem_inventory")
    assert result.returncode == 0
    expected = [tuple(line.split("\t")) for line in result.stdout.splitlines() if line.strip()]
    ours = [(name, str(binders), rendered) for name, binders, rendered in rows]
    assert ours == expected


def test_inventory_filter_that_matches_nothing_is_empty(nat_kernel: Kernel) -> None:
    assert theorem_inventory(nat_kernel, "no_such_theorem_anywhere") == []
    assert len(theorem_inventory(nat_kernel, "add_comm")) >= 1


# --------------------------------------------------------------------------
# Axiom footprints
# --------------------------------------------------------------------------


def test_every_nat_theorem_is_axiom_free(nat_kernel: Kernel) -> None:
    names = theorem_names(nat_kernel)
    assert len(names) > 0
    offenders = [name for name in names if nat_kernel.axiom_footprint(name)]
    assert offenders == []


def test_every_int_theorem_is_axiom_free() -> None:
    kernel = Kernel()
    kernel.build_int_prelude()
    names = theorem_names(kernel)
    assert len(names) > 0
    assert [name for name in names if kernel.axiom_footprint(name)] == []


def test_every_creal_theorem_is_axiom_free() -> None:
    kernel = Kernel()
    kernel.build_creal_prelude()
    names = theorem_names(kernel)
    assert len(names) > 0
    assert [name for name in names if kernel.axiom_footprint(name)] == []


def test_axreal_footprints_total_thirty_distinct_axioms(arith_kernel: Kernel) -> None:
    # The negative control for every axiom-freedom measurement above. 30 is a
    # FLOOR, not a dial: AxReal's carrier is opaque, so every operation and law
    # must be assumed. Declared, and reached by no shipped route.
    axioms: set[str] = set()
    settled = 0
    for name, declaration in arith_kernel.declarations():
        if declaration.kind in {"theorem", "axiom"}:
            settled += 1
            axioms.update(arith_kernel.axiom_footprint(name))
    assert settled > 0
    assert len(axioms) == 30
    assert all(axiom.startswith("AxReal") for axiom in axioms)


def test_axreal_footprints_match_the_example(arith_kernel: Kernel) -> None:
    result = run_example("theorem_axiom_footprint")
    assert result.returncode == 0
    expected = {}
    for line in result.stdout.splitlines():
        prelude, name, _size, axioms = line.split("\t")
        if prelude == "axreal":
            expected[name] = [a for a in axioms.split(",") if a]
    assert len(expected) > 0
    ours = {
        name: arith_kernel.axiom_footprint(name)
        for name, declaration in arith_kernel.declarations()
        if declaration.kind in {"theorem", "axiom"}
    }
    assert ours == expected


def test_a_nat_theorem_is_axiom_free_by_footprint(nat_kernel: Kernel) -> None:
    assert nat_kernel.axiom_footprint("Nat.add_comm") == []
    assert nat_kernel.is_axiom_free("Nat.add_comm") is True


def test_an_axreal_theorem_is_not_axiom_free(arith_kernel: Kernel) -> None:
    assert arith_kernel.is_axiom_free("AxReal.le_trans") is False
    assert len(arith_kernel.axiom_footprint("AxReal.le_trans")) == 3


def test_axiom_footprint_of_an_absent_name_raises_keyerror(nat_kernel: Kernel) -> None:
    # The Rust function answers `[]` here -- byte-identical to axiom-free.
    with pytest.raises(KeyError):
        nat_kernel.axiom_footprint("Nat.Nonexistent")


def test_is_axiom_free_of_an_absent_name_raises_keyerror(nat_kernel: Kernel) -> None:
    with pytest.raises(KeyError):
        nat_kernel.is_axiom_free("Nonexistent")


def test_dependency_closure_of_an_absent_name_raises_keyerror(nat_kernel: Kernel) -> None:
    with pytest.raises(KeyError):
        nat_kernel.declaration_dependency_closure("Nonexistent")


def test_theorem_dependencies_of_an_absent_name_raises_keyerror(nat_kernel: Kernel) -> None:
    with pytest.raises(KeyError):
        nat_kernel.theorem_dependencies("Nonexistent")


def test_name_must_exist_raises_for_an_undeclared_name(nat_kernel: Kernel) -> None:
    with pytest.raises(KeyError):
        nat_kernel.name("Nat.Nonexistent", must_exist=True)
    assert nat_kernel.name("Nat.Nonexistent").raw >= 0


def test_dependency_closure_and_direct_dependencies_agree(nat_kernel: Kernel) -> None:
    closure = nat_kernel.declaration_dependency_closure("Nat.add_comm")
    direct = nat_kernel.theorem_dependencies("Nat.add_comm")
    assert len(closure) > 0
    assert len(direct) > 0
    assert set(direct).issubset(set(closure))


def test_declarations_reached_finds_the_constants_of_a_term(nat_kernel: Kernel) -> None:
    kernel = nat_kernel.fork()
    nat_type = kernel.const_(kernel.name("Nat", must_exist=True), [])
    reached = kernel.declarations_reached([nat_type])
    assert "Nat" in reached


# --------------------------------------------------------------------------
# The trusted gate
# --------------------------------------------------------------------------


def test_add_declaration_admits_an_axiom() -> None:
    kernel = Kernel()
    name = kernel.name("Demo.assumed")
    kernel.add_declaration(Declaration.axiom(name, [], kernel.sort_zero()))
    assert kernel.contains("Demo.assumed")
    assert kernel.get_declaration("Demo.assumed").kind == "axiom"
    # An axiom is its own footprint: the trusted surface is not empty here.
    assert kernel.axiom_footprint("Demo.assumed") == ["Demo.assumed"]


def test_duplicate_add_declaration_raises_declaration_exists() -> None:
    kernel = Kernel()
    name = kernel.name("Demo.twice")
    declaration = Declaration.axiom(name, [], kernel.sort_zero())
    kernel.add_declaration(declaration)
    with pytest.raises(KernelError) as raised:
        kernel.add_declaration(declaration)
    assert raised.value.variant == "DeclarationExists"
    assert set(raised.value.fields) == {"name"}
    assert raised.value.names["name"] == "Demo.twice"


def test_kernel_error_variant_for_an_unknown_constant() -> None:
    kernel = Kernel()
    dangling = kernel.const_(kernel.name("No.Such.Const"), [])
    with pytest.raises(KernelError) as raised:
        kernel.infer(dangling)
    assert raised.value.variant == "UnknownConst"
    assert "name" in raised.value.fields


def test_add_declaration_rejects_a_foreign_declaration() -> None:
    kernel, other = Kernel(), Kernel()
    foreign = Declaration.axiom(other.name("Demo.foreign"), [], other.sort_zero())
    with pytest.raises(EpochError):
        kernel.add_declaration(foreign)


def test_declaration_constructors_reject_mixed_epochs() -> None:
    kernel, other = Kernel(), Kernel()
    with pytest.raises(EpochError):
        Declaration.axiom(kernel.name("Demo.mixed"), [], other.sort_zero())


def test_hand_built_refl_theorem_checks_and_renders(nat_kernel: Kernel) -> None:
    kernel = nat_kernel.fork()
    universe = kernel.level_succ(kernel.level_zero())
    nat_type = kernel.const_(kernel.name("Nat", must_exist=True), [])
    eq = kernel.const_(kernel.name("Eq", must_exist=True), [universe])
    refl = kernel.const_(kernel.name("Eq.refl", must_exist=True), [universe])
    binder = kernel.name("n")
    body = kernel.app(kernel.app(kernel.app(eq, nat_type), kernel.bvar(0)), kernel.bvar(0))
    goal = kernel.pi(binder, nat_type, body, BinderInfo.Default)
    proof = kernel.lam(binder, nat_type, kernel.app(kernel.app(refl, nat_type), kernel.bvar(0)))
    assert kernel.def_eq(kernel.infer(proof), goal)
    theorem = Declaration.theorem(kernel.name("Demo.refl_all"), [], goal, proof)
    kernel.add_declaration(theorem)
    assert kernel.axiom_footprint("Demo.refl_all") == []
    rendered = kernel.render_lean_decl(theorem)
    assert rendered.startswith("theorem Demo.refl_all")
    assert "Eq.refl" in rendered
    assert "Eq" in kernel.render_lean(goal)


def test_def_eq_true_and_false_cases() -> None:
    kernel = Kernel()
    prop = kernel.sort_zero()
    type_one = kernel.sort(kernel.level_succ(kernel.level_zero()))
    assert kernel.def_eq(prop, prop) is True
    assert kernel.def_eq(prop, type_one) is False


def test_whnf_beta_reduces() -> None:
    kernel = Kernel()
    binder = kernel.name("x")
    prop = kernel.sort_zero()
    identity_fn = kernel.lam(binder, prop, kernel.bvar(0))
    applied = kernel.app(identity_fn, prop)
    assert kernel.render_lean(kernel.whnf(applied)) == kernel.render_lean(prop)


def test_infer_reports_a_loose_bvar() -> None:
    kernel = Kernel()
    with pytest.raises(KernelError) as raised:
        kernel.infer(kernel.bvar(0))
    assert raised.value.variant == "LooseBVar"


# --------------------------------------------------------------------------
# Terms: constructors, nodes, de Bruijn surgery
# --------------------------------------------------------------------------


def test_expr_node_destructures_every_constructor() -> None:
    kernel = Kernel()
    binder = kernel.name("x")
    prop = kernel.sort_zero()
    seen = {}
    seen["bvar"] = kernel.bvar(3)
    seen["fvar"] = kernel.fvar(7)
    seen["sort"] = prop
    seen["const"] = kernel.const_(kernel.name("Some.Const"), [kernel.level_zero()])
    seen["app"] = kernel.app(prop, prop)
    seen["lam"] = kernel.lam(binder, prop, kernel.bvar(0))
    seen["pi"] = kernel.pi(binder, prop, kernel.bvar(0), BinderInfo.Implicit)
    seen["let"] = kernel.let_(binder, prop, prop, kernel.bvar(0))
    seen["lit"] = kernel.lit(Lit.nat(5))
    seen["proj"] = kernel.proj(kernel.name("Some.Struct"), 1, prop)
    for kind, expr in seen.items():
        node = kernel.expr_node(expr)
        assert node.kind == kind
        assert len(node.args()) >= 1
    assert kernel.expr_node(seen["bvar"]).index == 3
    assert kernel.expr_node(seen["fvar"]).fvar_id == 7
    assert kernel.expr_node(seen["pi"]).binder == BinderInfo.Implicit
    assert kernel.expr_node(seen["proj"]).field_index == 1
    assert kernel.expr_node(seen["const"]).levels == [kernel.level_zero()]


def test_lit_carries_arbitrary_precision_naturals() -> None:
    kernel = Kernel()
    big = 2**80 + 7
    node = kernel.expr_node(kernel.lit(Lit.nat(big)))
    assert node.lit.kind == "nat"
    assert node.lit.value == big
    text = kernel.expr_node(kernel.lit(Lit.str("hello"))).lit
    assert (text.kind, text.value) == ("str", "hello")
    with pytest.raises(ValueError, match="non-negative"):
        Lit.nat(-1)


def test_loose_bvars_and_instantiate() -> None:
    kernel = Kernel()
    prop = kernel.sort_zero()
    open_body = kernel.bvar(0)
    assert kernel.has_loose_bvars(open_body) is True
    assert kernel.num_loose_bvars(open_body) == 1
    assert kernel.loose_bvar_range(open_body) == (0, 1)
    closed = kernel.instantiate(open_body, [prop])
    assert kernel.has_loose_bvars(closed) is False
    assert closed == prop


def test_abstract_fvars_and_lift_loose_bvars() -> None:
    kernel = Kernel()
    free = kernel.fvar(42)
    assert kernel.has_fvars(free) is True
    abstracted = kernel.abstract_fvars(free, [42])
    assert kernel.has_fvars(abstracted) is False
    assert kernel.expr_node(abstracted).kind == "bvar"
    lifted = kernel.lift_loose_bvars(abstracted, 0, 2)
    assert kernel.expr_node(lifted).index == kernel.expr_node(abstracted).index + 2


def test_lam_body_and_pi_body() -> None:
    kernel = Kernel()
    binder = kernel.name("x")
    prop = kernel.sort_zero()
    lam = kernel.lam(binder, prop, kernel.bvar(0))
    pi = kernel.pi(binder, prop, kernel.bvar(0))
    assert kernel.lam_body(lam) == kernel.bvar(0)
    assert kernel.pi_body(pi) == kernel.bvar(0)
    assert kernel.lam_body(pi) is None
    assert kernel.pi_body(lam) is None


def test_levels_compare_and_simplify() -> None:
    kernel = Kernel()
    zero = kernel.level_zero()
    one = kernel.level_succ(zero)
    assert kernel.level_is_zero(zero) is True
    assert kernel.level_is_nonzero(one) is True
    assert kernel.level_leq(zero, one) is True
    assert kernel.level_leq(one, zero) is False
    assert kernel.level_is_equiv(kernel.level_max(zero, one), one) is True
    assert kernel.level_succs(kernel.level_offset(zero, 3)) == (zero, 3)
    assert kernel.simplify_level(kernel.level_max(zero, zero)) == zero


def test_name_components_round_trip() -> None:
    kernel = Kernel()
    root = kernel.anon()
    a = kernel.name_str(root, "a")
    numbered = kernel.name_num(a, 7)
    assert kernel.display_name(numbered) == "a.7"
    # `lean_name` is NOT `display_name`: a numeric component is not a legal Lean
    # identifier on its own, and the computational naturals are rooted at AxNat.
    assert kernel.lean_name(numbered) == "a._7"
    assert kernel.name_node(numbered)[0] == "num"
    with pytest.raises(ValueError):
        kernel.name("Nat..add")


# --------------------------------------------------------------------------
# Rendering, export, identity
# --------------------------------------------------------------------------


def test_render_lean_module_and_compact_agree_on_content(nat_kernel: Kernel) -> None:
    kernel = nat_kernel.fork()
    prop = kernel.sort_zero()
    binder = kernel.name("x")
    goal = kernel.pi(binder, prop, kernel.bvar(0))
    proof = kernel.lam(binder, prop, kernel.bvar(0))
    module = kernel.render_lean_module("Demo.id", goal, proof)
    compact = kernel.render_lean_module_compact("Demo.id", goal, proof)
    assert "Demo.id" in module
    assert "Demo.id" in compact


def test_render_lean4export_ndjson_roots(nat_kernel: Kernel) -> None:
    name = nat_kernel.name("Nat.add_comm", must_exist=True)
    ndjson = nat_kernel.render_lean4export_ndjson_roots("4.30.0", [name])
    lines = ndjson.splitlines()
    assert len(lines) > 1
    assert any("axeyum-lean-kernel" in line for line in lines)


def test_identity_hashes_are_stable_across_kernels() -> None:
    first, second = Kernel(), Kernel()
    first.build_nat_prelude()
    second.build_nat_prelude()
    left = identity.canonical_declaration_sha256(first, "Nat.add_comm")
    right = identity.canonical_declaration_sha256(second, "Nat.add_comm")
    assert len(left) == 64
    assert left == right


def test_identity_expression_and_level_hashes() -> None:
    kernel = Kernel()
    prop = kernel.sort_zero()
    expression = identity.canonical_expression_sha256(kernel, prop)
    alpha = identity.canonical_alpha_expression_sha256(kernel, prop)
    shape = identity.canonical_kernel_type_shape_sha256(kernel, prop)
    level = identity.canonical_level_sha256(kernel, kernel.level_zero())
    assert {len(h) for h in (expression, alpha, shape, level)} == {64}


def test_identity_alpha_hash_ignores_binder_names() -> None:
    kernel = Kernel()
    prop = kernel.sort_zero()
    left = kernel.lam(kernel.name("x"), prop, kernel.bvar(0))
    right = kernel.lam(kernel.name("y"), prop, kernel.bvar(0))
    assert identity.canonical_expression_sha256(
        kernel, left
    ) != identity.canonical_expression_sha256(kernel, right)
    assert identity.canonical_alpha_expression_sha256(
        kernel, left
    ) == identity.canonical_alpha_expression_sha256(kernel, right)


def test_identity_rejects_an_absent_declaration(nat_kernel: Kernel) -> None:
    with pytest.raises(KeyError):
        identity.canonical_declaration_sha256(nat_kernel, "Nonexistent")


def test_declarations_snapshot_is_owned(nat_kernel: Kernel) -> None:
    kernel = nat_kernel.fork()
    snapshot = kernel.declarations()
    kernel.add_declaration(Declaration.axiom(kernel.name("Demo.later"), [], kernel.sort_zero()))
    assert len(kernel.declarations()) == len(snapshot) + 1
    assert all(isinstance(name, str) for name, _ in snapshot)
    assert snapshot[0][1].epoch == kernel.epoch
