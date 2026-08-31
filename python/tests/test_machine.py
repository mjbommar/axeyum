"""The Python machine surface is a faithful projection of Rust semantics."""

from __future__ import annotations

import pytest

from axeyum import machine


def test_a0_word_readings_and_modular_construction() -> None:
    word = machine.a0.Word(8, 0x1FF)
    assert word.width == 8
    assert word.unsigned == 0xFF
    assert word.signed == -1
    assert word.high_bit is True
    assert int(word) == 0xFF


def test_a0_word_little_endian_round_trip() -> None:
    word = machine.a0.Word.from_little_endian([0x34, 0x12])
    assert word == machine.a0.Word(16, 0x1234)
    assert word.little_endian_bytes() == bytes([0x34, 0x12])


def test_a0_word_width_changes_are_explicit() -> None:
    negative = machine.a0.Word(8, 0x80)
    assert negative.zero_extend(16).unsigned == 0x0080
    assert negative.sign_extend(16).unsigned == 0xFF80
    assert negative.sign_extend(16).truncate(8) == negative


@pytest.mark.parametrize("width", [0, 7, 72])
def test_a0_word_rejects_unsupported_widths(width: int) -> None:
    with pytest.raises(ValueError, match="invalid A0 word width"):
        machine.a0.Word(width, 0)


def test_a0_word_rejects_wrong_direction_width_changes() -> None:
    word = machine.a0.Word(16, 1)
    with pytest.raises(ValueError, match="invalid width conversion"):
        word.zero_extend(8)
    with pytest.raises(ValueError, match="invalid width conversion"):
        word.truncate(24)


def test_a0_memory_supports_dense_and_sparse_domains() -> None:
    dense = machine.a0.Memory.from_bytes([0x10, 0x20, 0x30])
    assert len(dense) == 3
    assert dense.byte_at(1) == 0x20
    assert dense.byte_at(3) is None
    assert dense.entries() == [(0, 0x10), (1, 0x20), (2, 0x30)]

    sparse = machine.a0.Memory.from_entries([(255, 0xAA), (0, 0xBB)])
    assert sparse.entries() == [(0, 0xBB), (255, 0xAA)]
    with pytest.raises(ValueError, match="duplicate A0 memory address 1"):
        machine.a0.Memory.from_entries([(1, 0), (1, 1)])


def test_a0_state_is_immutable_validated_and_canonical() -> None:
    state = machine.a0.State(16, machine.a0.Memory.zeroed(4), machine.a0.Word(16, 0x100))
    state = state.with_register(2, machine.a0.Word(16, 0xABCD))
    state = state.with_conditions(machine.a0.Conditions(True, False, True, False))
    assert state.register(2).unsigned == 0xABCD
    assert state.registers[2] == state.register(2)
    assert state.conditions.zero is True
    assert state.conditions.carry is True
    assert state.outcome.kind == "running"
    assert machine.a0.State.decode(state.encode()).encode() == state.encode()

    with pytest.raises(ValueError, match="register index must be 0 through 7"):
        state.register(8)
    with pytest.raises(ValueError, match="state component register"):
        state.with_register(0, machine.a0.Word(8, 1))


def test_a0_all_instruction_factories_round_trip_canonically() -> None:
    instructions = [
        machine.a0.Instruction.mov(2, 1),
        machine.a0.Instruction.mov_immediate(2, -7),
        machine.a0.Instruction.load(2, 1, -3),
        machine.a0.Instruction.store(1, 2, 3),
        machine.a0.Instruction.add(2, 1, 3),
        machine.a0.Instruction.sub(2, 1, 3),
        machine.a0.Instruction.and_(2, 1, 3),
        machine.a0.Instruction.or_(2, 1, 3),
        machine.a0.Instruction.xor(2, 1, 3),
        machine.a0.Instruction.not_(2, 1),
        machine.a0.Instruction.shift_left(2, 1, 3),
        machine.a0.Instruction.shift_right(2, 1, 3),
        machine.a0.Instruction.arithmetic_shift_right(2, 1, 3),
        machine.a0.Instruction.compare(1, 3),
        machine.a0.Instruction.branch("eq", -1),
        machine.a0.Instruction.jump(2),
        machine.a0.Instruction.halt(),
    ]
    assert len({instruction.kind for instruction in instructions}) == 17
    for instruction in instructions:
        encoded = instruction.encode()
        assert len(encoded) == 4
        assert machine.a0.Instruction.decode(encoded) == instruction

    add = machine.a0.Instruction.add(2, 1, 3)
    assert (add.rd, add.rs1, add.rs2) == (2, 1, 3)
    branch = machine.a0.Instruction.branch("HS", -4)
    assert (branch.condition, branch.offset) == ("hs", -4)
    with pytest.raises(ValueError, match="invalid A0 register r8"):
        machine.a0.Instruction.add(8, 1, 2)
    with pytest.raises(ValueError, match="exactly four bytes"):
        machine.a0.Instruction.decode([0, 1, 2])
    with pytest.raises(ValueError, match="condition must be"):
        machine.a0.Instruction.branch("always", 0)


def test_a0_add_example_executes_with_complete_state() -> None:
    add = machine.a0.Instruction.add(2, 1, 3)
    program = machine.a0.Program(8, machine.a0.Word(8, 0), add.encode())
    before = machine.a0.State(8, machine.a0.Memory.zeroed(0), program.entry)
    before = before.with_register(1, machine.a0.Word(8, 0x7F))
    before = before.with_register(3, machine.a0.Word(8, 1))

    after = machine.a0.step(program, before)
    assert after.register(2).unsigned == 0x80
    assert after.register(1) == before.register(1)
    assert after.pc.unsigned == 4
    assert after.conditions == machine.a0.Conditions(False, True, False, True)
    assert after.outcome.kind == "running"


def test_a0_memory_execution_and_traps_are_atomic() -> None:
    store = machine.a0.Instruction.store(1, 2, 0)
    load = machine.a0.Instruction.load(3, 1, 0)
    program = machine.a0.Program(
        16,
        machine.a0.Word(16, 0),
        store.encode() + load.encode(),
    )
    before = machine.a0.State(16, machine.a0.Memory.zeroed(2), program.entry)
    before = before.with_register(1, machine.a0.Word(16, 0))
    before = before.with_register(2, machine.a0.Word(16, 0xABCD))
    stored = machine.a0.step(program, before)
    assert stored.memory.entries() == [(0, 0xCD), (1, 0xAB)]
    loaded = machine.a0.step(program, stored)
    assert loaded.register(3).unsigned == 0xABCD

    too_small = machine.a0.State(16, machine.a0.Memory.zeroed(1), program.entry)
    too_small = too_small.with_register(2, machine.a0.Word(16, 0xABCD))
    trapped = machine.a0.step(program, too_small)
    assert trapped.outcome.kind == "trapped"
    assert trapped.outcome.trap.kind == "data-range"
    assert trapped.memory.entries() == [(0, 0)]


def test_a0_run_and_prefix_report_distinct_stop_reasons() -> None:
    jump = machine.a0.Instruction.jump(-1)
    loop = machine.a0.Program(8, machine.a0.Word(8, 0), jump.encode())
    initial = machine.a0.State(8, machine.a0.Memory.zeroed(0), loop.entry)
    assert machine.a0.run(loop, initial, 2).stop == "bound-exhausted"
    prefix = machine.a0.run_prefix(loop, initial, 2)
    assert prefix.stop == "prefix-returned"
    assert len(prefix) == 3

    halt = machine.a0.Program(8, machine.a0.Word(8, 0), machine.a0.Instruction.halt().encode())
    halted = machine.a0.run(halt, initial, 2)
    assert halted.stop == "halted"
    assert len(halted.states) == 2
    assert machine.a0.step(halt, halted.states[-1]).encode() == halted.states[-1].encode()


def rv64_code(*instructions: object) -> bytes:
    return b"".join(instruction.encode().to_bytes(4, "little") for instruction in instructions)


def test_rv64_all_selected_instruction_factories_round_trip() -> None:
    instructions = [
        machine.rv64.Instruction.add_immediate(3, 2, -7),
        machine.rv64.Instruction.add(3, 2, 1),
        machine.rv64.Instruction.sub(3, 2, 1),
        machine.rv64.Instruction.or_(3, 2, 1),
        machine.rv64.Instruction.xor(3, 2, 1),
        machine.rv64.Instruction.load_double(3, 2, 8),
        machine.rv64.Instruction.store_double(2, 3, 8),
        machine.rv64.Instruction.branch_equal(2, 3, -4),
        machine.rv64.Instruction.branch_not_equal(2, 3, 4),
        machine.rv64.Instruction.branch_greater_equal(2, 3, 4),
        machine.rv64.Instruction.jump_and_link(1, 8),
        machine.rv64.Instruction.jump_and_link_register(1, 2, 8),
    ]
    assert len({instruction.kind for instruction in instructions}) == 12
    for instruction in instructions:
        assert machine.rv64.Instruction.decode(instruction.encode()) == instruction

    with pytest.raises(ValueError, match="InvalidRegister"):
        machine.rv64.Instruction.add(32, 1, 2)
    with pytest.raises(ValueError, match="MisalignedImmediate"):
        machine.rv64.Instruction.branch_equal(1, 2, 3)


def test_rv64_step_preserves_x0_and_uses_instruction_pc_for_branches() -> None:
    add = machine.rv64.Instruction.add(0, 1, 2)
    branch = machine.rv64.Instruction.branch_not_equal(1, 2, -4)
    program = machine.rv64.Program(0, rv64_code(add, branch))
    state = machine.rv64.State(machine.a0.Memory.zeroed(0), 0)
    state = state.with_register(0, 99).with_register(1, 7).with_register(2, 5)
    after_add = machine.rv64.step(program, state)
    assert after_add.register(0) == 0
    assert after_add.pc == 4
    after_branch = machine.rv64.step(program, after_add)
    assert after_branch.pc == 0


def test_rv64_load_store_projection_and_atomic_trap() -> None:
    store = machine.rv64.Instruction.store_double(1, 2, 0)
    load = machine.rv64.Instruction.load_double(3, 1, 0)
    program = machine.rv64.Program(0, rv64_code(store, load))
    state = machine.rv64.State(machine.a0.Memory.zeroed(8), 0)
    state = state.with_register(1, 0).with_register(2, 0x0123456789ABCDEF)
    stored = machine.rv64.step(program, state)
    loaded = machine.rv64.step(program, stored)
    assert loaded.register(3) == 0x0123456789ABCDEF
    assert loaded.memory.entries() == list(enumerate(bytes.fromhex("efcdab8967452301")))

    projection = machine.rv64.project_state(loaded, [3, 0])
    assert projection.registers == [(0, 0), (3, 0x0123456789ABCDEF)]
    assert projection.pc == 8
    with pytest.raises(ValueError, match="DuplicateRegister"):
        machine.rv64.project_state(loaded, [3, 3])

    small = machine.rv64.State(machine.a0.Memory.zeroed(7), 0)
    small = small.with_register(2, 0x0123456789ABCDEF)
    trapped = machine.rv64.step(program, small)
    assert trapped.outcome.kind == "trapped"
    assert trapped.outcome.trap.kind == "data-access-fault"
    assert trapped.memory.entries() == list(enumerate(bytes(7)))


def test_rv64_source_identity_and_all_declared_traps_are_visible() -> None:
    assert machine.rv64.SOURCE_RELEASE == "20260120"
    assert len(machine.rv64.SOURCE_SHA256) == 64
    assert machine.rv64.RV64I_VERSION == "2.1"
    assert len(machine.rv64.SELECTED_FORMS) == 12

    empty = machine.a0.Memory.zeroed(0)
    cases = [
        (
            machine.rv64.Program(0, bytes(4)),
            machine.rv64.State(empty, 2),
            "instruction-address-misaligned",
        ),
        (
            machine.rv64.Program(0, bytes(4)),
            machine.rv64.State(empty, 4),
            "incomplete-instruction-fetch",
        ),
        (
            machine.rv64.Program(0, bytes(4)),
            machine.rv64.State(empty, 0),
            "illegal-instruction",
        ),
        (
            machine.rv64.Program(0, rv64_code(machine.rv64.Instruction.load_double(2, 1, 0))),
            machine.rv64.State(machine.a0.Memory.zeroed(8), 0).with_register(1, 1),
            "data-address-misaligned",
        ),
        (
            machine.rv64.Program(0, rv64_code(machine.rv64.Instruction.load_double(2, 1, 0))),
            machine.rv64.State(machine.a0.Memory.zeroed(7), 0),
            "data-access-fault",
        ),
    ]
    for program, state, expected in cases:
        trapped = machine.rv64.step(program, state)
        assert trapped.outcome.trap.kind == expected
        assert machine.rv64.step(program, trapped).registers == trapped.registers
