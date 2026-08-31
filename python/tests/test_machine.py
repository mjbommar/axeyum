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
