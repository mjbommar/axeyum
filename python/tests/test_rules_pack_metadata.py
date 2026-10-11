"""Public pack loading must enforce Gregorian effective intervals."""
import json
from pathlib import Path
import shutil
import pytest
from axeyum.rules import Pack

SOURCE = Path(__file__).resolve().parents[2] / 'docs/rules-as-code/examples/benefit-eligibility-v0'

@pytest.mark.parametrize('interval', [
    {'from': '2024-02-30', 'to': None},
    {'from': '2024-01-01', 'to': '2024-02-30'},
    {'from': '2024-01-01', 'to': '2024-01-01'},
    {'from': '2024-01-01', 'to': '2023-12-31'},
    {'from': '20240101', 'to': None},
    {'from': '2024-W01-1', 'to': None},
    {'from': True, 'to': None},
    {'to': None},
    None,
])
def test_pack_load_rejects_invalid_effective_interval(tmp_path, interval):
    shutil.copytree(SOURCE, tmp_path / 'pack')
    path = tmp_path / 'pack/metadata.json'
    metadata = json.loads(path.read_text())
    metadata['effective_interval'] = interval
    path.write_text(json.dumps(metadata))
    with pytest.raises(ValueError):
        Pack(tmp_path / 'pack')


def test_pack_load_accepts_leap_day_interval(tmp_path):
    shutil.copytree(SOURCE, tmp_path / 'pack')
    path = tmp_path / 'pack/metadata.json'
    metadata = json.loads(path.read_text())
    metadata['effective_interval'] = {'from': '2024-02-29', 'to': '2024-03-01'}
    path.write_text(json.dumps(metadata))
    assert Pack(tmp_path / 'pack').metadata['effective_interval'] == metadata['effective_interval']
