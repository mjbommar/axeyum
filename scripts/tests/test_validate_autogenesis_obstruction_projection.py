from __future__ import annotations
import copy, importlib.util, json, pathlib, unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('op',ROOT/'scripts/validate-autogenesis-obstruction-projection.py'); assert spec and spec.loader
OP=importlib.util.module_from_spec(spec); spec.loader.exec_module(OP)
class Controls(unittest.TestCase):
  @classmethod
  def setUpClass(cls): cls.data=json.loads((ROOT/'artifacts/autogenesis/obstruction-projection-v1.json').read_text())
  def test_current_valid(self): self.assertEqual(OP.validate(self.data),[])
  def test_invented_resolution_rejected(self):
    d=copy.deepcopy(self.data); d['obstructions'][0]['resolution_commit']='deadbeef'; self.assertTrue(any('unbound resolution' in e for e in OP.validate(d)))
  def test_lost_episode_blocker_rejected(self):
    d=copy.deepcopy(self.data); d['obstructions'][0]['complete_known_blocker_set']=[]; self.assertTrue(any('blocker set' in e for e in OP.validate(d)))
if __name__=='__main__': unittest.main()
