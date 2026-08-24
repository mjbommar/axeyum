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
  def test_candidate_status_must_match_candidate(self):
    d=copy.deepcopy(self.data); o=next(o for o in d['obstructions'] if o['candidate_capability'] is not None); o['candidate_capability_internal_status']='not-applicable'; self.assertTrue(any('candidate capability and status disagree' in e for e in OP.validate(d)))
  def test_candidate_capability_status_is_accepted(self):
    self.assertTrue(any(o['candidate_capability_internal_status']=='candidate-in-knowledge-overlay' for o in self.data['obstructions']))
  def test_candidate_status_must_match_overlay(self):
    d=copy.deepcopy(self.data); o=next(o for o in d['obstructions'] if o['candidate_capability_internal_status']=='candidate-in-knowledge-overlay'); o['candidate_capability_internal_status']='active-in-knowledge-overlay'; self.assertTrue(any('does not match knowledge overlay' in e for e in OP.validate(d)))
if __name__=='__main__': unittest.main()
