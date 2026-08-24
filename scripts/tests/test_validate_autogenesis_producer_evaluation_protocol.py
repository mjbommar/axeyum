from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2];s=importlib.util.spec_from_file_location('ep',ROOT/'scripts/validate-autogenesis-producer-evaluation-protocol.py');assert s and s.loader;EP=importlib.util.module_from_spec(s);s.loader.exec_module(EP)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=json.loads((ROOT/'artifacts/autogenesis/producer-evaluation-protocol-v1.json').read_text())
 def test_current_valid(self):self.assertEqual(EP.validate(self.data),[])
 def test_missing_decline_class_rejected(self):
  d=copy.deepcopy(self.data);d['outcome_contract']['decline_taxonomy'].pop();self.assertTrue(any('taxonomy' in x for x in EP.validate(d)))
 def test_vacuous_controls_rejected(self):
  d=copy.deepcopy(self.data);d['inputs']['must_decline_control_count']=0;self.assertTrue(any('vacuous' in x for x in EP.validate(d)))
 def test_missing_stage_rejected(self):
  d=copy.deepcopy(self.data);d['outcome_contract']['required_stages'].pop();self.assertTrue(any('stages' in x for x in EP.validate(d)))
if __name__=='__main__':unittest.main()
