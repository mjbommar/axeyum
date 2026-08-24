from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('nat_modeq_selection',ROOT/'scripts/validate-autogenesis-nat-modeq-capability-selection.py');assert SPEC and SPEC.loader
NM=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(NM)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=json.loads((ROOT/'artifacts/autogenesis/nat-modeq-capability-selection-v1.json').read_text())
 def test_current_valid(self):self.assertEqual(NM.validate(self.data),[])
 def test_fact_substitution_rejected(self):
  d=copy.deepcopy(self.data);d['selected_facts'][0]='F:ml430-nat-modeq-comm-24b71e7a';self.assertTrue(any('selected fact' in e for e in NM.validate(d)))
 def test_authority_escalation_rejected(self):
  d=copy.deepcopy(self.data);d['state']='registered';self.assertTrue(any('grants too much authority' in e for e in NM.validate(d)))
if __name__=='__main__':unittest.main()
