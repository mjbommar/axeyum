from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('family_concept',ROOT/'scripts/validate-autogenesis-family-concept-crosswalk.py');assert SPEC and SPEC.loader
FC=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(FC)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=json.loads((ROOT/'artifacts/autogenesis/family-concept-crosswalk-v1.json').read_text())
 def test_current_valid(self):self.assertEqual(FC.validate(self.data),[])
 def test_duplicate_family_rejected(self):
  d=copy.deepcopy(self.data);d['mappings'].append(copy.deepcopy(d['mappings'][0]));self.assertTrue(any('duplicate family' in e for e in FC.validate(d)))
 def test_unpinned_external_revision_rejected(self):
  d=copy.deepcopy(self.data);d['sources']['math_education']['revision']='0'*40;self.assertTrue(any('revision differs' in e for e in FC.validate(d)))
if __name__=='__main__':unittest.main()
