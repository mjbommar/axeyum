from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('concept_coverage',ROOT/'scripts/validate-autogenesis-concept-coverage-projection.py');assert SPEC and SPEC.loader
CC=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(CC)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=json.loads((ROOT/'artifacts/autogenesis/concept-coverage-projection-v1.json').read_text())
 def test_current_valid(self):self.assertEqual(CC.validate(self.data),[])
 def test_invented_formal_count_rejected(self):
  d=copy.deepcopy(self.data);r=next(r for r in d['concepts'] if r['qualified_formalization_fact_ids']);r['qualified_formalization_fact_count']+=1;self.assertTrue(any('formalization count' in e for e in CC.validate(d)))
 def test_topic_only_cannot_claim_formalization(self):
  d=copy.deepcopy(self.data);r=next(r for r in d['concepts'] if not r['qualified_formalization_fact_ids']);r['coverage_state']='fact-formalization-present';self.assertTrue(any('conflates' in e for e in CC.validate(d)))
if __name__=='__main__':unittest.main()
