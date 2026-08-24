from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2]
SPEC=importlib.util.spec_from_file_location('transport_projection',ROOT/'scripts/validate-autogenesis-transport-projection.py');assert SPEC and SPEC.loader
TP=importlib.util.module_from_spec(SPEC);SPEC.loader.exec_module(TP)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):cls.data=json.loads((ROOT/'artifacts/autogenesis/transport-projection-v1.json').read_text())
 def test_current_valid(self):self.assertEqual(TP.validate(self.data),[])
 def test_complete_chain_cannot_lose_binding(self):
  d=copy.deepcopy(self.data);c=next(r for r in d['chains'] if r['status']=='complete');c['checked_evidence_bindings']=[];self.assertTrue(any('lacks evidence binding' in e for e in TP.validate(d)))
 def test_adapter_binding_requires_target_hash(self):
  d=copy.deepcopy(self.data);c=next(r for r in d['chains'] if any(b['binding']=='adapter-goal-and-target' for b in r['checked_evidence_bindings']));c['target_content_sha256']=None;self.assertTrue(any('lacks target-content hash' in e for e in TP.validate(d)))
if __name__=='__main__':unittest.main()
