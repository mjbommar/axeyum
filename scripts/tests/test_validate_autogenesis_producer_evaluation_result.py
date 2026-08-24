from __future__ import annotations
import copy,importlib.util,json,pathlib,unittest
ROOT=pathlib.Path(__file__).resolve().parents[2];s=importlib.util.spec_from_file_location('er',ROOT/'scripts/validate-autogenesis-producer-evaluation-result.py');assert s and s.loader;ER=importlib.util.module_from_spec(s);s.loader.exec_module(ER)
class Controls(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  f=json.loads((ROOT/'artifacts/autogenesis/producer-evaluation-frontier-v1.json').read_text());p=ER.sha(ROOT/'artifacts/autogenesis/producer-evaluation-protocol-v1.json');ids=sorted(x for g in f['groups'] for x in g['fact_ids']);cls.data={'schema_version':1,'kind':'axeyum-autogenesis-producer-evaluation-result','protocol_sha256':p,'rows':[{'fact_id':i,'adapter':'declined','producer':'not-reached','reconstruction':'not-reached','checker':'not-reached'} for i in ids],'funnel':{'eligible':len(ids),'proposals':0,'kernel_accepted':0,'cleanly_reproduced':0,'admitted':0}}
 def test_valid_zero_result(self):self.assertEqual(ER.validate(self.data),[])
 def test_missing_row_rejected(self):
  d=copy.deepcopy(self.data);d['rows'].pop();self.assertTrue(any('every evaluation' in x for x in ER.validate(d)))
 def test_control_acceptance_rejected(self):
  d=copy.deepcopy(self.data);control=json.loads((ROOT/'artifacts/autogenesis/producer-evaluation-frontier-v1.json').read_text())['must_decline_control_fact_ids'][0];next(r for r in d['rows'] if r['fact_id']==control)['checker']='admitted';self.assertTrue(any('must-decline' in x for x in ER.validate(d)))
if __name__=='__main__':unittest.main()
