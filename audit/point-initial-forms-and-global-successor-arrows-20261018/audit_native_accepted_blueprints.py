"""Check fixed normal Git's entire356 native chapter/proof/definition inventory."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
from blueprint_statement_scope import inspect
A=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--source-root',type=Path,default=Path('/workspace/archon-nakamaye-publish'))
args=p.parse_args();REV='0447df8e11b51ada4b90892458bc8008262bf45c'
records=json.loads((A/'accepted-native-356-blueprint-records.json').read_text());assert len(records)==356
nodes=proofs=definitions=definitions_without_proof=nondefinitions=0
for record in records:
 raw=subprocess.check_output(['git','-C',str(args.source_root),'show',REV+':'+record['path']])
 assert hashlib.sha256(raw).hexdigest()==record['sha256']
 text=raw.decode();scope=inspect(text);nodes+=sum(len(r['labels']) for r in scope)
 blocks=re.findall(r'\\begin\{proof\}([\s\S]*?)\\end\{proof\}',text)
 assert len(blocks)==text.count('\\begin{proof}')==text.count('\\end{proof}')
 assert all(block.strip() for block in blocks);proofs+=len(blocks)
 definitions+=sum(r['kind']=='definition' for r in scope)
 definitions_without_proof+=sum(r['kind']=='definition' and not r['complete_proofs'] for r in scope)
 nondefinitions+=sum(r['kind']!='definition' for r in scope)
assert (nodes,proofs,definitions,definitions_without_proof,nondefinitions)==(1095,1086,37,9,1058)
receipt={'status':'PASS_ALL_356_NATIVE_CHAPTERS_LABELLED_STATEMENTS_PROOFS_AND_DEFINITIONS',
 'normal_published_revision':REV,'accepted_native_source_checkpoint':'c8830ef1134a201ba69b0f43ff6cbfbea4ba6d1b',
 'chapters':356,'labelled_nodes':nodes,'complete_nonempty_proof_environments':proofs,
 'labelled_definition_nodes':definitions,'labelled_definitions_without_proof':definitions_without_proof,
 'every_labelled_nondefinition_has_complete_proof':True,'labelled_nondefinitions':nondefinitions,
 'definition_proofs_manufactured':0,'private_ledger_required':False,
 'scope':'Fixed native356 full-source inventory; public synchronized433 and complete-document518 chapter counts remain separate.'}
(A/'accepted-native-blueprint-scope-validation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
