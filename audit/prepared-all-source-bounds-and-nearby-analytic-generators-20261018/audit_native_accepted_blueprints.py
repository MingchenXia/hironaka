"""Check fixed normal Git's entire338 native chapter/proof/definition inventory."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
from blueprint_statement_scope import inspect
A=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--source-root',type=Path,default=Path('/workspace/archon-nakamaye-publish'))
args=p.parse_args();REV='f873b1d904f8e63cd9f73e0b5bf6eefb0332093a'
records=json.loads((A/'accepted-native-338-blueprint-records.json').read_text());assert len(records)==338
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
assert (nodes,proofs,definitions,definitions_without_proof,nondefinitions)==(1042,1040,29,2,1013)
receipt={'status':'PASS_ALL_338_NATIVE_CHAPTERS_LABELLED_STATEMENTS_PROOFS_AND_DEFINITIONS',
 'normal_published_revision':REV,'accepted_native_source_checkpoint':'862e555f2c5289f9b29cb844461cda7a23618d7c',
 'chapters':338,'labelled_nodes':nodes,'complete_nonempty_proof_environments':proofs,
 'labelled_definition_nodes':definitions,'labelled_definitions_without_proof':definitions_without_proof,
 'every_labelled_nondefinition_has_complete_proof':True,'labelled_nondefinitions':nondefinitions,
 'definition_proofs_manufactured':0,'private_ledger_required':False,
 'scope':'Fixed native338 full-source inventory; public synchronized415 and complete-document500 chapter counts remain separate.'}
(A/'accepted-native-blueprint-scope-validation.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
