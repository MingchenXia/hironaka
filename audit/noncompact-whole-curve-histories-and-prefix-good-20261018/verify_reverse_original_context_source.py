"""Reverse only recorded administrative contexts, then compare complete sources."""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
SOURCE=Path('/workspace/archon-nakamaye-main');REV='6a888f9dc4155b9ec1407b27223eb37218957159'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
sys.path.insert(0,str(ROOT/'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in['','2','3','4']])
profile=ROOT/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
source=profile.read_text();fn=next(n for n in ast.parse(source).body if isinstance(n,ast.FunctionDef)and n.name=='relocate')
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(profile),'exec'),env)
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
records=json.loads((A/'provenance.json').read_text())+json.loads((A/'older-whole-source-provenance.json').read_text());assert len(records)==16
rows=[]
for r in records:
 raw=subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+r['source_path']]);assert sha(raw)==r['source_sha256']
 current=(ROOT/r['destination_path']).read_bytes();assert sha(current)==r['destination_sha256'];reversed_source=current.decode()
 for c in reversed(r['administrative_elaboration_contexts']):
  assert reversed_source.count(c['after'])==1;reversed_source=reversed_source.replace(c['after'],c['before'],1)
 original=header+env['relocate'](raw.decode());assert reversed_source==original
 rows.append({'module':r['destination_module'],'published_original_sha256':sha(raw),'current_source_sha256':sha(current),'reversed_source_sha256':sha(reversed_source.encode()),'initial_relocated_source_sha256':sha(original.encode()),'recorded_contexts':len(r['administrative_elaboration_contexts'])})
support_rows=[]
for r in json.loads((A/'original-support-source-provenance.json').read_text()):
 raw=subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+r['source_parent_path']]);assert sha(raw)==r['source_parent_sha256']
 assert r['original_variable_context']in raw.decode()
 for declaration,h in r['complete_declaration_sha256'].items():
  body=(A/(r['source_parent_module'].split('.')[-1]+'-'+declaration+'-original.lean.txt')).read_bytes()
  assert sha(body)==h and body.decode().rstrip()in raw.decode()
 current=(ROOT/r['destination_path']).read_bytes();assert sha(current)==r['destination_sha256']
 generated=header+''.join('import '+m+'\n'for m in r['new_imports'])+'\n'+env['relocate'](r['source_generator_template'])
 assert current.decode()==generated
 support_rows.append({'module':r['destination_module'],'source_parent_sha256':sha(raw),'complete_original_declarations':r['complete_declaration_sha256'],'current_source_sha256':sha(current),'recorded_original_generator_exact':True})
assert len(rows)==16 and len(support_rows)==3
(A/'reverse-original-context-source-guard.json').write_text(json.dumps({'status':'PASS_ALL19_ORIGINAL_SOURCES_BYTE_EXACT_AFTER_RECORDED_CONTEXT_REVERSAL','normal_published_revision':REV,'whole_modules':16,'support_modules':3,'complete_explicit_original_support_declarations':5,'original_type_or_proof_token_changes':0,'rows':rows,'support_rows':support_rows},indent=2)+'\n')
print('PASS_ALL19_SOURCE_REVERSE_CONTEXT_AND_COMPLETE_ORIGINAL_SUPPORT_GUARD')
