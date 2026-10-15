"""Read-only replay of this increment from normal, published upstream Git.

Does not need Horizon or the private historical ledger. Every copied module,
complete blueprint and extracted original declaration is byte-checked, after
only the recorded namespace relocation, headers and pure support imports.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
p=argparse.ArgumentParser();p.add_argument('--source-root',type=Path,required=True)
p.add_argument('--revision',default='fb619fede1f7a4e8d4224a1d10756f059ae77513');a=p.parse_args()
audit=Path(__file__).resolve().parent;dest=audit.parents[1]
sys.path.insert(0,str(dest/'scripts'))
import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
sha=lambda s:hashlib.sha256(s).hexdigest()
def show(path):return subprocess.check_output(['git','-C',str(a.source_root),'show',a.revision+':'+path])
assert re.fullmatch('[0-9a-f]{40}',a.revision)
flat=names.flattened_short()
fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
def relocate(source):
 lines=[];in_open=False
 for line in source.splitlines(keepends=True):
  match=re.fullmatch(r'import (TranscendentalNakamaye\.[\w.]+)\s*',line)
  if match:lines.append('import '+names.new_mod(match.group(1))+'\n');continue
  line=fq.sub('Hironaka.',names.rename_text_names(line))
  if re.match(r'^\s*(namespace|end|section)\b',line):line=re.sub(r'(?<![\w.])(FirstPass|Pending)\.', '',line)
  else:line=re.sub(r'(?<![\w.])(FirstPass|Pending)\.', 'Hironaka.',line)
  if re.match(r'^\S',line) or re.match(r'^\s*open\b',line):in_open=bool(re.match(r'^\s*open\b',line))
  if in_open:
   line=' '.join(t for t in line.split(' ') if t.strip() not in ('FirstPass','Pending',*flat))
   if re.fullmatch(r'\s*open\s*',line):line='\n'
  lines.append(line)
 return ''.join(lines)
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
records=json.loads((audit/'provenance.json').read_text());imports=json.loads((audit/'additional-pure-support-imports.json').read_text())
for rec in records:
 raw=show(rec['source_path']);assert sha(raw)==rec['source_sha256'],rec['source_path']
 output=header+relocate(raw.decode());assert sha(output.encode())==rec['initial_synchronized_destination_sha256']
 for x in rec['administrative_elaboration_contexts']:
  assert output.count(x['before'])==1;output=output.replace(x['before'],x['after'])
 extras=rec['additional_pure_support_imports'];assert extras==imports.get(rec['destination_module'],[])
 for extra in extras:assert (dest/(extra.replace('.','/')+'.lean')).is_file()
 if extras:
  first=re.search(r'^import ',output,re.M)
  output=output[:first.start()]+''.join('import '+extra+'\n' for extra in extras)+output[first.start():]
 actual=(dest/(rec['destination_module'].replace('.','/')+'.lean')).read_bytes()
 assert actual==output.encode() and sha(actual)==rec['destination_sha256'],rec['destination_module']
external=json.loads((dest/'scripts/upstream_blueprint_external_bindings.json').read_text())
unbound=json.loads((dest/'scripts/upstream_blueprint_unbound_bindings.json').read_text())
typography=json.loads((dest/'scripts/upstream_blueprint_typography.json').read_text())
bps=json.loads((audit/'blueprint-provenance.json').read_text())
for bp in bps:
 raw=show(bp['source_path']);assert sha(raw)==bp['source_sha256']
 output=names.rename_text_names(raw.decode()).replace('\\chapter{','\\section{')
 for x in typography.get(Path(bp['destination_path']).name,[]):
  assert output.count(x['before'])==1;output=output.replace(x['before'],x['after'])
 output=annotate(output,external,unbound)
 actual=(dest/bp['destination_path']).read_bytes()
 assert actual==output.encode() and sha(actual)==bp['destination_sha256'],bp['destination_path']
 assert output.count('\\begin{proof}')==bp['proofs']
supports=json.loads((audit/'new-support-provenance.json').read_text())
for rec in supports:
 raw=show(rec['source_path']);assert sha(raw)==rec['source_parent_sha256']
 originals=[f for f in audit.glob('*-original-declaration.lean.txt') if sha(f.read_bytes())==rec['source_complete_declaration_sha256']]
 assert len(originals)==1;body=originals[0].read_bytes();assert raw.count(body)==1
 actual=(dest/rec['destination_path']).read_bytes()
 assert sha(actual)==rec['destination_sha256'] and actual.count(relocate(body.decode()).encode())==1
# Preserve every mathematical module of the preceding published checkpoint.
base='a2644ad18502f8b7622ba535ba5e8c6e32156b9f'
old=subprocess.check_output(['git','-C',str(dest),'ls-tree','-r','--name-only',base,'--','Hironaka']).decode().splitlines()
old=[f for f in old if f.endswith('.lean')]
for f in old:
 before=subprocess.check_output(['git','-C',str(dest),'show',base+':'+f]);assert (dest/f).read_bytes()==before,f
oldroot=subprocess.check_output(['git','-C',str(dest),'show',base+':Hironaka.lean']).decode()
newroot=(dest/'Hironaka.lean').read_text();added=['import '+r['destination_module'] for r in records if r['source_module'] in json.loads((audit/'root-source-modules.json').read_text())]
for line in added:assert newroot.count(line+'\n')==1;newroot=newroot.replace(line+'\n\n','',1)
assert newroot==oldroot,'Root has changes beyond the thirteen recorded imports'
receipt={'status':'PASS_EXACT_PUBLISHED_SOURCE_REPLAY_AND_OLD_SOURCE_GUARD','published_native_revision':a.revision,'private_ledger_required':False,'complete_new_modules':len(records),'complete_new_blueprints':len(bps),'complete_original_proofs':sum(bp['proofs'] for bp in bps),'new_support_modules':len(set(r['destination_module'] for r in supports)),'exact_original_support_declarations':len(supports),'old_mathematical_modules_byte_identical':len(old),'root_changes_only_thirteen_recorded_imports':True}
(audit/'published-source-replay.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
