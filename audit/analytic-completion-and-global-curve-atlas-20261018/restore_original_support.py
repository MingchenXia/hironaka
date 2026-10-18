"""Recover complete original admissibility proofs with every original local context.

The three declarations form the original module's exact initial proof segment.
Compiler .ilean ranges are bound to the normal published frozen source bytes.
"""
from pathlib import Path
import ast,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
SOURCE=Path('/workspace/archon-nakamaye-publish');NATIVE=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
REV='7266ce19c9d3f79a8693f7ded964755af7af59a7';CHECKPOINT='879b6a01452b3d57b502d3f3568df2876f816d66'
sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path.insert(0,str(ROOT/'scripts'));import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['','2','3','4']])
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
frozen=ROOT/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
fn=next(n for n in ast.parse(frozen.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[fn],type_ignores=[]),str(frozen),'exec'))
module='TranscendentalNakamaye.Pending.MemberRestrictAdmissible';source_path='TranscendentalNakamaye/'+module.replace('.','/')+'.lean'
raw=subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+source_path]);assert raw==(NATIVE/(module.replace('.','/')+'.lean')).read_bytes()
text=raw.decode();lines=text.splitlines(keepends=True)
ilean=NATIVE/'.lake/build/lib/lean'/(module.replace('.','/')+'.ilean');decls=json.loads(ilean.read_text())['decls']
selected=['isAdmissibleCentre_memberRestrict_iff',"isAdmissibleCentre_memberRestrict_iff'",'isAdmissibleCentre_lowerMarked_succ_iff']
records=[];pieces=[]
for suffix in selected:
    found=[(n,r) for n,r in decls.items() if n.endswith('.'+suffix)];assert len(found)==1
    name,r=found[0];sl,sc,el,ec=r[:4]
    block=lines[sl][sc:]+''.join(lines[sl+1:el])+lines[el][:ec] if sl!=el else lines[sl][sc:ec]
    assert text.count(block)==1
    sidecar='MemberLowerMarkedAdmissibleExact-'+suffix+'-original.lean.txt'
    (HERE/sidecar).write_text(block)
    records.append({'source_revision':CHECKPOINT,'published_source_revision':REV,'source_module':module,'source_path':source_path,'source_parent_sha256':sha(raw),'compiler_ilean_sha256':sha(ilean.read_bytes()),'actual_original_declaration':name,'compiler_source_range':r[:4],'source_complete_declaration_file':sidecar,'source_complete_declaration_sha256':sha(block.encode()),'destination_module':'Hironaka.Support.MemberLowerMarkedAdmissibleExact','destination_path':'Hironaka/Support/MemberLowerMarkedAdmissibleExact.lean'})
    pieces.append((r[:4],block))
sl,sc,el,ec=pieces[-1][0];prefix=''.join(lines[:el])+lines[el][:ec]
assert all(prefix.count(block)==1 for _,block in pieces)
closing=['end Masked\n','end\n\nend TranscendentalNakamaye.Pending.MemberRestrictAdmissible\n']
assert all(text.count(x)==1 for x in closing)
imports=['Hironaka.Invariant.MemberRestrictAdmissible']
output='/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/\n'+''.join('import '+m+'\n' for m in imports)+relocate(prefix)+'\n\n'+''.join(relocate(x) for x in closing)
p=ROOT/records[0]['destination_path']
prior=json.loads((HERE/'new-support-provenance.json').read_text()) if (HERE/'new-support-provenance.json').exists() else []
if p.exists():
    old=next(r for r in prior if r['destination_path']==records[0]['destination_path']);assert sha(p.read_bytes())==old['destination_sha256'],'Owned support source changed outside this generator'
if not p.exists() or p.read_text()!=output:p.write_text(output)
for record in records:record['destination_sha256']=sha(output.encode())
(HERE/'new-support-provenance.json').write_text(json.dumps(records,indent=2)+'\n')
context={'source_module':module,'source_parent_sha256':sha(raw),'destination_module':records[0]['destination_module'],'destination_path':records[0]['destination_path'],'original_complete_prefix_through_selected_third_declaration':prefix,'original_initial_prelude':''.join(lines[:pieces[0][0][0]]),'original_inter_declaration_contexts':[prefix[prefix.index(a)+len(a):prefix.index(b)] for (_,a),(_,b) in zip(pieces,pieces[1:])],'original_closing_scope_pieces':closing,'pure_existing_imports':imports,'omitted_original_imports_or_opens':[],'omitted_original_proof_tokens':0,'destination_sha256':sha(output.encode())}
(HERE/'original-support-contexts.json').write_text(json.dumps([context],indent=2)+'\n')
(HERE/'additional-pure-support-imports.json').write_text(json.dumps({'Hironaka.Resolution.HironakaOriginalPositiveStepOneCutLowerTest':['Hironaka.Support.MemberLowerMarkedAdmissibleExact']},indent=2)+'\n')
print(json.dumps({'status':'RESTORED_COMPLETE_ORIGINAL_PROOFS_AND_CONTEXTS','support_modules':1,'complete_original_declarations':len(records),'support_sha256':sha(output.encode())}))
