"""Preserve full325 candidate and stage authorized whole-module export323 scope.

No mathematical source or proof is edited; no within-module declaration is
filtered. Both deferred modules and chapters are copied byte-for-byte to audit.
"""
from pathlib import Path
import json,hashlib,shutil
A=Path(__file__).resolve().parent;R=A.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
P=json.loads((A/'provenance.json').read_text());B=json.loads((A/'blueprint-provenance.json').read_text())
assert len(P)==325 and len(B)==311
names={'Hironaka.Resolution.HironakaOriginalGlobalOffZero','Hironaka.Resolution.HironakaOriginalGlobalProperModification'}
chapters={'blueprint/hironaka-original-global-off-zero-extension.tex','blueprint/hironaka-original-global-proper-modification-extension.tex'}
snap=A/'full325-candidate-frozen-before-export323';snap.mkdir(exist_ok=True)
manifest=[]
def copy(src,dst):
 raw=src.read_bytes();dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert dst.read_bytes()==raw,dst
 else:dst.write_bytes(raw)
 manifest.append({'source':str(src.relative_to(R)),'capture':str(dst.relative_to(A)),'sha256':sha(raw),'bytes':len(raw)})
for p in [*[R/x['destination_path']for x in P],*[R/x['destination_path']for x in B],R/'Hironaka.lean',R/'blueprint/extensions.tex']:
 copy(p,snap/'candidate-files'/p.relative_to(R))
for p in A.glob('*'):
 if p.is_file()and p.suffix in ['.json','.py','.tsv','.txt','.md','.lean']:copy(p,snap/'audit-state'/p.name)
for folder in ['new-original-prerequisite-extracts','new-source-context-restoration','new-kernel']:
 for p in (A/folder).rglob('*'):
  if p.is_file():copy(p,snap/'audit-state'/p.relative_to(A))
for p in [A/'final-per-module-expressions/status.json']:
 copy(p,snap/'audit-state'/p.relative_to(A))
deferred=[]
for row in P:
 if row['destination_module']not in names:continue
 path=row['destination_path'];draft='deferred-complete-modules-20261021/sources/'+path
 copy(R/path,A/draft)
 deferred.append({'module':row['destination_module'],'source_module':row['source_module'],'destination_path':path,'canonical_draft_capture':draft,'sha256':row['destination_sha256'],'source_path':row['source_path'],'original_source_sha256':row['source_sha256'],'reason':'Whole-module strict original/public expression identity is blocked by immutable inherited local-inverse callee type, or imports that blocked module. No claim of synchronized formal export.'})
bp=[]
for row in B:
 if row['destination_path']not in chapters:continue
 path=row['destination_path'];draft='deferred-complete-modules-20261021/'+path
 copy(R/path,A/draft);bp.append({'destination_path':path,'canonical_draft_capture':draft,'sha256':row['destination_sha256'],'complete_written_proofs':row['proofs'],'nodes':row['nodes'],'bindings':row['local_bindings']})
assert len(deferred)==2 and len(bp)==2 and sum(x['complete_written_proofs']for x in bp)==7
partition={'status':'AUTHORIZED_WHOLE_MODULE_PUBLICATION_SCOPE_323_PLUS_2_DEFERRED','published_source_revision':'4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07','full_candidate_new_modules':325,'published_new_modules':323,'deferred_complete_modules':deferred,'deferred_complete_blueprint_chapters':bp,'entire_originals_and_all_raw_differences_retained':True,'within_module_root_filtering':False,'comparator_or_frozen_profile_edits':False,'old1159_sources_unchanged':True,'full_candidate_snapshot':str(snap.relative_to(A)),'full_candidate_umbrella':{'capture':str((snap/'candidate-files/Hironaka.lean').relative_to(A)),'sha256':sha((R/'Hironaka.lean').read_bytes())},'full_candidate_master':{'capture':str((snap/'candidate-files/blueprint/extensions.tex').relative_to(A)),'sha256':sha((R/'blueprint/extensions.tex').read_bytes())},'independent_feasibility_review':'support-prep/canonical-offzero-feasibility/constraint-and-publication-review-canonical.json'}
(A/'deferred-complete-module-partition.json').write_text(json.dumps(partition,indent=2)+'\n')
(snap/'immutable-snapshot-manifest.json').write_text(json.dumps({'scope':'Complete full325 candidate source/proof/plans/status preserved before whole-module publication partition; not an all325 verification PASS','files':manifest},indent=2)+'\n')
print('Preserved full325 candidate and exact whole2source/2chapter audit drafts; no production file removed yet.')
