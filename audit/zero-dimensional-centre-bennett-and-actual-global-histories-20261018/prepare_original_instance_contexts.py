"""Describe only exact original instance routes witnessed by frozen ALL proof values."""
from pathlib import Path
import hashlib,json,subprocess
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
whole=json.loads((A/'provenance.json').read_text());support=json.loads((A/'original-major-support-provenance.json').read_text())
rows=[]
specs=[('HironakaActualHomogeneousInitialHS','actual_initial_product_degree_lift','IsOrderedRing.toIsOrderedAddMonoid'),('HironakaActualFiniteInitialGeneration','actualFormalQuotient_vertex_product_component','IsOrderedRing.toIsOrderedAddMonoid'),('HironakaActualFiniteInitialGeneration','actualHomogeneousInitialIdeal_eq_initial_vertex_span','IsOrderedRing.toIsOrderedAddMonoid'),('HironakaActualPointUnitCoordinateChange','actualPointUnitGermEquiv_dehomogenization','SubsemiringClass.toAddSubmonoidClass'),('HironakaActualPointInitialIdealInclusion','actual_dehomogenized_component_mem_axis_normalized_image','SubsemiringClass.toAddSubmonoidClass'),('TranslatedInitialHSOriginalExact','translated_initial_zero','SubsemiringClass.toAddSubmonoidClass')]
contexts={}
for stem,decl,selector in specs:
 rec=next(r for r in whole+support if r['destination_module'].split('.')[-1]==stem)
 p=ROOT/rec['destination_path'];text=p.read_text()
 token=('private theorem ' if decl=='translated_initial_zero' else 'theorem ')+decl
 pos=text.index(token);start=pos
 preceding=text[:pos].rstrip()
 if preceding.endswith('-/') and preceding.rfind('/--')>preceding.rfind('\n\n'):
  start=preceding.rfind('/--')
 before=text[start:pos+len(token)]
 prefix='attribute [local instance 2000] '+selector+' in\n'
 change={'before':before,'after':prefix+before,'kind':'declaration_local_recovery_of_original_compiled_instance_route','actual_original_selector':selector,'original_declaration':decl,'reason':'Exact original instance projection occurs in retained frozen native entire proof Expr; public imported context currently selects a different route. Recover the original declaration-local route, retaining the entire original declaration and proof byte-for-byte. No new instances or source theorem tokens.'}
 contexts.setdefault(rec['destination_module'],[]).append(change)
 family='support' if stem=='TranslatedInitialHSOriginalExact' else 'whole'
 report=json.loads((A/('strict-'+family+'-expression-comparison.json')).read_text())
 diffs=[d for d in report['differences'] if d['constant'][1].endswith('.'+decl)]
 assert len(diffs)==1
 rows.append({'destination_module':rec['destination_module'],'destination_path':rec['destination_path'],'source_before_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'source_parent_module':rec.get('source_module',rec.get('source_parent_module')),'source_parent_sha256':rec.get('source_sha256',rec.get('source_parent_sha256')),'original_selector':selector,'complete_frozen_difference':diffs[0],'proof_type_tokens_edited':0,'candidate_change':change})
(A/'original-instance-context-restorations.json').write_text(json.dumps(contexts,indent=2)+'\n')
(A/'original-instance-context-evidence.json').write_text(json.dumps({'status':'CANDIDATE_ORIGINAL_CONTEXT_RECOVERY_REVIEW_AND_STRICT_PROOF_CHECK_PENDING','native_and_public_root_inventories_identical':True,'complete_native_captures_retained':'strict-attempt-01/retained-unfiltered-capture-manifest.json','original_parent_captures_complete':True,'context_source_only_changes':rows,'precedent':'audit/analytic-completion-and-global-curve-atlas-20261018/original-instance-context-provenance.json','numeric_names_or_binders_normalized':False,'serializer_changes':False},indent=2)+'\n')
print(json.dumps({'declarations':len(rows),'modules':len(contexts),'source_files_not_edited_here':True}))
