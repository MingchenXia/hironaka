"""Only new files: reuse preceding original declarations and retain complete missing originals.
No preceding mathematical source, statement, proof or frozen comparison tool is edited.
"""
from pathlib import Path
import hashlib,json,re
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
repairs={
 'Hironaka/Resolution/HironakaSmoothCentreRealDomainSaturation.lean':(['idealFGAt_of_coherentOn'],['Hironaka.Support.RealDomainLocalCoherenceExact']),
 'Hironaka/Resolution/HironakaSmoothCentreRealDomainInitialRelations.lean':(['mk_mem_originalOriginIdeal_iff_of_local'],['Hironaka.Support.RealDomainOriginDictionaryExact']),
 'Hironaka/Resolution/HironakaSmoothCentreRealDomainOriginalStalkFreeness.lean':(['whole_original_stalk_dictionary_at_actual_target'],['Hironaka.Support.OriginalFixedFlatteningStalkDictionaryExact']),
 'Hironaka/Resolution/HironakaOriginalGlobalPrincipalization.lean':(['isInvertible_of_open_cover'],['Hironaka.Support.OriginalInvertibleOpenCoverExact']),
 'Hironaka/MarkedIdeal/MaximalContact.lean':(['iterDerivIdeal_iterDerivIdeal','IsMaximalOrder','IsMaximalOrder.iterDerivIdeal','cosupport_add_subset_cosupport_iterDerivIdeal'],['Hironaka.MarkedIdeal.MaximalOrderDefinition']),
 'Hironaka/Analytic/TowerPreimageCompact.lean':(['exists_restrict_step','proj_mem_cosupp_append','countCentresMeeting_eq_inter_cosupp'],['Hironaka.Invariant.TowerRestrictionStep','Hironaka.Invariant.TowerCosupportCentreCounting']),
}
plan=json.loads((A/'initial-port-plan.json').read_text());provenance=json.loads((A/'provenance.json').read_text());by_path={x['destination_path']:x for x in provenance};out=A/'missing-original-complement-recovery';out.mkdir(exist_ok=True);records=[]
for path,(names,imports)in repairs.items():
 assert path not in plan['existing_destination_math_source_digests'],path
 p=ROOT/path;raw=p.read_bytes();row=by_path[path];assert sha(raw)==row['initial_synchronized_destination_sha256'],('Unexpected new-file change',path)
 text=raw.decode();removed=[]
 for n in names:
  match=re.search(r'^(?:@\[[^\n]*\] )?(?:private )?(?:theorem|def) '+re.escape(n)+r'(?=[\s{(:])',text,re.M);assert match,n
  start=match.start();doc=text.rfind('/--',0,start)
  if doc>=0 and text[text.index('-/',doc)+2:start].strip()=='':start=doc
  if text[:start].endswith('open Classical in\n'):start-=len('open Classical in\n')
  tail=text[match.end():];nxt=re.search(r'\n(?=/--|(?:@\[[^\n]*\] )?(?:private )?(?:theorem|def) |end\b|section\b)',tail);assert nxt,n
  end=match.end()+nxt.start();body=text[start:end];removed.append({'complete_existing_original_declaration':n,'canonical_original_declaration':body,'sha256':sha(body.encode())});text=text[:start]+text[end:]
 at=text.index('import ');text=text[:at]+''.join('import '+m+'\n'for m in imports)+text[at:]
 (out/(p.stem+'-initial-complete-copy.lean.txt')).write_bytes(raw)
 rec={'destination_path':path,'initial_full_copy_sha256':sha(raw),'new_complement_sha256':sha(text.encode()),'reuse_existing_original_imports':imports,'removed_already_present_complete_original_declarations':removed,'complete_missing_original_declaration_and_context_tokens_changed':0,'preceding_mathematical_files_edited':0,'source_blueprint_present_before_recovery':True,'original_parent_module':row['source_module'],'original_parent_source_sha256':row['source_sha256']};records.append(rec);p.write_text(text)
(out/'six-parent-complements.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'new_parent_complements':len(records),'already_present_complete_original_declarations_reused':sum(len(r['removed_already_present_complete_original_declarations'])for r in records),'preceding_sources_edited':0,'proof_or_type_tokens_edited':0}))
