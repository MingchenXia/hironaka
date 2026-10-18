"""Recover complete original prerequisites omitted by the initial partial extraction.

Compiler declaration ranges select complete original text, never replacement proofs.
Every range and context is retained for read-only source replay and full-expression audit.
"""
from pathlib import Path
import ast, hashlib, json, re, subprocess, sys

HERE=Path(__file__).resolve().parent
DEST=HERE.parents[1]
NATIVE=Path('/workspace/archon-nakamaye/TranscendentalNakamaye')
SOURCE_ROOT=NATIVE.parent
CHECKPOINT='db4e4065403b4ab8b077fac41985825931e5cc02'
sys.path.insert(0,str(DEST/'scripts'))
import upstream_namespace_map as names
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
flat=names.flattened_short()
fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
previous=DEST/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
tree=ast.parse(previous.read_text())
relocation=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='relocate')
exec(compile(ast.Module(body=[relocation],type_ignores=[]),str(previous),'exec'))
sha=lambda b:hashlib.sha256(b).hexdigest()
common='variable {n : ℕ} {M : Type*} [TopologicalSpace M]\n  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]\n'
configs=[
 ('Pending.AnalyticDimensionBasics','AnalyticDimensionCoreExact',
  ['ProperOn','LocDimLE','LocDimGE.le_of_locDimLE','DimLE.locDimLE',
   'locDimLE_of_regularAtDim','locDimGE_zero','not_accPt_of_locDimLE_zero'],None,[],
  ['Hironaka.Analytic.RemmertStatements','Hironaka.Analytic.GenericSections']),
 ('Pending.AnalyticSubsetOpens','AnalyticSubsetPresentationsExact',
  ['chartAt_opens_apply','chart_mem_opens_target',
   'presentationPreimageVal','isComplexAnalyticSubset_preimage_val','presentationOfPreimageVal',
   'isComplexAnalyticSubset_of_forall_opens','isComplexAnalyticSubset_iff_forall_opens',
   'isComplexAnalyticSubset_image_val',
   'regularAtDim_image_val_iff','mem_opens_of_regularAtDim_image_val',
   'dimLE_preimage_val','dimLE_image_val_iff','isPureDim_image_val_iff','nhds_opens_eq_comap',
   'locDimGE_preimage_val_iff','locDimLE_preimage_val_iff'],None,['variable {U : Opens M}\n'],
  ['Hironaka.Analytic.RemmertStatements','Hironaka.Analytic.FibreDimensionLowerBound',
   'Hironaka.Analytic.AnalyticImageDimension','Hironaka.Analytic.RemmertSteinCoordinates',
   'Hironaka.Analytic.RemmertSteinFlatBadSet','Hironaka.Analytic.RemmertSteinFlat']),
 ('Pending.ConstantRankSubmanifold','ConstantRankImageGraphExact',
  ['planeSubmodule','exists_image_eq_graph'],'contiguous',[],
  ['Hironaka.Analytic.FiniteMapDimension','Hironaka.Analytic.RemmertSteinCoordinates']),
 ('Pending.AnalyticIrreducibleComponents','AnalyticIrreducibleUnivExact',
  ['isComplexAnalyticallyIrreducible_univ','exists_mem_regularLocus_not_mem_of_not_subset'],None,[],
  ['Hironaka.Analytic.AnalyticComplementConnected']),
 ('FirstPass.AnalyticSubsetTopology','AnalyticIdentityInteriorExact',
  ['IsComplexAnalyticSubset.isClosed_interior','IsComplexAnalyticSubset.eq_univ_of_interior_nonempty',
   'isComplexAnalyticallyIrreducible_univ_of_connectedSpace'],None,[common],
  ['Hironaka.Analytic.AnalyticCodimTwoStratification']),
 ('Pending.RiemannExtension','RiemannBoundedExact',
  ['exists_extension_of_bounded'],'section Parametric',['section Euclidean\n'],
  ['Hironaka.Analytic.RiemannExtensionThin']),
 ('Pending.AnalyticDescendingChain','AnalyticDescendingLocalStableExact',
  ['exists_isOpen_inter_subset_of_chartGerm_le','exists_germ_stable','exists_local_stable'],None,[],
  ['Hironaka.Resolution.HironakaActualWholeAmbientHSSuperlevel']),
 ('Pending.ResolutionInvariantOrder','InvUSCSuperlevelExact',
  ['IsInvUSCOn.isClosed_superlevel'],None,['variable {f : X → Λ} {s t : Set X}\n'],
  ['Hironaka.Resolution.HironakaOriginalCompactUpperCutGlobalPhase']),
 ('Pending.NonmonomialOrderLocal','NonmonomialDiffeoExact',
  ['nmOrd_pullback_diffeo'],'section Order',['section Local\n','variable {M M\' : CMfd.{u} n}\n'],
  ['Hironaka.Resolution.HironakaOriginalWholeContactLowerFirstAnalytic']),
 ('Pending.BlowupTowerSplitIso','TowerIsoBaseCongrExact',
  ['IsTowerIso.congr_base'],None,[],
  ['Hironaka.Resolution.HironakaSharpActualCurvePaddedComparisonRestriction']),
 ('Pending.PositiveDimensionalComponent','PositiveDimensionalAccPtExact',
  ['subset_singleton_of_isPreconnected','exists_isIrreducibleComponent_pos_dim_of_accPt'],None,[],[]),
 ('Pending.HolomorphicConstantRank','HolomorphicNormalFormGraphExact',
  ['image_eq_graph'],None,[],[]),
 ('FirstPass.NonKahlerLocus','OriginalIrreducibleComponentExact',
  ['IsIrreducibleComponent'],'analytic_component_context',[],[]),
 ('Pending.RestrictedIdealExtension','SumIdealCoherentInclusionsExact',
  ['le_sumIdeal_left','le_sumIdeal_right'],None,[],
  ['Hironaka.Resolution.HironakaOriginalCoherentHistoryYearIdeal']),
 ('Pending.RegularLocusComponent','RegularComponentClosureExact',
  ['regularAtDim_closure_component'],None,[],[]),
 ('Pending.ClosureDifferenceAnalytic','IrreducibleOpenEqualityExact',
  ['eq_of_subset_of_inter_open_subset'],None,
  ['variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]\n  [IsComplexManifold n M]\n'],[]),
 ('Pending.IrreducibleComponentFilling','ComponentRegularFillingExact',
  ['exists_isOpen_subset_inter_subset_of_mem','exists_mem_regularLocus_isOpen_inter_subset'],None,[],[]),
 ('Pending.StrictTransformLocus','StrictTransformDensityExact',
  ['subset_of_inter_isOpen_subset','exists_subset_of_inter_isOpen_subset_iUnion'],
  'strict_density_context',[],[]),
 ('Pending.GermIdealOrder','UnitIdealCosupportExact',
  ['cosupport_unitIdeal'],None,['variable {N : Set M} {x : M} {g : M → ℂ}\n', '\nvariable {𝔞 : GermIdeal n M}\n'],
  ['Hironaka.Resolution.HironakaOriginalReferenceValueLocalBlowup']),
 ('FirstPass.ComplexAnalyticSubvarieties','IrreducibleNonemptyExact',
  ['IsComplexAnalyticallyIrreducible.nonempty'],'irreducible_nonempty_context',
  ['variable [hM : IsComplexManifold n M]\n',
   'namespace IsComplexAnalyticallyIrreducible\n','variable {A B C : Set M}\n'],
  ['Hironaka.Analytic.ProperImageIrreducible']),
 ('Pending.DimensionMonotone','LocalDimensionMonotoneExact',
  ['LocDimGE.mono'],None,
  ['variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]\n  [IsComplexManifold n M]\n'],
  ['Hironaka.Analytic.RemmertStatements']),
 ('Pending.HolomorphicGenericRank','HolomorphicMaxRankDenseExact',
  ['subset_closure_maxRank'],None,[],['Hironaka.Analytic.FiniteMapDimension']),
]
records=[];contexts=[];imports={
 'Hironaka.Resolution.HironakaOriginalCoherentCompanionCountOpenNaturality':
 ['Hironaka.Blowup.BlowupTowerRestrictLengthExact'],
 'Hironaka.Resolution.HironakaOriginalReferenceValueLocalBlowup':
 ['Hironaka.Blowup.BlowupStrictIdealControlled'],
 'Hironaka.Analytic.ImageDimensionBound':['Hironaka.Analytic.ThinAnalyticDimensionBound'],
 'Hironaka.Analytic.RemmertSteinGeneral':['Hironaka.Manifold.LocalHolomorphicOpenPartialExact']}
old_records=json.loads((HERE/'new-support-provenance.json').read_text()) if (HERE/'new-support-provenance.json').exists() else []
old_digests={r['destination_path']:r['destination_sha256'] for r in old_records}
old_imports=json.loads((HERE/'additional-pure-support-imports.json').read_text()) if (HERE/'additional-pure-support-imports.json').exists() else {}
support_imports={
 'AnalyticDimensionCoreExact':['Hironaka.Support.PositiveDimensionalAccPtExact',
   'Hironaka.Support.ComponentRegularFillingExact'],
 'ConstantRankImageGraphExact':['Hironaka.Support.HolomorphicNormalFormGraphExact'],
 'AnalyticIrreducibleUnivExact':['Hironaka.Support.AnalyticIdentityInteriorExact'],
 'PositiveDimensionalAccPtExact':['Hironaka.Support.OriginalIrreducibleComponentExact',
   'Hironaka.Support.RegularComponentClosureExact','Hironaka.Support.IrreducibleOpenEqualityExact'],
 'ComponentRegularFillingExact':['Hironaka.Support.StrictTransformDensityExact',
   'Hironaka.Support.OriginalIrreducibleComponentExact'],
 'StrictTransformDensityExact':['Hironaka.Resolution.StrictTransformSubvariety',
   'Hironaka.Support.AnalyticIrreducibleUnivExact'],
 'AnalyticSubsetPresentationsExact':['Hironaka.Analytic.AnalyticSubsetOpenMaps',
   'Hironaka.Support.AnalyticDimensionCoreExact','Hironaka.Analytic.GeometricPureDimension'],
}
parent_imports={'StrictTransformDensityExact':[]}
ledger=['git','--git-dir='+str(SOURCE_ROOT/'.archon-horizon/vcs/workspace.git'),
        '--work-tree='+str(SOURCE_ROOT)]
for short,support,selected,mode,extra,users in configs:
    module='TranscendentalNakamaye.'+short
    source=NATIVE/(module.replace('.','/')+'.lean')
    raw=source.read_bytes();text=raw.decode();lines=text.splitlines(keepends=True)
    source_path=str(source.relative_to(SOURCE_ROOT))
    assert raw==subprocess.check_output(ledger+['show',CHECKPOINT+':'+source_path],cwd=SOURCE_ROOT)
    declarations=json.loads((NATIVE/'.lake/build/lib/lean'/(module.replace('.','/')+'.ilean')).read_text())['decls']
    chosen=[]
    for suffix in selected:
        found=[(n,r) for n,r in declarations.items() if n.endswith('.'+suffix)]
        assert len(found)==1,(module,suffix,found)
        chosen.append(found[0])
    def fragment(r):
        sl,sc,el,ec=r[:4]
        assert not lines[el][ec:].strip(),(module,r)
        return lines[sl][sc:]+''.join(lines[sl+1:el])+lines[el][:ec] if sl!=el else lines[sl][sc:ec]
    first=min(r[0] for r in declarations.values())
    prelude=''.join(lines[:first])
    source_initial_prelude=prelude
    context_adjustments=[]
    if mode=='analytic_component_context':
        # Only original analytic section context is needed by this original
        # definition; the initial partial extraction already owns all types.
        first_context=text.index('variable {n : ℕ} {M : Type*}')
        context_end=text.index('\n\n',first_context)
        prelude='open Set Filter\nopen scoped Topology ENNReal NNReal ContDiff\n'+\
          'namespace TranscendentalNakamaye.FirstPass.NonKahlerLocus\nnoncomputable section\n'+text[first_context:context_end]+'\n'
        context_adjustments.append({'before':source_initial_prelude,'after':prelude,
          'reason':'Select the original analytic namespace, open Set/Filter and scoped notation, noncomputable section and original manifold variables; omit the imported potential theory and unrelated PositiveClasses/NumericalRestrictedVolumeScaffold opens.'})
    elif mode=='irreducible_nonempty_context':
        # Select the original scope commands and variables. The source module's
        # public module/import exposure commands are administrative only and
        # cannot occur after an import of its unchanged public parent.
        prelude=source_initial_prelude[source_initial_prelude.index('open Set\n'):]
        context_adjustments.append({'before':source_initial_prelude,'after':prelude,
          'reason':'Retain the original open/scoped notation, analytic namespace, noncomputable section and manifold variables; omit only the original module/public import/exposure header before importing the unchanged public parent.'})
    elif mode=='strict_density_context':
        # The two complete analytic proofs do not use the later potential or
        # blowup sections. Keep the original density section and its variables,
        # but omit imports and open tokens for those unrelated sections.
        for old in re.findall(r'^import TranscendentalNakamaye\.[^\n]+\n',prelude,re.M):
            prelude=prelude.replace(old,'',1)
            context_adjustments.append({'before':old,'after':'',
              'reason':'The selected original analytic density proofs use only the existing pure strict-transform component geometry, irreducible regular-point support, and the retained original Baire import.'})
        old='open FirstPass FirstPass.PositiveClasses FirstPass.NonKahlerLocus FirstPass.BlowupSequences\n  FirstPass.NumericalRestrictedVolumeScaffold\n'
        new='open FirstPass FirstPass.NonKahlerLocus\n'
        assert prelude.count(old)==1
        prelude=prelude.replace(old,new,1)
        context_adjustments.append({'before':old,'after':new,
          'reason':'Omit only unused original opens for potential, numerical restricted volume and blowup sections outside the selected analytic proof slice.'})
    elif mode and mode!='contiguous':prelude=text[:text.index(mode)]
    if support=='ComponentRegularFillingExact':
        old='import TranscendentalNakamaye.Pending.StrictTransformLocus\n'
        assert prelude.count(old)==1
        prelude=prelude.replace(old,'',1)
        context_adjustments.append({'before':old,'after':'',
          'reason':'Replace the unrelated potential/blowup parent import with the complete original two-proof analytic density slice in Hironaka.Support.StrictTransformDensityExact.'})
    # An omit-command attached to the excluded first declaration is not a
    # section assumption of a later, different extracted declaration.
    prelude=re.sub(r'\nomit [^\n]+\bin\n\s*$','\n',prelude)
    prelude=re.sub(r'\nvariable [^\n]+\bin\n\s*$','\n',prelude)
    for part in extra:assert part in text,(module,part)
    prelude+=''.join(extra)
    blocks=[]
    if mode=='contiguous':
        start=min(r[0] for _,r in chosen);end=max(r[2] for _,r in chosen)
        chosen=sorted([(n,r) for n,r in declarations.items() if start<=r[0] and r[2]<=end],key=lambda p:p[1][0])
        last=max(chosen,key=lambda p:p[1][2])[1]
        blocks=[''.join(lines[start:last[2]])+lines[last[2]][:last[3]]]
    else:
        for name,r in chosen:
            body=fragment(r)
            if r[0]>0 and lines[r[0]-1].startswith('omit '):body=lines[r[0]-1]+body
            blocks.append(body)
    scopes=[]
    for line in prelude.splitlines():
        ns=re.match(r'^namespace (\S+)',line)
        section=re.match(r'^(?:noncomputable )?section(?: (\S+))?\s*$',line)
        if ns:scopes.append(ns[1])
        elif section:scopes.append(section[1] or '')
        elif re.match(r'^end\b',line):scopes.pop()
    destination_module='Hironaka.Support.'+support
    destination_path=destination_module.replace('.','/')+'.lean'
    output='/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/\n'
    output+=''.join('import '+m+'\n' for m in support_imports.get(support,[]))
    output+=''.join('import '+m+'\n' for m in parent_imports.get(support,[names.new_mod(module)]))
    output+=relocate(prelude).replace('Hironaka.NonKahlerLocus','Hironaka')+'\n'
    output+='\n\n'.join(relocate(b) for b in blocks)+'\n\n'+''.join(relocate('end'+(' '+n if n else '')+'\n').replace('Hironaka.NonKahlerLocus','Hironaka') for n in reversed(scopes))
    path=DEST/destination_path
    if path.exists():
        assert sha(path.read_bytes())==old_digests[destination_path],path
        backup=HERE/'rejected-original-support-03'/(path.name+'.'+sha(path.read_bytes())+'.txt');backup.parent.mkdir(exist_ok=True)
        if not backup.exists():backup.write_bytes(path.read_bytes())
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(output)
    for name,r in chosen:
        body=fragment(r);sidecar=name.rsplit('.',1)[-1]+'-'+support+'-original-declaration.lean.txt'
        (HERE/sidecar).write_text(body)
        assert text.count(body)==1 and output.count(relocate(body))==1,name
        records.append({'source_revision':CHECKPOINT,'source_module':module,'source_path':source_path,
          'source_parent_sha256':sha(raw),'actual_original_declaration':name,'compiler_source_range':r[:4],
          'source_complete_declaration_sha256':sha(body.encode()),'source_complete_declaration_file':sidecar,
          'destination_module':destination_module,'destination_path':destination_path,'destination_sha256':sha(output.encode())})
    contexts.append({'source_module':module,'destination_module':destination_module,
       'source_original_initial_prelude':source_initial_prelude,
       'compiler_first_declaration_start_line':first,
       'original_context_selection_mode':mode,
       'original_prelude':prelude,'original_declaration_blocks':blocks,'closing_scopes':list(reversed(scopes)),
       'appended_original_contexts':extra,
       'pure_support_imports':support_imports.get(support,[]),
       'unchanged_parent_imports':parent_imports.get(support,[names.new_mod(module)]),
       'administrative_context_adjustments':context_adjustments,
       'canonical_open_namespace_relocation':{'before':'Hironaka.NonKahlerLocus','after':'Hironaka',
          'reason':'The frozen namespace rules flatten original FirstPass.NonKahlerLocus to the genuine Hironaka namespace; this affects original open context only.'},
       'method':'Exact original compiler source ranges and original local section variables; pure import of unchanged parent. No replacement declaration or proof.'})
    for user in users:imports.setdefault(user,[]).append(destination_module)

provenance=json.loads((HERE/'provenance.json').read_text())
for rec in provenance:
    previous_imports=old_imports.get(rec['destination_module'],[])
    rec['additional_pure_support_imports']=imports.get(rec['destination_module'],[])
    if not rec['additional_pure_support_imports']:continue
    f=DEST/(rec['destination_module'].replace('.','/')+'.lean');s=f.read_text()
    for previous in previous_imports:
        assert s.count('import '+previous+'\n')==1
        s=s.replace('import '+previous+'\n','',1)
    administrative=rec.get('administrative_elaboration_contexts',[])
    for adjustment in reversed(administrative):
        assert s.count(adjustment['after'])==1,(rec['destination_module'],adjustment)
        s=s.replace(adjustment['after'],adjustment['before'],1)
    if 'initial_synchronized_destination_sha256' not in rec:
        rec['initial_synchronized_destination_sha256']=rec['destination_sha256']
    assert sha(s.encode())==rec['initial_synchronized_destination_sha256']
    for adjustment in administrative:
        assert s.count(adjustment['before'])==1,(rec['destination_module'],adjustment)
        s=s.replace(adjustment['before'],adjustment['after'],1)
    first=re.search(r'^import ',s,re.M)
    s=s[:first.start()]+''.join('import '+m+'\n' for m in rec['additional_pure_support_imports'])+s[first.start():]
    f.write_text(s);rec['destination_sha256']=sha(s.encode())
(HERE/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
(HERE/'additional-pure-support-imports.json').write_text(json.dumps(imports,indent=2)+'\n')
(HERE/'new-support-provenance.json').write_text(json.dumps(records,indent=2)+'\n')
(HERE/'original-support-contexts.json').write_text(json.dumps(contexts,indent=2)+'\n')
print('Recovered',len(records),'complete original declarations in',len(contexts),'pure support modules')
