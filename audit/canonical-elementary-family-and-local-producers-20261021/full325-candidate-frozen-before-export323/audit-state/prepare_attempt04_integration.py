"""Stage only reviewed administrative contexts/imports; preserve all prior sources.

This preparation does not write production Lean, frozen profiles, or proof text.
It records the exact previous new-file versions permitted by the source replay.
"""
from pathlib import Path
import hashlib,json,re
A=Path(__file__).resolve().parent;R=A.parents[1]
sha=lambda x:hashlib.sha256(x).hexdigest()
load=lambda n:json.loads((A/n).read_text())
def save(n,x):(A/n).write_text(json.dumps(x,indent=2)+'\n')
C=load('new-original-elaboration-contexts-attempt04-PENDING.json')
I=load('new-original-support-imports-attempt04-PENDING.json')
scopes=load('support-prep/principal-parts/three-division-basis-original-context-scope-map.json')['scopes']
for s in scopes:
 m='Hironaka.Resolution.'+s['module'];p=R/(m.replace('.','/')+'.lean')
 assert sha(p.read_bytes())==s['current_source_sha256']
 assert p.read_text().count(s['before'])==1
 adj={k:s[k]for k in ['before','after']}
 if adj not in C['contexts'].setdefault(m,[]):C['contexts'][m].append(adj)
imports={
 'Hironaka.Resolution.HironakaActualGraphContactCoefficient':['Hironaka.Support.LocalGiraudRegularZeroSetOriginalExact'],
 'Hironaka.Resolution.HironakaActualAnalyticSubspaceRegularityConverse':['Hironaka.Support.ConstantRankImageGraphExact','Hironaka.Support.AnalyticSubsetPresentationsExact'],
 'Hironaka.Resolution.HironakaHomogeneousCanonicalNeighbourhoods':['Hironaka.Support.GeoResolutionRestrictExact'],
 'Hironaka.Resolution.HironakaOriginalStoppedPrefixSmoothComparison':['Hironaka.Support.EmbeddedOriginalRegularPrefixExact'],
 'Hironaka.Resolution.HironakaOriginalBoundaryEmptyFilterComparison':['Hironaka.Support.NormalCrossingsWellFormedSublistOriginalExact'],
 'Hironaka.Resolution.HironakaOriginalFirstMeetingPrefixUniqueness':['Hironaka.Support.RestrictEmptyTowerAppendOriginalExact'],
 'Hironaka.Resolution.HironakaOriginalStoppedBoundaryTransport':['Hironaka.Support.RestrictEmptyTowerAppendOriginalExact'],
 'Hironaka.Resolution.HironakaOriginalFullDimensionIdentity':['Hironaka.Support.IrreducibleFullDimensionOpenOriginalExact'],
 'Hironaka.Resolution.HironakaOriginalLocalCanonicalIrreducibleFamily':['Hironaka.Support.IrreducibleFullDimensionOpenOriginalExact'],
}
for m,ms in imports.items():
 for n in ms:
  if n not in I['imports'].setdefault(m,[]):I['imports'][m].append(n)
S=load('new-original-prerequisite-extracts/plan-attempt04-PENDING.json')
assert len(S)==9
for s in S:
 if s['destination_module']=='Hironaka.Support.EmbeddedOriginalRegularPrefixExact':
  imp='Hironaka.Support.CompactBlowupSurjectiveOriginalExact'
  if imp not in s['imports']:
   s['imports'].insert(0,imp)
   piece=s['canonical_source_layout'][0]
   before=piece['canonical_administrative_context'];assert before.count('import ')==1
   after=before.replace('import ','import '+imp+'\nimport ',1)
   piece['canonical_administrative_context']=after;piece['sha256']=sha(after.encode())
   d=A/'new-original-prerequisite-extracts/EmbeddedOriginalRegularPrefixExact.lean'
   previous=d.read_bytes();assert sha(previous)==s['prepared_destination_sha256']
   s['administrative_additional_support_import']={'import':imp,'before_sha256':sha(previous),'proof_payload_edits':0}
   d.write_text(d.read_text().replace(before,after,1));s['prepared_destination_sha256']=sha(d.read_bytes())
save('new-original-elaboration-contexts-attempt04-PENDING.json',C)
save('new-original-support-imports-attempt04-PENDING.json',I)
save('new-original-prerequisite-extracts/plan-attempt04-PENDING.json',S)
P=load('new-source-context-restoration/preflight.json')
prov={x['destination_module']:x for x in load('provenance.json')}
for m in sorted(set(C['contexts'])|set(I['imports'])):
 row=prov[m];path=row['destination_path'];raw=(R/path).read_bytes();assert sha(raw)==row['destination_sha256'],m
 capture='new-source-context-restoration/attempt03-before04/'+path
 d=A/capture;d.parent.mkdir(parents=True,exist_ok=True)
 if d.exists():assert d.read_bytes()==raw
 else:d.write_bytes(raw)
 if path not in P['sources']:
  P['sources'][path]={'before_sha256':sha(raw),'before_capture':capture}
 p=P['sources'][path];record={'path':capture,'sha256':sha(raw)}
 if sha(raw)!=p['before_sha256']and record not in p.setdefault('approved_intermediate_captures',[]):p['approved_intermediate_captures'].append(record)
 p['new_original_context_commands']=C['contexts'].get(m,[])
 p['new_pure_original_support_imports']=I['imports'].get(m,[])
save('new-source-context-restoration/preflight-attempt04-PENDING.json',P)
profiles=load('new-actual-callee-owner-profiles.json')
for s in S:
 m=s['destination_module']
 if m not in profiles:
  profiles[m]={'scope':'ONLY the actual extracted original physical-module owner; unchanged V3, every numerical/hygienic component preserved',
   'pairs':[{'original_module':s['source_module'],'actual_public_owner':m}],
   'actual_copy_source_sha256':s['prepared_destination_sha256'],'actual_original_source_sha256':s['source_sha256'],
   'complete_original_payload_sha256':s['original_selected_sha256'],'proof_type_edits':0,'frozen_V3_or_comparator_modified':False}
profiles['Hironaka.Resolution.HironakaActualAnalyticSubspaceResidue']={
 'scope':'ONLY the genuine inherited constHom_apply hygienic module frame; all original numbers preserved',
 'pairs':[{'original_module':'TranscendentalNakamaye.Pending.HolomorphicGermRing.1824106335._hygCtx',
 'actual_public_owner':'Hironaka.Support.HolGermMkSubPrimeOriginalExact.1824106335._hygCtx'}],
 'actual_original_complete_callee':'HolGerm.constHom_apply','source_support_plan':'new-original-prerequisite-extracts/plan.json',
 'numeric_scope':1824106335,'hygienic_tail':28,'necessary_affected_capture_recapture':True,'frozen_V3_or_comparator_modified':False}
save('new-actual-callee-owner-profiles-attempt04-PENDING.json',profiles)
print('Staged reviewed attempt04 contexts/imports, nine complete-original supports, exact prior-new-source guards, owner profiles. No production source written.')
