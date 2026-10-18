"""Recover complete older original producers and exact original support declarations.

All mathematics comes from the fixed ordinary published native443 revision.
Complete original blueprint nodes precede their newly recovered Lean sources.
"""
from pathlib import Path
import argparse,ast,hashlib,json,re,subprocess,sys
sys.dont_write_bytecode=True
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
REV='6a888f9dc4155b9ec1407b27223eb37218957159'
SOURCE=Path('/workspace/archon-nakamaye-main')
HEADER='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
sha=lambda raw:hashlib.sha256(raw).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');p.add_argument('--source-root',type=Path,default=SOURCE);args=p.parse_args();SOURCE=args.source_root
def show(path):return subprocess.check_output(['git','-C',str(SOURCE),'show',REV+':'+path])
def install(path,raw,before=None):
 raw=raw.encode()if isinstance(raw,str)else raw;target=ROOT/path
 if args.check:assert target.read_bytes()==raw,path
 elif target.exists():
  assert target.read_bytes()==raw or(before is not None and target.read_bytes()==before),('Unexpected existing file',path)
  target.write_bytes(raw)
 else:target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw)
def save(name,value):
 raw=(json.dumps(value,indent=2)+'\n').encode()
 if args.check:assert(A/name).read_bytes()==raw,name
 else:(A/name).write_bytes(raw)
sys.path.insert(0,str(ROOT/'scripts'))
import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['','2','3','4']])
FROZEN=ROOT/'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
frozen=FROZEN.read_text();fn=next(n for n in ast.parse(frozen).body if isinstance(n,ast.FunctionDef)and n.name=='relocate');flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])');env={'re':re,'names':names,'flat':flat,'fq':fq};exec(compile(ast.Module(body=[fn],type_ignores=[]),str(FROZEN),'exec'),env);relocate=env['relocate']
external=json.loads((ROOT/'scripts/upstream_blueprint_external_bindings.json').read_text());unbound=json.loads((ROOT/'scripts/upstream_blueprint_unbound_bindings.json').read_text())
bindings=lambda text,kind='lean':[x.strip()for group in re.findall(r'\\'+kind+r'\{([^}]+)\}',text)for x in group.split(',')]
blueprints=[]
def blueprint(stem,fragment=None,destination=None,title=None):
 path='TranscendentalNakamaye/blueprint/src/'+stem+'.tex';raw=show(path);text=raw.decode();selected=fragment(text)if fragment else text
 if fragment:
  archive=A/'original-blueprint-parents'/(stem+'.tex');install(str(archive.relative_to(ROOT)),raw)
  output='\\section{'+title+'}\n\n'+names.rename_text_names(selected)
 else:output=names.rename_text_names(text).replace('\\chapter{','\\section{')
 output=annotate(output,external,unbound);dst='blueprint/'+(destination or stem)+'.tex';install(dst,output)
 blueprints.append({'published_source_revision':REV,'source_path':path,'source_sha256':sha(raw),'source_kind':'complete_original_statement_and_proof_fragment'if fragment else'whole_original_chapter','selected_original_source_sha256':sha(selected.encode()),'selected_original_source':selected if fragment else None,'destination_path':dst,'destination_sha256':sha(output.encode()),'nodes':len(re.findall(r'\\label\{',output)),'proofs':output.count('\\begin{proof}'),'local_bindings':bindings(output),'upstream_bindings':bindings(output,'upstreamlean'),'unbound_upstream_bindings':bindings(output,'upstreamunbound')})
for stem in ['hironaka-smooth-centre-nearby-stalks-extension','hironaka-smooth-centre-nearby-ideal-extension']:blueprint(stem)
def first_node(text):
 start=text.index('\\begin{lemma}');end=text.index('\\end{proof}',start)+len('\\end{proof}');return text[start:end]+'\n'
def first_two_nodes(text):
 start=text.index('\\begin{theorem}');first=text.index('\\end{proof}',start)+len('\\end{proof}');end=text.index('\\end{proof}',first)+len('\\end{proof}');return text[start:end]+'\n'
blueprint('hironaka-smooth-centre-real-domain-original-stalk-freeness-extension',first_node,'hironaka-original-fixed-flattening-stalk-dictionary-support','Original fixed-flattening whole stalk dictionary')
blueprint('hironaka-smooth-centre-real-domain-actual-ambient-hs-extension',first_two_nodes,'hironaka-original-fixed-real-ambient-hs-dictionary-support','Original complete ambient quotient transport and fixed-real dictionary')

# Blueprint bytes above are present before any recovered Lean source.
whole=[]
for stem in ['HironakaSmoothCentreNearbyStalks','HironakaSmoothCentreNearbyIdeal']:
 module='TranscendentalNakamaye.Pending.'+stem;path='TranscendentalNakamaye/'+module.replace('.','/')+'.lean';raw=show(path);dest=names.new_mod(module);dst=dest.replace('.','/')+'.lean';output=initial=HEADER+relocate(raw.decode());contexts=json.loads((A/'original-instance-context-restorations.json').read_text()).get(dest,[])if(A/'original-instance-context-restorations.json').exists()else[]
 for context in contexts:
  assert output.count(context['before'])==1;output=output.replace(context['before'],context['after'],1)
 install(dst,output,initial.encode())
 whole.append({'source_revision':REV,'published_source_revision':REV,'source_module':module,'source_path':path,'source_sha256':sha(raw),'destination_module':dest,'destination_path':dst,'initial_synchronized_destination_sha256':sha(initial.encode()),'destination_sha256':sha(output.encode()),'administrative_elaboration_contexts':contexts,'additional_pure_support_imports':[],'cohort':'older_original_whole_producer','proof_edits':False})

def original(stem):
 module='TranscendentalNakamaye.Pending.'+stem;path='TranscendentalNakamaye/'+module.replace('.','/')+'.lean';return module,path,show(path).decode()
def declaration(raw,name):
 match=re.search(r'^(?:@\[[^\n]*\] )?(?:private )?(?:theorem|def) '+re.escape(name)+r'\b',raw,re.M);assert match,name
 start=match.start();doc=raw.rfind('/--',0,start)
 if doc>=0 and raw[raw.index('-/',doc)+2:start].strip()=='':start=doc
 tail=raw[match.end():];next_decl=re.search(r'\n(?=/--|(?:@\[[^\n]*\] )?(?:private )?(?:theorem|def) |end\b|section\b)',tail)
 assert next_decl,name
 return raw[start:match.end()+next_decl.start()].rstrip()+'\n'
supports=[]
def support(stem,dest,decls,imports,opens,section_context,scoped='Topology Manifold ContDiff',universe=''):
 module,path,raw=original(stem);bodies=[declaration(raw,n)for n in decls]
 for name,body in zip(decls,bodies):
  assert raw.count(body.rstrip())==1;install(str((A/(stem+'-'+name+'-original.lean.txt')).relative_to(ROOT)),body)
 assert section_context in raw,('Original variable context missing',stem)
 source='set_option autoImplicit false\nopen Set Filter\nopen scoped '+scoped+'\n'+universe+'namespace '+module+'\nnoncomputable section\n'+opens+'\n'+section_context+'\n\n'+'\n'.join(bodies)+'\nend\nend '+module+'\n'
 output=HEADER+''.join('import '+m+'\n'for m in imports)+'\n'+relocate(source);dst=dest.replace('.','/')+'.lean';install(dst,output)
 supports.append({'published_source_revision':REV,'source_parent_module':module,'source_parent_path':path,'source_parent_sha256':sha(raw.encode()),'complete_original_declarations':decls,'complete_declaration_sha256':{n:sha(b.encode())for n,b in zip(decls,bodies)},'original_variable_context':section_context,'original_namespace_context_tokens_selected':opens,'new_imports':imports,'source_generator_template':source,'destination_module':dest,'destination_path':dst,'destination_sha256':sha(output.encode()),'original_type_and_proof_token_changes':0})
manifold='variable {n : ℕ} {M : Type*} [TopologicalSpace M]\n  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]'
support('HironakaSmoothCentreRealDomainOriginalStalkFreeness','Hironaka.Support.OriginalFixedFlatteningStalkDictionaryExact',['whole_original_stalk_dictionary_at_actual_target'],['Hironaka.Resolution.HironakaSmoothCentreNearbyIdeal'],'open FirstPass FirstPass.HolomorphicIdealSheaves HolGerm OkaRelationSheaf\n  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks\n  HironakaSmoothCentreNearbyIdeal HironakaHolomorphicJetRankLoci\n  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations\n  InvertibleIdealQuotient',manifold,'DirectSum Topology Manifold ContDiff')
support('HironakaSmoothCentreRealDomainActualAmbientHS','Hironaka.Support.OriginalFixedRealAmbientHSDictionaryExact',['fixed_real_original_whole_stalk_ambient_hs_dictionary'],['Hironaka.Support.OriginalFixedFlatteningStalkDictionaryExact','Hironaka.Support.GenuineAmbientJetAlgEquivExact'],'open FirstPass FirstPass.HolomorphicIdealSheaves HolGerm\n  HironakaHolomorphicPointJets HironakaSmoothCentreRealDomainOriginalStalkFreeness\n  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreCoherentDomain\n  HironakaSmoothCentreNearbyIdeal HironakaHolomorphicJetRankLoci\n  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations',manifold,'Topology Manifold ContDiff DirectSum')
support('RestrictEmptyTower','Hironaka.Support.OriginalCentresOverAppendHeadExact',['centresOver_step_iff','centresOver_append_iff','centresOver_head'],['Hironaka.Invariant.RestrictEmptyTower'],'open FirstPass FirstPass.BlowupSequences\nopen TranscendentalNakamaye.Pending.BlowupTowers TranscendentalNakamaye.Pending.BlowupTowerTransforms\n  TranscendentalNakamaye.Pending.BlowupTowerSplit','variable {n : ℕ} {X : CMfd.{u} n}',universe='universe u\n')
save('older-whole-source-provenance.json',whole);save('original-support-source-provenance.json',supports);save('supplementary-blueprint-provenance.json',blueprints)
save('prerequisite-source-recovery.json',{'status':'COMPLETE_OLDER_ORIGINAL_SOURCE_AND_BLUEPRINTS_RECOVERED','published_source_revision':REV,'whole_older_modules':2,'pure_original_support_modules':3,'complete_explicit_original_support_declarations':5,'supplementary_blueprints':4,'supplementary_nodes':sum(r['nodes']for r in blueprints),'supplementary_proofs':sum(r['proofs']for r in blueprints),'original_type_and_proof_text_changes':0,'private_ledger_required':False})
print(json.dumps({'whole_older_modules':len(whole),'original_support_modules':len(supports),'explicit_support_declarations':sum(len(r['complete_original_declarations'])for r in supports),'supplementary_blueprints':len(blueprints),'supplementary_proofs':sum(r['proofs']for r in blueprints)}))
