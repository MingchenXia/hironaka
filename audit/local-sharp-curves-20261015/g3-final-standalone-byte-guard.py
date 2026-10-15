from pathlib import Path
import hashlib, json, re, subprocess, sys, difflib
R=Path('/workspace/hironaka')
A=Path('/workspace/archon-nakamaye/TranscendentalNakamaye/audit/hironaka-continuation-20261014-three-lanes')
sha=lambda b:hashlib.sha256(b).hexdigest()
sys.path.insert(0,str(R/'scripts'))
import upstream_namespace_map as names
names.set_api_modules(['TranscendentalNakamaye.Pending.HironakaAPI'+s for s in ['','2','3','4']])
G=['git','--git-dir=/workspace/archon-nakamaye/.archon-horizon/vcs/workspace.git','--work-tree=/workspace/archon-nakamaye']
S=['git','-C',str(R)]
def blobs(g, specs):
    p=subprocess.run(g+['cat-file','--batch'],input=('\n'.join(specs)+'\n').encode(),capture_output=True,check=True)
    at=0; result={}
    for spec in specs:
        end=p.stdout.index(b'\n',at); h=p.stdout[at:end].split(); assert len(h)==3 and h[1]==b'blob',(spec,h)
        size=int(h[2]); at=end+1; result[spec]=p.stdout[at:at+size]; at+=size; assert p.stdout[at:at+1]==b'\n';at+=1
    assert at==len(p.stdout)
    return result
cohorts=[]
for leaf,cp,n in [('local-sharp-curves-20261015','6968ee2596d43d4a5c965a9b0cadad66ec0fc703',87),('controlled-smooth-pullback-20261015','d5d387143239a2776b1e55ef529e65229b120448',95)]:
    d=R/'audit'/leaf
    entries=json.loads((d/'provenance.json').read_text());bp=json.loads((d/'blueprint-provenance.json').read_text())
    assert len(entries)==n and all(e['source_revision']==cp for e in entries)
    cohorts.append((leaf,cp,entries,bp))
imports=json.loads((R/'scripts/upstream_additional_imports.json').read_text());assert len(imports)==21 and all(len(v)==1 for v in imports.values())
typography=json.loads((R/'scripts/upstream_blueprint_typography.json').read_text());assert len(typography)==5 and sum(map(len,typography.values()))==38
contexts=json.loads((R/'scripts/upstream_elaboration_contexts.json').read_text())
assert set(contexts)=={'Hironaka.Resolution.HironakaSmoothSubmersionProjectionIdealColon'}
assert [len(contexts[m]) for m in contexts]==[3]
for x in contexts['Hironaka.Resolution.HironakaSmoothSubmersionProjectionIdealColon']:
    assert x['after']=='attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in\n'+x['before']
repairs=json.loads((R/'scripts/upstream_original_context_repairs.json').read_text());assert len(repairs)==2
repair=repairs[0];assert repair['protected_module']=='Hironaka.MarkedIdeal.GermIdealOrderValue'
assert repair['before']=='variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]\n  [IsComplexManifold n M]\n'
assert repair['after']=='variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]\nvariable {N : Set M} {x : M} {g : M → ℂ}\nvariable {𝔞 : GermIdeal n M}\n'
callee=repairs[1];assert callee['protected_module']=='Hironaka.Analytic.HolomorphicGermReducednessBridge'
assert callee['replacements']==[
    {'before':'import Hironaka.Analytic.AnalyticJacobianSingularCore\n','after':'import Mathlib.Analysis.CStarAlgebra.Classes\nimport Hironaka.Analytic.AnalyticJacobianSingularCore\n','role':'Restore availability of the original complex CStar instance definition.'},
    {'before':'/-- A coordinate projection is holomorphic as a germ at the origin. -/\ntheorem eventually_differentiableAt_coordinate (j : Fin n) :','after':'attribute [local instance 2000] CommCStarAlgebra.toNormedCommRing in\n/-- A coordinate projection is holomorphic as a germ at the origin. -/\ntheorem eventually_differentiableAt_coordinate (j : Fin n) :','role':'Restore the original declaration-local outer projection priority; original doccomment, statement and proof retained.'}]
external=json.loads((R/'scripts/upstream_blueprint_external_bindings.json').read_text());unbound=set(json.loads((R/'scripts/upstream_blueprint_unbound_bindings.json').read_text()))
assert len(external)==len(set(external.values()))==243 and len(unbound)==2 and unbound<=set(external.values())
assert all(names.rename_text_names(v)==k for k,v in external.items())
upstream=json.loads((R/'audit/local-sharp-curves-20261015/upstream-only-binding-provenance.json').read_text());assert len(upstream)==243
assert {e['canonical_public_name']:e['original'] for e in upstream}==external
published='7d0a4d88308ef45c16f25c2e9991e76c1f6ae4b4'
specs=list(dict.fromkeys([cp+':'+e['source_path'] for _,cp,es,bs in cohorts for e in es+bs]+[cp+':'+e['source_path'] for e in upstream if e['original'] not in unbound for cp in [e['native_checkpoint'],published]]+[x['source_revision']+':'+x['source_path'] for x in repairs]))
native=blobs(G,specs)
for e in upstream:
    if e['original'] in unbound:
        assert e['status']=='PRESERVED_HISTORICAL_UNBOUND_REFERENCE';continue
    assert e['status']=='ACTUAL_UPSTREAM_CONSTANT_STANDARD_THREE'
    assert sha(native[e['native_checkpoint']+':'+e['source_path']])==e['source_sha256']
    assert sha(native[published+':'+e['source_path']])==e['source_sha256']
    assert e['published_source_url']=='https://github.com/MingchenXia/archon-nakamaye/blob/'+published+'/'+e['source_path']
probe=(R/'audit/local-sharp-curves-20261015/upstream-actual-blueprint-bindings.log').read_text()
actual_upstream=dict(re.findall(r'^UPSTREAM_ACTUAL_BINDING (\S+) OWNER (\S+)$',probe,re.M))
assert set(actual_upstream)==set(external.values())-unbound and len(actual_upstream)==241
assert set(re.findall(r'^PRESERVED_BASELINE_UNBOUND_REFERENCE (\S+)$',probe,re.M))==unbound
assert 'EXACT_UPSTREAM_BLUEPRINT_BINDINGS 241; BASELINE_UNBOUND_REFERENCES 2; STANDARD_THREE_ONLY' in probe
assert all(e['actual_owner_module']==actual_upstream[e['original']] for e in upstream if e['original'] not in unbound)
frozen=json.loads((R/'audit/local-sharp-curves-20261015/final-export-configuration-sha256.json').read_text())
assert all(sha((R/p).read_bytes())==h for p,h in frozen.items()),'final configuration changed'
flat=names.flattened_short();fq=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
def canon(s,multiline_open=True):
    out=[];in_open=False
    for line in s.splitlines(keepends=True):
        m=re.fullmatch(r'import (TranscendentalNakamaye\.[\w.]+)\s*',line)
        if m:out.append('import '+names.new_mod(m.group(1))+'\n');continue
        line=fq.sub('Hironaka.',names.rename_text_names(line))
        if re.match(r'^\s*(namespace|end|section)\b',line):line=re.sub(r'(?<![\w.])(FirstPass|Pending)\.','',line)
        else:line=re.sub(r'(?<![\w.])(FirstPass|Pending)\.','Hironaka.',line)
        if re.match(r'^\S',line) or re.match(r'^\s*open\b',line):in_open=bool(re.match(r'^\s*open\b',line))
        if in_open if multiline_open else bool(re.match(r'^\s*open\b',line)):
            line=' '.join(t for t in line.split(' ') if t.strip() not in ('FirstPass','Pending',*flat))
            if re.fullmatch(r'\s*open\s*',line):line='\n'
        out.append(line)
    return header+''.join(out)
def bp_scope(s):
    # Independent metadata reconstruction; no exporter helper is imported.
    blocks=re.split(r'(?=\\begin\{(?:lemma|theorem|proposition|corollary|definition|remark|convention)\})',s)
    out=[]
    for block in blocks:
        original=[x.strip() for g in re.findall(r'\\lean\{([^}]+)\}',block) for x in g.split(',')]
        def attach(match):
            groups=[]
            for x in [x.strip() for x in match[1].split(',')]:
                native_name=external.get(x)
                kind='lean' if native_name is None else ('upstreamunbound' if native_name in unbound else 'upstreamlean')
                value=x if native_name is None else native_name
                if groups and groups[-1][0]==kind:groups[-1][1].append(value)
                else:groups.append((kind,[value]))
            return ''.join('\\'+kind+'{'+','.join(xs)+'}' for kind,xs in groups)
        block=re.sub(r'\\lean\{([^}]+)\}',attach,block)
        if any(x in external for x in original):
            status='historicalleanok' if any(external.get(x) in unbound for x in original) else ('mixedleanok' if any(x not in external for x in original) else 'upstreamleanok')
            block=block.replace('\\leanok','\\'+status)
        out.append(block)
    return ''.join(out)
def strip_attachment_metadata(s):
    s=re.sub(r'\\(?:lean|upstreamlean|upstreamunbound)\{[^}]+\}','',s)
    return re.sub(r'\\(?:leanok|upstreamleanok|mixedleanok|historicalleanok)','',s)
open_changes=[];allbindings=[];local_bindings=[];verified_bindings=[];unbound_bindings=[];own_bindings=set();seen=set();callers=[];reports=[];bp_paths=set();old=json.loads((R/'audit/local-sharp-curves-20261015/preceding-source-manifest.json').read_text())
for leaf,cp,es,bs in cohorts:
    nodes=proofs=bindings=original_lines=0
    for e in es:
        raw=native[cp+':'+e['source_path']];assert sha(raw)==e['source_sha256'];src=raw.decode();m=names.new_mod(e['source_module']);assert m==e['destination_module'] and m not in seen;seen.add(m)
        p=m.replace('.','/')+'.lean';assert p not in old
        init=canon(src);oldinit=canon(src,False)
        if init!=oldinit:
            diff=list(difflib.ndiff(oldinit.splitlines(keepends=True),init.splitlines(keepends=True)));removed=[x[2:] for x in diff if x.startswith('- ')];added=[x[2:] for x in diff if x.startswith('+ ')];assert len(removed)==len(added)==1 and removed[0].split().count('FirstPass')==1 and removed[0].replace('FirstPass ','',1)==added[0];open_changes.append(dict(module=m,old_initial_sha=sha(oldinit.encode()),final_initial_sha=sha(init.encode()),before=removed[0],after=added[0]))
        assert sha(init.encode())==e['initial_synchronized_destination_sha256'];out=init
        adjustments=contexts.get(m,[]);assert e['administrative_elaboration_contexts']==adjustments
        for x in adjustments:
            assert out.count(x['before'])==1;out=out.replace(x['before'],x['after'])
        after_context=out;extras=imports.get(m,[]);assert extras==e['additional_pure_support_imports']
        for extra in extras:
            assert (R/(extra.replace('.','/')+'.lean')).is_file();line='import '+extra+'\n';assert line not in init;i=re.search(r'^import ',out,re.M).start();out=out[:i]+line+out[i:]
        assert sha(out.encode())==e['destination_sha256'] and (R/p).read_bytes()==out.encode(),p
        if extras:
            first=re.search(r'^import ',out,re.M).start();line='import '+extras[0]+'\n';assert out.index(line)==first and out.count(line)==1 and out.replace(line,'',1)==after_context
            callers.append(dict(module=m,extra=extras[0],initial_sha=sha(init.encode()),final_sha=sha(out.encode())))
        for mod in re.findall(r'^import ([\w.]+)',out,re.M):
            if mod.startswith('Hironaka.'):assert (R/(mod.replace('.','/')+'.lean')).is_file(),(m,mod)
        original_lines+=len(src.splitlines())
    for e in bs:
        raw=native[cp+':'+e['source_path']];assert sha(raw)==e['source_sha256'];src=raw.decode();out=names.rename_text_names(src).replace('\\chapter{','\\section{');p=e['destination_path'];assert p not in bp_paths;bp_paths.add(p)
        adjustments=typography.get(Path(p).name,[])
        if leaf=='local-sharp-curves-20261015':assert not adjustments
        for adjustment in adjustments:
            assert out.count(adjustment['before'])==1;out=out.replace(adjustment['before'],adjustment['after'])
        before_scope=out;out=bp_scope(out)
        assert strip_attachment_metadata(before_scope)==strip_attachment_metadata(out),'BP mathematical text changed'
        assert sha(out.encode())==e['destination_sha256'] and (R/p).read_bytes()==out.encode(),p
        for macro,field,acc in [('lean','local_bindings',local_bindings),('upstreamlean','upstream_bindings',verified_bindings),('upstreamunbound','unbound_upstream_bindings',unbound_bindings)]:
            xs=[x.strip() for g in re.findall(r'\\'+macro+r'\{([^}]+)\}',out) for x in g.split(',')]
            assert xs==e[field];acc.extend(xs)
        nn=len(re.findall(r'\\label\{',src));pp=src.count('\\begin{proof}');bb=[b.strip() for group in re.findall(r'\\lean\{([^}]+)\}',src) for b in group.split(',')]
        assert nn==e['nodes'] and pp==e['proofs'] and bb==e['bindings'];nodes+=nn;proofs+=pp;bindings+=len(bb);allbindings.extend(bb)
        own_bindings.update(names.rename_text_names(b) for b in bb if any(b.startswith(x['source_module']+'.') for x in es))
        line='\\input{'+Path(p).stem+'}';assert (R/'blueprint/extensions.tex').read_text().splitlines().count(line)==1
    reports.append(dict(cohort=leaf,revision=cp,whole_modules=len(es),original_Lean_lines=original_lines,whole_BP_chapters=len(bs),nodes=nodes,complete_proofs=proofs,exact_bindings=bindings))
assert len(open_changes)==1 and open_changes[0]['module']=='Hironaka.Resolution.HironakaSharpActualCurveTwoPhaseDefectErasure'
assert set(imports)=={c['module'] for c in callers} and len(seen)==182 and len(callers)==21
whole_files={str(p.relative_to(R)) for p in (R/'Hironaka').rglob('*.lean')}
support_paths=sorted(whole_files-set(old)-{m.replace('.','/')+'.lean' for m in seen})
assert len(whole_files)==743 and len(support_paths)==16
support_hashes={p:sha((R/p).read_bytes()) for p in support_paths}
assert len(set(local_bindings))==1991 and len(set(verified_bindings))==241 and len(set(unbound_bindings))==2
assert set(verified_bindings)==set(actual_upstream) and set(unbound_bindings)==unbound
assert set(local_bindings).isdisjoint(external) and len(own_bindings)==1375 and own_bindings<=set(local_bindings)
assert set(names.rename_text_names(x) for x in allbindings)==set(local_bindings)|set(external)
BASE='6c2b1c10e592e92801955a6d03718ecbcf5794dc'
base=blobs(S,[BASE+':'+p for p in old]+[BASE+':Hironaka.lean']);head=blobs(S,['HEAD:'+p for p in old]);assert len(old)==545
repairs_by_path={x['protected_module'].replace('.','/')+'.lean':x for x in repairs}
for p,h in old.items():
    assert sha(base[BASE+':'+p])==h,p
    if p in repairs_by_path:
        x=repairs_by_path[p];assert h==x['prior_sha256'];s=base[BASE+':'+p].decode()
        for delta in x.get('replacements',[{'before':x.get('before'),'after':x.get('after')}]):
            assert delta['before'] and s.count(delta['before'])==1;s=s.replace(delta['before'],delta['after'],1)
        expected=s.encode();assert sha(expected)==x['after_sha256'] and (R/p).read_bytes()==expected
        assert sha(head['HEAD:'+p]) in {h,x['after_sha256']},p
    else:assert sha((R/p).read_bytes())==sha(head['HEAD:'+p])==h,p
for x in repairs:
    original_context_source=native[x['source_revision']+':'+x['source_path']];assert sha(original_context_source)==x['source_whole_sha256']
    field='definition' if 'complete_unchanged_definition_interval_inclusive' in x else 'declaration'
    lo,hi=x['complete_unchanged_'+field+'_interval_inclusive'];original_def=''.join(original_context_source.decode().splitlines(keepends=True)[lo-1:hi]);assert sha(original_def.encode())==x['complete_unchanged_'+field+'_sha256']
    assert names.rename_text_names(original_def) in (R/(x['protected_module'].replace('.','/')+'.lean')).read_text()
root=(R/'Hironaka.lean').read_text();root_old=base[BASE+':Hironaka.lean'].decode();marker=root.index('/-!');om=root_old.index('/-!');roots=['Hironaka.Resolution.HironakaSharpActualCurveLocalSharpEndpoints','Hironaka.Resolution.HironakaOriginalUntestedControlledSmoothPullback'];root_lines=['import '+m for m in roots]
for line in root_lines:assert root.splitlines().count(line)==1 and root.index(line)<marker
assert root[marker:]==root_old[om:],'old complete root document/EOF changed'
changes=list(difflib.ndiff(root_old.splitlines(keepends=True),root.splitlines(keepends=True)))
assert not any(x.startswith('- ') for x in changes)
assert all(x[2:].strip() in root_lines or not x[2:].strip() for x in changes if x.startswith('+ '))
hashes=frozen
report=dict(status='PASS_FINAL_WHOLE_SOURCE_AND_BP_RECONSTRUCTION',cohorts=reports,whole_Lean_modules=182,administrative_multiline_open_changes=open_changes,administrative_local_elaboration_prefixes=contexts,raw_BP_bindings=len(allbindings),unique_BP_bindings=len(set(allbindings)),local_distinct_bindings=1991,verified_upstream_distinct_bindings=241,historical_unbound_distinct_bindings=sorted(unbound),own_new182_distinct_bindings_local=1375,import_only_callers=callers,whole_protected_math_files=545,protected_byte_identical_files=543,protected_original_context_restorations=repairs,root_imports_exactly_once_before_first_module_doc=roots,root_old_document_and_EOF_exact=True,blueprint_adjustment_chapters=5,blueprint_exact_adjustments=38,no_curve_BP_typography_changes=True,blueprint_statement_and_proof_text_preserved_beyond_explicit_typography=True,final_hashes=hashes,scope='Every complete source/BP reconstructed independently from exact immutable source revisions through canonical import/namespace mapping, explicit21 first imports,3 local administrative TC prefixes,38 typography substitutions, and attachment/status-only identity annotations. Old543 entire bytes exact; two old modules have only explicitly authorized original context restored, each affected declaration statement/body unchanged: unused GermIdealOrder context and actual CStar defining import/local projection priority. Prime consumer has no local prefix or source type annotation. Native241 probe log/source provenance inspected; historical2 explicitly unbound. No new whole build/axiom/AST comparison or Lean execution performed by this guard; earlier OOM exit137 is not a passing kernel audit.')
report.update(total_mathematical_module_files_excluding_root=743,pure_support_module_count=16,pure_support_file_hashes=support_hashes,verified_upstream_published_source_revision=published,verified_upstream_published_file_bytes_equal_native_provenance=True)
report.update(protected_original_standalone_base_revision=BASE,current_standalone_git_head=subprocess.check_output(S+['rev-parse','HEAD']).decode().strip())
(A/'g3-final-standalone-byte-guard.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='import_only_callers'},ensure_ascii=False))
