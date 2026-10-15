#!/usr/bin/env python3
"""Independent read-only byte/provenance review, NOT a Lean build or math review."""
from pathlib import Path
import difflib, hashlib, importlib.util, json, os, re, subprocess, sys
sys.dont_write_bytecode = True
SRC = Path(os.environ.get('HIRONAKA_REVIEW_SOURCE_ROOT','/workspace/archon-nakamaye'))
DEST = Path(os.environ.get('HIRONAKA_REVIEW_DESTINATION_ROOT','/workspace/hironaka'))
CP = 'd5d387143239a2776b1e55ef529e65229b120448'
READ_CP = os.environ.get('HIRONAKA_REVIEW_PUBLISHED_SOURCE_REVISION',CP)
STANDARD_GIT = os.environ.get('HIRONAKA_REVIEW_STANDARD_GIT')=='1'
OUT = Path(os.environ.get('HIRONAKA_REVIEW_AUDIT_ROOT',str(SRC/'TranscendentalNakamaye/audit/hironaka-continuation-20261014-three-lanes')))
REPORT = Path(os.environ.get('HIRONAKA_REVIEW_REPORT_ROOT',str(OUT)))
AUDIT = DEST/'audit/controlled-smooth-pullback-20261015'
TYPOGRAPHY_SHA256 = '3da11d14bad7066bd53d3386455822275d9a707b4a8286c1508cb0afcbf076df'
BASELINE_SHA256 = '4f2d361605f644a534c98b0a61456a15cdc9d5b9b40a24f57b4b469fcc9728b8'
IMPORTS_SHA256 = 'f7060d38c1541f69063f17e91ba045571504083ec78409927b608535acaf0ea4'
SUPPORT_FILES_SHA256 = '47a5fd3406b9a7e7b9536da943a743d8032b593754daea61a8b91bd02c132c86'
FINAL_METADATA_SHA256 = 'c3fc6cc3298fdad3d4bfbcb5f8f5a02fc7ea86c303d186244daa4dc134afbf3b'
GIT = ['git','-C',str(SRC)]if STANDARD_GIT else['git', f'--git-dir={SRC}/.archon-horizon/vcs/workspace.git', f'--work-tree={SRC}']
sha = lambda b: hashlib.sha256(b).hexdigest()
errors = []
def require(ok, message):
    if not ok: errors.append(message)
def gitout(*args):
    return subprocess.check_output(GIT+list(args), cwd=SRC)
final_raw=(OUT/'g2-controlled-export-reviewed-final-metadata.json').read_bytes()
if sha(final_raw)!=FINAL_METADATA_SHA256:
    raise SystemExit('Final export metadata has not been independently frozen; no old review JSON is overwritten')
final_metadata=json.loads(final_raw)
def reviewed_file(relative):
    raw=(DEST/relative).read_bytes()
    if sha(raw)!=final_metadata['files'][relative]:
        raise SystemExit('Unreviewed final metadata bytes: '+relative)
    return raw
for relative in final_metadata['files']:
    reviewed_file(relative)
contexts=json.loads(reviewed_file('scripts/upstream_elaboration_contexts.json'))
external_bindings=json.loads(reviewed_file('scripts/upstream_blueprint_external_bindings.json'))
unbound_bindings=json.loads(reviewed_file('scripts/upstream_blueprint_unbound_bindings.json'))
reviewed_file('scripts/upstream_blueprint_scope.py')
require(len(contexts)==1 and sum(map(len,contexts.values()))==3,'Exactly THREE scoped prefixes in ONE new original module')
require(len(external_bindings)==243 and len(unbound_bindings)==2,'Exactly243 missing-local original attachments, TWO unresolved')
old_contexts=final_metadata['exact_old_original_context_restorations']
require(len(old_contexts)==2,'Exactly TWO explicitly authorized original declaration-context restorations')
old_contexts_by_path={entry['path']:entry for entry in old_contexts}
require(len(old_contexts_by_path)==2,'The TWO context restorations affect distinct original modules')
def blobs(paths):
    refs=[f'{READ_CP}:{p}' for p in paths]
    raw=subprocess.check_output(GIT+['cat-file','--batch'], input=('\n'.join(refs)+'\n').encode(), cwd=SRC)
    ans={}; pos=0
    for path in paths:
        end=raw.index(b'\n',pos); header=raw[pos:end].split(); pos=end+1
        if len(header)!=3 or header[1]!=b'blob': raise RuntimeError((path,header))
        n=int(header[2]); ans[path]=raw[pos:pos+n]; pos+=n+1
    require(pos==len(raw),'batch blob parser consumed every byte')
    return ans
sources=json.loads((AUDIT/'provenance.json').read_text())
bps=json.loads((AUDIT/'blueprint-provenance.json').read_text())
# Pin the PREVIOUS successful 95/95 review and the independently reviewed FINAL
# explicit typography map. An unknown map is NEVER used to derive expected text.
baseline_raw=(OUT/'g2-controlled-export-pre-typography-byteguard.json').read_bytes()
require(sha(baseline_raw)==BASELINE_SHA256,'Original successful pre-typography review is immutable')
baseline=json.loads(baseline_raw)
baseline_sources={x['source_module']:x for x in baseline['source_entries']}
baseline_bps={x['destination_path']:x for x in baseline['blueprint_entries']}
typography_raw=(DEST/'scripts/upstream_blueprint_typography.json').read_bytes()
reviewed_raw=(OUT/'g2-controlled-export-reviewed-typography.json').read_bytes()
typography_exact=sha(typography_raw)==sha(reviewed_raw)==TYPOGRAPHY_SHA256 and typography_raw==reviewed_raw
require(typography_exact,'ONLY the exact independently reviewed final typography map is permitted')
typography=json.loads(reviewed_raw) if typography_exact else {}
require(len(typography)==5 and sum(map(len,typography.values()))==38,'Exactly five reviewed files / 38 ordered replacements')
require(set(typography)<={Path(x['source_path']).name for x in bps},'Every typography exception belongs to this95 BP cohort')
imports_raw=(DEST/'scripts/upstream_additional_imports.json').read_bytes()
reviewed_imports=(OUT/'g2-controlled-export-reviewed-additional-imports.json').read_bytes()
imports_exact=sha(imports_raw)==sha(reviewed_imports)==IMPORTS_SHA256 and imports_raw==reviewed_imports
require(imports_exact,'ONLY the exact final21 pure-support import map is permitted')
additional_imports=json.loads(reviewed_imports) if imports_exact else {}
require(len(additional_imports)==21 and all(len(v)==1 for v in additional_imports.values()),'Exactly21 explicit callers, one added import each')
support_raw=(OUT/'g2-controlled-export-reviewed-support-files.json').read_bytes()
require(sha(support_raw)==SUPPORT_FILES_SHA256,'Exact reviewed16 support-file fingerprint manifest')
support_files=json.loads(support_raw)
require(len(support_files)==16,'Exactly16 recovered original support modules')
support_checks=[]
for module,h in support_files.items():
    path=DEST/(module.replace('.','/')+'.lean');ok=path.exists() and sha(path.read_bytes())==h
    require(ok,'Recovered original support changed after complete source review: '+module)
    support_checks.append(dict(module=module,sha256=h,reviewed_complete_source_bytes_preserved=ok))
require(sha((DEST/'scripts/upstream_namespace_map.py').read_bytes())=='3288e4879c78e75227926cebeec7e5c0e03a90df19639663c80a03f3cfa4bfe0','Canonical namespace map unchanged')
reviewed_file('scripts/sync_upstream_subgoal.py')
reviewed_file('audit/controlled-smooth-pullback-20261015/provenance.json')
reviewed_file('audit/controlled-smooth-pullback-20261015/blueprint-provenance.json')
reviewed_file('audit/local-sharp-curves-20261015/blueprint-provenance.json')
require(len(sources)==95 and len(bps)==95,'Expected exactly95 source and95 BP entries')
require(re.fullmatch('[0-9a-f]{40}',READ_CP)and gitout('rev-parse',READ_CP).decode().strip()==READ_CP,'Full actual immutable source revision resolves exactly')
require(all(x['source_revision']==CP for x in sources),'All95 source revisions fixed')
require(len({x['source_module']for x in sources})==95,'Source modules unique')
require(len({x['destination_module']for x in sources})==95,'Destination modules unique')
require(len({x['source_path']for x in bps})==95,'Source BP paths unique')
require(len({x['destination_path']for x in bps})==95,'Destination BP paths unique')
# Use the reviewed canonical map, but independently reproduce the actual per-line
# transformation without importing or executing the mutating exporter.
spec=importlib.util.spec_from_file_location('reviewed_canonical_names',DEST/'scripts/upstream_namespace_map.py')
names=importlib.util.module_from_spec(spec); spec.loader.exec_module(names)
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}'for s in ['', '2','3','4']])
flat=names.flattened_short()
flat_qual=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
HEADER='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
def canonical_source(raw,legacy_first_line_open_only=False):
    lines=[];in_open=False
    for line in raw.decode().splitlines(keepends=True):
        match=re.fullmatch(r'import (TranscendentalNakamaye\.[\w.]+)\s*',line)
        if match:
            lines.append('import '+names.new_mod(match.group(1))+'\n'); continue
        line=flat_qual.sub('Hironaka.',names.rename_text_names(line))
        if re.match(r'^\s*(namespace|end|section)\b',line):
            line=re.sub(r'(?<![\w.])(FirstPass|Pending)\.', '',line)
        else:
            line=re.sub(r'(?<![\w.])(FirstPass|Pending)\.', 'Hironaka.',line)
        if re.match(r'^\S',line) or re.match(r'^\s*open\b',line):
            in_open=bool(re.match(r'^\s*open\b',line))
        active=bool(re.match(r'^\s*open\b',line)) if legacy_first_line_open_only else in_open
        if active:
            line=' '.join(t for t in line.split(' ')if t.strip()not in ('FirstPass','Pending',*flat))
            if re.fullmatch(r'\s*open\s*',line):line='\n'
        lines.append(line)
    return (HEADER+''.join(lines)).encode()
def with_exact_imports(module,raw):
    text=raw.decode()
    for change in contexts.get(module,[]):
        require(text.count(change['before'])==1,'Exact original next-declaration context scope: '+module)
        text=text.replace(change['before'],change['after'],1)
    for extra in additional_imports.get(module,[]):
        first=re.search(r'^import ',text,re.M)
        require(first is not None,'Original first import exists: '+module)
        if first:text=text[:first.start()]+'import '+extra+'\n'+text[first.start():]
    return text.encode()
source_bytes=blobs([x['source_path']for x in sources])
imp_re=re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',re.M)
source_results=[];module_sources={};unsupported_imports=[]
for x in sources:
    raw=source_bytes[x['source_path']]; orig=raw.decode(); module_sources[x['source_module']]=orig
    expected_path='TranscendentalNakamaye/'+x['source_module'].replace('.','/')+'.lean'
    mod=names.new_mod(x['source_module']);dst=DEST/(mod.replace('.','/')+'.lean')
    actual=dst.read_bytes();canonical=canonical_source(raw);expected=with_exact_imports(mod,canonical)
    checks={'path_dictionary':x['source_path']==expected_path,
            'source_sha256':sha(raw)==x['source_sha256'],
            'canonical_module':mod==x['destination_module'],
            'destination_sha256':sha(actual)==x['destination_sha256'],
            'entire_canonical_bytes_with_only_pinned_imports':actual==expected,
            'original_body_unchanged_since_pre_typography':sha(canonical)==baseline_sources[x['source_module']]['destination_sha256'],
            'exact_initial_canonical_sha256':sha(canonical)==x['initial_synchronized_destination_sha256'],
            'exact_recorded_additional_imports':x['additional_pure_support_imports']==additional_imports.get(mod,[]),
            'exact_recorded_administrative_contexts':x['administrative_elaboration_contexts']==contexts.get(mod,[]),
            'no_axiom_sorry_tokens':not re.search(r'^\s*axiom\b|\bsorry\b|\bsorryAx\b',orig,re.M)}
    for name,ok in checks.items():require(ok,f"{x['source_module']}: {name}")
    for line in orig.splitlines(keepends=True):
        for imp in imp_re.findall(line):
            if imp.startswith('TranscendentalNakamaye.') and not re.fullmatch(r'import (TranscendentalNakamaye\.[\w.]+)\s*',line):
                unsupported_imports.append((x['source_module'],line))
    source_results.append(dict(source_module=x['source_module'],destination_module=mod,source_path=x['source_path'],
        source_sha256=sha(raw),canonical_before_support_imports_sha256=sha(canonical),canonical_output_sha256=sha(expected),destination_sha256=sha(actual),
        explicit_additional_imports=additional_imports.get(mod,[]),whole_file_unchanged_since_pre_typography=sha(actual)==baseline_sources[x['source_module']]['destination_sha256'],
        source_bytes=len(raw),destination_bytes=len(actual),source_lines=len(orig.splitlines()),checks=checks))
require(not unsupported_imports,'All actual95 source import lines use supported canonical form')
# Establish exact95 closure relative to the545 committed old modules and87 prior
# exported sources; these are read-only validated boundaries, not missing imports.
prior=json.loads((DEST/'audit/local-sharp-curves-20261015/provenance.json').read_text())
reviewed_file('audit/local-sharp-curves-20261015/provenance.json')
prior_by_dest={x['destination_module']:x for x in prior}
old=json.loads((DEST/'audit/local-sharp-curves-20261015/preceding-source-manifest.json').read_text())
old_checks=[]
for path,h in old.items():
    now=(DEST/path).read_bytes();head=subprocess.check_output(['git','show','HEAD:'+path],cwd=DEST)
    if path in old_contexts_by_path:
        old_context=old_contexts_by_path[path]
        replacements=old_context['replacements']
        previous_text=now.decode();replacement_counts_exact=True
        for change in reversed(replacements):
            replacement_counts_exact= replacement_counts_exact and previous_text.count(change['after'])==1
            previous_text=previous_text.replace(change['after'],change['before'],1)
        previous=previous_text.encode()
        original=blobs([old_context['source_path']])[old_context['source_path']]
        lo,hi=old_context['complete_unchanged_declaration_interval_inclusive']
        whole_definition=''.join(original.decode().splitlines(keepends=True)[lo-1:hi])
        ok=(replacement_counts_exact and sha(now)==old_context['after_sha256']
            and sha(previous)==h==old_context['before_sha256'] and (head==previous or head==now)
            and sha(original)==old_context['source_whole_sha256']
            and sha(whole_definition.encode())==old_context['complete_unchanged_declaration_sha256']
            and now.decode().count(whole_definition)==1
            and previous.decode().count(whole_definition)==1)
        require(ok,'ONLY the exact independently reviewed original declaration-context replacement may change: '+path)
    else:
        ok=sha(now)==h and now==head;require(ok,'Old mathematical source changed: '+path)
    old_checks.append(dict(path=path,sha256=sha(now),matches_manifest_and_gitHEAD=sha(now)==h and now==head,
        exact_authorized_original_context_or_unchanged=ok))
require(len(old_checks)==545,'All545 old mathematical sources verified')
require(sum(x['matches_manifest_and_gitHEAD']for x in old_checks)==543,'Exactly543 protected originals byte-identical plus TWO exact original-context restorations')
prior_checks=[];prior_originals=blobs([x['source_path']for x in prior]);canonical_open_fixes=[]
prior_baseline={x['destination_module']:x['sha256']for x in baseline['all87_prior_export_checks']}
for x in prior:
    module=x['destination_module'];path=DEST/(module.replace('.','/')+'.lean');canonical=canonical_source(prior_originals[x['source_path']])
    legacy=canonical_source(prior_originals[x['source_path']],legacy_first_line_open_only=True)
    if canonical!=legacy:
        only_fix=(module=='Hironaka.Resolution.HironakaSharpActualCurveTwoPhaseDefectErasure'
            and legacy.count(b' FirstPass ')==1 and canonical==legacy.replace(b' FirstPass ',b' ',1))
        require(only_fix,'ONLY the one reviewed multiline-open bare namespace alias fix is allowed: '+module)
        canonical_open_fixes.append(dict(module=module,previous_canonical_sha256=sha(legacy),
            corrected_canonical_sha256=sha(canonical),exact_change='Remove ONLY the single bare FirstPass namespace token in the continued original open command',only_reviewed_fix=only_fix))
    expected=with_exact_imports(module,canonical)
    ok=(sha(path.read_bytes())==x['destination_sha256'] and path.read_bytes()==expected
        and sha(legacy)==prior_baseline[module] and sha(canonical)==x['initial_synchronized_destination_sha256']
        and sha(prior_originals[x['source_path']])==x['source_sha256']
        and x['additional_pure_support_imports']==additional_imports.get(module,[])
        and x['administrative_elaboration_contexts']==contexts.get(module,[]))
    require(ok,'Prior87 source/canonical body or explicit imports changed: '+str(path))
    prior_checks.append(dict(destination_module=module,sha256=sha(path.read_bytes()),original_body_sha256=sha(canonical),
        explicit_additional_imports=additional_imports.get(module,[]),matches_fixed_source_and_exact_import_map=ok))
require(len(prior_checks)==87,'All87 immediately preceding exports verified')
require(len(canonical_open_fixes)==1,'Exactly ONE prior87 module has the reviewed multiline-open canonical context repair')
mods={x['source_module']for x in sources};destmods={x['destination_module']for x in sources}
require(set(additional_imports)<=(destmods|set(prior_by_dest)),'Every21 explicit import caller belongs to the182 whole copied modules')
oldmodules={p.removesuffix('.lean').replace('/','.')for p in old}
require(all(m in support_files or m in oldmodules for v in additional_imports.values()for m in v),'Only reviewed16 native supports or verified preexisting owner modules may be added')
require(not(destmods & set(prior_by_dest)),'New95 disjoint from prior87 sources')
require(not{m.replace('.','/')+'.lean'for m in destmods}&set(old),'New95 disjoint from original545')
root='TranscendentalNakamaye.Pending.HironakaOriginalUntestedControlledSmoothPullback'
seen=set();ordered=[];boundary=set();missing=[]
def walk(mod):
    if mod in seen:return
    seen.add(mod)
    if mod not in mods:
        dst=names.new_mod(mod);path=DEST/(dst.replace('.','/')+'.lean')
        require(path.exists(),'Missing closure dependency '+mod)
        require(dst in prior_by_dest or dst.replace('.','/')+'.lean'in old,'Unverified closure boundary '+mod)
        boundary.add(mod);return
    for imp in imp_re.findall(module_sources[mod]):
        if imp.startswith('TranscendentalNakamaye.'):walk(imp)
    ordered.append(mod)
walk(root)
require(set(ordered)==mods,'Root import traversal reaches EVERY new95 source exactly')
require(ordered==[x['source_module']for x in sources],'Provenance order equals actual dependency-first traversal')
for x in sources:
    dst=DEST/(x['destination_module'].replace('.','/')+'.lean')
    for imp in imp_re.findall(dst.read_text()):
        if imp.startswith('Hironaka.'):
            require((DEST/(imp.replace('.','/')+'.lean')).exists(),'Missing destination import '+imp)
require((AUDIT/'old-modules.tsv').read_text()==''.join(f"{x['source_module']}\t{x['destination_module']}\n"for x in sources),'Exact old module comparison table')
require((AUDIT/'new-modules.tsv').read_text()==''.join(f"{x['destination_module']}\t{x['destination_module']}\n"for x in sources),'Exact new module comparison table')
allpaths=gitout('ls-tree','-r','--name-only',READ_CP,'--','TranscendentalNakamaye/TranscendentalNakamaye').decode().splitlines()
allmods=[p.removeprefix('TranscendentalNakamaye/').removesuffix('.lean').replace('/','.')for p in allpaths if p.endswith('.lean')]
exact=''.join(f'{m}\t{names.new_mod(m)}\n'for m in allmods if m.startswith(('TranscendentalNakamaye.FirstPass.','TranscendentalNakamaye.Pending.')))
recorded_module_map=(AUDIT/'exact-module-renames.tsv').read_text()
published_additional_native_modules=[]
if STANDARD_GIT:
    recorded_modules={line.split('\t')[0]for line in recorded_module_map.splitlines()}
    public_modules={m for m in allmods if m.startswith(('TranscendentalNakamaye.FirstPass.','TranscendentalNakamaye.Pending.'))}
    published_additional_native_modules=sorted(public_modules-recorded_modules)
    subset=''.join(f'{m}\t{names.new_mod(m)}\n'for m in allmods if m in recorded_modules)
    require(recorded_module_map==subset and recorded_modules<=public_modules,'Every original module-table entry retains its exact canonical rename and exists in published checkout')
else:
    require(recorded_module_map==exact,'Full fixed-checkpoint canonical module map table')
# Independently select every source BP containing an actual attachment to the95
# modules, then compare ENTIRE text, metadata, statements/proofs and scope text.
all_bp_paths=[p for p in gitout('ls-tree','-r','--name-only',READ_CP,'--','TranscendentalNakamaye/blueprint/src').decode().splitlines()if p.endswith('.tex')]
all_bp=blobs(all_bp_paths);selected=[]
for path,raw in all_bp.items():
    s=raw.decode();bindings=[b.strip()for z in re.findall(r'\\lean\{([^}]+)\}',s)for b in z.split(',')]
    if any(any(b.startswith(mod+'.')for mod in mods)for b in bindings):selected.append(path)
require(selected==[x['source_path']for x in bps],'ALL95 complete attached source BP chapters selected exactly')
bp_results=[];nonproof_labels=[];all_definitions_complete=True;typography_results=[];changed_bps=[]
def without_reviewed_typography(s):
    # The only grouping changes in the PINNED map: two identical exponent
    # groupings and one subscript grouping. This is a supplementary content
    # check, not an authorization for arbitrary substitutions of these forms.
    return s.replace('$','').replace('C^{(m-n)}','C^(m-n)').replace('I_{(f^{-1}C)}','I_(f^{-1}C)')
def attachments(text,kind='lean'):
    return [b.strip()for group in re.findall(r'\\'+kind+r'\{([^}]+)\}',text)for b in group.split(',')]
node_boundary=re.compile(r'(?=\\begin\{(?:lemma|theorem|proposition|corollary|definition|remark|convention)\})')
def independently_annotate_scope(text):
    blocks=[]
    for block in node_boundary.split(text):
        refs=attachments(block);outside=[x for x in refs if x in external_bindings]
        def annotation(match):
            refs=[x.strip()for x in match[1].split(',')]
            if not any(x in external_bindings for x in refs):return match[0]
            groups=[]
            for ref in refs:
                value=external_bindings.get(ref,ref)
                kind=('upstreamunbound'if value in unbound_bindings else'upstreamlean')if ref in external_bindings else'lean'
                if groups and groups[-1][0]==kind:groups[-1][1].append(value)
                else:groups.append((kind,[value]))
            return ''.join('\\'+kind+'{'+','.join(values)+'}'for kind,values in groups)
        block=re.sub(r'\\lean\{([^}]+)\}',annotation,block)
        if outside:
            status='historicalleanok'if any(external_bindings[x]in unbound_bindings for x in outside)else('mixedleanok'if any(x not in external_bindings for x in refs)else'upstreamleanok')
            block=block.replace('\\leanok','\\'+status)
        blocks.append(block)
    return ''.join(blocks)
def strip_only_explicit_binding_metadata(text):
    text=re.sub(r'\\(?:lean|upstreamlean|upstreamunbound)\{[^}]+\}','',text)
    return re.sub(r'\\(?:leanok|upstreamleanok|mixedleanok|historicalleanok)\b','',text)
all_original_binding_names=set();all_local_binding_names=set();all_upstream_binding_names=set();all_unbound_binding_names=set()
def review_binding_partition(original_canonical,actual,x):
    refs=attachments(original_canonical)
    local=[b for b in refs if b not in external_bindings]
    upstream=[external_bindings[b]for b in refs if b in external_bindings and external_bindings[b]not in unbound_bindings]
    unbound=[external_bindings[b]for b in refs if b in external_bindings and external_bindings[b]in unbound_bindings]
    require(attachments(actual)==local,'Exact local attachment subsequence: '+x['source_path'])
    require(attachments(actual,'upstreamlean')==upstream,'Exact original-qualified verified-upstream subsequence: '+x['source_path'])
    require(attachments(actual,'upstreamunbound')==unbound,'Exact original-qualified unresolved historical subsequence: '+x['source_path'])
    require(x['local_bindings']==local and x['upstream_bindings']==upstream and x['unbound_upstream_bindings']==unbound,'Exact three-way BP provenance partition: '+x['source_path'])
    require(strip_only_explicit_binding_metadata(actual)==strip_only_explicit_binding_metadata(original_canonical),'ENTIRE mathematical prose/proofs unchanged after ONLY explicit metadata removal: '+x['source_path'])
    for block in node_boundary.split(actual):
        if attachments(block,'upstreamunbound'):
            require('\\leanok'not in block and '\\upstreamleanok'not in block and '\\mixedleanok'not in block,'Unresolved historical node NEVER marked verified: '+x['source_path'])
    all_original_binding_names.update(refs);all_local_binding_names.update(local)
    all_upstream_binding_names.update(upstream);all_unbound_binding_names.update(unbound)
    return dict(local=len(local),verified_upstream=len(upstream),unresolved_historical=len(unbound))
for x in bps:
    raw=all_bp[x['source_path']];orig=raw.decode();dst=DEST/x['destination_path'];actual=dst.read_bytes()
    canonical=names.rename_text_names(orig).replace('\\chapter{','\\section{')
    expected_text=canonical;adjustments=typography.get(dst.name,[])
    for i,a in enumerate(adjustments,1):
        before=a['before'];after=a['after'];unique=expected_text.count(before)==1
        content_preserved=without_reviewed_typography(before)==without_reviewed_typography(after)
        operations=[dict(kind=op,removed=before[l:r],inserted=after[u:v])
            for op,l,r,u,v in difflib.SequenceMatcher(None,before,after,autojunk=False).get_opcodes() if op!='equal']
        insertion_only=all(z['kind']=='insert' and set(z['inserted'])<={'$','{','}'} for z in operations)
        require(unique,f'{dst.name} typography #{i}: exactly ONE original match')
        require(content_preserved and insertion_only,f'{dst.name} typography #{i}: ONLY delimiters/grouping, all original content unchanged')
        line=expected_text[:expected_text.index(before)].count('\n')+1 if unique else None
        typography_results.append(dict(file=dst.name,ordinal=i,before=before,after=after,line=line,
            unique_original_match=unique,original_content_preserved=content_preserved,
            insertion_only_delimiters_and_grouping=insertion_only,operations=operations))
        if unique:expected_text=expected_text.replace(before,after,1)
    restored=expected_text
    for a in reversed(adjustments):
        unique=restored.count(a['after'])==1
        require(unique,f'{dst.name}: unique reverse typography replacement')
        if unique:restored=restored.replace(a['after'],a['before'],1)
    require(restored==canonical,f'{dst.name}: ENTIRE original canonical text recovered by ONLY inverse explicit map')
    original_typography_text=expected_text
    expected_text=independently_annotate_scope(expected_text)
    partition=review_binding_partition(original_typography_text,actual.decode(),x)
    expected=expected_text.encode()
    unchanged_before=sha(original_typography_text.encode())==baseline_bps[x['destination_path']]['destination_sha256']
    require(unchanged_before==(not bool(adjustments)),f'{dst.name}: exact change boundary relative to successful pre-typography95 review')
    if not unchanged_before:changed_bps.append(dst.name)
    bindings=[b.strip()for z in re.findall(r'\\lean\{([^}]+)\}',orig)for b in z.split(',')]
    labels=list(re.finditer(r'\\label\{([^}]+)\}',orig));proofs=re.findall(r'\\begin\{proof\}([\s\S]*?)\\end\{proof\}',orig)
    checks={'source_sha256':sha(raw)==x['source_sha256'],'destination_sha256':sha(actual)==x['destination_sha256'],
        'entire_canonical_bytes_with_only_pinned_typography_and_explicit_binding_scope':actual==expected,
        'entire_original_text_recovered':restored==canonical,
        'unchanged_without_explicit_typography_exception':unchanged_before==(not bool(adjustments)),
        'node_count':len(labels)==x['nodes'],'proof_count':len(proofs)==x['proofs'],
        'proof_begin_end_balance':orig.count('\\begin{proof}')==orig.count('\\end{proof}')==len(proofs),
        'nonempty_entire_proofs':all(p.strip()for p in proofs),'exact_original_bindings':bindings==x['bindings'],
        'all_original_binding_names_preserved_in_explicit_partition':sum(partition.values())==len(bindings),
        'destination_path':x['destination_path']=='blueprint/'+Path(x['source_path']).name}
    for n,ok in checks.items():require(ok,f"{x['source_path']}: {n}")
    for i,label in enumerate(labels):
        end=labels[i+1].start()if i+1<len(labels)else len(orig);part=orig[label.start():end]
        if '\\begin{proof}'not in part:
            envs=list(re.finditer(r'\\begin\{([^}]+)\}',orig[:label.start()]));env=envs[-1].group(1)if envs else 'section'
            ok=env=='section'or(env=='definition'and'\\end{definition}'in part)
            require(ok,'Non-definition mathematical node missing proof: '+label.group(1))
            nonproof_labels.append(dict(source_path=x['source_path'],label=label.group(1),environment=env,complete_definition_or_section=ok))
    bp_results.append(dict(source_path=x['source_path'],destination_path=x['destination_path'],source_sha256=sha(raw),
        canonical_output_sha256=sha(expected),destination_sha256=sha(actual),source_bytes=len(raw),source_lines=len(orig.splitlines()),
        canonical_output_before_typography_sha256=sha(canonical.encode()),
        original_pre_typography_destination_sha256=baseline_bps[x['destination_path']]['destination_sha256'],
        reviewed_typography_replacements=len(adjustments),
        explicit_attachment_partition=partition,
        nodes=len(labels),proofs=len(proofs),bindings=len(bindings),leanok_count=orig.count('\\leanok'),notready_count=orig.count('\\notready'),checks=checks))
# The final scope update also touches the87 prior complete chapters. Review their
# ENTIRE immutable original text, not only the newly selected95 chapter cohort.
prior_bps=json.loads(reviewed_file('audit/local-sharp-curves-20261015/blueprint-provenance.json'))
require(len(prior_bps)==87,'Exactly87 preceding whole BP chapters')
require(not({x['source_path']for x in prior_bps}&{x['source_path']for x in bps}),'Preceding87 and new95 BP chapters are disjoint')
prior_bp_results=[]
for x in prior_bps:
    raw=all_bp[x['source_path']];orig=raw.decode();actual=(DEST/x['destination_path']).read_bytes()
    canonical=names.rename_text_names(orig).replace('\\chapter{','\\section{')
    require(Path(x['source_path']).name not in typography,'No unreviewed typography change in prior87 chapters')
    expected=independently_annotate_scope(canonical).encode()
    partition=review_binding_partition(canonical,actual.decode(),x)
    proofs=re.findall(r'\\begin\{proof\}([\s\S]*?)\\end\{proof\}',orig)
    checks={'immutable_complete_source_sha256':sha(raw)==x['source_sha256'],
        'entire_canonical_bytes_with_only_pinned_attachment_scope':actual==expected,
        'destination_sha256':sha(actual)==x['destination_sha256'],
        'exact_original_attachments':attachments(orig)==x['bindings'],
        'proof_begin_end_balance':orig.count('\\begin{proof}')==orig.count('\\end{proof}')==len(proofs),
        'all_complete_proofs_nonempty':all(p.strip()for p in proofs),
        'node_count':len(re.findall(r'\\label\{',orig))==x['nodes'],
        'proof_count':len(proofs)==x['proofs']}
    for key,ok in checks.items():require(ok,'Prior87 BP '+x['source_path']+': '+key)
    prior_bp_results.append(dict(source_path=x['source_path'],destination_path=x['destination_path'],source_sha256=sha(raw),
        destination_sha256=sha(actual),nodes=x['nodes'],proofs=len(proofs),bindings=len(attachments(orig)),
        source_bytes=len(raw),explicit_attachment_partition=partition,checks=checks))
require(len(all_original_binding_names)==2234 and len(all_local_binding_names)==1991,'All182 chapters exactly2234 distinct original references /1991 local references')
require(len(all_upstream_binding_names)==241 and len(all_unbound_binding_names)==2,'Exactly241 verified upstream-only and TWO unresolved historical names')
require(set(external_bindings)=={names.rename_text_names(x)for x in all_upstream_binding_names|all_unbound_binding_names},'Exact missing-local map; no original attachment dropped or invented')
require(all_local_binding_names.isdisjoint(set(external_bindings)),'Local and external original references are disjoint')
require(set(unbound_bindings)==all_unbound_binding_names and all_upstream_binding_names.isdisjoint(all_unbound_binding_names),'Verified-upstream and unresolved names are disjoint and exhaustive')
for public_name,original_name in external_bindings.items():
    require(names.rename_text_names(original_name)==public_name,'Exact original/public qualified-name map: '+original_name)
upstream_log=reviewed_file('audit/local-sharp-curves-20261015/upstream-actual-blueprint-bindings.log').decode()
actual_upstream_owners=dict(re.findall(r'^UPSTREAM_ACTUAL_BINDING (\S+) OWNER (\S+)$',upstream_log,re.M))
require(set(actual_upstream_owners)==all_upstream_binding_names,'Native actual-owner evidence covers ONLY all241 verified upstream references')
require('EXACT_UPSTREAM_BLUEPRINT_BINDINGS 241; BASELINE_UNBOUND_REFERENCES 2; STANDARD_THREE_ONLY'in upstream_log,'Exact parent native241/std3 and2unresolved result retained')
upstream_owner_paths={owner:'TranscendentalNakamaye/'+owner.replace('.','/')+'.lean'for owner in set(actual_upstream_owners.values())}
upstream_owner_sources=blobs(list(upstream_owner_paths.values()))
upstream_source_fingerprints=(OUT/'g2-controlled-export-reviewed-upstream-owner-sources.json').read_bytes()
require(sha(upstream_source_fingerprints)=='5a464d7c52219529cf525251f39d549bd35500c97577da47ddfab4efdf6110a3','Exact native241 actual-owner source fingerprints')
reviewed_upstream_sources=json.loads(upstream_source_fingerprints)
require(set(reviewed_upstream_sources)==set(upstream_owner_paths.values()),'Exactly54 complete original native owners for all241 verified upstream facts')
for path,digest in reviewed_upstream_sources.items():
    require(sha(upstream_owner_sources[path])==digest,'Actual241-fact owner whole source matches original-reviewed source SHA: '+path)
upstream_owner_checks=[dict(original_owner=owner,source_path=path,original_provenance_revision=CP,actual_source_read_revision=READ_CP,whole_source_sha256=sha(upstream_owner_sources[path]))
    for owner,path in sorted(upstream_owner_paths.items())]
upstream_provenance=json.loads(reviewed_file('audit/local-sharp-curves-20261015/upstream-only-binding-provenance.json'))
require(len(upstream_provenance)==243 and {x['original']for x in upstream_provenance}==all_upstream_binding_names|all_unbound_binding_names,'All243 external provenance records present, including TWO unresolved names')
all_original_bp_metadata=bps+prior_bps
for entry in upstream_provenance:
    original=entry['original'];expected_sources=sorted(x['source_path']for x in all_original_bp_metadata if original in x['bindings'])
    require(entry['native_checkpoint']==CP and entry['canonical_public_name']==names.rename_text_names(original),'Exact original241+2 declaration provenance: '+original)
    require(sorted(entry['blueprint_sources'])==expected_sources,'Every original BP occurrence of external attachment retained: '+original)
extensions=(DEST/'blueprint/extensions.tex').read_text();root_text=(DEST/'Hironaka.lean').read_text()
for x in bps+prior_bps:require(extensions.splitlines().count('\\input{'+Path(x['destination_path']).stem+'}')==1,'Exactly one extension input '+x['destination_path'])
doc_marker=root_text.find('/-!')
require(doc_marker>=0,'Actual standalone root retains its original module documentation')
root_import_checks=[]
for original_root in [root,'TranscendentalNakamaye.Pending.HironakaSharpActualCurveLocalSharpEndpoints']:
    line='import '+names.new_mod(original_root)
    count=root_text.splitlines().count(line)
    before_doc=count==1 and 0<=root_text.find(line)<doc_marker
    require(count==1 and before_doc,'Exactly ONE actual root import BEFORE first module doc: '+original_root)
    root_import_checks.append(dict(original_root=original_root,destination_import=line,count=count,before_first_module_doc=before_doc))
require(all(m.start()<doc_marker for m in re.finditer(r'^import\b',root_text,re.M)),'EVERY actual root-file import precedes the module doc')
require(len(nonproof_labels)==16,'Exactly16 original nonproof labels classified')
require(sum(x['environment']=='definition'for x in nonproof_labels)==14,'Exactly14 complete original definitions')
require(sum(x['environment']=='section'for x in nonproof_labels)==2,'Exactly2 original section labels')
require(set(changed_bps)==set(typography),'Exactly the FIVE explicit BP exceptions changed; the other90 are byte-identical')
require(len(typography_results)==38,'All38 pinned adjustments actually applied exactly once')
# Actual destination closure from BOTH original root exports, including the exact
# added support modules. This is additional to the original95-source traversal.
all_whole_modules=destmods|set(prior_by_dest)
actual_seen=set();actual_new_supports=set();actual_old_boundaries=set()
def actual_walk(module):
    if module in actual_seen:return
    actual_seen.add(module)
    require(module in all_whole_modules or module in support_files or module in oldmodules,'Unverified actual Hironaka dependency: '+module)
    path=DEST/(module.replace('.','/')+'.lean')
    require(path.exists(),'Missing actual destination dependency: '+module)
    if not path.exists():return
    if module in support_files:actual_new_supports.add(module)
    if module in oldmodules:actual_old_boundaries.add(module)
    for imp in imp_re.findall(path.read_text()):
        if imp.startswith('Hironaka.'):actual_walk(imp)
for module in [names.new_mod(root),'Hironaka.Resolution.HironakaSharpActualCurveLocalSharpEndpoints']:actual_walk(module)
require(all_whole_modules<=actual_seen,'BOTH actual roots reach ALL182 copied whole source modules')
require(set(support_files)==actual_new_supports,'BOTH actual roots reach ALL16 reviewed native support modules')
summary=dict(status='passed'if not errors else'failed',claim_class='independent export/provenance byte integrity ONLY; not mathematical self-review or compiled-expression validation',
    fixed_source_revision=CP,source_count=len(sources),source_lines=sum(x['source_lines']for x in source_results),
    actual_source_read_revision=READ_CP,standard_git_backend=STANDARD_GIT,
    original_source_revision_metadata_preserved=True,
    published_additional_native_modules_outside_original_inventory=published_additional_native_modules,
    source_bytes=sum(x['source_bytes']for x in source_results),blueprint_count=len(bps),blueprint_lines=sum(x['source_lines']for x in bp_results),
    blueprint_bytes=sum(x['source_bytes']for x in bp_results),labels=sum(x['nodes']for x in bp_results),proofs=sum(x['proofs']for x in bp_results),
    bindings=sum(x['bindings']for x in bp_results),original_complete_definitions=14,original_section_labels=2,verified_original_baseline_sources=len(old_checks),
    unchanged_original_baseline_sources=543,exact_original_declaration_context_restorations=old_contexts,
    verified_prior_export_sources=len(prior_checks),verified_dependency_boundary_modules=len(boundary),controlled_root_deferred=False,
    both_new_roots_imported_once_before_module_doc=all(x['count']==1 and x['before_first_module_doc']for x in root_import_checks),
    root_aggregator_sha256=sha((DEST/'Hironaka.lean').read_bytes()),
    typography_map_sha256=sha(typography_raw),reviewed_typography_files=len(typography),reviewed_typography_replacements=len(typography_results),
    all95_original_lean_bodies_unchanged_since_pre_typography=all(x['checks']['original_body_unchanged_since_pre_typography']for x in source_results),
    final_explicit_import_map_sha256=sha(imports_raw),explicit_import_only_callers=len(additional_imports),
    callers_in_new95=sum(x['destination_module']in additional_imports for x in sources),callers_in_prior87=sum(x['destination_module']in additional_imports for x in prior),
    reviewed_original_support_modules=len(support_files),reviewed_support_fingerprint_sha256=sha(support_raw),
    complete_open_namespace_repairs=canonical_open_fixes,
    exact_original_scoped_instance_restorations=contexts,
    complete_blueprints_reviewed=len(bps)+len(prior_bps),all182_distinct_original_blueprint_references=len(all_original_binding_names),
    all182_original_labels=sum(x['nodes']for x in bp_results+prior_bp_results),
    all182_original_complete_proofs=sum(x['proofs']for x in bp_results+prior_bp_results),
    all182_local_reference_names=len(all_local_binding_names),all182_verified_upstream_reference_names=len(all_upstream_binding_names),
    all182_unresolved_historical_reference_names=len(all_unbound_binding_names),
    actual_both_root_whole_module_closure=len(all_whole_modules&actual_seen),actual_support_module_closure=len(actual_new_supports),
    unchanged_blueprints_before_only_explicit_scope_metadata=len(bps)-len(changed_bps),typography_changed_blueprints=changed_bps,
    pre_typography_guard_sha256=sha(baseline_raw),
    exporter_sha256=sha((DEST/'scripts/sync_upstream_subgoal.py').read_bytes()),namespace_map_sha256=sha((DEST/'scripts/upstream_namespace_map.py').read_bytes()),
    source_provenance_sha256=sha((AUDIT/'provenance.json').read_bytes()),blueprint_provenance_sha256=sha((AUDIT/'blueprint-provenance.json').read_bytes()),
    destination_git_head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=DEST).decode().strip(),errors=errors)
result=dict(summary=summary,source_entries=source_results,blueprint_entries=bp_results,original_nonproof_labels=nonproof_labels,
    root_dependency_order=ordered,verified_existing_boundaries=sorted(boundary),all545_old_source_checks=old_checks,all87_prior_export_checks=prior_checks,
    unsupported_import_forms=unsupported_imports)
result['typography_entries']=typography_results
result['root_import_checks']=root_import_checks
result['reviewed_original_support_file_checks']=support_checks
result['actual_both_root_whole_module_closure']=sorted(all_whole_modules&actual_seen)
result['actual_both_root_support_module_closure']=sorted(actual_new_supports)
result['actual_verified_old_dependency_closure']=sorted(actual_old_boundaries)
result['all87_complete_prior_blueprint_checks']=prior_bp_results
result['all182_blueprint_binding_partition']=dict(local=sorted(all_local_binding_names),verified_upstream_only=sorted(all_upstream_binding_names),unresolved_historical=sorted(all_unbound_binding_names))
result['native_upstream_actual_owner_source_checks']=upstream_owner_checks
(REPORT/'g2-controlled-export-byteguard.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(summary,indent=2))
if errors:sys.exit(1)
