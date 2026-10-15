#!/usr/bin/env python3
"""Copy complete committed upstream modules through the release's canonical rename.

Existing mathematical modules are never overwritten. Use the generated provenance,
then build, audit every actual compiled constant and compare complete expressions
before publishing. The source revision must be a fixed accepted ledger commit.
"""
from pathlib import Path
import argparse, hashlib, json, re, subprocess, sys

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-root',type=Path,required=True)
parser.add_argument('--checkpoint',required=True)
parser.add_argument('--audit',type=Path,required=True)
parser.add_argument('--defer-root',action='store_true',help='Copy accepted modules now; add the root import after another build completes')
parser.add_argument('roots',nargs='+')
a=parser.parse_args();dest=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(Path(__file__).parent))
import upstream_namespace_map as names
typography_file=Path(__file__).parent/'upstream_blueprint_typography.json'
typography=json.loads(typography_file.read_text()) if typography_file.exists() else {}
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2','3','4']])
git=['git',f'--git-dir={a.source_root}/.archon-horizon/vcs/workspace.git',f'--work-tree={a.source_root}']
def show(path):return subprocess.check_output(git+['show',f'{a.checkpoint}:{path}'],cwd=a.source_root).decode()
assert re.fullmatch('[0-9a-f]{40}',a.checkpoint),'Pin a complete immutable source SHA'
assert subprocess.check_output(git+['rev-parse',a.checkpoint],cwd=a.source_root).decode().strip()==a.checkpoint
imp_re=re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',re.M)
prior_file=a.audit/'provenance.json'
prior=json.loads(prior_file.read_text()) if prior_file.exists() else []
assert all(x['source_revision']==a.checkpoint for x in prior)
previously_owned={x['source_module'] for x in prior}
prior_bp_file=a.audit/'blueprint-provenance.json'
prior_bps={x['source_path']:x for x in json.loads(prior_bp_file.read_text())} if prior_bp_file.exists() else {}
seen=set();ordered=[]
def visit(m):
 if m in seen:return
 seen.add(m)
 if (dest/(names.new_mod(m).replace('.','/')+'.lean')).exists() and m not in previously_owned:return
 src=show('TranscendentalNakamaye/'+m.replace('.','/')+'.lean')
 assert not re.search(r'^\s*axiom\b|\bsorry\b|\bsorryAx\b',src,re.M),m
 for i in imp_re.findall(src):
  if i.startswith('TranscendentalNakamaye.'):visit(i)
 ordered.append((m,src))
for m in a.roots:visit(m)
flat=names.flattened_short()
flat_qual=re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:'+'|'.join(flat)+r')\.(?=[\w«])')
header='/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
a.audit.mkdir(parents=True,exist_ok=True)
records=[]
for m,source in ordered:
 lines=[]
 for line in source.splitlines(keepends=True):
  match=re.fullmatch(r'import (TranscendentalNakamaye\.[\w.]+)\s*',line)
  if match:lines.append('import '+names.new_mod(match.group(1))+'\n');continue
  line=flat_qual.sub('Hironaka.',names.rename_text_names(line))
  if re.match(r'^\s*(namespace|end|section)\b',line):line=re.sub(r'(?<![\w.])(FirstPass|Pending)\.', '',line)
  else:line=re.sub(r'(?<![\w.])(FirstPass|Pending)\.', 'Hironaka.',line)
  if re.match(r'^\s*open\b',line):
   line=' '.join(t for t in line.split(' ') if t.strip() not in ('FirstPass','Pending',*flat))
   if re.fullmatch(r'\s*open\s*',line):line='\n'
  lines.append(line)
 newm=names.new_mod(m);p=dest/(newm.replace('.','/')+'.lean')
 output=header+''.join(lines)
 if p.exists():assert m in previously_owned and p.read_text()==output,('Refusing to replace existing source',p)
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_text(output)
 records.append(dict(source_revision=a.checkpoint,source_module=m,source_path='TranscendentalNakamaye/'+m.replace('.','/')+'.lean',source_sha256=hashlib.sha256(source.encode()).hexdigest(),destination_module=newm,destination_sha256=hashlib.sha256(output.encode()).hexdigest()))
rootfile=dest/'Hironaka.lean';content=rootfile.read_text()
for m in a.roots:
 line='import '+names.new_mod(m)
 marker=content.find('/-!')
 if marker<0:marker=len(content)
 if line in content.splitlines():
  if content.index(line)<marker:continue
  assert content.splitlines().count(line)==1
  content=content.replace('\n'+line+'\n','\n')
  marker=content.find('/-!')
  if marker<0:marker=len(content)
 content=content[:marker]+line+'\n\n'+content[marker:]
if not a.defer_root and rootfile.read_text()!=content:rootfile.write_text(content)
(a.audit/'provenance.json').write_text(json.dumps(records,indent=2)+'\n')
(a.audit/'old-modules.tsv').write_text(''.join(f'{x["source_module"]}\t{x["destination_module"]}\n' for x in records))
(a.audit/'new-modules.tsv').write_text(''.join(f'{x["destination_module"]}\t{x["destination_module"]}\n' for x in records))
allmods=subprocess.check_output(git+['ls-tree','-r','--name-only',a.checkpoint,'--','TranscendentalNakamaye/TranscendentalNakamaye'],cwd=a.source_root).decode().splitlines()
mods=[p.removeprefix('TranscendentalNakamaye/').removesuffix('.lean').replace('/','.') for p in allmods if p.endswith('.lean')]
(a.audit/'exact-module-renames.tsv').write_text(''.join(f'{m}\t{names.new_mod(m)}\n' for m in mods if m.startswith(('TranscendentalNakamaye.FirstPass.','TranscendentalNakamaye.Pending.'))))
bpfiles=subprocess.check_output(git+['ls-tree','-r','--name-only',a.checkpoint,'--','TranscendentalNakamaye/blueprint/src'],cwd=a.source_root).decode().splitlines()
bps=[]
for f in bpfiles:
 if not f.endswith('.tex'):continue
 src=show(f)
 if not any(x['source_module']+'.' in src for x in records):continue
 bindings=[b.strip() for group in re.findall(r'\\lean\{([^}]+)\}',src) for b in group.split(',')]
 if not any(any(b.startswith(x['source_module']+'.') for x in records) for b in bindings):continue
 out=names.rename_text_names(src).replace('\\chapter{','\\section{');p=dest/'blueprint'/Path(f).name
 for adjustment in typography.get(p.name,[]):
  assert out.count(adjustment['before'])==1,(f,adjustment)
  out=out.replace(adjustment['before'],adjustment['after'])
 if p.exists():
  assert f in prior_bps and p.read_text()==out and prior_bps[f]['source_sha256']==hashlib.sha256(src.encode()).hexdigest(),('Refusing to replace existing blueprint',p)
 else:p.write_text(out)
 bps.append(dict(source_path=f,source_sha256=hashlib.sha256(src.encode()).hexdigest(),destination_path=str(p.relative_to(dest)),destination_sha256=hashlib.sha256(out.encode()).hexdigest(),nodes=len(re.findall(r'\\label\{',src)),proofs=src.count('\\begin{proof}'),bindings=bindings))
content=(dest/'blueprint/extensions.tex').read_text();needle='\\begin{thebibliography}{99}';assert content.count(needle)==1
lines=['\\input{'+Path(b['destination_path']).stem+'}' for b in bps]
content=content.replace(needle,''.join(line+'\n' for line in lines if line not in content.splitlines())+needle)
if (dest/'blueprint/extensions.tex').read_text()!=content:(dest/'blueprint/extensions.tex').write_text(content)
(a.audit/'blueprint-provenance.json').write_text(json.dumps(bps,indent=2)+'\n')
print(json.dumps(dict(complete_new_modules=len(records),derived_blueprint_chapters=len(bps),new_roots=a.roots,checkpoint=a.checkpoint)))
