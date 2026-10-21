"""Render a generated copy while preserving every published blueprint input."""
from pathlib import Path
import argparse,hashlib,json,re,shutil,subprocess,tempfile,time
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
p=argparse.ArgumentParser();p.add_argument('attempt');args=p.parse_args();out=A/args.attempt
assert not out.exists();out.mkdir()
sha=lambda raw:hashlib.sha256(raw).hexdigest()
inputs={q.name:q.read_bytes()for q in (ROOT/'blueprint').glob('*.tex')}
plan=[{'file':'hironaka-actual-homogeneous-initial-hs-extension.tex','before':r'\\[H]_{q-d}B','after':r'\\{}[H]_{q-d}B','reason':'Empty group disambiguates an existing formula from optional row spacing; the original statement/proof source is preserved.'}]
for name,raw in inputs.items():
 for line in raw.decode().splitlines():
  m=re.fullmatch(r'(\\begin\{(?:theorem|lemma|proposition|corollary|definition|remark|convention)\})\[(.*)\]',line)
  if m and ('[' in m[2] or ']' in m[2]):
   plan.append({'file':name,'before':line,'after':m[1]+'[{'+m[2]+'}]','reason':'Protect nested brackets in an optional theorem title by a purely typesetting group; all title characters and mathematical content are retained.'})
(out/'typesetting-plan.json').write_text(json.dumps(plan,indent=2)+'\n')
(out/'renderer.py.txt').write_bytes(Path(__file__).read_bytes())
result={'status':'RUNNING','input_sha256':{name:sha(raw)for name,raw in inputs.items()},'typesetting_plan':plan,'published_source_edits':0,'generated_input_changes':[],'passes':[]}
start=time.monotonic()
with tempfile.TemporaryDirectory(prefix='hironaka-blueprint-',dir='/tmp')as folder:
 tmp=Path(folder)
 for name,raw in inputs.items():(tmp/name).write_bytes(raw)
 for op in plan:
  q=tmp/op['file'];before=q.read_text();assert before.count(op['before'])==1;after=before.replace(op['before'],op['after']);q.write_text(after)
  result['generated_input_changes'].append({'file':op['file'],'source_sha256':sha(before.encode()),'render_input_sha256':sha(after.encode())})
  (out/(op['file']+'.render-input.txt')).write_text(after)
 for n in range(1,4):
  with(out/f'pass{n}.stdout.log').open('w')as f:proc=subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error','-output-directory='+str(out),'extensions.tex'],cwd=tmp,stdout=f,stderr=subprocess.STDOUT)
  (out/f'pass{n}.exit').write_text(str(proc.returncode)+'\n');result['passes'].append({'pass':n,'exit':proc.returncode})
  assert all((ROOT/'blueprint'/name).read_bytes()==raw for name,raw in inputs.items()),'Original inputs changed while rendering'
  if proc.returncode:
   result['status']='BLOCKED_LATEX_ERROR';break
 else:result['status']='PASS_RENDERED_GENERATED_TYPESETTING_COPY'
result['seconds']=round(time.monotonic()-start,1);result['published_inputs_unchanged']=True
(out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
print({k:v for k,v in result.items()if k not in {'input_sha256','typesetting_plan','generated_input_changes'}})
last=result['passes'][-1]['pass'];print('\n'.join((out/f'pass{last}.stdout.log').read_text().splitlines()[-18:]))
