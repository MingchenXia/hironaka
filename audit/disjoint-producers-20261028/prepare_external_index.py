#!/usr/bin/env python3
"""Fixed ordinary-source external pointers; no local theorem/export assertions."""
from pathlib import Path
import hashlib,json,re,subprocess
A=Path(__file__).resolve().parent;plan=json.loads((A/'plan.json').read_text())
N=Path(plan['native_source_checkout']);rev=plan['native_revision'];D=A.parents[1]
wanted=['hir:actual-point-weighted-controlled-stalk-colon','mc:homogenized-basic',
 'mc:homogenized-along-etale','hir:restricted-equivalence','mc:field-chain-rule',
 'mc:derivative-along-coherent','mc:homogenized-along-basic','mc:tangent-direction-along',
 'mc:contact-hypersurface-along','mc:derivative-along','mc:contact-lower-value',
 'hir:geo-transform-coherent']
files=['hironaka-actual-point-weighted-controlled-stalk-extension.tex','hironaka.tex','maximal-contact.tex']
records=[]
for fn in files:
 path='TranscendentalNakamaye/blueprint/src/'+fn
 raw=subprocess.check_output(['git','-C',str(N),'show',rev+':'+path]);text=raw.decode()
 parent=A/'external-native-parents'/fn;parent.parent.mkdir(exist_ok=True)
 if parent.exists():assert parent.read_bytes()==raw
 else:parent.write_bytes(raw)
 for label in wanted:
  needle='\\label{'+label+'}'
  if needle not in text:continue
  assert text.count(needle)==1
  pos=text.index(needle);begins=list(re.finditer(r'\\begin\{(definition|lemma|theorem|proposition|corollary)\}',text[:pos]))
  assert begins,label
  start=begins[-1].start();kind=begins[-1].group(1)
  end=text.index('\\end{'+kind+'}',pos)+len('\\end{'+kind+'}')
  nxt=re.search(r'\\begin\{(?:definition|lemma|theorem|proposition|corollary)\}',text[end:])
  limit=len(text)if nxt is None else end+nxt.start()
  proof=re.search(r'\\begin\{proof\}',text[end:limit])
  if proof:
   pend=text.index('\\end{proof}',end+proof.start())+len('\\end{proof}')
   assert pend<=limit;end=pend
  else:
   # Definitions can have ordinary following explanatory justification.
   end=limit
  node=text[start:end];capture='external-native-nodes/'+label.replace(':','-')+'.tex'
  target=A/capture;target.parent.mkdir(exist_ok=True);target.write_text(node)
  records.append({'label':label,'source_revision':rev,'source_path':path,
    'source_parent_sha256':hashlib.sha256(raw).hexdigest(),
    'source_parent_capture':str(parent.relative_to(A)),
    'source_label_line':text[:pos].count('\n')+1,
    'complete_native_node_capture':capture,'complete_native_node_sha256':hashlib.sha256(node.encode()).hexdigest(),
    'native_source_attachments':[b.strip()for group in re.findall(r'\\lean\{([^}]+)\}',node)for b in group.split(',')],
    'local_export_or_local_kernel_claim':False})
assert set(r['label']for r in records)==set(wanted)
lines=['\\section{External native prerequisites for this export}',
 'The following anchors point to complete statements and proofs in the fixed',
 'native source revision \\texttt{'+rev+'}. They are external documentation',
 'prerequisites, not additional locally exported theorems or local kernel',
 'verification claims. Complete original source parents, node/proof captures',
 'and their original declaration attachments are retained in the audit.',
 '\\begin{description}']
for row in records:
 url='https://github.com/MingchenXia/archon-nakamaye/blob/'+rev+'/'+row['source_path']+'#L'+str(row['source_label_line'])
 lines+=['\\item[\\texttt{'+row['label']+'}]\\label{'+row['label']+'}',
         '\\href{'+url+'}{Fixed original native statement and proof}.']
lines+=['\\end{description}','']
out='\n'.join(lines);(A/'external-prerequisite-index.tex').write_text(out)
(A/'external-prerequisite-plan.json').write_text(json.dumps({'status':'FIXED_ORIGINAL_SOURCE_POINTERS',
 'source_revision':rev,'anchors':records,'new_lean_bindings':0,'leanok_markers':0,
 'complete_proof_captures_retained':True,'output_sha256':hashlib.sha256(out.encode()).hexdigest()},indent=2)+'\n')
print('PREPARED12_FIXED_NATIVE_EXTERNAL_ANCHORS')
