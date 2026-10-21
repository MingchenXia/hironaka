"""Deterministic documentation metadata overlay; mathematical proof text is unchanged."""
from pathlib import Path
import json
A=Path(__file__).resolve().parent
PLAN=json.loads((A/'blueprint-documentation-overlay-plan.json').read_text())
def chapter(path,text):
 for op in PLAN['label_disambiguations']:
  if op['destination_path']==path:
   before='\\label{'+op['old_label']+'}';after='\\label{'+op['new_label']+'}'
   assert text.count(before)==1,(path,before)
   text=text.replace(before,after)
 return text
def external_index():
 out=[r'\section{External prerequisites for the synchronized continuation}',r'\label{sec:external-prerequisites-20261021}',r'The following pointers identify original prerequisite labels in the fixed native source.',r'They are external documentation references, not additional locally exported theorems or local verification claims.',r'The complete original statements and proofs remain available at the linked source revision.',r'The earlier source-and-verification overview describes the preceding increment; current scope is recorded in the new audit report.']
 rev=PLAN['native_revision']
 for name,row in sorted(PLAN['external_original_sources'].items()):
  out.append(r'\par\medskip\noindent\texttt{\detokenize{'+name+r'}}\par')
  out.extend(r'\label{'+label+'}' for label in row['labels'])
  url='https://github.com/MingchenXia/archon-nakamaye/blob/'+rev+'/'+row['native_path']
  out.append(r'\href{'+url+r'}{Original prerequisite source, fixed revision '+rev[:7]+r'.}\par')
 return '\n'.join(out)+'\n'
