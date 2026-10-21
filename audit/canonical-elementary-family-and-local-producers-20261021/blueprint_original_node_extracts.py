"""Complete original node/context selections from newly introduced broad chapters.
Whole raw originals remain preserved. Logical statement/proof text is never rewritten.
"""
from pathlib import Path
import json,re
A=Path(__file__).resolve().parent
PLAN=json.loads((A/'blueprint-original-node-extract-plan.json').read_text())

def block(text,label):
 pos=text.index('\\label{'+label+'}')
 begins=list(re.finditer(r'\\begin\{(?:lemma|theorem|proposition|corollary|definition|remark|convention)\}',text[:pos]))
 assert begins,label
 start=begins[-1].start();tail=text[start:]
 kind=re.match(r'\\begin\{([^}]+)\}',tail)[1];end=text.index('\\end{'+kind+'}',pos)+len('\\end{'+kind+'}')
 proof=text.find('\\begin{proof}',end);next_node=re.search(r'\\begin\{(?:lemma|theorem|proposition|corollary|definition|remark|convention)\}',text[end:]);next_at=len(text)if next_node is None else end+next_node.start()
 if proof>=0 and proof<next_at:end=text.index('\\end{proof}',proof)+len('\\end{proof}')
 return text[start:end]

def append_original_node_layout(result,text,spec):
 # The layout contains only approved complete original nodes, shared native
 # subsection assumptions, and literal original following explanation text.
 for item in spec.get('additional_original_node_layout',[]):
  context=item.get('context_before','')
  if context:
   assert text.count(context)==1,item['label']
   result+='\n'+context+'\n'
  payload=block(text,item['label'])
  following=item['following_original_text']
  if following:
   start=text.index(payload)
   assert text.startswith(following,start+len(payload)),item['label']
  result+='\n'+payload+following+'\n'
 return result

def chapter(path,text):
 if path not in PLAN['extracts']:return text
 spec=PLAN['extracts'][path]
 if path=='blueprint/analytic.tex':
  result='\\section{Original analytic prerequisites and submanifold charts}\n\n'+'\n\n'.join(block(text,label)for label in spec['labels'])+'\n'
 elif path=='blueprint/maximal-contact.tex':
  first=text.index('\\subsection{Marked ideals of maximal order and tangent directions}')
  stop=text.index('\\subsection{Derivative ideals under a blowup}',first)
  context_end=text.index('\\begin{lemma}',stop)
  result='\\section{Original maximal order and tangent directions}\n\\label{sec:maximal-contact}\n\n'+text[first:stop]+text[stop:context_end]+block(text,'mc:maximal-order-transform')+'\n'
  result+='\n\n'.join(block(text,label)for label in spec.get('additional_support_labels',[]))+'\n'
 else:
  assert path=='blueprint/hironaka.tex'
  result='\\section{Original well-founded canonical-segment prerequisite}\n\n'+'\n\n'.join(block(text,label)for label in spec.get('initial_original_labels',spec['labels']))+'\n'
 result=append_original_node_layout(result,text,spec)
 # Established attachment/status metadata only. Every mathematical statement
 # and whole written proof remains the canonical original node text.
 from upstream_blueprint_scope import annotate
 result=annotate(result,spec['separately_verified_original_bindings'],{})
 assert [x for x in re.findall(r'\\label\{([^}]+)\}',result)if not x.startswith('sec:')]==spec['labels']
 return result
