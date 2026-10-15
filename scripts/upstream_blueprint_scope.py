"""Keep full upstream proofs while labelling declarations not exported locally.

Only attachment/status macros change. Mathematical statements, proofs, labels,
references and dependency prose retain their complete canonical text.
"""
import re
BINDINGS=re.compile(r'\\lean\{([^}]+)\}')
NODE=re.compile(r'(?=\\begin\{(?:lemma|theorem|proposition|corollary|definition|remark|convention)\})')
def annotate(text,external,unbound=()):
 result=[]
 for block in NODE.split(text):
  bindings=[b.strip() for match in BINDINGS.findall(block) for b in match.split(',')]
  upstream=[b for b in bindings if b in external];local=[b for b in bindings if b not in external]
  def replace(match):
   xs=[b.strip() for b in match[1].split(',')]
   if not any(x in external for x in xs):return match[0]
   groups=[]
   for x in xs:
    kind=('upstreamunbound' if external[x] in unbound else 'upstreamlean') if x in external else 'lean';value=external[x] if x in external else x
    if groups and groups[-1][0]==kind:groups[-1][1].append(value)
    else:groups.append((kind,[value]))
   return ''.join('\\'+kind+'{'+','.join(values)+'}' for kind,values in groups)
  block=BINDINGS.sub(replace,block)
  if upstream:
   status='historicalleanok' if any(external[x] in unbound for x in upstream) else ('mixedleanok' if local else 'upstreamleanok')
   block=block.replace('\\leanok','\\'+status)
  result.append(block)
 return ''.join(result)
