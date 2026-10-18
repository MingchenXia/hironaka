"""Check labelled source statements and their following complete proof environments.

Definitions are mathematical inputs and may have no proof. A labelled theorem,
lemma, proposition or corollary must have a nonempty complete proof before the
next labelled statement. No proof is manufactured for a definition.
"""
import hashlib,re

STATEMENT=re.compile(r'\\begin\{(theorem|lemma|proposition|corollary|definition)\}(.*?)\\end\{\1\}',re.S)
PROOF=re.compile(r'\\begin\{proof\}(.*?)\\end\{proof\}',re.S)

def inspect(text):
    statements=list(STATEMENT.finditer(text));records=[]
    for index,match in enumerate(statements):
        labels=re.findall(r'\\label\{([^}]+)\}',match[2])
        if not labels:continue
        stop=statements[index+1].start() if index+1<len(statements) else len(text)
        following=text[match.end():stop];proofs=PROOF.findall(following)
        assert following.count('\\begin{proof}')==following.count('\\end{proof}')==len(proofs),labels
        assert all(proof.strip() for proof in proofs),labels
        if match[1]!='definition':assert proofs,('Missing complete non-definition proof',labels)
        records.append({'kind':match[1],'labels':labels,'complete_proofs':len(proofs),
            'statement_sha256':hashlib.sha256(match[0].encode()).hexdigest(),
            'proof_sha256':[hashlib.sha256(p.encode()).hexdigest() for p in proofs]})
    assert {label for record in records for label in record['labels']}==set(re.findall(r'\\label\{([^}]+)\}',text))
    return records
