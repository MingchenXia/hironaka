"""Read-only exact DAG diagnosis; writes sidecars/draft only, never Lean."""
from pathlib import Path
import gzip
import hashlib
import json
import subprocess

A = Path('/workspace/hironaka/audit/canonical-elementary-family-and-local-producers-20261021')
OUT = Path(__file__).resolve().parent
ATTEMPT = A / 'final-per-module-expressions/Hironaka.Resolution.HironakaActualPointOrderRetainingHS/attempt1'
sha = lambda b: hashlib.sha256(b).hexdigest()
report_path = ATTEMPT / 'raw-complete-parent-comparison.json'
report = json.loads(report_path.read_text())
before = {p.name: sha(p.read_bytes()) for p in ATTEMPT.iterdir() if p.is_file()}

def load(side):
    path = ATTEMPT / (side + '-unfiltered.jsonl.gz')
    raw = gzip.decompress(path.read_bytes())
    expected = report['old' if side == 'original' else 'native']['sha256']
    assert sha(raw) == expected
    return {x['name']: x for line in raw.decode().splitlines() if (x := json.loads(line))}

old, new = load('original'), load('public')
def name(x):
    return '' if x[0] == 'anonymous' else (name(x[1]) + '.' + str(x[2])).lstrip('.')

def spine(nodes, i):
    args = []
    while nodes[i]['tag'] == 'application':
        i, arg = nodes[i]['children']; args.append(arg)
    n = nodes[i]
    head = name(n['data'][0]) if n['tag'] == 'constant' else n['tag']
    return head, args[::-1], i

def compact(nodes, i):
    n = nodes[i]
    if n['tag'] == 'application':
        h, args, _ = spine(nodes, i)
        return h + '[' + str(len(args)) + ']'
    if n['tag'] == 'constant': return name(n['data'][0])
    if n['tag'] in ('lambda', 'forall', 'let'): return n['tag'] + ' ' + name(n['data'][0])
    return n['tag'] + ':' + json.dumps(n['data'], ensure_ascii=False)

def first(x, y, rx, ry):
    pending = [(rx, ry, [])]; seen = set()
    while pending:
        i, j, path = pending.pop()
        if (i, j) in seen: continue
        seen.add((i, j)); a, b = x[i], y[j]
        if a['tag'] != b['tag'] or a['data'] != b['data'] or len(a['children']) != len(b['children']):
            return i, j, path
        pending.extend((u, v, path + [(i, j, k)]) for k, (u, v) in enumerate(zip(a['children'], b['children'])))
    return None

rows = []
for d in report['differences']:
    nm = d['constant'][1]
    if not (nm.endswith('.reduced_component_member_span') or nm.endswith('.actualHomogeneousInitialIdeal_eq_reduced_component_span')):
        continue
    o, n = old[nm], new[nm]; x, y = o['fullExprNodes'], n['fullExprNodes']
    assert first(x, y, o['typeRoot'], n['typeRoot']) is None
    i, j, path = first(x, y, o['valueRoot'], n['valueRoot'])
    assert (i, j) == (d['difference']['old_node'], d['difference']['native_node'])
    paired = []
    binders = []
    for u, v, k in path:
        row = {'child': k, 'original_node': u, 'public_node': v,
               'original_head': compact(x, u), 'public_head': compact(y, v),
               'original_exact_node': x[u], 'public_exact_node': y[v]}
        paired.append(row)
        if x[u]['tag'] in ('lambda', 'forall', 'let'):
            binders.append(row)
    ancestor = next((u, v) for u, v, _ in reversed(path)
                    if spine(x, u)[0] == 'IsOrderedRing.toIsOrderedAddMonoid'
                    and spine(y, v)[0] == 'LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid')
    def reachable(nodes, root):
        todo=[root]; found=set()
        while todo:
            k=todo.pop()
            if k not in found: found.add(k);todo.extend(nodes[k]['children'])
        return [{'id': k, **nodes[k]} for k in sorted(found)]
    addleft = next((u, v) for u, v, _ in reversed(path)
                   if spine(x, u)[0] == spine(y, v)[0] == 'IsOrderedAddMonoid.toAddLeftMono')
    cast = next((u, v) for u, v, _ in reversed(path)
                if spine(x, u)[0] == spine(y, v)[0] == 'Nat.cast_lt._simp_1')
    rows.append({'declaration': nm, 'field': d['field'], 'types_exact': True,
                 'first_difference': {'original_node': i, 'public_node': j, 'original': x[i], 'public': y[j]},
                 'first_difference_reproduces_frozen_report': True,
                 'complete_paired_root_path': paired, 'complete_binder_let_ancestry': binders,
                 'nearest_common_addleftmono': {'original_node': addleft[0], 'public_node': addleft[1]},
                 'nat_cast_lt_application': {'original_node': cast[0], 'public_node': cast[1]},
                 'genuine_instance_ancestor': {
                     'original_root': ancestor[0], 'public_root': ancestor[1],
                     'original_head': spine(x, ancestor[0])[0], 'public_head': spine(y, ancestor[1])[0],
                     'original_complete_reachable_nodes': reachable(x, ancestor[0]),
                     'public_complete_reachable_nodes': reachable(y, ancestor[1])}})
assert len(rows) == 2

native_path = 'TranscendentalNakamaye/TranscendentalNakamaye/Pending/HironakaActualPointOrderRetainingHS.lean'
rev = '47cef49895832e3bfe492f66e1f2ac68785187dd'
native = subprocess.check_output(['git', '-C', '/workspace/archon-publish', 'show', rev + ':' + native_path])
public_path = Path('/workspace/hironaka/Hironaka/Resolution/HironakaActualPointOrderRetainingHS.lean')
frozen_public_path = A / 'additive40-frozen-preparation/candidate/Hironaka/Resolution/HironakaActualPointOrderRetainingHS.lean'
public = frozen_public_path.read_bytes()
observed_current = public_path.read_bytes()
(OUT / 'native-fixed-original.lean.txt').write_bytes(native)
(OUT / 'public-before-context.lean.txt').write_bytes(public)
(OUT / 'public-current-observed-owner-context.lean.txt').write_bytes(observed_current)

attr = 'attribute [local instance 2000] IsOrderedRing.toIsOrderedAddMonoid in\n'
anchors = ['private theorem reduced_component_member_span ',
           'theorem actualHomogeneousInitialIdeal_eq_reduced_component_span (I : Ideal R) :']
candidate = public.decode(); scopes = []
for anchor in anchors:
    assert candidate.count(anchor) == 1
    assert attr + anchor not in candidate
    line = public.decode()[:public.decode().index(anchor)].count('\n') + 1
    scopes.append({'before': anchor, 'after': attr + anchor, 'public_anchor_line': line,
                   'context_only': True, 'proof_or_statement_token_edits': 0})
    candidate = candidate.replace(anchor, attr + anchor, 1)
(OUT / 'candidate-two-declaration-context-only.lean.txt').write_text(candidate)
restored = candidate
for scope in reversed(scopes):
    assert restored.count(scope['after']) == 1
    restored = restored.replace(scope['after'], scope['before'], 1)
assert restored.encode() == public
assert candidate.encode() == observed_current

mathlib = []
for relative in ['Mathlib/Data/ENat/Basic.lean', 'Mathlib/Algebra/Order/Ring/Defs.lean',
                 'Mathlib/Algebra/Order/Monoid/Defs.lean', 'Mathlib/Algebra/Order/AddGroupWithTop.lean',
                 'Mathlib/Data/Nat/Cast/Order/Basic.lean']:
    p = Path('/workspace/hironaka/.lake/packages/mathlib') / relative
    q = Path('/workspace/archon-nakamaye/TranscendentalNakamaye/.lake/packages/mathlib') / relative
    assert p.read_bytes() == q.read_bytes()
    mathlib.append({'source': relative, 'native_public_source_bytes_identical': True, 'sha256': sha(p.read_bytes())})

proof_locations = []
for text in ['(lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self q) hprod)',
             'exact_mod_cast (show Finsupp.degree α<actualHomogeneousInitialDegree F.val F.property.2 from']:
    assert native.decode().count(text) == public.decode().count(text) == 1
    proof_locations.append({'literal_original_source_text': text,
        'native_line': native.decode()[:native.decode().index(text)].count('\n') + 1,
        'public_line': public.decode()[:public.decode().index(text)].count('\n') + 1})

result = {'status': 'READ_ONLY_EXACT_FIRST_DAG_CONTEXT_DIAGNOSIS_PENDING_PUBLIC_REPLAY',
          'scope': 'Only the two mathematical reduced-component proof differences; raw frontend differences remain in the unmodified attempt1 report.',
          'report': {'path': str(report_path), 'sha256': sha(report_path.read_bytes()), 'raw_status_retained': report['status']},
          'lossless_input_fingerprints': before, 'paired_results': rows,
          'fixed_native_source': {'revision': rev, 'path': native_path, 'sha256': sha(native)},
          'frozen_public_source_before': {'path': str(frozen_public_path), 'sha256': sha(public)},
          'public_current_observed_owner_context': {'path': str(public_path), 'sha256': sha(observed_current), 'exactly_the_two_recorded_context_insertions': True},
          'literal_exact_mod_cast_source_locations': proof_locations,
          'same_pinned_mathlib_sources': mathlib,
          'authentic_original_instance_path': ['Nat.cast_lt._simp_1', 'IsOrderedAddMonoid.toAddLeftMono', 'IsOrderedRing.toIsOrderedAddMonoid', 'instIsOrderedRingENat'],
          'public_instance_path': ['Nat.cast_lt._simp_1', 'IsOrderedAddMonoid.toAddLeftMono', 'LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid', 'instLinearOrderedAddCommMonoidWithTopENat'],
          'cause': 'Different genuine existing IsOrderedAddMonoid ENat ancestry selected by elaboration. The exact proofs establish the original path; no native explicit priority command is claimed.',
          'proposed_declaration_local_restoration': scopes,
          'candidate_only_path': 'candidate-two-declaration-context-only.lean.txt',
          'candidate_sha256': sha(candidate.encode()),
          'new_instance_definition_or_payload_replacement': False,
          'raw_gate_or_expr_evidence_modified': False,
          'production_or_git_modified': False,
          'lean_build_kernel_or_expr_runtime_invoked': False,
          'acceptance': 'Not a post-context PASS. Frontier must elaborate and repeat the unchanged strict whole-parent comparison; all raw FAIL evidence remains.'}
(OUT / 'paired-first-dag-context-proposal.json').write_text(json.dumps(result, indent=2, ensure_ascii=False) + '\n')
after = {p.name: sha(p.read_bytes()) for p in ATTEMPT.iterdir() if p.is_file()}
assert after == before
print(json.dumps({'status': result['status'], 'mathematical_results': len(rows),
                  'source_proof_locations': proof_locations, 'scopes': scopes,
                  'candidate_sha256': result['candidate_sha256'], 'raw_attempt_byte_identical': True}, ensure_ascii=False, indent=2))
