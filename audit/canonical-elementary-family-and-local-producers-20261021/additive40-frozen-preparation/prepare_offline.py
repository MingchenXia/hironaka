#!/usr/bin/env python3
"""OFFLINE candidates only. Never installs, builds, or changes either Git HEAD."""
import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
OUT = Path(__file__).resolve().parent
SRC = Path('/workspace/archon-publish')
DST = Path('/workspace/hironaka')
A = DST / 'audit/canonical-elementary-family-and-local-producers-20261021'
FINAL = '47cef49895832e3bfe492f66e1f2ac68785187dd'
BASE = '4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
EVIDENCE = 'TranscendentalNakamaye/audit/hironaka-all-nine-phase3-20261021/checkpoint-45/evidence/'
FINAL_MANIFEST = EVIDENCE + 'work/g1-g9-20261021-phase3/independent/phase3-45-modules-independent-manifest.json'
FIVE_MANIFEST = 'TranscendentalNakamaye/audit/hironaka-all-nine-phase3-20261021/checkpoint-5/evidence/work/g1-g9-20261021-phase3/independent/phase3-5-modules-independent-manifest.json'
sha = lambda b: hashlib.sha256(b).hexdigest()


def write(path, data):
    path = OUT / path
    assert path.resolve().is_relative_to(OUT)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data.encode() if isinstance(data, str) else data)


def js(path, obj):
    write(path, json.dumps(obj, indent=2, ensure_ascii=False) + '\n')


def git(*args):
    return subprocess.check_output(['git', '-C', str(SRC), *args])


def show(rev, path):
    return git('show', rev + ':' + path)


def batch(rev, paths):
    paths = list(dict.fromkeys(paths))
    raw = subprocess.check_output(['git', '-C', str(SRC), 'cat-file', '--batch'],
        input=''.join(rev + ':' + p + '\n' for p in paths).encode())
    pos = 0
    result = {}
    for p in paths:
        end = raw.index(b'\n', pos)
        header = raw[pos:end].split()
        assert len(header) == 3 and header[1] == b'blob', (p, header)
        size = int(header[2]); pos = end + 1
        result[p] = raw[pos:pos + size]; pos += size + 1
    assert pos == len(raw)
    return result


for rev in (FINAL, BASE):
    assert git('cat-file', '-t', rev).strip() == b'commit'

# Frozen production scripts are read/imported only, with bytecode writes disabled.
frozen_inputs = {}
for rel in ['provenance.json', 'blueprint-provenance.json', 'initial-port-plan.json',
            'new-native-actual-name-inventory.json', 'new-original-prerequisite-extracts/plan.json',
            'support-prep/principal-parts/missing-prerequisite-preflight/old1159-actual-moduledata-names.json',
            'sync_frozen_sources.py']:
    raw = (A / rel).read_bytes()
    frozen_inputs[str((A / rel).relative_to(DST))] = {'sha256': sha(raw), 'bytes': len(raw)}
    write('frozen-inputs/' + rel, raw)

base_records = json.loads((A / 'provenance.json').read_text())
base_blueprints = json.loads((A / 'blueprint-provenance.json').read_text())
initial = json.loads((A / 'initial-port-plan.json').read_text())
assert len(base_records) == 325
for rel, expected in initial['toolchain_profiles'].items():
    assert sha((DST / rel).read_bytes()) == expected, rel
    frozen_inputs[rel] = {'sha256': expected, 'bytes': (DST / rel).stat().st_size}

sys.path.insert(0, str(DST / 'scripts'))
import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
flat = names.flattened_short()
fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:' + '|'.join(flat) + r')\.(?=[\w«])')
frozen_rel = 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
frozen = (DST / frozen_rel).read_text()
fn = next(n for n in ast.parse(frozen).body if isinstance(n, ast.FunctionDef) and n.name == 'relocate')
env = {'re': re, 'names': names, 'flat': flat, 'fq': fq}
exec(compile(ast.Module(body=[fn], type_ignores=[]), str(DST / frozen_rel), 'exec'), env)
relocate = env['relocate']
sync_tree = ast.parse((A / 'sync_frozen_sources.py').read_text())
HEADER = ast.literal_eval(next(n.value for n in sync_tree.body
    if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'HEADER' for t in n.targets)))

for rel in ['scripts/upstream_namespace_map.py', 'scripts/upstream_blueprint_scope.py',
            'scripts/upstream_blueprint_external_bindings.json', 'scripts/upstream_blueprint_unbound_bindings.json',
            'scripts/upstream_blueprint_typography.json', frozen_rel]:
    raw = (DST / rel).read_bytes()
    frozen_inputs[rel] = {'sha256': sha(raw), 'bytes': len(raw)}
    write('frozen-contracts/' + rel, raw)
external = json.loads((DST / 'scripts/upstream_blueprint_external_bindings.json').read_text())
unbound = json.loads((DST / 'scripts/upstream_blueprint_unbound_bindings.json').read_text())
typography = json.loads((DST / 'scripts/upstream_blueprint_typography.json').read_text())

manifest_raw = show(FINAL, FINAL_MANIFEST)
five_raw = show(BASE, FIVE_MANIFEST)
manifest = json.loads(manifest_raw); five = json.loads(five_raw)
write('fixed-manifests/final45.json', manifest_raw); write('fixed-manifests/excluded5.json', five_raw)
all45 = {x['module']: x for x in manifest['modules']}
excluded = {x['module']: x for x in five['modules']}
selected = {m: r for m, r in all45.items() if m not in excluded}
assert len(all45) == 45 and len(excluded) == 5 and len(selected) == 40
base_modules = {x['source_module'] for x in base_records}
base_destinations = {x['destination_module'] for x in base_records}
assert set(excluded) <= base_modules
old_guard = initial['existing_destination_math_source_digests']
base_bp_paths = {x['destination_path'] for x in base_blueprints}
base_tree = set(git('ls-tree', '-r', '--name-only', BASE, '--', 'TranscendentalNakamaye/TranscendentalNakamaye').decode().splitlines())
files = batch(FINAL, [r[k]['path'] for r in all45.values() for k in ['source', 'blueprint']] +
              [EVIDENCE + r['receipt']['path'] for r in selected.values()])
excluded_rows = []
for m, r in excluded.items():
    final_r = all45[m]
    assert sha(files[final_r['source']['path']]) == r['source']['sha256']
    assert sha(show(BASE, r['source']['path'])) == r['source']['sha256']
    assert sha(files[final_r['blueprint']['path']]) == r['blueprint']['sha256']
    excluded_rows.append({'module': m, 'destination_module': names.new_mod(m),
        'source_sha256': r['source']['sha256'], 'blueprint_sha256': r['blueprint']['sha256'],
        'actual_root_observations': r['actual_root_count'], 'already_in_base325': True,
        'source_and_blueprint_unchanged_in_final45': True})
js('excluded-five.json', excluded_rows)

IMPORT = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', re.M)
modules = []; blueprints = []; roots = []; bindings = []; proofs = []; dependencies = []
module_collisions = []; chapter_collisions = []; mismatches = []; hist = {}
for m, r in sorted(selected.items()):
    src = files[r['source']['path']]; bp = files[r['blueprint']['path']]
    receipt_raw = files[EVIDENCE + r['receipt']['path']]
    assert sha(src) == r['source']['sha256'] and sha(bp) == r['blueprint']['sha256']
    assert sha(receipt_raw) == r['receipt']['sha256']
    assert r['source']['path'] not in base_tree, m
    receipt = json.loads(receipt_raw)
    out_m = names.new_mod(m); dst = out_m.replace('.', '/') + '.lean'
    output = HEADER + relocate(src.decode())
    existing = (DST / dst).exists()
    if existing: module_collisions.append({'module': m, 'destination': dst, 'sha256': sha((DST / dst).read_bytes())})
    rec = {'published_source_revision': FINAL, 'immutable_base_revision': BASE, 'source_module': m,
        'source_path': r['source']['path'], 'source_sha256': sha(src), 'source_bytes': len(src),
        'destination_module': out_m, 'destination_path': dst, 'destination_sha256': sha(output.encode()),
        'candidate_path': 'candidate/' + dst, 'whole_original_source_preserved': True,
        'proof_body_edits': 0, 'additional_support_imports': [], 'administrative_context_edits': [],
        'actual_root_observations': r['actual_root_count'], 'independent_receipt_git_path': EVIDENCE + r['receipt']['path'],
        'independent_receipt_sha256': sha(receipt_raw), 'destination_already_exists': existing}
    modules.append(rec)
    write('original/' + r['source']['path'], src); write('candidate/' + dst, output)
    write('fixed-receipts/' + m + '.json', receipt_raw)
    imports = IMPORT.findall(src.decode())
    for dep in imports:
        if not dep.startswith('TranscendentalNakamaye.'):
            dependencies.append({'module': m, 'dependency': dep, 'kind': 'external_import', 'destination_dependency': dep})
            continue
        dest_dep = names.new_mod(dep); dest_path = dest_dep.replace('.', '/') + '.lean'
        kind = ('additive40' if dep in selected else 'base325' if dep in base_modules else
                'preserved_old_public' if dest_path in old_guard else 'existing_unclassified' if (DST / dest_path).exists() else 'MISSING')
        dependencies.append({'module': m, 'dependency': dep, 'destination_dependency': dest_dep,
            'destination_path': dest_path, 'kind': kind})
    source_bindings = [x.strip() for g in re.findall(r'\\lean\{([^}]+)\}', bp.decode()) for x in g.split(',')]
    bp_dst = 'blueprint/' + Path(r['blueprint']['path']).name
    text = names.rename_text_names(bp.decode()).replace('\\chapter{', '\\section{')
    adjustments = typography.get(Path(bp_dst).name, [])
    for adj in adjustments:
        assert text.count(adj['before']) == 1
        text = text.replace(adj['before'], adj['after'])
    text = annotate(text, external, unbound)
    if (DST / bp_dst).exists():
        chapter_collisions.append({'source': r['blueprint']['path'], 'destination': bp_dst,
            'in_base311': bp_dst in base_bp_paths, 'sha256': sha((DST / bp_dst).read_bytes())})
    source_proofs = re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}', bp.decode(), re.S)
    out_proofs = re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}', text, re.S)
    assert len(source_proofs) == len(out_proofs)
    for i, (before, after) in enumerate(zip(source_proofs, out_proofs)):
        expected = names.rename_text_names(before)
        ok = expected == after
        proofs.append({'module': m, 'proof_index': i, 'original_sha256': sha(before.encode()),
            'relocated_expected_sha256': sha(expected.encode()), 'candidate_sha256': sha(after.encode()),
            'whole_proof_retained_after_frozen_name_relocation': ok})
        if not ok: mismatches.append({'module': m, 'proof_index': i})
    local_bindings = [x.strip() for g in re.findall(r'\\lean\{([^}]+)\}', text) for x in g.split(',')]
    assert len(source_bindings) == len(local_bindings), m
    for original, local in zip(source_bindings, local_bindings):
        bindings.append({'owner_module': m, 'source_name': original, 'candidate_name': local})
    blueprints.append({'module': m, 'published_source_revision': FINAL, 'source_path': r['blueprint']['path'],
        'source_sha256': sha(bp), 'destination_path': bp_dst, 'destination_sha256': sha(text.encode()),
        'candidate_path': 'candidate/' + bp_dst, 'labels': re.findall(r'\\label\{([^}]+)\}', text),
        'proofs': len(source_proofs), 'definitions': len(re.findall(r'\\begin\{definition\}', text)),
        'original_bindings': source_bindings, 'local_bindings': local_bindings,
        'whole_original_chapter_preserved': True, 'complete_node_extraction': False,
        'typography_adjustments': adjustments})
    write('original/' + r['blueprint']['path'], bp); write('candidate/' + bp_dst, text)
    assert len(receipt['actual_roots']) == r['actual_root_count']
    for root in receipt['actual_roots']:
        original = root['name']; local = names.rename_const(original)
        ax = ', '.join(sorted(root['transitive_axioms'])) or '(none)'; hist[ax] = hist.get(ax, 0) + 1
        roots.append({'owner_source_module': m, 'owner_destination_module': out_m,
            'source_name': original, 'candidate_name': local,
            'is_private': original.startswith('_private.'), 'transitive_axioms': root['transitive_axioms'],
            'evidence': EVIDENCE + r['receipt']['path']})

# Actual installed old/public inventories are read, never re-exported or replayed.
old_actual = json.loads((A / 'support-prep/principal-parts/missing-prerequisite-preflight/old1159-actual-moduledata-names.json').read_text())
base_actual = json.loads((A / 'new-native-actual-name-inventory.json').read_text())
supplements = json.loads((A / 'new-original-prerequisite-extracts/plan.json').read_text())
known = {}
for row in old_actual:
    for name in row['actual_roots']: known.setdefault(name, []).append({'cohort': 'old1159', 'module': row['module']})
for row in base_actual:
    for root in row['actual_roots']:
        name = names.rename_const(root['original_name'])
        known.setdefault(name, []).append({'cohort': 'base316', 'module': row['source_module']})
for row in supplements:
    for name in row['complete_original_declarations']:
        known.setdefault(names.rename_const(name), []).append({'cohort': 'supplement13', 'module': row['destination_module']})
collisions = [{'root': r, 'existing_owners': known[r['candidate_name']]} for r in roots if r['candidate_name'] in known]
new_by_name = {}
for r in roots: new_by_name.setdefault(r['candidate_name'], []).append(r['owner_source_module'])
new_duplicates = [{'name': n, 'owner_modules': ms} for n, ms in new_by_name.items() if len(ms) > 1]

ordered = []; seen = set(); visiting = set()
def visit(m):
    if m in seen: return
    assert m not in visiting, ('Import cycle', m)
    visiting.add(m)
    for row in dependencies:
        if row['module'] == m and row['kind'] == 'additive40': visit(row['dependency'])
    visiting.remove(m); seen.add(m); ordered.append(m)
for m in sorted(selected): visit(m)
write('module-renames.tsv', ''.join(r['source_module'] + '\t' + r['destination_module'] + '\n' for r in modules))
write('topological-modules.txt', ''.join(names.new_mod(m) + '\n' for m in ordered))
write('candidate-root-imports.txt', ''.join('import ' + names.new_mod(m) + '\n' for m in ordered))
write('candidate-blueprint-inputs.txt', ''.join('\\input{' + Path(r['destination_path']).stem + '}\n' for r in blueprints))
js('module-provenance-plan.json', modules); js('blueprint-provenance-plan.json', blueprints)
js('actual-root-name-relocations.json', roots); js('literal-blueprint-bindings.json', bindings)
js('whole-blueprint-proof-preservation.json', proofs); js('dependencies.json', dependencies)
js('collision-preflight.json', {'public_root_collisions': [r for r in collisions if not r['root']['is_private']],
    'private_root_collisions': [r for r in collisions if r['root']['is_private']],
    'candidate_duplicate_names': new_duplicates, 'module_path_collisions': module_collisions,
    'blueprint_path_collisions': chapter_collisions, 'old_actual_observations': sum(len(x['actual_roots']) for x in old_actual),
    'base316_actual_observations': sum(len(x['actual_roots']) for x in base_actual),
    'supplement_actual_selected_names': sum(len(x['complete_original_declarations']) for x in supplements),
    'actual_existing_compiled_names_not_lexical_grep': True})
outside = [r for r in dependencies if r['kind'] not in ['additive40', 'base325', 'external_import']]
js('outside-base325-dependencies.json', outside)
js('input-fingerprints.json', {'ordinary_repository': str(SRC), 'fixed_final': FINAL, 'fixed_base': BASE,
    'fixed_final_manifest': {'git_path': FINAL_MANIFEST, 'sha256': sha(manifest_raw)},
    'fixed_excluded_five_manifest': {'git_path': FIVE_MANIFEST, 'sha256': sha(five_raw)},
    'standalone_frozen_inputs': frozen_inputs})
summary = {'status': 'OFFLINE_CANDIDATES_AND_STATIC_PREFLIGHT_ONLY', 'fixed_ordinary_final45': FINAL,
    'fixed_ordinary_base': BASE, 'base325_existing_sources': len(base_records), 'excluded_existing_five': len(excluded),
    'additional_whole_source_modules': len(modules), 'additional_whole_chapters': len(blueprints),
    'actual_root_observations': len(roots), 'distinct_actual_root_names': len(new_by_name),
    'actual_transitive_axiom_histogram_from_frozen_receipts': hist,
    'complete_proof_nodes': sum(r['complete_proof_leanok_nodes'] for r in selected.values()),
    'definition_nodes': sum(r['ready_definition_nodes'] for r in selected.values()),
    'literal_blueprint_binding_observations': len(bindings), 'distinct_literal_bindings': len({r['source_name'] for r in bindings}),
    'whole_BP_proofs_checked': len(proofs), 'whole_BP_proof_preservation_mismatches': mismatches,
    'module_path_collisions': len(module_collisions), 'chapter_path_collisions': len(chapter_collisions),
    'actual_public_root_collisions': sum(not r['root']['is_private'] for r in collisions),
    'actual_private_root_collisions': sum(r['root']['is_private'] for r in collisions),
    'new_name_duplicates': len(new_duplicates), 'dependency_edges': len(dependencies),
    'outside_base325_direct_dependencies': len(outside), 'unresolved_missing_imports': [r for r in dependencies if r['kind'] == 'MISSING'],
    'production_source_BP_master_or_Git_edits': False, 'Lean_build_kernel_Expr_invocations': 0,
    'standalone_mathematical_verification_claimed': False,
    'install_only_after_retained_base323_critical_gates': True,
    'pending': ['Frontier install/replay after retained base323 gates', 'Lean elaboration and native build',
        'Complete actual module metadata roots', 'Kernel replay', 'Whole type/value expression comparison',
        'Whole transitive axiom and literal binding checks', 'Final source and blueprint preservation/reproducibility checks']}
assert len(modules) == 40 and len(blueprints) == 40
assert len(roots) == manifest['phase3_actual_root_observations'] - five['phase3_actual_root_observations']
assert not mismatches
js('summary.json', summary)
print(json.dumps(summary, indent=2))
