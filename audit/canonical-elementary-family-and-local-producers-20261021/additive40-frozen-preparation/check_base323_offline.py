#!/usr/bin/env python3
"""Static native/destination import closure only; never invokes Lean or installs."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

OUT = Path(__file__).resolve().parent
DST = Path('/workspace/hironaka')
SRC = Path('/workspace/archon-publish')
REV = '47cef49895832e3bfe492f66e1f2ac68785187dd'
BASE = '4c6cdc79e7f8e506fb4b9a820c0a7b2946ad2a07'
DEFERRED = {
    'TranscendentalNakamaye.Pending.HironakaOriginalGlobalOffZero': 'Hironaka.Resolution.HironakaOriginalGlobalOffZero',
    'TranscendentalNakamaye.Pending.HironakaOriginalGlobalProperModification': 'Hironaka.Resolution.HironakaOriginalGlobalProperModification',
}
IMP = re.compile(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)', re.M)
sha = lambda raw: hashlib.sha256(raw).hexdigest()
read = lambda p: json.loads((OUT / p).read_text())


def save(p, obj):
    (OUT / p).write_text(json.dumps(obj, indent=2) + '\n')


def git(*args):
    return subprocess.check_output(['git', '-C', str(SRC), *args])


def batch(rev, paths):
    paths = list(dict.fromkeys(paths))
    raw = subprocess.check_output(['git', '-C', str(SRC), 'cat-file', '--batch'],
        input=''.join(rev + ':' + p + '\n' for p in paths).encode())
    pos = 0; result = {}
    for p in paths:
        end = raw.index(b'\n', pos); h = raw[pos:end].split()
        assert len(h) == 3 and h[1] == b'blob', (p, h)
        pos = end + 1; size = int(h[2]); result[p] = raw[pos:pos + size]; pos += size + 1
    assert pos == len(raw)
    return result


mods = read('module-provenance-plan.json')
base_records = read('frozen-inputs/provenance.json')
assert len(base_records) == 325 and set(DEFERRED) <= {r['source_module'] for r in base_records}
base323 = [r for r in base_records if r['source_module'] not in DEFERRED]
assert len(base323) == 323
selected = {r['source_module']: r for r in mods}
destination_selected = {r['destination_module']: r for r in mods}
base323_sources = {r['source_module'] for r in base323}
base323_destinations = {r['destination_module'] for r in base323}
deferred_destinations = set(DEFERRED.values())

native_paths = set(git('ls-tree', '-r', '--name-only', REV, '--',
    'TranscendentalNakamaye/TranscendentalNakamaye').decode().splitlines())
native_graph = {}; native_missing = []; parents = {m: None for m in selected}; frontier = list(selected)
while frontier:
    usable = []
    for m in frontier:
        p = 'TranscendentalNakamaye/' + m.replace('.', '/') + '.lean'
        if p not in native_paths:
            native_missing.append({'module': m, 'path': p}); continue
        usable.append((m, p))
    blobs = batch(REV, [p for _, p in usable])
    next_wave = []
    for m, p in usable:
        raw = blobs[p]; imports = IMP.findall(raw.decode())
        native_graph[m] = {'source_path': p, 'source_sha256': sha(raw), 'imports': imports,
            'scope': 'additive40' if m in selected else 'available_base323' if m in base323_sources else
                'DEFERRED' if m in DEFERRED else 'older_native_dependency'}
        for dep in imports:
            if dep.startswith('TranscendentalNakamaye.') and dep not in parents:
                parents[dep] = m; next_wave.append(dep)
    frontier = next_wave


def chain(name, parent):
    result = [name]
    while parent.get(name) is not None:
        name = parent[name]; result.append(name)
    return list(reversed(result))


native_blocked = [{'module': m, 'dependency_chain': chain(m, parents)} for m in DEFERRED if m in parents]
# Explicit comparison of every non-additive native dependency at the two fixed commits.
base_paths = set(git('ls-tree', '-r', '--name-only', BASE, '--',
    'TranscendentalNakamaye/TranscendentalNakamaye').decode().splitlines())
prior_paths = [r['source_path'] for m, r in native_graph.items() if m not in selected and r['source_path'] in base_paths]
before = batch(BASE, prior_paths)
preservation = [{'module': m, 'source_path': r['source_path'], 'base_sha256': sha(before[r['source_path']]),
    'final_sha256': r['source_sha256'], 'byte_identical': sha(before[r['source_path']]) == r['source_sha256']}
    for m, r in native_graph.items() if m not in selected and r['source_path'] in before]
new_unlisted = [{'module': m, 'source_path': r['source_path']} for m, r in native_graph.items()
    if m not in selected and r['source_path'] not in base_paths]

# Effective standalone imports include the real existing base context/support imports.
# Deferred modules are UNAVAILABLE even if a stale production file is still present.
destination_graph = {}; destination_missing = []
destination_parents = {m: None for m in destination_selected}; queue = list(destination_selected)
while queue:
    m = queue.pop(0)
    if m in deferred_destinations:
        destination_graph[m] = {'scope': 'DEFERRED_UNAVAILABLE', 'physical_file_ignored': True}; continue
    p = m.replace('.', '/') + '.lean'
    path = OUT / 'candidate' / p if m in destination_selected else DST / p
    if not path.exists():
        destination_missing.append({'module': m, 'path': p, 'dependency_chain': chain(m, destination_parents)}); continue
    raw = path.read_bytes(); imports = IMP.findall(raw.decode())
    destination_graph[m] = {'path': p, 'sha256': sha(raw), 'imports': imports,
        'scope': 'additive40_candidate' if m in destination_selected else 'available_base323' if m in base323_destinations else 'older_or_support_standalone_dependency'}
    for dep in imports:
        if dep.startswith('Hironaka.') and dep not in destination_parents:
            destination_parents[dep] = m; queue.append(dep)
destination_blocked = [{'module': m, 'dependency_chain': chain(m, destination_parents)}
    for m in deferred_destinations if m in destination_parents]

collisions = read('collision-preflight.json')
for row in collisions['public_root_collisions']:
    r = row['root']
    row['foreign_namespace_root'] = not r['source_name'].startswith(r['owner_source_module'] + '.')
    row['generated_helper_suffix'] = bool(re.search(r'\.(?:eq_\d+|congr_simp)$', r['source_name']))
    row['classification'] = ('FOREIGN_GENERATED_HELPER_OVERLAP_REQUIRES_WHOLE_IDENTITY_CHECK'
        if row['foreign_namespace_root'] and row['generated_helper_suffix'] else 'SOURCE_DECLARATION_COLLISION_REVIEW_REQUIRED')
    row['policy'] = 'Retain this actual root observation. Do not erase, rename, filter, or assume type/value equality; later imported-owner and whole-expression gates must resolve reuse.'
save('collision-preflight.json', collisions)

# Blueprint labels/uses are inspected statically against the existing files plus candidates.
existing_labels = {}
for p in sorted((DST / 'blueprint').glob('*.tex')):
    for label in re.findall(r'\\label\{([^}]+)\}', p.read_text()): existing_labels.setdefault(label, []).append(str(p.relative_to(DST)))
chapters = read('blueprint-provenance-plan.json'); new_labels = {}
for bp in chapters:
    for label in bp['labels']: new_labels.setdefault(label, []).append(bp['destination_path'])
label_collisions = [{'label': l, 'new_chapters': ps, 'existing_chapters': existing_labels[l]}
    for l, ps in new_labels.items() if l in existing_labels]
missing_uses = []; total_uses = 0
for bp in chapters:
    text = (OUT / bp['candidate_path']).read_text()
    for group in re.findall(r'\\uses\{([^}]+)\}', text):
        for dep in group.split(','):
            dep = dep.strip(); total_uses += 1
            if dep not in new_labels and dep not in existing_labels:
                missing_uses.append({'chapter': bp['destination_path'], 'label': dep})
save('blueprint-static-checks.json', {'new_labels': len(new_labels), 'use_observations': total_uses,
    'label_collisions': label_collisions, 'duplicate_new_labels': {l: ps for l, ps in new_labels.items() if len(ps) > 1},
    'unresolved_uses': missing_uses, 'existing_labels_are_static_source_only': True})

save('native-transitive-import-closure.json', native_graph)
save('standalone-transitive-import-closure.json', destination_graph)
save('dependency-source-preservation.json', preservation)
result = {'status': 'OFFLINE_BASE323_IMPORT_CLOSURE_PREFLIGHT_ONLY', 'base325_records': 325,
    'available_base323_records': 323, 'deferred_whole_modules': DEFERRED,
    'additive_whole_modules': 40, 'proposed_source_partition': '323 retained-base candidates + 40 additive candidates; deferred 2 excluded',
    'native_transitive_modules': len(native_graph), 'native_deferred_dependency_chains': native_blocked,
    'native_missing_sources': native_missing, 'additional_unlisted_postbase_dependencies': new_unlisted,
    'prior_native_dependencies_compared_at_fixed_commits': len(preservation),
    'changed_prior_native_dependencies': [x for x in preservation if not x['byte_identical']],
    'effective_standalone_transitive_modules': len(destination_graph),
    'standalone_deferred_dependency_chains': destination_blocked, 'standalone_missing_imports': destination_missing,
    'no_new40_dependency_on_OffZero_or_ProperModification': not native_blocked and not destination_blocked,
    'public_root_overlap_count': len(collisions['public_root_collisions']),
    'foreign_generated_helper_overlap_count': sum(r['classification'].startswith('FOREIGN_GENERATED') for r in collisions['public_root_collisions']),
    'handwritten_source_declaration_collision_count': sum(r['classification'].startswith('SOURCE_DECLARATION') for r in collisions['public_root_collisions']),
    'blueprint_label_collisions': len(label_collisions), 'blueprint_unresolved_uses': len(missing_uses),
    'no_Lean_or_Expr_or_kernel_commands': True, 'no_production_or_Git_changes': True,
    'full_constant_dependency_and_type_value_identity_gates_still_pending': True}
save('base323-availability.json', result)
summary = read('summary.json')
summary['effective_available_base_module_count'] = 323
summary['deferred_base_modules'] = DEFERRED
summary['base323_transitive_preflight'] = result
save('summary.json', summary)
print(json.dumps(result, indent=2))
