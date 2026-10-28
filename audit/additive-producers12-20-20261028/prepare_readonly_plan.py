#!/usr/bin/env python3
"""Read-only public checkout planning for the next immutable native cohort.

Writes only this separate new audit directory. Does not install public files,
run Lean, mutate Git, or replay earlier kernel/Expr gates.
"""
from pathlib import Path
import ast
import collections
import hashlib
import importlib.util
import json
import re
import subprocess
import sys

sys.dont_write_bytecode = True

E = Path(__file__).resolve().parent
D = E.parents[1]
A = D / 'audit/disjoint-producers-20261028'
R = Path('/workspace/hironaka-current-20261025')
REV = '6e453e142420e6a64ccfdb5cadd15abc2379f581'
sha = lambda data: hashlib.sha256(data).hexdigest()
assert not (E / 'plan.json').exists(), 'Keep immutable plans; add revisions explicitly'

def native(path, rev=REV):
    return subprocess.check_output(['git', '-C', str(R), 'show', rev + ':' + path])

def save(relative, data):
    path = E / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == data, ('Refuse changed capture', str(path))
    else:
        path.write_bytes(data)

def save_json(relative, value):
    save(relative, (json.dumps(value, indent=2) + '\n').encode())

cohort_path = 'TranscendentalNakamaye/audit/hironaka-disjoint-20261028/cohort.json'
cohort_raw = native(cohort_path)
cohort = json.loads(cohort_raw)
assert len(cohort) == 20
roots = cohort[11:]
assert len(roots) == 9
save('native-acceptance/cohort20.json', cohort_raw)
closure_path = 'TranscendentalNakamaye/audit/hironaka-disjoint-20261028/main-only-import-closure.json'
closure_raw = native(closure_path)
closure = json.loads(closure_raw)
assert closure['unmerged_pr244_imports'] == 0
save('native-acceptance/main-only-import-closure.json', closure_raw)
allowed = {row['module']: row for row in closure['pins']}

mapping_path = A / 'frozen-tools/upstream_namespace_map.py'
spec = importlib.util.spec_from_file_location('next_frozen_names', mapping_path)
names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
flat = names.flattened_short()
fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:' + '|'.join(flat) + r')\.(?=[\w«])')
node = next(node for node in ast.parse((A / 'frozen-tools/verify_incremental_source.py').read_text()).body if isinstance(node, ast.FunctionDef) and node.name == 'relocate')
scope = {'re': re, 'names': names, 'flat': flat, 'fq': fq}
exec(compile(ast.Module(body=[node], type_ignores=[]), 'frozen-canonical-relocation', 'exec'), scope)
import_scope = {'re': re}
nodes = [node for node in ast.parse((A / 'sync_cohort.py').read_text()).body if isinstance(node, ast.FunctionDef) and node.name in ['uncomment', 'imports']]
exec(compile(ast.Module(body=nodes, type_ignores=[]), 'native-import-parser', 'exec'), import_scope)
header = '/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'
seen = set()
modules = []
stopped = []

def visit(module, reason):
    if module in seen:
        return
    seen.add(module)
    destination = names.new_mod(module)
    destination_path = destination.replace('.', '/') + '.lean'
    path = 'TranscendentalNakamaye/' + module.replace('.', '/') + '.lean'
    raw = native(path)
    own = allowed.get(module, {}).get('own_new_module', False)
    if not own:
        assert raw == native(path, closure['base']), ('Accepted main parent changed', module)
    if (D / destination_path).exists():
        stopped.append({'source_module': module, 'destination_module': destination,
                        'destination_path': destination_path,
                        'existing_sha256': sha((D / destination_path).read_bytes()),
                        'ordinary_CI_visibility_not_inferred_from_path': True})
        return
    assert not re.search(r'^\s*axiom\b|\bsorry(?:Ax)?\b', import_scope['uncomment'](raw.decode()), re.M), module
    source_imports = import_scope['imports'](raw.decode())
    for dependency in source_imports:
        if dependency.startswith('TranscendentalNakamaye.'):
            visit(dependency, 'whole_original_import_dependency')
    capture = 'raw-source/' + Path(path).name
    draft = 'draft-source/' + Path(destination_path).name
    output = (header + scope['relocate'](raw.decode())).encode()
    save(capture, raw)
    save(draft, output)
    modules.append({'source_module': module, 'source_path': path, 'source_sha256': sha(raw),
                    'raw_capture': capture, 'source_lines': len(raw.decode().splitlines()),
                    'destination_module': destination, 'destination_path': destination_path,
                    'destination_sha256': sha(output), 'draft_capture': draft,
                    'source_imports': source_imports, 'reason': reason,
                    'own_native_producer': own,
                    'within_original_9root_import_closure': module in allowed,
                    'additional_pure_support_imports': [],
                    'administrative_elaboration_contexts': []})

for row in roots:
    visit(row['module'], 'requested_producer_12_through_20')
for name in ['HironakaActualZeroSectionBlowupComparison', 'HironakaActualZeroSectionConstructedBlowup']:
    visit('TranscendentalNakamaye.Pending.' + name, 'whole_original_blueprint_attachment_closure')
assert len(modules) == 14
for row in roots:
    actual = next(module for module in modules if module['source_module'] == row['module'])
    assert actual['source_sha256'] == row['source_sha256']

bp_paths = subprocess.check_output(['git', '-C', str(R), 'ls-tree', '-r', '--name-only', REV, '--', 'TranscendentalNakamaye/blueprint/src'], text=True).splitlines()
bp_paths = [path for path in bp_paths if path.endswith('.tex')]
# One ordinary Git batch read; this is source capture, not Lean compilation.
request = ''.join(REV + ':' + path + '\n' for path in bp_paths).encode()
raw_batch = subprocess.check_output(['git', '-C', str(R), 'cat-file', '--batch'], input=request)
native_bps = {}
offset = 0
for path in bp_paths:
    newline = raw_batch.index(b'\n', offset)
    fields = raw_batch[offset:newline].split()
    assert fields[1] == b'blob'
    size = int(fields[2])
    begin = newline + 1
    raw = raw_batch[begin:begin + size]
    assert raw_batch[begin + size:begin + size + 1] == b'\n'
    offset = begin + size + 1
    native_bps[path] = raw
assert offset == len(raw_batch)
bps = []
for path, raw in native_bps.items():
    text = raw.decode()
    bindings = [name.strip() for group in re.findall(r'\\lean\{([^}]+)\}', text) for name in group.split(',') if name.strip()]
    if not any(any(name.startswith(row['source_module'] + '.') for name in bindings) for row in modules):
        continue
    outside = [name for name in bindings if not any(name.startswith(row['source_module'] + '.') for row in modules)]
    assert not outside, ('Incomplete full-BP attachment closure', path, outside)
    destination = 'blueprint/' + Path(path).name
    assert not (D / destination).exists(), ('Existing public BP requires explicit complement', destination)
    capture = 'raw-blueprint/' + Path(path).name
    draft = 'draft-blueprint/' + Path(path).name
    output = names.rename_text_names(text).replace('\\chapter{', '\\section{').encode()
    save(capture, raw)
    save(draft, output)
    bps.append({'source_path': path, 'source_sha256': sha(raw), 'raw_capture': capture,
                'destination_path': destination, 'destination_sha256': sha(output),
                'draft_capture': draft, 'complete_original_proofs': text.count('\\begin{proof}'),
                'bindings': bindings, 'metadata_adjustments': [],
                'inherited_native_ready_markers': text.count('\\leanok'),
                'target_kernel_or_Expr_claim': False})
assert len(bps) == 12
assert sum(row['complete_original_proofs'] for row in bps) == 30
assert sum(len(row['bindings']) for row in bps) == 59

# Resolve the actual currently installed master input closure, then calculate
# all direct new label and dependency differences without altering it.
public_seen = {}
def visit_bp(path):
    path = path.resolve()
    if path in public_seen:
        return
    assert path.is_file(), str(path)
    text = path.read_text()
    public_seen[path] = text
    for name in re.findall(r'\\input\{([^}]+)\}', text):
        child = path.parent / name
        visit_bp(child if child.suffix else child.with_suffix('.tex'))
visit_bp(D / 'blueprint/extensions.tex')
label_sources = collections.defaultdict(list)
for path, text in public_seen.items():
    for label in re.findall(r'\\label\{([^}]+)\}', text):
        label_sources[label].append(str(path.relative_to(D)))
new_label_sources = collections.defaultdict(list)
used = []
for row in bps:
    text = (E / row['draft_capture']).read_text()
    for label in re.findall(r'\\label\{([^}]+)\}', text):
        new_label_sources[label].append(row['destination_path'])
    for group in re.findall(r'\\uses\{([^}]+)\}', text):
        used.extend(name.strip() for name in group.split(',') if name.strip())
collisions = {label: label_sources[label] + paths for label, paths in new_label_sources.items() if label in label_sources or len(paths) != 1}
assert not collisions, collisions
missing_uses = sorted(set(used) - set(label_sources) - set(new_label_sources))
source_label_parents = collections.defaultdict(list)
for path, raw in native_bps.items():
    for label in re.findall(r'\\label\{([^}]+)\}', raw.decode()):
        if label in missing_uses:
            source_label_parents[label].append(path)
assert all(len(source_label_parents[label]) == 1 for label in missing_uses), source_label_parents
external = []
for label in missing_uses:
    path = source_label_parents[label][0]
    capture = 'external-native-parents/' + Path(path).name
    if not (E / capture).exists():
        save(capture, native_bps[path])
    text = native_bps[path].decode()
    source_line = text[:text.index('\\label{' + label + '}')].count('\n') + 1
    external.append({'label': label, 'source_revision': REV, 'source_path': path,
                    'source_parent_sha256': sha(native_bps[path]), 'source_parent_capture': capture,
                    'source_label_line': source_line,
                    'complete_node_capture_and_honest_external_index_pending': True,
                    'no_local_binding_or_ready_claim': True})

old_plan = json.loads((A / 'plan.json').read_text())
first_additive = json.loads((A / 'additive-oldbranch-attachments-20261028/plan.json').read_text())
guards = dict(old_plan['old_file_guards'])
previous_modules = old_plan['source_modules'] + old_plan['support_extracts'] + first_additive['whole_modules']
assert len(previous_modules) == 33
for row in previous_modules:
    source = D / row['destination_path']
    guards[row['destination_path']] = sha(source.read_bytes())
    relative = Path(*row['destination_module'].split('.'))
    for sub in ['lib/lean', 'ir']:
        base = D / '.lake/build' / sub / relative
        for path in base.parent.glob(base.name + '.*'):
            if path.is_file():
                guards[str(path.relative_to(D))] = sha(path.read_bytes())
for row in old_plan['blueprints'] + old_plan['documentation_pointers']:
    guards[row['destination_path']] = sha((D / row['destination_path']).read_bytes())
for path in ['Hironaka.lean', 'blueprint/extensions.tex']:
    guards[path] = sha((D / path).read_bytes())
for sub in ['lib/lean', 'ir']:
    base = D / '.lake/build' / sub / 'Hironaka'
    for path in base.parent.glob(base.name + '.*'):
        if path.is_file():
            guards[str(path.relative_to(D))] = sha(path.read_bytes())
for path, digest in guards.items():
    assert sha((D / path).read_bytes()) == digest, path
save_json('initial-existing-source-BP-artifact-guards.json', guards)
save('native-modules.txt', ''.join(row['source_module'] + '\n' for row in modules).encode())
plan = {
    'status': 'READONLY_PREPARATION_NO_PUBLIC_INSTALL_OR_COMPILER',
    'native_revision': REV, 'native_source_checkout': str(R),
    'first33_publication_base_pending': True,
    'frozen_native_base': closure['base'], 'unmerged_PR244_imports': 0,
    'roots': [row['module'] for row in roots], 'native_root_acceptance': roots,
    'source_modules': modules, 'whole_blueprints': bps,
    'source_module_count': len(modules), 'source_lines': sum(row['source_lines'] for row in modules),
    'own_roots': 9, 'accepted_main_parents': 5,
    'complete_original_blueprint_chapters': 12, 'complete_original_blueprint_proofs': 30,
    'literal_bindings': 59,
    'all_whole_BP_attachments_in_source_cohort': True,
    'stopped_existing_modules': stopped,
    'ordinary_CI_visibility': 'PENDING_ONE_NEW_14MODULE_METADATA_PREFLIGHT_AFTER_FIRST33_PUBLICATION',
    'support_restoration_needs': 'NOT_ASSUMED_NONE; pending actual whole type/value ordinary callee metadata',
    'current_master_input_files': len(public_seen),
    'new_labels': len(new_label_sources), 'new_label_collisions': collisions,
    'uses_observations': len(used), 'missing_uses': missing_uses,
    'external_original_reference_parent_captures': external,
    'guard_file': 'initial-existing-source-BP-artifact-guards.json',
    'guard_paths': len(guards), 'original_old_guard_paths': len(old_plan['old_file_guards']),
    'guard_refresh_after_first33_commit_required': True,
    'frozen_tool_inputs': {str(path.relative_to(D)): sha(path.read_bytes()) for path in [mapping_path, A / 'frozen-tools/verify_incremental_source.py', A / 'frozen-tools/CanonicalStandaloneAllScopedOwnersV3.lean', A / 'frozen-tools/compare_full_expr_dag.py']},
    'no_existing_33_source_BP_artifact_mutation': True,
    'no_public_source_root_BP_install': True,
    'compiler_kernel_fullExpr_used': False,
    'old33_kernel_or_Expr_replay': False,
    'merge_authorized': False,
}
save_json('plan.json', plan)
print(json.dumps({key: value for key, value in plan.items() if key not in ['source_modules', 'whole_blueprints', 'native_root_acceptance', 'stopped_existing_modules']}, indent=2))
