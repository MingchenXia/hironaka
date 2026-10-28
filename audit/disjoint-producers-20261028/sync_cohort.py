#!/usr/bin/env python3
"""BP-first, whole-source export from a fixed ordinary Git revision.

Only this new audit and its explicitly listed NEW public files may be written.
Existing root/master are append-only. Frozen rename/relocate code is read from
the immutable standalone base, including when old audit files are sparse.
"""
from pathlib import Path
import argparse, ast, hashlib, importlib.util, json, re, subprocess, sys
sys.dont_write_bytecode = True
A = Path(__file__).resolve().parent
D = A.parents[1]
BASE = '1dcf29586578031c66fa9cd7061b8004f3b807dd'
sha = lambda b: hashlib.sha256(b).hexdigest()
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--source-root', type=Path, required=True)
p.add_argument('--revision', required=True)
p.add_argument('mode', choices=['prepare', 'install', 'check'])
args = p.parse_args()
assert re.fullmatch('[0-9a-f]{40}', args.revision)
ngit = ['git', '-C', str(args.source_root)]
pgit = ['git', '-C', str(D)]
def gitread(git, revision, path):
    return subprocess.check_output(git + ['show', revision + ':' + path])
assert subprocess.check_output(ngit + ['rev-parse', args.revision], text=True).strip() == args.revision
assert subprocess.check_output(pgit + ['rev-parse', 'HEAD'], text=True).strip() == BASE
native = lambda path: gitread(ngit, args.revision, path)
base = lambda path: gitread(pgit, BASE, path)
def write_audit(path, data):
    target = A/path
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        assert target.read_bytes() == data, ('Refuse audit overwrite', path)
    else:
        target.write_bytes(data)
def write_json(path, obj):
    write_audit(path, (json.dumps(obj, indent=2) + '\n').encode())

map_path = 'scripts/upstream_namespace_map.py'
assert (D/map_path).read_bytes() == base(map_path)
spec = importlib.util.spec_from_file_location('frozen_namespace_map', D/map_path)
names = importlib.util.module_from_spec(spec)
spec.loader.exec_module(names)
names.set_api_modules([f'TranscendentalNakamaye.Pending.HironakaAPI{s}' for s in ['', '2', '3', '4']])
reference = 'audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py'
frozen = base(reference).decode()
node = next(n for n in ast.parse(frozen).body if isinstance(n, ast.FunctionDef) and n.name == 'relocate')
flat = names.flattened_short()
fq = re.compile(r'(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:' + '|'.join(flat) + r')\.(?=[\w«])')
scope = {'re': re, 'names': names, 'flat': flat, 'fq': fq}
exec(compile(ast.Module(body=[node], type_ignores=[]), reference, 'exec'), scope)
relocate = scope['relocate']
header = '/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n'

def uncomment(text):
    # Delete nested block and line comments, preserving header line boundaries.
    out = []; depth = 0; i = 0
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; i += 2
        elif pair == '--':
            j = text.find('\n', i); i = len(text) if j < 0 else j
        else: out.append(text[i]); i += 1
    assert not depth
    return ''.join(out)

def imports(text):
    result = []
    for line in uncomment(text).splitlines():
        m = re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$', line)
        if m:
            tokens = m.group(1).split()
            assert all(re.fullmatch(r'[\w.]+', t) for t in tokens), line
            result.extend(tokens)
    return result

if args.mode == 'prepare':
    assert not (A/'plan.json').exists(), 'Preserve the frozen plan; use a separate append cohort'
    cohort_path = 'TranscendentalNakamaye/audit/hironaka-disjoint-20261028/cohort.json'
    cohort_raw = native(cohort_path); cohort = json.loads(cohort_raw)
    write_audit('native-acceptance/cohort.json', cohort_raw)
    roots = [r['module'] for r in cohort]
    assert len(roots) == len(set(roots))
    seen = set(); ordered = []; stopped = []
    def visit(module):
        if module in seen: return
        seen.add(module)
        destmod = names.new_mod(module)
        destpath = destmod.replace('.', '/') + '.lean'
        if (D/destpath).exists():
            stopped.append({'source_module': module, 'destination_module': destmod,
                            'destination_path': destpath, 'sha256': sha((D/destpath).read_bytes())})
            return
        path = 'TranscendentalNakamaye/' + module.replace('.', '/') + '.lean'
        raw = native(path); text = raw.decode()
        assert not re.search(r'^\s*axiom\b|\bsorry(?:Ax)?\b', uncomment(text), re.M), module
        imps = imports(text)
        for dependency in imps:
            if dependency.startswith('TranscendentalNakamaye.'): visit(dependency)
        capture = 'raw-source/' + path
        write_audit(capture, raw)
        out = header + relocate(text)
        ordered.append({'source_module': module, 'source_path': path, 'source_sha256': sha(raw),
                        'raw_capture': capture, 'source_imports': imps,
                        'destination_module': destmod, 'destination_path': destpath,
                        'initial_synchronized_destination_sha256': sha(out.encode()),
                        'destination_sha256': sha(out.encode()),
                        'additional_pure_support_imports': [], 'administrative_elaboration_contexts': []})
    for root in roots: visit(root)
    for row in cohort:
        actual = next(r for r in ordered if r['source_module'] == row['module'])
        assert actual['source_sha256'] == row['source_sha256']
        assert sha(native(row['blueprint_path'])) == row['ready_blueprint_sha256']
    paths = subprocess.check_output(ngit + ['ls-tree', '-r', '--name-only', args.revision,
                    'TranscendentalNakamaye/blueprint/src'], text=True).splitlines()
    bps = []
    for path in paths:
        if not path.endswith('.tex'): continue
        raw = native(path); text = raw.decode()
        binds = [b.strip() for group in re.findall(r'\\lean\{([^}]+)\}', text) for b in group.split(',')]
        if not any(any(b.startswith(r['source_module'] + '.') for b in binds) for r in ordered): continue
        destination = 'blueprint/' + Path(path).name
        assert not (D/destination).exists(), ('Existing BP needs explicit source-facing complement plan', destination)
        capture = 'raw-blueprint/' + path
        write_audit(capture, raw)
        out = names.rename_text_names(text).replace('\\chapter{', '\\section{')
        bps.append({'source_path': path, 'source_sha256': sha(raw), 'raw_capture': capture,
                    'destination_path': destination, 'destination_sha256': sha(out.encode()),
                    'proofs': text.count('\\begin{proof}'), 'bindings': binds,
                    'metadata_adjustments': []})
    oldpaths = subprocess.check_output(pgit + ['ls-tree', '-r', '--name-only', BASE], text=True).splitlines()
    guards = {}
    for path in oldpaths:
        if path in ['Hironaka.lean', 'blueprint/extensions.tex']: continue
        if path.startswith(('Hironaka/', 'blueprint/', 'vendor/')) or path in [
                'README.md', 'LICENSE', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', map_path]:
            if (D/path).is_file(): guards[path] = sha((D/path).read_bytes())
    profiles = [map_path, reference,
        'audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean',
        'audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean',
        'audit/local-sharp-curves-20261015/compare_full_expr_dag.py']
    profile_records = {}
    for path in profiles:
        raw = base(path); capture = 'frozen-tools/' + Path(path).name
        write_audit(capture, raw); profile_records[path] = {'sha256': sha(raw), 'capture': capture}
    write_audit('before-Hironaka.lean', (D/'Hironaka.lean').read_bytes())
    write_audit('before-extensions.tex', (D/'blueprint/extensions.tex').read_bytes())
    plan = {'standalone_base': BASE, 'native_revision': args.revision,
            'native_source_checkout': str(args.source_root), 'roots': roots,
            'native_root_acceptance': cohort, 'source_modules': ordered, 'blueprints': bps,
            'stopped_existing_modules': stopped, 'old_file_guards': guards,
            'frozen_tools': profile_records, 'documentation_pointers': [],
            'deferred_prior_modules': ['HironakaOriginalGlobalOffZero', 'HironakaOriginalGlobalProperModification']}
    write_json('plan.json', plan)
    print(json.dumps({'status': 'PREPARED_ONLY', 'whole_modules': len(ordered),
        'whole_blueprints': len(bps), 'written_proofs': sum(r['proofs'] for r in bps),
        'ordinary_native_pin': args.revision, 'no_runtime_gates': True}, indent=2))
    raise SystemExit(0)

plan = json.loads((A/'plan.json').read_text())
assert plan['native_revision'] == args.revision and plan['standalone_base'] == BASE
for path, digest in plan['old_file_guards'].items(): assert sha((D/path).read_bytes()) == digest, path
for path, record in plan['frozen_tools'].items():
    assert sha(base(path)) == record['sha256']
    assert sha((A/record['capture']).read_bytes()) == record['sha256']
def original(row):
    raw = native(row['source_path'])
    assert sha(raw) == row['source_sha256'] and raw == (A/row['raw_capture']).read_bytes()
    return raw.decode()
def install(path, output):
    target = D/path; data = output.encode()
    assert path not in plan['old_file_guards'], ('Refuse old file write', path)
    if target.exists():
        current = target.read_bytes()
        if current != data:
            approvals = plan.get('approved_new_file_before_states', {}).get(path, [])
            allowed = []
            for entry in approvals:
                before = (A/entry['capture']).read_bytes()
                assert sha(before) == entry['sha256']
                allowed.append(before)
            assert args.mode == 'install' and current in allowed, ('Refuse existing file overwrite', path)
            target.write_bytes(data)
    else:
        assert args.mode == 'install', ('Missing synchronized file', path)
        target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
# Whole source-facing statements and proofs are public before any Lean source.
for row in plan['blueprints']:
    out = names.rename_text_names(original(row)).replace('\\chapter{', '\\section{')
    for adjustment in row['metadata_adjustments']:
        assert out.count(adjustment['before']) == 1
        out = out.replace(adjustment['before'], adjustment['after'])
    assert sha(out.encode()) == row['destination_sha256']
    install(row['destination_path'], out)
for row in plan['documentation_pointers']:
    out = (A/row['capture']).read_text(); assert sha(out.encode()) == row['destination_sha256']
    install(row['destination_path'], out)
for row in plan.get('support_extracts', []):
    parent = native(row['source_path'])
    assert sha(parent) == row['source_parent_sha256']
    assert parent == (A/row['source_parent_capture']).read_bytes()
    text = row['original_context_segments'][0]
    for i, chunk in enumerate(row['selected_original_declarations']):
        raw = chunk['original_text']
        assert sha(raw.encode()) == chunk['sha256'] and parent.decode().count(raw) == 1
        lo, hi = chunk['inclusive_lines']
        assert ''.join(parent.decode().splitlines(keepends=True)[lo-1:hi]) == raw
        text += raw + row['original_context_segments'][i+1]
    out = header + 'import ' + row['original_import'] + '\n\n'
    out += 'set_option autoImplicit false\nset_option linter.unusedSectionVars false\n\n' + relocate(text)
    assert sha(out.encode()) == row['draft_sha256'] and out == (A/row['draft_capture']).read_text()
    for extra in row['additional_pure_support_imports']:
        at = re.search(r'^import ', out, re.M).start()
        out = out[:at] + 'import ' + extra + '\n' + out[at:]
    for adjustment in row['administrative_elaboration_contexts']:
        assert out.count(adjustment['before']) == 1
        out = out.replace(adjustment['before'], adjustment['after'])
    assert sha(out.encode()) == row['destination_sha256']
    install(row['destination_path'], out)
for row in plan['source_modules']:
    out = header + relocate(original(row))
    assert sha(out.encode()) == row['initial_synchronized_destination_sha256']
    if row['additional_pure_support_imports']:
        at = re.search(r'^import ', out, re.M).start()
        out = out[:at] + ''.join('import ' + m + '\n' for m in row['additional_pure_support_imports']) + out[at:]
    for adjustment in row['administrative_elaboration_contexts']:
        assert out.count(adjustment['before']) == 1
        out = out.replace(adjustment['before'], adjustment['after'])
    assert sha(out.encode()) == row['destination_sha256']
    install(row['destination_path'], out)
before_root = (A/'before-Hironaka.lean').read_text(); at = before_root.index('/-!')
after_root = before_root[:at] + ''.join('import ' + r['destination_module'] + '\n'
                                    for r in plan['source_modules']) + '\n' + before_root[at:]
before_master = (A/'before-extensions.tex').read_text(); at = before_master.rindex('\\end{document}')
after_master = before_master[:at] + ''.join('\\input{' + Path(r['destination_path']).stem + '}\n'
                 for r in [*plan['blueprints'], *plan['documentation_pointers']]) + before_master[at:]
for path, before, after in [('Hironaka.lean', before_root, after_root),
                            ('blueprint/extensions.tex', before_master, after_master)]:
    allowed = [before, after]
    if path in plan.get('approved_root_master_before_states', {}):
        record = plan['approved_root_master_before_states'][path]
        earlier = (A/record['capture']).read_bytes()
        assert sha(earlier) == record['sha256']
        allowed.append(earlier.decode())
    current = (D/path).read_text(); assert current in allowed, ('Non-append-only change', path)
    if args.mode == 'check': assert current == after
    elif current != after: (D/path).write_text(after)
receipt = {'status': 'PASS_WHOLE_SOURCE_BP_REPLAY', 'mode': args.mode,
    'ordinary_native_revision': args.revision, 'standalone_base': BASE,
    'whole_modules': len(plan['source_modules']), 'whole_blueprints': len(plan['blueprints']),
    'complete_proofs': sum(r['proofs'] for r in plan['blueprints']),
    'new_source_facing_support_proofs': sum(r.get('proofs', 0) for r in plan['documentation_pointers']),
    'complete_original_support_files': len(plan.get('support_extracts', [])),
    'actual_new_physical_module_roster': len(plan['source_modules']) + len(plan.get('support_extracts', [])),
    'old_files_byte_preserved': len(plan['old_file_guards']), 'root_master_append_only': True,
    'proof_or_type_payload_edits': 0, 'plan_sha256': sha((A/'plan.json').read_bytes()),
    'runtime_gates_covered': False}
(A/('source-' + args.mode + '-receipt.json')).write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
