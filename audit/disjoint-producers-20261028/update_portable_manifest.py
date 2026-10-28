"""Hash the published source/evidence scope without Git, Lean, or builds."""
from pathlib import Path
import hashlib
import json

A = Path(__file__).resolve().parent
S = A.parents[1]
E = S / 'audit/additive-producers12-20-20261028'
output = A / 'publication-evidence-manifest.json'
v = json.loads((A / 'publication-verification.json').read_text())
assert v['status'] == 'PASS_SOURCE_FAITHFUL_COMPOSITE49_PUBLICATION'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
paths = {S / path for path in v['publication_paths']}
paths.add(S / 'README.md')
excluded = []
for directory in [A, E]:
    for path in directory.rglob('*'):
        if not path.is_file():
            continue
        relative = path.relative_to(S)
        if path == output:
            continue
        if '.lake' in relative.parts or '__pycache__' in relative.parts or path.suffix == '.pyc':
            excluded.append(str(relative))
            continue
        if path.suffix in {'.olean', '.ilean', '.o', '.so', '.a'}:
            excluded.append(str(relative))
            continue
        assert not path.is_symlink(), relative
        paths.add(path)
for path in paths:
    assert path.is_file(), str(path)
files = {str(path.relative_to(S)): sha(path) for path in sorted(paths)}
assert len(v['source_modules']) == 49
assert all(row['source_path'] in files for row in v['source_modules'])
assert all(row['path'] in files for row in v['whole_blueprint_pins'])
assert {'Hironaka.lean', 'blueprint/extensions.tex', 'STATUS.md', 'docs/API.md', 'README.md'} <= set(files)
manifest = {
    'status': 'CURRENT49_PORTABLE_SOURCE_AND_EVIDENCE_MANIFEST',
    'files': files,
    'audit_roots': [str(A.relative_to(S)), str(E.relative_to(S))],
    'source_modules': 49,
    'excluded_private_or_cache_paths': sorted(excluded),
    'omitted_gitignored_paths': [],
    'exclusion_policy': 'Private compiled captures, any .lake or __pycache__ path, .pyc and compiled binary artifacts are excluded directly. No Git command is used.',
    'compiled_artifact_captures': 'Local compiled binaries are not published; complete expression captures, original source, hashes and gate receipts are published. The optional --artifacts verifier checks current local caches.',
    'manifest_self_hash_excluded': True,
}
output.write_text(json.dumps(manifest, indent=2) + '\n')
print('PORTABLE_MANIFEST', len(files), 'files;', len(excluded), 'private/cache paths excluded')
