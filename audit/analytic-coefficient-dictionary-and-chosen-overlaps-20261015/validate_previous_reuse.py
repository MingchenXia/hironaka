"""Require fresh replay of the entire repaired prerequisite's import cone.

Every reused module must retain its complete source and all kernel parts from
the pinned verified predecessor. Byte equality never exempts a dependent of
the repaired definition from fresh replay.
"""
from pathlib import Path
import hashlib
import json
import subprocess

BASE = '3aa1692af186967f63d4197a34114d6e316aed95'
REPAIR = 'Hironaka.Analytic.GeometricPureDimension'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def module_parts(parts, module):
    prefix = '.lake/build/lib/lean/' + module.replace('.', '/') + '.olean'
    return {key: value for key, value in parts.items()
            if key == prefix or key in (prefix + '.server', prefix + '.private')}


def validate_reuse(here, before):
    root = here.parents[1]
    previous = here.parent / 'local-coefficients-and-curve-overlaps-20261015'
    guard = json.loads((here / 'previous-frozen-kernel-data-reuse.json').read_text())
    old_raw = (previous / 'kernel-artifacts-after.json').read_bytes()
    receipt_raw = (previous / 'incremental-kernel-replay.json').read_bytes()
    for name, raw in [('kernel-artifacts-after.json', old_raw),
                      ('incremental-kernel-replay.json', receipt_raw)]:
        relative = str((previous / name).relative_to(root))
        assert subprocess.check_output(['git', '-C', str(root), 'show', BASE + ':' + relative]) == raw
    assert digest(old_raw) == guard['previous_snapshot_sha256']
    assert digest(receipt_raw) == guard['previous_kernel_receipt_sha256']
    old = json.loads(old_raw)
    receipt = json.loads(receipt_raw)
    assert receipt['status'] == 'PASS_ALL_NEW_MODULES_AND_IMPORT_ROOT_FROZEN_KERNEL_REPLAY'
    assert receipt['total_local_modules'] == old['mathematical_modules_including_root'] == 888
    paths = {source.removesuffix('.lean').replace('/', '.'): source
             for source in before['sources'] if source != 'Hironaka.lean'}
    old_modules = {source.removesuffix('.lean').replace('/', '.')
                   for source in old['sources'] if source != 'Hironaka.lean'}
    assert len(old_modules) == 887 and len(paths) == 968
    dependencies = {}
    for module, source in paths.items():
        raw = (root / source).read_bytes()
        assert digest(raw) == before['sources'][source]
        metadata_path = '.lake/build/lib/lean/' + module.replace('.', '/') + '.ilean'
        metadata_raw = (root / metadata_path).read_bytes()
        assert digest(metadata_raw) == before['compiled_import_metadata_sha256'][metadata_path]
        metadata = json.loads(metadata_raw)
        assert metadata['module'] == module
        direct_imports = [row[0] for row in metadata['directImports']]
        assert direct_imports == before['actual_compiler_direct_imports'][module]
        dependencies[module] = set(direct_imports) & set(paths)
    affected = {REPAIR}
    while True:
        extended = affected | {module for module, deps in dependencies.items() if deps & affected}
        if extended == affected:
            break
        affected = extended
    changed_sources = {module for module in old_modules
                       if before['sources'][paths[module]] != old['sources'][paths[module]]}
    assert changed_sources == {REPAIR}
    new_modules = set(json.loads((here / 'new-module-targets.json').read_text()))
    assert len(new_modules) == 81 and new_modules == set(paths) - old_modules
    mandatory = new_modules | (old_modules & affected)
    reused = []
    additional = []
    for module in sorted(old_modules - affected):
        assert before['sources'][paths[module]] == old['sources'][paths[module]]
        old_parts = module_parts(old['compiled_kernel_data_parts'], module)
        current_parts = module_parts(before['compiled_kernel_data_parts'], module)
        assert old_parts and current_parts
        if current_parts == old_parts:
            reused.append(module)
        else:
            additional.append(module)
    expected = mandatory | set(additional)
    targets = json.loads((here / 'kernel-modules.json').read_text())
    assert len(targets) == len(set(targets)) and set(targets) == expected
    assert set(reused).isdisjoint(expected) and set(reused) | expected == set(paths)
    assert guard['reused_nonroot_modules'] == len(reused)
    assert set(guard['reused_exact_module_inventory']) == set(reused)
    assert set(guard['affected_preceding_modules_fresh_replay']) == old_modules & affected
    assert set(guard['additional_changed_kernel_modules_fresh_replay']) == set(additional)
    assert guard['status'] == 'PASS_PINNED_PREDECESSOR_REUSE_OUTSIDE_ENTIRE_REPAIR_CONE'
    return {'reused_preceding_modules': len(reused),
            'fresh_new_modules': len(new_modules),
            'fresh_affected_preceding_modules': len(old_modules & affected),
            'fresh_additional_changed_kernel_modules': len(additional),
            'fresh_mathematical_modules': len(expected),
            'all_repaired_prerequisite_dependents_replayed': True}


if __name__ == '__main__':
    here = Path(__file__).resolve().parent
    print(json.dumps(validate_reuse(here, json.loads((here / 'kernel-artifacts-before.json').read_text()))))
