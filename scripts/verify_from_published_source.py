#!/usr/bin/env python3
"""Read-only export replay from a normal checkout of the published native source.

Requires Git and Python, not Lean, Lake, Horizon or private ledger objects.
No source, blueprint, frozen map or provenance is rewritten. Only verification
receipts are written under --output-dir. Historical source_revision fields stay
unchanged; every actual source blob is read at the explicit public revision.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

PUBLISHED_REVISION = '7d0a4d88308ef45c16f25c2e9991e76c1f6ae4b4'
SUPPORT_PARENTS_SHA256 = 'bc8ef506f7e4f70cfeee9cd961d0d35a25d8d718e9ac47c526c2c19fe7ea7d2b'
sha = lambda raw: hashlib.sha256(raw).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, required=True,
                        help='A standard Git checkout of MingchenXia/archon-nakamaye')
    parser.add_argument('--revision', default=PUBLISHED_REVISION,
                        help='Full published native commit; original source hashes must all match')
    parser.add_argument('--destination-root', type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output-dir', type=Path)
    args = parser.parse_args()
    source = args.source_root.resolve()
    dest = args.destination_root.resolve()
    fixtures = dest / 'audit/local-sharp-curves-20261015'
    output = (args.output_dir or fixtures / 'published-source-replay').resolve()
    if not re.fullmatch('[0-9a-f]{40}', args.revision):
        parser.error('--revision must be a full immutable 40-character commit')
    git = ['git', '-C', str(source)]
    resolved = subprocess.check_output(git + ['rev-parse', args.revision], text=True).strip()
    if resolved != args.revision:
        raise RuntimeError('The supplied published commit did not resolve exactly')
    raw = (fixtures / 'g2-controlled-export-reviewed-support-parent-sources.json').read_bytes()
    if sha(raw) != SUPPORT_PARENTS_SHA256:
        raise RuntimeError('Unreviewed support-parent provenance fingerprint')
    support = json.loads(raw)
    for path, digest in support['whole_provenance_file_sha256'].items():
        if sha((dest / path).read_bytes()) != digest:
            raise RuntimeError('Changed original support provenance: ' + path)
    for module, digest in support['destination_support_file_sha256'].items():
        if sha((dest / (module.replace('.', '/') + '.lean')).read_bytes()) != digest:
            raise RuntimeError('Changed recovered complete support module: ' + module)
    paths = list(support['original_source_parent_sha256'])
    refs = [f'{args.revision}:{path}' for path in paths]
    batch = subprocess.check_output(git + ['cat-file', '--batch'],
                                    input=('\n'.join(refs) + '\n').encode())
    position = 0
    parents = []
    for path in paths:
        end = batch.index(b'\n', position)
        header = batch[position:end].split()
        position = end + 1
        if len(header) != 3 or header[1] != b'blob':
            raise RuntimeError('Missing published support parent: ' + path)
        length = int(header[2])
        body = batch[position:position + length]
        position += length + 1
        expected = support['original_source_parent_sha256'][path]
        if sha(body) != expected:
            raise RuntimeError('Published support-parent SHA mismatch: ' + path)
        parents.append(dict(source_path=path, expected_original_sha256=expected,
                            published_source_sha256=sha(body),
                            actual_source_read_revision=args.revision))
    if position != len(batch):
        raise RuntimeError('Support-parent parser did not consume every byte')
    output.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(HIRONAKA_REVIEW_SOURCE_ROOT=str(source),
               HIRONAKA_REVIEW_DESTINATION_ROOT=str(dest),
               HIRONAKA_REVIEW_AUDIT_ROOT=str(fixtures),
               HIRONAKA_REVIEW_REPORT_ROOT=str(output),
               HIRONAKA_REVIEW_PUBLISHED_SOURCE_REVISION=args.revision,
               HIRONAKA_REVIEW_STANDARD_GIT='1')
    result = subprocess.run([sys.executable, str(fixtures / 'g2-controlled-export-byteguard.py')],
                            env=env, cwd=dest, text=True, capture_output=True)
    (output / 'replay.log').write_text(result.stdout + result.stderr)
    if result.returncode:
        print(result.stdout + result.stderr, file=sys.stderr)
        return result.returncode
    replay = json.loads((output / 'g2-controlled-export-byteguard.json').read_text())
    summary = replay['summary']
    if (summary['status'] != 'passed' or not summary['standard_git_backend']
            or summary['actual_source_read_revision'] != args.revision
            or not summary['original_source_revision_metadata_preserved']
            or summary['unchanged_original_baseline_sources'] != 543
            or len(summary['exact_original_declaration_context_restorations']) != 2):
        raise RuntimeError('Published-source replay did not verify the requested backend/revision')
    receipt = dict(status='PASS_STANDARD_PUBLISHED_GIT_SOURCE_REPLAY',
                   source_checkout=str(source), published_source_revision=args.revision,
                   original_provenance_revision=summary['fixed_source_revision'],
                   original_provenance_metadata_unchanged=True,
                   horizon_private_ledger_or_original_revision_objects_required=False,
                   complete_lean_modules=182, complete_blueprint_chapters=182,
                   original_complete_proofs=summary['all182_original_complete_proofs'],
                   support_modules=16, support_source_parents=len(parents),
                   protected_byte_identical_modules=543,
                   exact_original_declaration_context_restores=2,
                   original_declaration_context_checks=summary['exact_original_declaration_context_restorations'],
                   exact_original_source_and_export_replay=summary['status'],
                   local_declaration_references=summary['all182_local_reference_names'],
                   verified_upstream_only_references=summary['all182_verified_upstream_reference_names'],
                   unresolved_historical_references=summary['all182_unresolved_historical_reference_names'],
                   published_additional_native_modules_outside_original_inventory=summary['published_additional_native_modules_outside_original_inventory'],
                   build_lean_kernel_axiom_or_ast_audit_started=False,
                   support_parent_checks=parents,
                   replay_report_sha256=sha((output / 'g2-controlled-export-byteguard.json').read_bytes()))
    (output / 'published-source-verification.json').write_text(
        json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({key: value for key, value in receipt.items()
                      if key not in ('support_parent_checks', 'original_declaration_context_checks')}, indent=2))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
