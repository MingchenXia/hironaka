#!/usr/bin/env python3
"""Future workflow entry point. Explicit draft-only writes; never create/publish.

Importing performs no I/O. Tests inject local fake gh clients. This script is
invoked only after every physical build/axiom/kernel check completed.
"""
import json
import os
from pathlib import Path
import shutil
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'cache_tools'))
sys.path.insert(0, str(HERE.parent / 'cache_tools/github_release_adapter'))
import rolling_cache as rc
from github_release_sink import GhClient, GhRunner, GitHubReleaseSink
from build_all import check_source, inventory, require_space

DESTINATION = 'MingchenXia/hironaka'


def publication_gate(project, state):
    receipt = json.loads((state / 'build-receipt.json').read_text())
    modules, hashes = inventory(project)
    prior = json.loads((state / 'module-inventory.json').read_text())
    if (receipt.get('status') != 'complete' or receipt.get('source_axioms') != 'passed'
            or receipt.get('source_kernel') != 'passed' or receipt.get('default_build') != 'passed'
            or receipt.get('source_commit') != os.environ['SOURCE_REF']
            or receipt.get('physical_module_count') != len(modules)
            or prior != {'modules': modules, 'source_sha256': hashes}
            or receipt.get('covered_modules') != modules):
        raise ValueError('Incomplete or mismatched every-physical-module evidence; publication forbidden')
    check_source(project, os.environ['SOURCE_REF'])
    lean = Path(shutil.which('lean') or '').resolve()
    if not lean.is_file() or rc.merger.identity(project, lean) != json.loads((state / 'identity.json').read_text()):
        raise ValueError('Publication identity differs from verified build')
    require_space(project, 2)
    return lean


def publish(project, state, tag, *, client=None):
    if os.environ.get('GITHUB_REPOSITORY') != DESTINATION:
        raise ValueError('Only explicit cache destination is supported')
    lean = publication_gate(project, state)
    if client is None:
        if not os.environ.get('GH_TOKEN'):
            raise ValueError('Own-repository workflow token required')
        client = GhClient(GhRunner(timeout=900), release_id=int(os.environ['CACHE_RELEASE_ID']))
    sink = GitHubReleaseSink(DESTINATION, tag, client=client)
    # Constructor verifies draft + pins numeric ID. Core checks fresh manifest
    # absence and independently reads every uploaded part before final commit.
    sidecars = json.loads((state / 'sidecars.json').read_text())
    result = rc.publish_project(project, lean, sidecars, sink, state / 'spool')
    scratch = state / 'remote-recheck'
    scratch.mkdir()
    manifest = rc.validate_sink(sink, result['manifest_sha256'], scratch)
    verification = {'status': 'complete', 'repo': DESTINATION, 'draft_tag': tag,
                    'source_commit': manifest['identity']['source_commit'],
                    'manifest_sha256': result['manifest_sha256'], 'chunks': len(manifest['chunks']),
                    'members': len(manifest['members']),
                    'verification': 'full independent remote-stream audit; no fresh-runner restore/rebuild claimed'}
    rc.atomic_json(state / 'publication-receipt.json', verification)
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as output:
            output.write(f"Verified draft cache `{tag}` for `{verification['source_commit']}`. "
                         f"Manifest SHA256 `{verification['manifest_sha256']}`. "
                         "Every physical module compiled; both unchanged source CI checks passed. "
                         "Full remote bytes verified; independent fresh-runner restore/rebuild remains a separate check.\n")
    return verification


if __name__ == '__main__':
    print(json.dumps(publish(Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve(), sys.argv[3]), indent=2))
