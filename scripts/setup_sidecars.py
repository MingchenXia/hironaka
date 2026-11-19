"""Finalize verified compressed setup-only checkpoints before deleting originals.

Call only while Lake is stopped. Oleans, ileans, traces, C and IR are untouched.
Returned triples implement the unchanged rolling publisher's sidecar contract.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def checkpoint(project, roots, state):
    previous = json.loads((state / 'sidecars.json').read_text()) if (state / 'sidecars.json').exists() else []
    for root in roots:
        ir = project / root / 'ir'
        if not ir.exists():
            continue
        if ir.is_symlink():
            raise ValueError('Linked IR root rejected')
        files = sorted(ir.rglob('*.setup.json'))
        if not files:
            continue
        folder = state / 'sidecars' / f'{len(previous):06}'
        folder.mkdir(parents=True, exist_ok=False)
        metadata = {'files': {}}
        archive = folder / 'setup.tar.zst'
        for path in files:
            if path.is_symlink() or not path.is_file() or any(p.is_symlink() for p in path.parents if p != ir):
                raise ValueError('Linked/nonregular setup rejected')
            metadata['files'][path.relative_to(ir).as_posix()] = {'size': path.stat().st_size, 'sha256': digest(path)}
        with archive.open('xb') as output, subprocess.Popen(
                ['zstd', '-q', '-T1', '-3', '-c'], stdin=subprocess.PIPE, stdout=output) as encode:
            with tarfile.open(fileobj=encode.stdin, mode='w|') as tar:
                for path in files:
                    tar.add(path, arcname=path.relative_to(ir).as_posix(), recursive=False)
            encode.stdin.close()
            if encode.wait():
                raise RuntimeError('Setup checkpoint compression failed; originals retained')
            output.flush(); os.fsync(output.fileno())
        # Independently decode and check EVERY member before any deletion.
        seen = set()
        with subprocess.Popen(['zstd', '-qdc', str(archive)], stdout=subprocess.PIPE) as decode:
            with tarfile.open(fileobj=decode.stdout, mode='r|') as tar:
                for item in tar:
                    if not item.isfile() or item.name in seen or item.name not in metadata['files']:
                        raise ValueError('Unexpected checkpoint member')
                    expected = metadata['files'][item.name]
                    with tar.extractfile(item) as stream:
                        sha = hashlib.file_digest(stream, 'sha256').hexdigest()
                    if item.size != expected['size'] or sha != expected['sha256']:
                        raise ValueError('Setup archive did not preserve exact bytes')
                    seen.add(item.name)
            if decode.wait() or seen != metadata['files'].keys():
                raise ValueError('Incomplete checkpoint')
        metadata['archive_sha256'] = digest(archive)
        md = folder / 'setup.json'
        prune = folder / 'pruned.json'
        md.write_text(json.dumps(metadata, sort_keys=True) + '\n')
        # Finalize report + index BEFORE pruning: a crash retains all candidates.
        prune.write_text(json.dumps({'archive': archive.name, 'removed': sorted(seen)}) + '\n')
        previous.append([str(Path(root) / 'ir'), str(prune), str(md)])
        pending = state / 'sidecars.pending.json'
        pending.write_text(json.dumps(previous, indent=2) + '\n')
        for finalized in [archive, md, prune, pending]:
            with finalized.open('rb') as stream: os.fsync(stream.fileno())
        for directory in [folder, folder.parent, state]:
            fd = os.open(directory, os.O_RDONLY | os.O_DIRECTORY)
            try: os.fsync(fd)
            finally: os.close(fd)
        pending.replace(state / 'sidecars.json')
        fd = os.open(state, os.O_RDONLY | os.O_DIRECTORY)
        try: os.fsync(fd)
        finally: os.close(fd)
        for path in files:
            expected = metadata['files'][path.relative_to(ir).as_posix()]
            if path.stat().st_size != expected['size'] or digest(path) != expected['sha256']:
                raise ValueError('Live setup changed; refusing to delete')
            path.unlink()
    return previous
