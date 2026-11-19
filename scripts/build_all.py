#!/usr/bin/env python3
"""Every-physical-module build/check, bounded batches, finalized setup sidecars.

No source files/options/dependency revisions are changed. Capacity/timeouts
remain hard failures; an incomplete build cannot pass the publication gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / 'cache_tools'))
import rolling_cache as rc

GIB = 1024**3
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')


def code_only(text):
    """Erase nested Lean comments and string literals, retaining line boundaries."""
    output, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair = text[i:i+2]
        char = text[i]
        if depth:
            if pair == '/-': depth += 1; i += 2; continue
            if pair == '-/': depth -= 1; i += 2; continue
            output.append('\n' if char == '\n' else ' '); i += 1; continue
        if string:
            if char == '\\':
                output.extend('\n' if c == '\n' else ' ' for c in text[i:i+2]); i += 2; continue
            if char == '"': string = False
            output.append('\n' if char == '\n' else ' '); i += 1; continue
        if pair == '/-': depth = 1; output.append('  '); i += 2; continue
        if pair == '--':
            end = text.find('\n', i)
            if end < 0: break
            output.append('\n'); i = end+1; continue
        if char == '"': string = True; output.append(' '); i += 1; continue
        output.append(char); i += 1
    if depth or string:
        raise ValueError('Unterminated Lean comment/string')
    return ''.join(output)


def inventory(project, with_graph=False):
    paths = [project / 'Hironaka.lean', *sorted((project / 'Hironaka').rglob('*.lean'))]
    modules = {}
    for path in paths:
        if not path.is_file() or path.is_symlink():
            raise ValueError(f'Missing or linked source: {path}')
        name = '.'.join(path.relative_to(project).with_suffix('').parts)
        if not MODULE.fullmatch(name):
            raise ValueError(f'Unsupported module path: {name}')
        modules[name] = path
    dependencies = {}
    for name, path in modules.items():
        imports = set()
        for line in code_only(path.read_text()).splitlines():
            match = re.match(r'^\s*(?:(?:public|private|meta)\s+)?import\s+(?:all\s+)?(.+?)\s*$', line)
            if not match:
                continue
            for target in match[1].split():
                if not MODULE.fullmatch(target):
                    raise ValueError(f'Unsupported import syntax in {name}: {target}')
                if target == 'Hironaka' or target.startswith('Hironaka.'):
                    if target not in modules:
                        raise ValueError(f'Missing local import {target} from {name}')
                    imports.add(target)
        dependencies[name] = imports
    ordered = []
    # Iterative Kahn sort avoids exceeding Python's recursion limit on long proofs.
    import heapq
    reverse = {name: [] for name in modules}
    degree = {name: len(ds) for name, ds in dependencies.items()}
    ready = [name for name, count in degree.items() if not count]
    heapq.heapify(ready)
    for name, ds in dependencies.items():
        for dependency in ds: reverse[dependency].append(name)
    while ready:
        name = heapq.heappop(ready); ordered.append(name)
        for dependent in reverse[name]:
            degree[dependent] -= 1
            if degree[dependent] == 0: heapq.heappush(ready, dependent)
    if len(ordered) != len(modules): raise ValueError('Local import cycle')
    result = (ordered, {name: hashlib.sha256(modules[name].read_bytes()).hexdigest() for name in ordered})
    return (*result, dependencies) if with_graph else result


def check_source(project, expected):
    if not re.fullmatch('[0-9a-f]{40}', expected):
        raise ValueError('Exact lowercase source SHA required')
    actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=project, text=True).strip()
    dirty = subprocess.check_output(['git', 'status', '--porcelain'], cwd=project, text=True)
    if actual != expected or dirty: raise ValueError('Source checkout is not the exact clean input')
    manifest = json.loads((project / 'lake-manifest.json').read_text())
    for dependency in manifest['packages']:
        if (dependency['type'] != 'git' or not re.fullmatch('[0-9a-f]{40}', dependency['rev'])
                or not dependency['url'].startswith('https://github.com/')):
            raise ValueError('Only exact public HTTPS GitHub dependency revisions supported')


def require_space(path, gib):
    free = shutil.disk_usage(path).free
    if free < gib * GIB:
        raise RuntimeError(f'Insufficient runner disk: measured {free} bytes, need {gib} GiB. Select a larger runner.')
    return free


class Commands:
    def __init__(self, project, state, deadline):
        self.project, self.state, self.deadline, self.count = project, state, deadline, 0

    def run(self, args, label, env=None):
        remaining = self.deadline-time.monotonic()
        if remaining <= 0: raise TimeoutError('Runner build/check budget exhausted; cache remains incomplete')
        self.count += 1
        log = self.state / 'logs' / f'{self.count:05}-{label}.log'
        print(f'{label}: {args[:5]} ({remaining:.0f}s remaining)', flush=True)
        # Logs are streamed to disk, never captured unbounded in memory/console.
        with log.open('xb') as output:
            process = subprocess.Popen(args, cwd=self.project, env=env, stdout=output,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                while process.poll() is None:
                    if time.monotonic() >= self.deadline:
                        raise TimeoutError('Runner build/check budget exhausted; cache remains incomplete')
                    if log.stat().st_size > 64*1024**2:
                        raise RuntimeError('Single build log exceeded64MiB; stopped before filling runner disk')
                    require_space(self.project, 2)
                    time.sleep(.2)
                code = process.returncode
            except BaseException:
                try: os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError: pass
                process.wait(); raise
        if code:
            with log.open('rb') as stream:
                stream.seek(max(0, log.stat().st_size-12000))
                print(stream.read().decode(errors='replace'), flush=True)
            raise RuntimeError(f'{label} failed (exit {code}); full log: {log}')


def build(project, state, budget_minutes=315, batch_size=32):
    if state.exists(): raise ValueError('Fresh evidence directory required')
    state.mkdir(parents=True)
    (state / 'logs').mkdir()
    receipt = {'status': 'incomplete', 'scope': 'every physical Hironaka .lean module plus Hironaka.lean',
               'supplemental_batches': [], 'covered_modules': []}
    rc.atomic_json(state / 'build-receipt.json', receipt)
    deadline = time.monotonic() + budget_minutes*60
    commands = Commands(project, state, deadline)
    try:
        expected = os.environ['SOURCE_REF']
        check_source(project, expected)
        lean = Path(shutil.which('lean') or '').resolve()
        if not lean.is_file(): raise ValueError('Exact Lean executable missing from PATH')
        ordered, source_hashes, graph = inventory(project, with_graph=True)
        rc.atomic_json(state / 'module-inventory.json', {'modules': ordered, 'source_sha256': source_hashes})
        receipt['source_commit'] = expected
        receipt['physical_module_count'] = len(ordered)
        require_space(project, 24)
        # Lake materializes only the manifest's pinned dependencies. No lake update.
        commands.run(['lake', 'exe', 'cache', 'get'], 'mathlib-cache')
        # Exact pinned Mathlib API: downloaded compressed ltar files are no
        # longer needed after successful verified unpack. Built products stay.
        commands.run(['lake', 'exe', 'cache', 'clean!'], 'mathlib-download-clean')
        check_source(project, expected)
        identity = rc.merger.identity(project, lean)
        rc.atomic_json(state / 'identity.json', identity)
        # Some unused git dependencies may have no build product; cache roots
        # are still exact ignored directories, never links or source changes.
        for root in identity['roots']:
            destination = project / root
            if not destination.resolve().is_relative_to(project): raise ValueError('Build root escape')
            if any(p.is_symlink() for p in [destination, *destination.parents] if p != project.parent):
                raise ValueError('Linked build root')
            destination.mkdir(parents=True, exist_ok=True)
        # Match the source's existing ordinary umbrella CI build first. These
        # oleans also build its transitive Hironaka import closure.
        commands.run(['lake', 'build'], 'default-build')
        receipt['default_build'] = 'passed'
        def olean(name):
            return project / '.lake/build/lib/lean' / (name.replace('.', '/')+'.olean')
        closure, pending = set(), ['Hironaka']
        while pending:
            current = pending.pop()
            if current in closure: continue
            closure.add(current); pending.extend(graph[current])
        supplemental = [name for name in ordered if name not in closure]
        absent = [name for name in ordered if not olean(name).is_file()]
        if any(name in closure for name in absent):
            raise ValueError('Default build succeeded without its complete umbrella import closure')
        receipt.update(umbrella_closure_count=len(closure), supplemental_source_count=len(supplemental),
                       supplemental_missing_count=len(absent))
        # Ask Lake to validate supplemental outputs even after restoring a warm build.
        for start in range(0, len(supplemental), batch_size):
            batch = supplemental[start:start+batch_size]
            require_space(project, 6)
            commands.run(['lake', 'build', *['+'+m+':olean' for m in batch]], f'build-{start:05}')
            for name in batch:
                if not olean(name).is_file():
                    raise ValueError(f'Lake succeeded without expected olean: {name}')
            receipt['supplemental_batches'].append(batch)
            rc.atomic_json(state / 'build-receipt.json', receipt)
        coverage = {name: {'path': str(olean(name).relative_to(project)), 'bytes': olean(name).stat().st_size}
                    for name in ordered if olean(name).is_file() and not olean(name).is_symlink()}
        if set(coverage) != set(ordered): raise ValueError('Not every physical source has a compiled olean')
        receipt['covered_modules'] = ordered
        rc.atomic_json(state / 'olean-coverage.json', coverage)
        final_order, final_hashes = inventory(project)
        if final_order != ordered or final_hashes != source_hashes:
            raise ValueError('Source changed while building')
        if rc.merger.identity(project, lean) != identity: raise ValueError('Source/dependency/toolchain identity changed')
        receipt.update(status='complete', checks='every physical module compiled',
                       lean=str(lean), elapsed_seconds=budget_minutes*60-(deadline-time.monotonic()),
                       final_free_bytes=require_space(project, 4))
        rc.atomic_json(state / 'build-receipt.json', receipt)
        return receipt
    except BaseException as error:
        receipt['failure_type'] = type(error).__name__
        receipt['failure'] = str(error)[:2000]
        rc.atomic_json(state / 'build-receipt.json', receipt)
        raise


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', type=Path)
    parser.add_argument('state', type=Path)
    parser.add_argument('--budget-minutes', type=int, default=315)
    parser.add_argument('--batch-size', type=int, default=32)
    args = parser.parse_args()
    if not 1 <= args.batch_size <= 32 or not 1 <= args.budget_minutes <= 330:
        parser.error('Batch size1..32 and budget1..330 minutes required')
    print(json.dumps(build(args.project.resolve(), args.state.resolve(), args.budget_minutes, args.batch_size), indent=2))
