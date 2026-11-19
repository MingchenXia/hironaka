#!/usr/bin/env python3
"""Stream a live Lake build cache plus explicitly recorded missing setup files."""
import argparse
from contextlib import ExitStack
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile
import tempfile

from cache import digest, identity, verify


def rel(name):
    path = PurePosixPath(name)
    if path.is_absolute() or not path.parts or ".." in path.parts:
        raise ValueError(f"Unsafe path {name}")
    return path


def batch(root, prune, manifest):
    mount = rel(root)
    report = json.loads(prune.read_text())
    archive_name = rel(report["archive"])
    if len(archive_name.parts) != 1:
        raise ValueError("A checkpoint archive must be a sibling of its prune report")
    archive = prune.parent / archive_name
    metadata = json.loads(manifest.read_text())
    if digest(archive) != metadata["archive_sha256"]:
        raise ValueError(f"Checkpoint archive digest mismatch: {archive}")
    removed = set(report["removed"])
    for name in metadata["files"]:
        if str(rel(name)) != name or not name.endswith(".setup.json"):
            raise ValueError(f"Invalid setup member {name}")
    if not removed <= metadata["files"].keys():
        raise ValueError("Prune report contains paths missing from its archive manifest")
    return mount, archive, metadata, removed


def copy_live(project, roots, chunk_paths, output):
    seen = set()
    with ExitStack() as stack:
        if chunk_paths:
            source = stack.enter_context(subprocess.Popen(
                ["cat", *chunk_paths], stdout=subprocess.PIPE))
            tar = stack.enter_context(subprocess.Popen(
                ["zstd", "-qdc"], stdin=source.stdout, stdout=subprocess.PIPE))
            source.stdout.close()
        else:
            source = None
            tar = stack.enter_context(subprocess.Popen(
                ["tar", "-cf", "-", "--", *roots], cwd=project, stdout=subprocess.PIPE))
        with tarfile.open(fileobj=tar.stdout, mode="r|") as live:
            for entry in live:
                path = rel(entry.name)
                if (path in seen or not (entry.isfile() or entry.isdir())
                        or not any(path.is_relative_to(root) for root in roots)):
                    raise ValueError(f"Unexpected live member {entry.name}")
                seen.add(path)
                output.addfile(entry, live.extractfile(entry) if entry.isfile() else None)
        while tar.stdout.read(1024 * 1024):
            pass
        if tar.wait() or (source is not None and source.wait()):
            raise RuntimeError("Could not stream the base build")
    if not {rel(root) for root in roots} <= seen:
        raise ValueError("Base archive missing pinned build roots")
    return seen


def copy_missing(checkpoint, owners, index, seen, output):
    mount, archive, metadata, removed = checkpoint
    entries = dict(metadata["files"])
    copied = 0
    with subprocess.Popen(["zstd", "-qdc", str(archive)], stdout=subprocess.PIPE) as decode:
        with tarfile.open(fileobj=decode.stdout, mode="r|") as recorded:
            for entry in recorded:
                path = mount / rel(entry.name)
                expected = entries.pop(entry.name)
                if not entry.isfile() or entry.size != expected["size"]:
                    raise ValueError(f"Setup member metadata mismatch: {entry.name}")
                with recorded.extractfile(entry) as source:
                    data = source.read()
                if hashlib.sha256(data).hexdigest() != expected["sha256"]:
                    raise ValueError(f"Setup member digest mismatch: {entry.name}")
                if entry.name not in removed or path in seen or owners[path] != index:
                    continue
                for parent in reversed(path.parents):
                    if not parent.is_relative_to(mount) or parent in seen:
                        continue
                    directory = tarfile.TarInfo(str(parent))
                    directory.type = tarfile.DIRTYPE
                    directory.mode = 0o755
                    output.addfile(directory)
                    seen.add(parent)
                entry.name = str(path)
                entry.pax_headers.pop("path", None)
                output.addfile(entry, io.BytesIO(data))
                seen.add(path)
                copied += 1
        while decode.stdout.read(1024 * 1024):
            pass
        if decode.wait():
            raise RuntimeError(f"Could not decode {archive}")
    if entries:
        raise ValueError(f"Archive missing setup members: {archive}")
    return copied


def write_chunks(source, directory, limit):
    chunks = []
    while first := source.read(min(limit, 1024 * 1024)):
        name = f"cache-{len(chunks):06}.tar.zst.part"
        checksum, size = hashlib.sha256(), 0
        with (directory / name).open("xb") as file:
            piece = first
            while piece:
                file.write(piece)
                checksum.update(piece)
                size += len(piece)
                if size == limit:
                    break
                piece = source.read(min(limit - size, 1024 * 1024))
        chunks.append({"name": name, "bytes": size, "sha256": checksum.hexdigest()})
    return chunks


def pack(project, lean, output, checkpoints, limit, base_cache):
    meta = identity(project, lean)
    chunk_paths = []
    if base_cache is not None:
        base_cache = base_cache.resolve()
        base = verify(base_cache)
        if base["identity"] != meta:
            raise ValueError("Base cache identity does not match the checkout")
        chunk_paths = [str(base_cache / row["name"]) for row in base["chunks"]]
    valid_mounts = {rel(root) / "ir" for root in meta["roots"]}
    owners = {}
    for index, (mount, _, _, removed) in enumerate(checkpoints):
        if mount not in valid_mounts:
            raise ValueError(f"Setup mount is not a pinned Lake IR root: {mount}")
        for name in removed:
            owners[mount / rel(name)] = index

    if output.exists() or output.is_symlink():
        raise ValueError(f"Output already exists: {output}")
    with tempfile.TemporaryDirectory(dir=output.parent) as work:
        stage = Path(work) / "cache"
        stage.mkdir()
        with subprocess.Popen([sys.executable, __file__, "_tar", "--project", str(project)],
                              stdin=subprocess.PIPE, stdout=subprocess.PIPE) as producer:
            request = json.dumps({
                "roots": meta["roots"],
                "base_chunks": chunk_paths,
                "checkpoints": [
                    [str(mount), str(archive), metadata, sorted(removed)]
                    for mount, archive, metadata, removed in checkpoints
                ],
            }).encode()
            producer.stdin.write(request)
            producer.stdin.close()
            with subprocess.Popen(["zstd", "-q", "-T0", "-c"],
                                  stdin=producer.stdout, stdout=subprocess.PIPE) as compressor:
                producer.stdout.close()
                chunks = write_chunks(compressor.stdout, stage, limit)
                if compressor.wait() or producer.wait():
                    raise RuntimeError("Cache stream failed")
        if not chunks:
            raise RuntimeError("Cache stream was empty")
        (stage / "cache.json").write_text(json.dumps(
            {"version": 1, "identity": meta, "chunks": chunks,
             "setup_checkpoints": [
                 {"mount": str(mount), "archive_sha256": md["archive_sha256"],
                  "removed": sorted(removed)}
                 for mount, _, md, removed in checkpoints
             ]}, indent=2, sort_keys=True) + "\n")
        os.rename(stage, output)


def produce(project):
    request = json.load(sys.stdin)
    checkpoints = [(rel(m), Path(a), md, set(r)) for m, a, md, r in request["checkpoints"]]
    owners = {m / rel(name): i for i, (m, _, _, r) in enumerate(checkpoints) for name in r}
    with tarfile.open(fileobj=sys.stdout.buffer, mode="w|") as output:
        seen = copy_live(project, request["roots"], request["base_chunks"], output)
        copied = sum(copy_missing(b, owners, i, seen, output)
                     for i, b in enumerate(checkpoints))
        if not owners.keys() <= seen:
            raise ValueError("Some recorded setup paths were absent from the merged cache")
    print(f"Added {copied} recorded setup entries; kept {len(owners)-copied} live entries.",
          file=sys.stderr)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("output")
    p.add_argument("--project", type=Path, required=True)
    p.add_argument("--lean", type=Path)
    p.add_argument("--sidecar", nargs=3, action="append", default=[],
                   metavar=("IR_ROOT", "PRUNE_REPORT", "ARCHIVE_MANIFEST"))
    p.add_argument("--base-cache", type=Path, help="merge into a verified existing cache instead of live build directories")
    p.add_argument("--chunk-bytes", type=int, default=95 * 1024 * 1024)
    args = p.parse_args()
    if args.output == "_tar":
        produce(args.project)
        return
    if args.lean is None or not 0 < args.chunk_bytes <= 95 * 1024 * 1024:
        p.error("A pinned --lean and a valid chunk size are required")
    checks = [batch(root, Path(prune).resolve(), Path(manifest).resolve())
              for root, prune, manifest in args.sidecar]
    pack(args.project.resolve(), args.lean.resolve(), Path(args.output).resolve(),
         checks, args.chunk_bytes, args.base_cache)


if __name__ == "__main__":
    main()
