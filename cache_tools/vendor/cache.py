#!/usr/bin/env python3
"""Publishable, chunked copy of exactly the pinned Lake build directories."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import platform
import re
import subprocess
import tarfile
import tempfile


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def run(directory, *command):
    return subprocess.check_output(command, cwd=directory, text=True).strip()


def identity(project, lean):
    manifest = project / "lake-manifest.json"
    pinned = json.loads(manifest.read_text())
    packages = PurePosixPath(pinned["packagesDir"])
    if packages.is_absolute() or ".." in packages.parts:
        raise ValueError("packagesDir must be relative to the project")
    roots = [".lake/build"]
    revisions = {}
    for package in pinned["packages"]:
        name, rev = package["name"], package["rev"]
        if package["type"] != "git" or not re.fullmatch(r"[\w.-]+", name) or name in {".", ".."}:
            raise ValueError(f"Unsupported dependency {name}")
        repo = project / packages / name
        if run(repo, "git", "rev-parse", "HEAD") != rev:
            raise ValueError(f"Wrong revision of {name}")
        if run(repo, "git", "status", "--porcelain"):
            raise ValueError(f"Dirty dependency {name}")
        subdir = PurePosixPath(package.get("subDir") or ".")
        if subdir.is_absolute() or ".." in subdir.parts:
            raise ValueError(f"Invalid subDir for {name}")
        roots.append(str(packages / name / subdir / ".lake/build"))
        revisions[name] = rev
    if run(project, "git", "status", "--porcelain"):
        raise ValueError("Dirty source checkout")
    lake = lean.with_name("lake")
    sysroot = Path(run(project, str(lean), "--print-prefix"))
    return {
        "source_commit": run(project, "git", "rev-parse", "HEAD"),
        "source_tree": run(project, "git", "rev-parse", "HEAD^{tree}"),
        "manifest_sha256": digest(manifest),
        "toolchain_sha256": digest(project / "lean-toolchain"),
        "lean_version": run(project, str(lean), "--version"),
        "lean_sha256": digest(lean),
        "lake_sha256": digest(lake),
        "lean_core_sha256": digest(sysroot / "lib/lean/Init.olean"),
        "platform": [platform.system(), platform.machine(), *platform.libc_ver()],
        "dependencies": revisions,
        "roots": roots,
    }


def pack(project, lean, output, chunk_bytes):
    meta = identity(project, lean)
    for root in meta["roots"]:
        if not (project / root).is_dir() or (project / root).is_symlink():
            raise ValueError(f"Missing or linked build root {root}")
    output.mkdir()
    chunks = []
    with subprocess.Popen(["tar", "-cf", "-", "--", *meta["roots"]],
                          cwd=project, stdout=subprocess.PIPE) as tar:
        with subprocess.Popen(["zstd", "-q", "-T0", "-c"],
                              stdin=tar.stdout, stdout=subprocess.PIPE) as encode:
            tar.stdout.close()
            while first := encode.stdout.read(min(chunk_bytes, 1024 * 1024)):
                name = f"cache-{len(chunks):06}.tar.zst.part"
                size, checksum = 0, hashlib.sha256()
                with (output / name).open("xb") as out:
                    piece = first
                    while piece:
                        out.write(piece)
                        checksum.update(piece)
                        size += len(piece)
                        if size == chunk_bytes:
                            break
                        piece = encode.stdout.read(min(chunk_bytes - size, 1024 * 1024))
                chunks.append({"name": name, "bytes": size, "sha256": checksum.hexdigest()})
            if encode.wait() or tar.wait():
                raise RuntimeError("Cache compression failed")
    if not chunks:
        raise RuntimeError("Empty cache")
    (output / "cache.json").write_text(json.dumps(
        {"version": 1, "identity": meta, "chunks": chunks}, indent=2, sort_keys=True) + "\n")


def verify(cache):
    data = json.loads((cache / "cache.json").read_text())
    if data["version"] != 1 or not data["chunks"]:
        raise ValueError("Unsupported or empty cache")
    for i, item in enumerate(data["chunks"]):
        name = f"cache-{i:06}.tar.zst.part"
        path = cache / name
        if item["name"] != name or path.stat().st_size != item["bytes"] or digest(path) != item["sha256"]:
            raise ValueError(f"Incorrect chunk {name}")
    return data


def restore(project, lean, cache):
    data = verify(cache)
    meta = identity(project, lean)
    if meta != data["identity"]:
        raise ValueError("Cache identity does not match this checkout and toolchain")
    roots = [Path(root) for root in meta["roots"]]
    for root in roots:
        dest = project / root
        if dest.exists() or dest.is_symlink() or not dest.resolve().is_relative_to(project):
            raise ValueError(f"Expected an absent build directory inside the checkout: {root}")
    seen = set()

    def safe(member, destination):
        path = PurePosixPath(member.name)
        if path.is_absolute() or ".." in path.parts or not any(
            path.is_relative_to(root) for root in roots
        ):
            raise ValueError(f"Unexpected archive path {member.name}")
        if not (member.isdir() or member.isfile()):
            raise ValueError(f"Unexpected archive entry type {member.name}")
        if path in roots and member.isdir():
            seen.add(path)
        return tarfile.data_filter(member, destination)

    # Concatenate into zstd without creating a second compressed copy on disk.
    reader = subprocess.Popen(["cat", *(str(cache / ch["name"]) for ch in data["chunks"])],
                              stdout=subprocess.PIPE)
    try:
        with tempfile.TemporaryDirectory(dir=project) as temp:
            with subprocess.Popen(["zstd", "-q", "-d", "-c"], stdin=reader.stdout,
                                  stdout=subprocess.PIPE) as decode:
                reader.stdout.close()
                with tarfile.open(fileobj=decode.stdout, mode="r|") as archive:
                    archive.extractall(temp, filter=safe)
                # Consume end padding and let zstd verify the complete frame.
                while decode.stdout.read(1024 * 1024):
                    pass
                if decode.wait() or reader.wait():
                    raise RuntimeError("Cache decompression failed")
            if seen != set(roots):
                raise ValueError("Cache is missing build roots")
            for root in roots:
                (project / root).parent.mkdir(parents=True, exist_ok=True)
                os.rename(Path(temp) / root, project / root)
    finally:
        if reader.poll() is None:
            reader.terminate()
        reader.wait()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("pack", "verify", "restore"))
    parser.add_argument("cache", type=Path)
    parser.add_argument("--project", type=Path, default=Path.cwd())
    parser.add_argument("--lean", type=Path)
    parser.add_argument("--chunk-bytes", type=int, default=95 * 1024 * 1024)
    args = parser.parse_args()
    if args.action == "verify":
        verify(args.cache)
    elif args.lean is None or not 0 < args.chunk_bytes <= 95 * 1024 * 1024:
        parser.error("pack/restore require the exact --lean executable and a valid chunk size")
    elif args.action == "pack":
        pack(args.project.resolve(), args.lean.resolve(), args.cache.resolve(), args.chunk_bytes)
    else:
        restore(args.project.resolve(), args.lean.resolve(), args.cache.resolve())


if __name__ == "__main__":
    main()
