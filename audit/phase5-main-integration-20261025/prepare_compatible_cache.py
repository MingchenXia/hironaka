#!/usr/bin/env python3
"""Copy compatible standalone artifacts into this worktree's private cache.

This is a physical copy, never a hardlink, output symlink, namespace port,
trace rewrite or freshness claim. Lake's subsequent --no-build sentinel decides
whether the original traces remain usable under the newer main configuration.
"""
from pathlib import Path
import hashlib
import json
import shutil

ROOT = Path(__file__).resolve().parents[2]
OLD = Path("/workspace/hironaka")
AUDIT = ROOT / "audit/phase5-main-integration-20261025/cache-preflight"


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    assert not (ROOT / ".lake").exists(), "Never overwrite a prepared cache"
    AUDIT.mkdir(parents=True, exist_ok=True)
    src = OLD / ".lake/build/lib/lean"
    copied, modules, skipped = [], [], []
    source_pairs = []
    for olean in sorted(src.rglob("*.olean")):
        relative = olean.relative_to(src)
        source = relative.with_suffix(".lean")
        if source.as_posix() == "CheckAxioms.lean":
            source = Path("scripts/CheckAxioms.lean")
        old_source, new_source = OLD / source, ROOT / source
        if not old_source.is_file() or not new_source.is_file():
            skipped.append({"module": str(relative), "reason": "source absent / not in actual new source scope"})
            continue
        if old_source.read_bytes() != new_source.read_bytes():
            skipped.append({"module": str(relative), "reason": "source changed; rebuild genuinely required"})
            continue
        modules.append(relative.with_suffix("").as_posix().replace("/", "."))
        source_pairs.append({"path": str(source), "sha256": digest(old_source)})
        artifacts = [olean, olean.with_suffix(".ilean"), olean.with_suffix(".trace"),
                     Path(str(olean) + ".hash"), Path(str(olean.with_suffix(".ilean")) + ".hash")]
        c = OLD / ".lake/build/ir" / relative.with_suffix(".c")
        artifacts += [c, Path(str(c) + ".hash")]
        for origin in artifacts:
            assert origin.is_file() and not origin.is_symlink(), origin
            target = ROOT / origin.relative_to(OLD)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(origin, target)
            assert origin.stat().st_ino != target.stat().st_ino
            original_hash = digest(origin)
            assert digest(target) == original_hash
            copied.append({"path": str(target.relative_to(ROOT)), "bytes": target.stat().st_size,
                           "sha256": original_hash})
    assert len(modules) == 1558
    assert not list((ROOT / ".lake/build").rglob("*.setup.json"))
    packages = (OLD / ".lake/packages").resolve()
    assert packages.is_dir()
    (ROOT / ".lake/packages").symlink_to(packages, target_is_directory=True)
    result = {"status": "PHYSICAL_CACHE_COPY_COMPLETE_FRESHNESS_UNTESTED",
              "source": str(OLD), "target": str(ROOT), "compatible_source_modules": len(modules),
              "modules": modules, "source_guards": source_pairs,
              "copied_artifacts": copied, "copied_bytes": sum(x["bytes"] for x in copied),
              "skipped": skipped, "setup_json_copied": 0,
              "hardlinks_or_output_symlinks": 0,
              "package_consumer_symlink": str(packages),
              "package_readonly_enforcement": "command policy and snapshots; NOT an OS read-only mount",
              "freshness_status": "PENDING_UNCHANGED_NO_BUILD_SENTINEL"}
    (AUDIT / "cache-copy.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k:result[k] for k in ["status", "compatible_source_modules", "copied_bytes", "skipped"]}))


if __name__ == "__main__":
    main()
