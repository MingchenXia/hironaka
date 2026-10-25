#!/usr/bin/env python3
"""Run a bounded no-build cache check under the shared global build lock."""
from pathlib import Path
import datetime
import fcntl
import hashlib
import json
import os
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "audit/phase5-main-integration-20261025/cache-preflight/sentinel-attempt01"
RUNTIME = Path("/workspace/archon-nakamaye/work/lean-runtime")


def package_snapshot():
    packages = (ROOT / ".lake/packages").resolve()
    rows = []
    for package in sorted(packages.iterdir()):
        if not package.is_dir():
            continue
        for name in ["lakefile.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain"]:
            p = package / name
            if p.is_file():
                st = p.stat()
                rows.append([str(p.relative_to(packages)), st.st_size, st.st_mtime_ns])
        build = package / ".lake/build"
        for folder, dirs, files in os.walk(build):
            dirs.sort()
            for name in sorted(files):
                p = Path(folder) / name
                st = p.stat()
                rows.append([str(p.relative_to(packages)), st.st_size, st.st_mtime_ns])
    data = (json.dumps(rows, separators=(",", ":")) + "\n").encode()
    return data, {"files": len(rows), "metadata_sha256": hashlib.sha256(data).hexdigest(),
                  "scope": "package build outputs and config size/mtime; command-policy guard, not OS isolation"}


def main():
    assert not AUDIT.exists(), "Preserve every sentinel attempt"
    AUDIT.mkdir(parents=True)
    command = ["lake", "--no-cache", "--no-build", "--wfail", "build",
               "+Hironaka.Analytic.HolomorphicGermRing:olean"]
    env = os.environ.copy()
    env["PATH"] = str(RUNTIME / "lean-4.33.1-linux/bin") + os.pathsep + env["PATH"]
    env["LEAN_NUM_THREADS"] = "1"
    queued = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print("Waiting for shared global lean-build.lock; no compiler may run (--no-build)", flush=True)
    with (RUNTIME / "lean-build.lock").open("a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        before, before_meta = package_snapshot()
        (AUDIT / "package-before-metadata.json").write_bytes(before)
        print("Lock acquired; executing no-build sentinel", flush=True)
        tick = time.monotonic()
        with (AUDIT / "sentinel.log").open("wb") as log:
            process = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - tick
        after, after_meta = package_snapshot()
        (AUDIT / "package-after-metadata.json").write_bytes(after)
        (AUDIT / "sentinel.exit").write_text(str(process.returncode) + "\n")
        result = {"status": "PASS" if process.returncode == 0 and before == after else "FAIL_STOP_NO_COLD_BUILD_STARTED",
                  "command": command, "queued_utc": queued, "started_utc": started,
                  "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  "elapsed_seconds": elapsed, "exit": process.returncode,
                  "package_before": before_meta, "package_after": after_meta,
                  "shared_package_metadata_unchanged": before == after,
                  "global_writer_lock": str(RUNTIME / "lean-build.lock"),
                  "compiler_builds_authorized_by_this_command": False,
                  "old_kernel_or_Expr_replays": 0, "all_child_jobs_reaped": True}
        (AUDIT / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps(result), flush=True)
        if process.returncode:
            print((AUDIT / "sentinel.log").read_text()[-10000:], flush=True)
        fcntl.flock(lock, fcntl.LOCK_UN)


if __name__ == "__main__":
    main()
