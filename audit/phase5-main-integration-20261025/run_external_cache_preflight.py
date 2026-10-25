#!/usr/bin/env python3
"""Check every external source import with Lake --no-build; fail before cold work."""
from pathlib import Path
import datetime
import fcntl
import importlib.util
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "audit/phase5-main-integration-20261025"
RUNTIME = Path("/workspace/archon-nakamaye/work/lean-runtime")


def main():
    out = AUDIT / "cache-preflight/external-cache-only"
    assert not out.exists()
    out.mkdir()
    parents = [ROOT / "Hironaka.lean", *(ROOT / "Hironaka").rglob("*.lean"),
               *(ROOT / "vendor/DeJongAlterations").rglob("*.lean")]
    external = set()
    for p in parents:
        if ".lake" in p.parts:
            continue
        for line in p.read_text().splitlines():
            m = re.match(r"\s*(?:public\s+)?import\s+(.+)", line.split("--", 1)[0])
            if m:
                external.update(n for n in m[1].split() if not n.startswith(("Hironaka", "DeJongAlterations")))
    packages = (ROOT / ".lake/packages").resolve()
    libdirs = [p / ".lake/build/lib/lean" for p in packages.iterdir() if p.is_dir()]
    builtin = RUNTIME / "lean-4.33.1-linux/lib/lean"
    target, toolchain = [], []
    for name in sorted(external):
        relative = Path(name.replace(".", "/") + ".olean")
        if any((p / relative).is_file() for p in libdirs):
            target.append(name)
        else:
            assert (builtin / relative).is_file(), name
            toolchain.append(name)
    command = ["lake", "--no-cache", "--no-build", "build", *("+" + n + ":olean" for n in target)]
    spec = importlib.util.spec_from_file_location("sentinel_tools", AUDIT / "run_no_build_sentinel.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    env = os.environ.copy()
    env["PATH"] = str(RUNTIME / "lean-4.33.1-linux/bin") + os.pathsep + env["PATH"]
    env["LEAN_NUM_THREADS"] = "1"
    print(f"Cache-only external preflight queued: {len(target)} shared targets, {len(toolchain)} toolchain imports", flush=True)
    with (RUNTIME / "lean-build.lock").open("a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        before, bm = mod.package_snapshot()
        start = datetime.datetime.now(datetime.timezone.utc).isoformat()
        with (out / "preflight.log").open("wb") as log:
            process = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
        after, am = mod.package_snapshot()
        result = {"status": "PASS" if process.returncode == 0 and before == after else "FAIL_STOP",
                  "command": command, "started_utc": start,
                  "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  "exit": process.returncode, "external_shared_targets": target,
                  "toolchain_imports": toolchain, "shared_package_metadata_unchanged": before == after,
                  "package_before": bm, "package_after": am,
                  "compiler_builds_permitted": False, "all_child_jobs_reaped": True}
        (out / "preflight.exit").write_text(str(process.returncode) + "\n")
        (out / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps({k: result[k] for k in ["status", "exit", "shared_package_metadata_unchanged"]}), flush=True)
        print((out / "preflight.log").read_text()[-5000:], flush=True)


if __name__ == "__main__":
    main()
