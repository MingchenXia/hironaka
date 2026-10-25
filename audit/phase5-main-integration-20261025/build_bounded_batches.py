#!/usr/bin/env python3
"""Build this isolated graph in fair, recorded batches of at most four modules.

Requires an explicit baseline-completion marker supplied after coordination.
Never writes shared package outputs intentionally; the required cache-only
external preflight is a separate gate. Existing receipts are never replaced.
"""
from pathlib import Path
import argparse
import datetime
import fcntl
import hashlib
import json
import os
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "audit/phase5-main-integration-20261025"
RUNTIME = Path("/workspace/archon-nakamaye/work/lean-runtime")
FLOOR = 2 * 1024**3


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def own_setups():
    result = {}
    for root in [ROOT / ".lake/build/ir", ROOT / "vendor/DeJongAlterations/.lake/build/ir"]:
        for p in root.rglob("*.setup.json") if root.exists() else []:
            assert not p.is_symlink()
            st = p.stat()
            result[p] = (st.st_size, st.st_mtime_ns)
    return result


def own_running_compilers():
    found = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit():
            continue
        try:
            argv = (entry / "cmdline").read_bytes().split(b"\0")
        except (FileNotFoundError, PermissionError, ProcessLookupError):
            continue
        if not argv or Path(os.fsdecode(argv[0])).name != "lean" or b"-o" not in argv:
            continue
        if any(os.fsencode(str(ROOT)) in arg for arg in argv):
            found.append(int(entry.name))
    return found


def source_for(module):
    if module == "DeJongAlterations" or module.startswith("DeJongAlterations."):
        return ROOT / "vendor/DeJongAlterations" / (module.replace(".", "/") + ".lean")
    return ROOT / (module.replace(".", "/") + ".lean")


def hironaka_order():
    paths = [ROOT / "Hironaka.lean", *(ROOT / "Hironaka").rglob("*.lean")]
    modules = {p.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."): p for p in paths}
    deps = {}
    for name, p in modules.items():
        ds = set()
        for line in p.read_text().splitlines():
            m = re.match(r"\s*(?:public\s+)?import\s+(.+)", line.split("--", 1)[0])
            if m:
                for n in m[1].split():
                    if n == "Hironaka" or n.startswith("Hironaka."):
                        assert n in modules, (name, n)
                        ds.add(n)
        deps[name] = ds
    order, seen, visiting = [], set(), set()

    def visit(n):
        if n in seen:
            return
        assert n not in visiting, n
        visiting.add(n)
        for d in sorted(deps[n]):
            visit(d)
        visiting.remove(n)
        seen.add(n)
        order.append(n)

    visit("Hironaka")
    assert len(order) == len(modules) == 1560
    return order


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cohort", choices=["vendor", "hironaka"], required=True)
    ap.add_argument("--baseline-complete", type=Path, required=True)
    ap.add_argument("--batch-size", type=int, default=4)
    ap.add_argument("--max-batches", type=int, default=0)
    args = ap.parse_args()
    controller_sha256 = digest(Path(__file__))
    assert 1 <= args.batch_size <= 4
    assert args.baseline_complete.is_file(), "Wait for the native baseline completion signal"
    baseline = json.loads(args.baseline_complete.read_text())
    assert baseline["status"] == "PASS", "A running baseline is not a completion gate"
    preflight = json.loads((AUDIT / "cache-preflight/external-cache-only/verification.json").read_text())
    assert preflight["exit"] == 0 and preflight["shared_package_metadata_unchanged"]
    vendor = json.loads((AUDIT / "cache-preflight/vendor-topological-build-plan.json").read_text())
    order = vendor["topological_order"] if args.cohort == "vendor" else hironaka_order()
    run = AUDIT / "bounded-build" / args.cohort
    run.mkdir(parents=True, exist_ok=True)
    sources = {n: digest(source_for(n)) for n in order}
    configs = [ROOT / p for p in ["lakefile.toml", "lake-manifest.json", "lean-toolchain",
               "vendor/DeJongAlterations/lakefile.toml", "vendor/DeJongAlterations/lake-manifest.json",
               "vendor/DeJongAlterations/lean-toolchain"]]
    config_hashes = {str(p.relative_to(ROOT)): digest(p) for p in configs}
    plan = {"cohort": args.cohort, "order": order, "batch_size": args.batch_size,
            "module_source_hashes": sources, "configs": config_hashes,
            "baseline_complete_marker": str(args.baseline_complete),
            "baseline_marker_sha256": digest(args.baseline_complete), "disk_floor_bytes": FLOOR}
    plan_path = run / "plan.json"
    data = (json.dumps(plan, indent=2) + "\n").encode()
    if plan_path.exists():
        assert plan_path.read_bytes() == data, "Resume the exact same source plan"
    else:
        plan_path.write_bytes(data)
    env = os.environ.copy()
    env["PATH"] = str(RUNTIME / "lean-4.33.1-linux/bin") + os.pathsep + env["PATH"]
    env["LEAN_NUM_THREADS"] = "1"
    ran = 0
    pause = AUDIT / "bounded-build/PAUSE-REQUESTED.json"
    for offset in range(0, len(order), args.batch_size):
        batch = order[offset:offset + args.batch_size]
        directory = run / f"batch-{offset // args.batch_size + 1:04d}"
        if (directory / "verification.json").is_file():
            previous = json.loads((directory / "verification.json").read_text())
            assert previous["exit"] == 0, "Failed attempts require a separately recorded retry"
            continue
        if pause.exists():
            print("PAUSED at clean batch boundary by " + str(pause), flush=True)
            return
        assert not directory.exists(), "Preserve partial or failed attempts"
        directory.mkdir()
        with (RUNTIME / "lean-build.lock").open("a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            if pause.exists():
                directory.rmdir()
                print("PAUSED before new compiler after waiting for lock", flush=True)
                return
            available = shutil.disk_usage(ROOT).free
            if available < FLOOR:
                (directory / "PAUSED-DISK-FLOOR.json").write_text(json.dumps({"free": available, "floor": FLOOR}) + "\n")
                print("PAUSED below2GiB disk floor; no new compiler started", flush=True)
                return
            for p in configs:
                assert digest(p) == config_hashes[str(p.relative_to(ROOT))]
            for n in batch:
                assert digest(source_for(n)) == sources[n]
            before = own_setups()
            command = ["lake", "--no-cache", "build", *("+" + n + ":olean" for n in batch)]
            started = datetime.datetime.now(datetime.timezone.utc).isoformat()
            print(f"START {args.cohort} {offset // args.batch_size + 1} {batch}", flush=True)
            tick = time.monotonic()
            with (directory / "build.log").open("wb") as log:
                process = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
            # subprocess.run has waited and reaped the entire Lake invocation.
            # Lake's completed process owns no running child compiler now.
            elapsed = time.monotonic() - tick
            remaining_compilers = own_running_compilers()
            assert not remaining_compilers, remaining_compilers
            removed = []
            if process.returncode == 0:
                for p, stat in own_setups().items():
                    if before.get(p) == stat:
                        continue
                    assert str(p).startswith(str(ROOT) + "/") and not p.is_symlink()
                    removed.append({"path": str(p.relative_to(ROOT)), "sha256": digest(p), "bytes": p.stat().st_size})
                    p.unlink()
            log_text = (directory / "build.log").read_text()
            result = {"status": "PASS" if process.returncode == 0 else "FAIL_STOP",
                      "command": command, "modules": batch, "exit": process.returncode,
                      "started_utc": started, "elapsed_seconds": elapsed,
                      "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      "warnings_observed": [line for line in log_text.splitlines() if "warning:" in line],
                      "source_config_plan_sha256": digest(plan_path),
                      "controller_sha256": controller_sha256,
                      "new_own_successful_setup_json_removed": removed,
                      "compiler_process_reaped_before_cleanup": True,
                      "free_bytes_after": shutil.disk_usage(ROOT).free,
                      "global_lock_released_between_batches": True}
            (directory / "build.exit").write_text(str(process.returncode) + "\n")
            (directory / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
            print(f"END {args.cohort} {offset // args.batch_size + 1} exit={process.returncode} seconds={elapsed:.2f} free={result['free_bytes_after']}", flush=True)
            fcntl.flock(lock, fcntl.LOCK_UN)
        if process.returncode:
            raise SystemExit(process.returncode)
        if result["free_bytes_after"] < FLOOR:
            return
        ran += 1
        if args.max_batches and ran >= args.max_batches:
            return
        # Yield the lock to queued native mathematical writers.
        time.sleep(0.5)
    assert all(digest(source_for(n)) == sources[n] for n in order)
    (run / "COMPLETE.json").write_text(json.dumps({"status": "PASS", "modules": len(order),
        "source_plan_sha256": digest(plan_path), "new_kernel_or_expression_replays": 0}, indent=2) + "\n")
    print(f"COMPLETE {args.cohort} {len(order)} modules", flush=True)


if __name__ == "__main__":
    main()
