"""Replay every local module, recording success only for an unchanged full inventory."""
import datetime
import json
import os
from pathlib import Path
import subprocess
import sys
import time

audit = Path(__file__).resolve().parent
root = audit.parents[1]
before = audit / "kernel-artifacts-before.json"
after = audit / "kernel-artifacts-after.json"
log = audit / "all-library-kernel-replay-final.log"
snapshot = audit / "snapshot_kernel_artifacts.py"
start = time.monotonic()
started_at = datetime.datetime.now(datetime.timezone.utc).isoformat()
subprocess.run([sys.executable, str(snapshot), str(before)], cwd=root, check=True)
environment = os.environ.copy()
environment["LEAN_NUM_THREADS"] = "2"
with log.open("w") as stream:
    result = subprocess.run(["leanchecker", "-v", "Hironaka"], cwd=root,
                            env=environment, stdout=stream, stderr=subprocess.STDOUT)
subprocess.run([sys.executable, str(snapshot), str(after)], cwd=root, check=True)
first = json.loads(before.read_text())
last = json.loads(after.read_text())
expected = sorted(str(Path(p).with_suffix("")).replace("/", ".") for p in first["sources"])
observed = sorted(line.removeprefix("replaying ") for line in log.read_text().splitlines()
                  if line.startswith("replaying "))
unchanged = first == last
complete = expected == observed
passed = result.returncode == 0 and unchanged and complete
report = {
    "status": "PASS_ALL_LOCAL_MODULES_FROZEN_KERNEL_REPLAY" if passed else "FAIL",
    "started_at": started_at,
    "elapsed_seconds": round(time.monotonic() - start, 3),
    "exit_code": result.returncode,
    "lean_num_threads": 2,
    "expected_modules": len(expected),
    "replayed_modules": len(observed),
    "complete_exact_module_inventory": complete,
    "all_sources_and_kernel_data_parts_unchanged": unchanged,
    "kernel_data_parts": first["kernel_data_parts"],
    "before": before.name,
    "after": after.name,
    "log": log.name,
    "method": "Lean 4.33.1 leanchecker replayFromImports, including exported/server/private parts",
}
(audit / "all-library-kernel-replay-final.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report), flush=True)
sys.exit(0 if passed else 1)
