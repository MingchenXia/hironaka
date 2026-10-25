#!/usr/bin/env python3
"""Run only the required final checks after both real cold-build cohorts finish.

This does not replay old module kernels, Expr captures or frontend audits.
The published test driver is kept byte-for-byte; its scope is reported exactly.
"""
from pathlib import Path
import datetime
import fcntl
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "audit/phase5-main-integration-20261025"
RUNTIME = Path("/workspace/archon-nakamaye/work/lean-runtime")


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def load_helper(name):
    spec = importlib.util.spec_from_file_location(name, AUDIT / (name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def main():
    for cohort, count in [("vendor", 1113), ("hironaka", 1560)]:
        complete = json.loads((AUDIT / "bounded-build" / cohort / "COMPLETE.json").read_text())
        assert complete["status"] == "PASS" and complete["modules"] == count
    out = AUDIT / "combined-final"
    assert not out.exists(), "Keep every attempted final check; do not overwrite"
    out.mkdir()
    sentinel = load_helper("run_no_build_sentinel")
    batches = load_helper("build_bounded_batches")
    env = os.environ.copy()
    env["PATH"] = str(RUNTIME / "lean-4.33.1-linux/bin") + os.pathsep + env["PATH"]
    env["LEAN_NUM_THREADS"] = "1"
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    package_before, package_info = sentinel.package_snapshot()
    expected = json.loads((AUDIT / "cache-preflight/external-cache-only/verification.json").read_text())
    assert package_info == expected["package_after"], "Shared package inputs changed"

    def run(label, command, writer):
        log_path = out / (label + ".log")
        started = datetime.datetime.now(datetime.timezone.utc).isoformat()
        removed = []
        with (RUNTIME / "lean-build.lock").open("a+") as lock:
            if writer:
                fcntl.flock(lock, fcntl.LOCK_EX)
            before = batches.own_setups()
            print("FINAL START " + label, flush=True)
            with log_path.open("wb") as log:
                process = subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
            assert not batches.own_running_compilers()
            if writer and process.returncode == 0:
                for p, state in batches.own_setups().items():
                    if before.get(p) != state:
                        removed.append({"path": str(p.relative_to(ROOT)), "sha256": digest(p), "bytes": p.stat().st_size})
                        p.unlink()
            actual_log = log_path.read_text()
            jobs = re.search(r"Build completed successfully \((\d+) jobs\)", actual_log)
            result = {"status": "PASS" if process.returncode == 0 else "FAIL_STOP",
                      "command": command, "exit": process.returncode, "started_utc": started,
                      "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      "log_sha256": digest(log_path), "all_children_reaped": True,
                      "actual_reported_build_jobs": int(jobs[1]) if jobs else None,
                      "warnings_observed": [line for line in actual_log.splitlines() if "warning:" in line],
                      "new_own_successful_setup_removed": removed}
            (out / (label + ".exit")).write_text(str(process.returncode) + "\n")
            (out / (label + ".json")).write_text(json.dumps(result, indent=2) + "\n")
            print("FINAL END " + label + " exit=" + str(process.returncode), flush=True)
        if process.returncode:
            raise SystemExit(process.returncode)

    # These are the published default root and test driver, with only artifact
    # cache use disabled. Existing vendored warnings are preserved, not waived
    # by changing source or main's warningAsError configuration.
    run("root-build", ["lake", "--no-cache", "build"], True)
    run("lake-test", ["lake", "--no-cache", "test"], True)
    rows = json.loads((ROOT / "audit/phase5-original-producers-20261021/blueprint-provenance.json").read_text())
    names = sorted({n for row in rows for n in row["local_bindings"]})
    assert len(names) == 81
    names += ["Hironaka.deJongAlterationTheorem", "Hironaka.exists_alterationWithBoundary"]
    code = ["import Hironaka", "import Lean.Elab.Command", "open Lean", "run_cmd do", "  let env ← getEnv"]
    code += [f'  unless env.contains `{name} do throwError "Missing current literal attachment {name}"' for name in names]
    code += ['  logInfo "CURRENT_LITERAL_BINDINGS 83 PASS"']
    bindings = out / "CurrentLiteralBindings.lean"
    bindings.write_text("\n".join(code) + "\n")
    run("literal-bindings", [str(RUNTIME / "lean-probe.sh"), "lake", "env", "lean", str(bindings)], False)
    run("vendor-source", ["python3", "scripts/check_dejong_source.py"], False)
    package_after, package_after_info = sentinel.package_snapshot()
    assert package_before == package_after
    test_text = (out / "lake-test.log").read_text()
    counts = re.search(r"axioms check:\s*(\d+) declarations\s*\((\d+) Hironaka-owned,\s*(\d+) DeJongAlterations-owned\)", test_text)
    assert counts, "Keep the exact implemented test-driver scope and actual measured counts"
    result = {"status": "PASS_FRESH_COMBINED_ROOT_TEST_BINDINGS_SOURCE_PACKAGES",
              "audit_tool_sha256": digest(Path(__file__)),
              "source_plan_sha256": {c: digest(AUDIT / "bounded-build" / c / "plan.json") for c in ["vendor", "hironaka"]},
              "root_build": json.loads((out / "root-build.json").read_text()),
              "lake_test": json.loads((out / "lake-test.json").read_text()),
              "registered_global_names_axiom_test": {"total": int(counts[1]), "hironaka_owned": int(counts[2]),
                  "dejong_owned": int(counts[3]), "scope": "Published test driver: global Name environment, namespace OR actual module ownership, including private/generated; not a per-physical-duplicate-payload replay"},
              "current_literal_attachments": 83, "old_kernel_Expr_or_frontend_replays": 0,
              "packages_before": package_info, "packages_after": package_after_info,
              "shared_package_metadata_unchanged": True, "all_processes_reaped": True}
    (out / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"],
                      "actual_axiom_test": result["registered_global_names_axiom_test"],
                      "current_literal_attachments": 83}), flush=True)


if __name__ == "__main__":
    main()
