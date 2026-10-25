#!/usr/bin/env python3
"""Bind retained historical gates to the actual rebuilt kernel artifacts.

Byte comparisons only: no old kernel, Expr, payload or frontend replay.
Run after the genuine Hironaka cohort completes, never against copied-but-stale
artifacts before that cohort. A mismatch is a hard stop, not an identity waiver.
"""
from pathlib import Path
import datetime
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
AUDIT = ROOT / "audit/phase5-main-integration-20261025"
OLD = ROOT / "audit/phase5-original-producers-20261021"


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    cohort = json.loads((AUDIT / "bounded-build/hironaka/COMPLETE.json").read_text())
    assert cohort["status"] == "PASS" and cohort["modules"] == 1560
    summary = json.loads((OLD / "new-kernel-physical-build09-verification.json").read_text())
    assert summary["exact_installed_module_kernel_checks_valid_for_final_pins"] == 17
    for name, h in summary["receipt_files"].items():
        assert digest(OLD / name) == h, name
    status = json.loads((OLD / "new-kernel-status.json").read_text())
    assert status["status"] == "PASS_ALL17_NEW_EXACT_KERNEL_REPLAYS"
    rows = []
    for module, record in sorted(status["modules"].items()):
        assert record["exit_code"] == 0
        source = record["source"]
        assert digest(ROOT / source["path"]) == source["sha256"], module
        parts = []
        for part in record["kernel_parts"]:
            actual = ROOT / part["path"]
            measured = digest(actual)
            assert measured == part["sha256"], (module, "kernel artifact mismatch", measured, part["sha256"])
            assert actual.stat().st_size == part["bytes"]
            parts.append({**part, "rebuilt_sha256": measured, "byte_exact_to_historical_gate": True})
        rows.append({"module": module, "source": source, "kernel_parts": parts,
                     "historical_kernel_log": record["log"]})
    assert len(rows) == 17
    # Also compare every unchanged pre-existing Hironaka kernel file with the
    # concrete original-cache bytes recorded before this new worktree built.
    # These are dependency preservation pins, not new kernel replay receipts.
    copied = json.loads((AUDIT / "cache-preflight/cache-copy.json").read_text())
    dependency_rows = []
    for record in copied["copied_artifacts"]:
        if record["path"].endswith(".olean"):
            actual = ROOT / record["path"]
            measured = digest(actual)
            assert measured == record["sha256"], (record["path"], "unchanged dependency kernel bytes differ")
            dependency_rows.append({"path": record["path"], "sha256": measured})
    assert len(dependency_rows) == 1558
    result = {"status": "PASS_REBUILT_KERNEL_ARTIFACTS_BYTE_EXACT_TO_RETAINED_GATES",
              "audit_tool_sha256": digest(Path(__file__)),
              "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "fresh_hironaka_cohort_targets_completed": 1560,
              "retained_exact_kernel_checks": 17, "retained_physical_payload_roots": 340,
              "retained_expression_and_frontend_evidence_not_replayed": True,
              "old_gate_summary_sha256": digest(OLD / "new-kernel-physical-build09-verification.json"),
              "old_kernel_status_sha256": digest(OLD / "new-kernel-status.json"),
              "original_cache_copy_manifest_sha256": digest(AUDIT / "cache-preflight/cache-copy.json"),
              "gated_module_rows": rows, "unchanged_dependency_kernel_files": dependency_rows,
              "identity_method": "Exact SHA256 and byte-length match of the real kernel parts recorded by each historical gate, plus 1558 original dependency .olean preservation pins",
              "old_exits_relabelled_as_fresh_checks": False,
              "new_kernel_Expr_payload_or_frontend_replays": 0}
    out = AUDIT / "combined-final/historical-gate-artifact-identity.json"
    assert not out.exists(), "Keep every actual identity attempt"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "gated_modules": len(rows), "dependency_kernels": len(dependency_rows)}))


if __name__ == "__main__":
    main()
