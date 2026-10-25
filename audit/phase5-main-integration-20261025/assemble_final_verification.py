#!/usr/bin/env python3
"""Assemble actual combined results, retaining the source-only history unchanged.

This performs byte/hash bookkeeping and a final STATUS-only documentation
overlay. It runs no compiler, kernel, expression or frontend audit.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import importlib.util
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
A = ROOT / "audit/phase5-main-integration-20261025"
NATIVE = "6ae2122a9cf82f1469b68fe41e8e6cf115075d6a"
NATIVE_CODE = "400cbbc18ed04a473ec84e835a2c79adbe4875d3"


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read(path):
    return json.loads(path.read_text())


def data(value):
    return (json.dumps(value, indent=2) + "\n").encode()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    mechanical = read(A / "mechanical-source-verification.json")
    final = A / "combined-final"
    runtime = read(final / "verification.json")
    identity = read(final / "historical-gate-artifact-identity.json")
    assert runtime["status"] == "PASS_FRESH_COMBINED_ROOT_TEST_BINDINGS_SOURCE_PACKAGES"
    assert identity["status"] == "PASS_REBUILT_KERNEL_ARTIFACTS_BYTE_EXACT_TO_RETAINED_GATES"
    assert identity["retained_exact_kernel_checks"] == 17
    assert runtime["shared_package_metadata_unchanged"]
    assert runtime["all_processes_reaped"]

    # These are source-byte preservation checks, not old mathematical replays.
    for group in ["exact_fixed14_files", "main_materialized_files_preserved"]:
        for record in mechanical[group]:
            assert sha(ROOT / record["path"]) == record["sha256"], record["path"]
    for record in mechanical["explicit_merges"]:
        if record["path"] != "STATUS.md":
            assert sha(ROOT / record["path"]) == record["sha256"]
    assert len((ROOT / "README.md").read_text().splitlines()) == 61

    batches, warnings, artifacts = [], [], []
    for cohort, count in [("vendor", 1113), ("hironaka", 1560)]:
        complete = read(A / "bounded-build" / cohort / "COMPLETE.json")
        assert complete["status"] == "PASS" and complete["modules"] == count
        selected, compiled = [], []
        for path in sorted((A / "bounded-build" / cohort).glob("batch-*/verification.json")):
            record = read(path)
            assert record["status"] == "PASS" and record["exit"] == 0
            assert len(record["modules"]) <= 4
            assert record["compiler_process_reaped_before_cleanup"]
            selected += record["modules"]
            log = path.parent / "build.log"
            actual_compilers = re.findall(r"\bBuilt ([A-Za-z0-9_.]+) \(", log.read_text())
            compiled += actual_compilers
            batches.append({"cohort": cohort, "path": str(path.relative_to(ROOT)),
                            "sha256": sha(path), "modules": record["modules"],
                            "log_path": str(log.relative_to(ROOT)), "log_sha256": sha(log),
                            "actual_compiler_outputs": actual_compilers})
            warnings += record["warnings_observed"]
            for module in record["modules"]:
                prefix = ROOT / ("vendor/DeJongAlterations" if cohort == "vendor" else ".")
                path = prefix / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
                artifacts.append({"module": module, "path": str(path.relative_to(ROOT)),
                                  "sha256": sha(path), "bytes": path.stat().st_size})
        assert len(selected) == len(set(selected)) == count
        assert set(compiled) == set(selected), (cohort, "actual compiler-output coverage", sorted(set(selected)-set(compiled)))
    warning_locations = sorted(set(warnings))
    current_test = runtime["registered_global_names_axiom_test"]

    # Preserve the original source-only STATUS and receipt. The final overlay
    # is explicit and does not change any Lean, proof chapter or old audit.
    before = A / "status-before-final.md"
    status_path = ROOT / "STATUS.md"
    status_pin = next(r["sha256"] for r in mechanical["explicit_merges"] if r["path"] == "STATUS.md")
    if not before.exists():
        assert not args.check
        assert sha(status_path) == status_pin
        before.write_bytes(status_path.read_bytes())
    assert sha(before) == status_pin
    status = before.read_text()
    old_native = (
        "The separately advanced native repository records five closed original\n"
        "goals (G2, G5, G6, G7 and G9) at\n"
        "[checkpoint546](https://github.com/MingchenXia/archon-nakamaye/blob/c04efdbe221bdf608588adb87f66553951acb75c/TranscendentalNakamaye/audit/hironaka-original-tangent-symbols-20261023/all-nine-continuation-plan.json).\n"
        "Those later native producers are not part of this standalone export;\n"
        "G9 remains open in the exported scope described here.\n"
    )
    new_native = (
        "The separately advanced [native checkpoint](https://github.com/MingchenXia/archon-nakamaye/commit/" + NATIVE + ")\n"
        "has five closed goals (G2, G5, G6, G7 and G9); its 67-module increment\n"
        "is not exported here, where G9 remains open.\n"
    )
    assert status.count(old_native) == 1
    status = status.replace(old_native, new_native)
    pending = (
        "The [source-only integration record](audit/phase5-main-integration-20261025/mechanical-source-verification.json)\n"
        "separately checks this fixed export against the newer de Jong main.\n"
        "A combined build of the reconciled graph is pending; the historical\n"
        "receipts above do not claim that combined validation.\n"
    )
    passed = (
        "The [combined integration verification](audit/phase5-main-integration-20261025/publication-verification.json)\n"
        "records the actual rebuild of both libraries under main's unchanged\n"
        "configuration, followed by the default build, test and 83 current bindings.\n"
        f"Its test checks {current_test['total']:,} registered names with standard axioms;\n"
        "vendor warning logs are retained. The 17 historical kernel checks are\n"
        "reused only after exact identity of their rebuilt kernel artifacts.\n"
    )
    assert status.count(pending) == 1
    status = status.replace(pending, passed)
    overlay = {"status": "PASS_FINAL_STATUS_DOCUMENTATION_ONLY_OVERLAY",
               "before_sha256": sha(before), "after_sha256": hashlib.sha256(status.encode()).hexdigest(),
               "separate_native_revision_not_exported": NATIVE,
               "native_closed_goals": ["G2", "G5", "G6", "G7", "G9"],
               "standalone_analytic_closed_goals": ["G2", "G5", "G6", "G7"],
               "replacements": [{"before": old_native, "after": new_native},
                                {"before": pending, "after": passed}],
               "Lean_or_blueprint_payload_changes": 0, "README_changed": False}

    def emit(path, contents):
        if args.check:
            assert path.read_bytes() == contents, str(path)
        else:
            assert not path.exists() or path in [status_path, A / "README.md"], "Preserve every actual attempt"
            path.write_bytes(contents)

    emit(status_path, status.encode())
    emit(A / "final-status-overlay.json", data(overlay))
    emit(final / "actual-build-artifact-manifest.json", data({"modules": artifacts}))
    emit(final / "all-batch-receipt-manifest.json", data({"batches": batches,
        "warning_observations_including_dependency_replays": len(warnings),
        "distinct_warning_header_lines": warning_locations}))
    receipts = ["mechanical-source-verification.json", "final-status-overlay.json",
                "assemble_final_verification.py", "run_combined_final_checks.py",
                "verify_historical_gate_artifact_identity.py", "build_bounded_batches.py",
                "bounded-build/vendor/plan.json", "bounded-build/hironaka/plan.json",
                "bounded-build/vendor/COMPLETE.json", "bounded-build/hironaka/COMPLETE.json",
                "final-original-worktree-preservation.json",
                "cache-preflight/verification.json", "combined-final/verification.json",
                "combined-final/historical-gate-artifact-identity.json",
                "combined-final/actual-build-artifact-manifest.json",
                "combined-final/all-batch-receipt-manifest.json"]
    result = {"status": "PASS_ACTUAL_COMBINED_FIXED14_AND_DEJONG_INTEGRATION",
        "standalone_main": mechanical["standalone_main"],
        "fixed14_source": mechanical["fixed14_source"],
        "whole_analytic_modules": 14, "support_modules": 3,
        "whole_analytic_proof_chapters": 14, "complete_written_proofs": 52,
        "actual_rebuilt_vendor_targets": 1113, "actual_rebuilt_hironaka_targets": 1560,
        "batch_size_at_most": 4, "shared_global_writer_lock_released_between_batches": True,
        "actual_default_build_and_test": runtime,
        "historical_exact_kernel_checks_reused_after_actual_byte_identity": 17,
        "historical_physical_payload_roots_reused_after_actual_kernel_byte_identity": 340,
        "historical_strict_mathematical_expression_roots": 328,
        "historical_typed_frontend_body_differences_preserved": 12,
        "fresh_old_kernel_Expr_or_frontend_replays": 0,
        "historical_evidence_relabelled_as_fresh": False,
        "exact_fixed14_nonoverlap_files": len(mechanical["exact_fixed14_files"]),
        "main_materialized_files_preserved": len(mechanical["main_materialized_files_preserved"]),
        "README_main_bytes_preserved": True, "README_lines": 61,
        "vendor_source_license_contributor_headers_preserved": True,
        "two_old_whole_module_deferrals_preserved": True,
        "separate_native_current_not_exported": NATIVE,
        "native_accepted_code_checkpoint_same_source_tree": NATIVE_CODE,
        "new_math_source_edits_during_integration": 0,
        "shared_packages_policy_snapshot_unchanged_not_OS_readonly_mount": True,
        "no_trace_or_main_warning_configuration_edits": True,
        "distinct_vendor_warning_header_lines": len(warning_locations),
        "all_processes_reaped": True,
        "receipts": {name: sha(A / name) for name in receipts}}
    emit(A / "publication-verification.json", data(result))
    report = (
        "# Combined fixed14 and de Jong integration\n\n"
        "Both libraries were rebuilt in bounded batches under main's unchanged configuration. "
        "The default build, test, source checker and all 83 current bindings passed. "
        f"The published test checked {current_test['total']:,} registered names; its Name-based scope is recorded precisely.\n\n"
        f"The logs retain {len(warning_locations)} distinct vendor warning headers. "
        "All 17 historical kernel gates bind byte-identical rebuilt artifacts; "
        "the old kernel, expression and frontend gates were not rerun or relabelled as fresh.\n\n"
        "All 373 nonoverlap fixed14 files, main vendor/licenses/configuration, and the 61-line main README are preserved. "
        "Only the umbrella, blueprint master and explicit STATUS scope reconciliation differ. "
        "The later 67 native modules are not exported here. All child processes are reaped.\n\n"
        "`publication-verification.json` binds the final component receipts. The initial source-only "
        "and failed cache-sentinel evidence remain unchanged. Root owns commit, push and merge.\n"
    )
    emit(A / "final-report.md", report.encode())
    readme_before = A / "audit-readme-before-final.md"
    if not readme_before.exists():
        assert not args.check
        readme_before.write_bytes((A / "README.md").read_bytes())
    audit_readme = (
        "# Fixed14 and de Jong combined verification\n\n"
        "The actual combined build and test passed. See [the concise final report](final-report.md) "
        "and [the bound verification receipt](publication-verification.json). "
        "The repository's main README remains byte-identical at 61 lines.\n\n"
        "The [initial preparation README](audit-readme-before-final.md), source-only receipts, "
        "failed unchanged-cache sentinel, every batch log and historical mathematical audits "
        "remain as recorded. Their pending or failed statuses are not rewritten.\n\n"
        "After completing the recorded batches, reproduce the final byte/source bookkeeping "
        "without compiler, kernel, expression, frontend or network replay:\n\n"
        "```sh\npython3 audit/phase5-main-integration-20261025/assemble_final_verification.py --check\n```\n\n"
        "Commit, push and merge are handled separately by the root publication lane.\n"
    )
    emit(A / "README.md", audit_readme.encode())
    print(json.dumps({"status": result["status"], "mode": "check" if args.check else "assemble",
                      "sha256": sha(A / "publication-verification.json")}))


if __name__ == "__main__":
    main()
