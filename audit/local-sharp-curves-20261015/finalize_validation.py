"""Write the release receipt only after every independently recorded gate passes."""
import datetime
import hashlib
import json
from pathlib import Path

audit = Path(__file__).resolve().parent
root = audit.parents[1]


def read(name):
    return json.loads((audit / name).read_text())


def fingerprint(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


comparison_names = ["whole-module-full-expression-comparison.json",
                    "fragment-final-full-expression-comparison.json",
                    "fragment2-final-full-expression-comparison.json"]
comparisons = {}
for name in comparison_names:
    result = read(name)
    assert result["status"] == "EXACT_ALL_FULL_EXPR_DAG_MATCH", name
    for field in ("missing", "native_extras", "unapproved_native_extras", "differences"):
        assert not result.get(field), (name, field)
    for field in ("fallbacks", "auxiliaries_skipped", "proof_numbers_erased", "binder_names_erased"):
        assert result[field] == 0, (name, field)
    assert result["defeq_or_alpha_comparison"] is False
    counts = {key: sum(module[key] for module in result["module_counts"].values())
              for key in ("constants", "types_exact", "values_exact", "theorems", "theorem_proofs_exact")}
    assert counts["constants"] == counts["types_exact"] == counts["values_exact"]
    assert counts["theorems"] == counts["theorem_proofs_exact"]
    comparisons[name] = counts
assert [x["constants"] for x in comparisons.values()] == [2627, 13, 30]
assert [x["theorem_proofs_exact"] for x in comparisons.values()] == [2142, 12, 27]

for name in ("g2-final-expression-restoration/order-definition-comparison.json",
             "geometry-support/coordinate-callee-cstar-comparison.json"):
    assert read(name)["status"] == "EXACT_ALL_FULL_EXPR_DAG_MATCH", name

kernel = read("all-library-kernel-replay-final.json")
assert kernel["status"] == "PASS_ALL_LOCAL_MODULES_FROZEN_KERNEL_REPLAY"
assert kernel["exit_code"] == 0
assert kernel["expected_modules"] == kernel["replayed_modules"] == 744
assert kernel["complete_exact_module_inventory"]
assert kernel["all_sources_and_kernel_data_parts_unchanged"]
before = read("kernel-artifacts-before.json")
assert before == read("kernel-artifacts-after.json")
assert len(before["sources"]) == 744
assert kernel["kernel_data_parts"] == len(before["compiled_kernel_data_parts"])
assert kernel["log"] == "all-library-kernel-replay-final.log"
kernel_log = (audit / kernel["log"]).read_text()
assert "found a problem" not in kernel_log
expected = sorted(str(Path(p).with_suffix("")).replace("/", ".") for p in before["sources"])
observed = sorted(line.removeprefix("replaying ") for line in kernel_log.splitlines()
                  if line.startswith("replaying "))
assert observed == expected
for name, expected_hash in before["sources"].items():
    assert fingerprint(root / name) == expected_hash, ("Frozen mathematical source changed", name)

preservation = read("source-preservation.json")
assert preservation["status"] == "PASS"
assert preservation["preceding_modules_byte_identical"] == 543
assert preservation["original_declaration_context_repairs"] == 2
assert preservation["proof_body_edits"] == preservation["axiom_or_hole_introductions"] == 0
public = read("published-source-replay/published-source-verification.json")
assert public["status"] == "PASS_STANDARD_PUBLISHED_GIT_SOURCE_REPLAY"
assert public["published_source_revision"] == "7d0a4d88308ef45c16f25c2e9991e76c1f6ae4b4"
assert not public["horizon_private_ledger_or_original_revision_objects_required"]
configuration = read("final-export-configuration-sha256.json")
for name, expected in configuration.items():
    assert fingerprint(root / name) == expected, ("Frozen export configuration changed", name)
assert fingerprint(audit / "compare_full_expr_dag.py") == "28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063"
g2_review = read("g2-controlled-export-final-receipt.json")
g3_review = read("g3-final-standalone-review-receipt.json")
assert g2_review["status"] == "PASS_PRIVATE_AND_STANDARD_PUBLISHED_GIT_REPLAY"
assert g2_review["frozen_export_configuration_sha256"] == fingerprint(audit / "final-export-configuration-sha256.json")
assert g2_review["unchanged_original_modules"] == 543
assert g2_review["exact_original_declaration_context_repaired_modules"] == 2
assert g3_review["status"] == "FINAL_INDEPENDENT_SOURCE_EXPORT_METADATA_REPLAY_AND_RUNNER_REVIEW_PASS"
assert g3_review["frozen_configuration"] == configuration
assert "extensions.pdf (485 pages" in (audit / "blueprint-scope-pass2.log").read_text()
combined = read("combined-provenance.json")
other_audit = root / "audit/controlled-smooth-pullback-20261015"
assert combined["modules"] == read("provenance.json") + json.loads((other_audit / "provenance.json").read_text())
assert combined["blueprint_chapters"] == read("blueprint-provenance.json") + json.loads((other_audit / "blueprint-provenance.json").read_text())

summary = (audit / "all-actual-compiled-roots-contexts-final.log").read_text()
assert ("STANDALONE_MODULES 198; NEW_ACTUAL_ROOTS 2670; ALL_LIBRARY_ACTUAL_ROOTS 12366; "
        "EXACT_BINDINGS 1991; BINDINGS_IN_NEW_MODULES 1381; BINDINGS_IN_PRECEDING_LIBRARY 610; "
        "STANDARD_THREE_ONLY") in summary
assert "axioms check: 7585 declarations, all within" in (audit / "ci-all-axioms-contexts-final.log").read_text()
build = (audit / "build-final-contexts-frozen.log").read_text()
assert "Build completed successfully (4563 jobs)." in build
assert not any(line.startswith(("warning:", "error:", "⚠", "✖")) for line in build.splitlines())

inputs = comparison_names + [
    "g2-final-expression-restoration/order-definition-comparison.json",
    "geometry-support/coordinate-callee-cstar-comparison.json",
    "source-preservation.json", "published-source-replay/published-source-verification.json",
    "all-library-kernel-replay-final.json", "kernel-artifacts-before.json", "kernel-artifacts-after.json",
    "all-library-kernel-replay-final.log",
    "all-actual-compiled-roots-contexts-final.log", "ci-all-axioms-contexts-final.log",
    "build-final-contexts-frozen.log", "compare_full_expr_dag.py", "CanonicalStandaloneAllV2.lean",
    "CanonicalStandaloneFragmentsV1.lean", "CanonicalStandaloneFragmentsV2.lean",
    "relocated-imported-binder-origins.json", "relocated-binder-owner-probe.log",
    "g2-controlled-export-final-receipt.json", "g3-final-standalone-review-receipt.json",
    "snapshot_kernel_artifacts.py", "run_frozen_kernel_replay.py", "verification.md",
    "final-export-configuration-sha256.json", "blueprint-scope-pass2.log",
    "combined-provenance.json",
]
report = {
    "status": "PASS_ALL_PUBLICATION_GATES",
    "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
    "source_published_merge": public["published_source_revision"],
    "complete_module_expression_comparisons": comparisons,
    "all_new_actual_compiled_roots": 2670,
    "all_new_exact_theorem_proofs": 2181,
    "additional_exact_original_context_restored_declarations": 2,
    "all_library_axiom_audited_actual_roots": 12366,
    "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
    "full_build_jobs": 4563,
    "full_build_warnings": 0,
    "kernel_replay": kernel,
    "source_preservation": preservation,
    "blueprint": {
        "complete_chapters": 182, "complete_original_explicit_proofs": 770,
        "pages": 485, "latex_errors": 0,
        "standalone_bindings": 1991, "verified_upstream_only_bindings": 241,
        "explicit_historical_unbound_names": 2,
        "retained_reference_warning_occurrences": 618,
        "retained_latex_warnings": 661, "additional_hyperref_pdf_string_warnings": 6,
    },
    "input_sha256": {name: fingerprint(audit / name) for name in inputs},
    "controlled_report_sha256": fingerprint(root / "audit/controlled-smooth-pullback-20261015/verification.md"),
    "mathematical_scope": "Two completed subgoals; general Hironaka strengthenings remain open.",
}
(audit / "final-validation.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps({key: report[key] for key in ("status", "all_new_actual_compiled_roots", "all_library_axiom_audited_actual_roots", "full_build_jobs")}))
