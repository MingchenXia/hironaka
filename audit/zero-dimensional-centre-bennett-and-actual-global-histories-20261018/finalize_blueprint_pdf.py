"""Record a prepared PDF artifact without claiming publication or Lean validation."""
from pathlib import Path
import collections
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREVIOUS = HERE.parent / "point-initial-forms-and-global-successor-arrows-20261018"


def warnings(text):
    return {
        "reference": collections.Counter(re.findall(r"LaTeX Warning: Reference `([^']+)'", text)),
        "citation": collections.Counter(re.findall(r"LaTeX Warning: Citation `([^']+)'", text)),
        "missing_destination": collections.Counter(re.findall(r"pdfTeX warning[^\n]*name\{([^}]+)\}", text)),
    }


def main():
    digest = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
    log = (HERE / "blueprint-pdf-build/extensions.log").read_text()
    old_log = (PREVIOUS / "blueprint-pass-3.log").read_text()
    assert "Output written on" in log and "Rerun to get cross-references right" not in log
    assert not re.search(r"^!|LaTeX Error:", log, re.M)
    info = subprocess.check_output(["pdfinfo", str(HERE / "blueprint-pdf-build/extensions.pdf")], text=True)
    (HERE / "docs-pdfinfo.txt").write_text(info)
    pages = int(re.search(r"^Pages:\s+(\d+)", info, re.M)[1])
    for path, expected in json.loads((HERE / "blueprint-all-input-source-digests.json").read_text()).items():
        assert digest(ROOT / path) == expected, path
    render_records = json.loads((HERE / "docs-render-source-provenance.json").read_text())
    for record in render_records:
        assert digest(HERE / record["render_source_path"]) == record["render_source_sha256"]
    render_contexts = [context for record in render_records for context in record["explicit_render_only_contexts"]]
    current, previous = warnings(log), warnings(old_log)
    inventory = {
        kind: {"current": dict(counter), "previous": dict(previous[kind]), "introduced": dict(counter - previous[kind]), "resolved": dict(previous[kind] - counter)}
        for kind, counter in current.items()
    }
    (HERE / "docs-tex-warning-inventory.json").write_text(json.dumps(inventory, indent=2) + "\n")
    receipt = json.loads((HERE / "blueprint-source-scope-validation.json").read_text())
    receipt.update({
        "status": "PREPARED_FULL567_PDF_NO_LATEX_ERRORS_PUBLICATION_GATES_PENDING",
        "pages": pages,
        "pdf_path": "blueprint-pdf-build/extensions.pdf",
        "pdf_sha256": digest(HERE / "blueprint-pdf-build/extensions.pdf"),
        "pdf_bytes": (HERE / "blueprint-pdf-build/extensions.pdf").stat().st_size,
        "latex_errors": 0,
        "latex_warning_occurrences": log.count("LaTeX Warning:"),
        "reference_warning_occurrences": len(re.findall(r"LaTeX Warning: Reference ", log)),
        "citation_warning_occurrences": len(re.findall(r"LaTeX Warning: Citation ", log)),
        "pdf_bookmark_warning_occurrences": log.count("Package hyperref Warning:"),
        "missing_pdf_destination_warning_occurrences": log.count("pdfTeX warning"),
        "math_environment_warning_occurrences": log.count("Package amsmath Warning:"),
        "overfull_box_occurrences": len(re.findall(r"Overfull \\[hv]box", log)),
        "underfull_box_occurrences": len(re.findall(r"Underfull \\[hv]box", log)),
        "reference_warning_inventory_unchanged_from_predecessor": current["reference"] == previous["reference"],
        "missing_pdf_destination_inventory_unchanged_from_predecessor": current["missing_destination"] == previous["missing_destination"],
        "introduced_reference_spellings": sorted(inventory["reference"]["introduced"]),
        "introduced_citation_spellings": sorted(inventory["citation"]["introduced"]),
        "warnings_reported_in": "docs-tex-warning-inventory.json",
        "latex_passes": 3,
        "final_cross_references_stable": True,
        "input_sources_unchanged_during_render": True,
        "public_original_source_edits_for_render": 0,
        "explicit_render_only_typography_contexts": render_contexts,
        "render_source_provenance": "docs-render-source-provenance.json",
        "preserved_failed_attempts": "docs-render-failures.json" if (HERE / "docs-render-failures.json").exists() else None,
        "pdf_validation_status": "PREPARED_RENDERED_NO_LATEX_ERRORS; not publication approval",
        "compiled_binding_probe_status": "PENDING_PARENT_PROBE",
        "axiom_probe_status": "PENDING_PARENT_PROBE",
        "publication_status": "PENDING_PARENT_SOURCE_EXPRESSION_KERNEL_AND_REVIEW_GATES",
    })
    (HERE / "blueprint-validation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({key: receipt[key] for key in ["status", "pages", "pdf_sha256", "pdf_bytes", "complete_synchronized_chapters", "complete_original_proofs", "distinct_local_bindings", "all_document_chapters", "all_document_complete_proof_environments", "all_document_distinct_local_binding_spellings", "reference_warning_occurrences", "citation_warning_occurrences", "introduced_reference_spellings"]}))


if __name__ == "__main__":
    main()
