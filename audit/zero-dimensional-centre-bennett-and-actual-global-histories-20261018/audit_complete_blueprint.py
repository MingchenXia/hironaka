"""Audit current complete blueprint source without claiming compiled bindings.

The synchronized union, all document inputs, the 59 recovered chapters, and
the fixed native395 inventory have deliberately separate scopes.
"""
from pathlib import Path
import argparse
import collections
import hashlib
import json
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PREVIOUS = HERE.parent / "point-initial-forms-and-global-successor-arrows-20261018"
REV = "bae7068afc70d624cd8563fd4291436195a7f25f"
CP = "8230607eccbe39a30d5cdbd252781cfbe48d4dc8"
sys.path.insert(0, str(ROOT / "scripts"))
import upstream_namespace_map as names
from upstream_blueprint_scope import annotate
from blueprint_statement_scope import inspect, STATEMENT


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_text())


def save(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + "\n")


def refs(text, kind="lean"):
    return {name.strip() for group in re.findall(r"\\" + kind + r"\{([^}]+)\}", text) for name in group.split(",")}


def statement_findings(paths):
    failures = []
    for path in paths:
        text = (ROOT / path).read_text()
        try:
            inspect(text)
        except AssertionError as exc:
            accounted = {label for block in STATEMENT.finditer(text) for label in re.findall(r"\\label\{([^}]+)\}", block[2])}
            all_labels = set(re.findall(r"\\label\{([^}]+)\}", text))
            failures.append({
                "path": path,
                "source_sha256": digest(text.encode()),
                "strict_inspector_failure": str(exc) or "Statement inspector label coverage differs from all source labels",
                "labels_outside_supported_statement_environments": sorted(all_labels - accounted),
                "source_label_lines": {label: text[:text.index("\\label{" + label + "}")].count("\n") + 1 for label in sorted(all_labels - accounted)},
            })
    return failures


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path("/workspace/archon-nakamaye-main"))
    args = parser.parse_args()
    names.set_api_modules([f"TranscendentalNakamaye.Pending.HironakaAPI{s}" for s in ("", "2", "3", "4")])
    profile = load(HERE / "frozen-source-profile-sha256.json")
    for path, expected in profile["profiles"].items():
        assert digest((ROOT / path).read_bytes()) == expected, path
    old = load(PREVIOUS / "complete-synchronized-blueprint-paths.json")
    new = load(HERE / "blueprint-provenance.json")
    paths = list(dict.fromkeys(old + [record["destination_path"] for record in new]))
    assert len(old) == 433 and len(new) == 59 and len(paths) == 482
    external = load(ROOT / "scripts/upstream_blueprint_external_bindings.json")
    unbound = load(ROOT / "scripts/upstream_blueprint_unbound_bindings.json")
    typography = load(ROOT / "scripts/upstream_blueprint_typography.json")
    old_digests = load(PREVIOUS / "blueprint-all-input-source-digests.json")
    old_full_paths = [path for path in old_digests if path != "blueprint/extensions.tex"]
    assert len(old_full_paths) == 518
    for path in old_full_paths:
        assert digest((ROOT / path).read_bytes()) == old_digests[path], ("Preceding document source changed", path)

    new_scope = {}
    for record in new:
        raw = (args.source_root / record["source_path"]).read_bytes()
        assert digest(raw) == record["source_sha256"], record["source_path"]
        output = names.rename_text_names(raw.decode()).replace("\\chapter{", "\\section{")
        for change in typography.get(Path(record["destination_path"]).name, []):
            assert output.count(change["before"]) == 1
            output = output.replace(change["before"], change["after"])
        output = annotate(output, external, unbound)
        actual = (ROOT / record["destination_path"]).read_text()
        assert actual == output and digest(actual.encode()) == record["destination_sha256"]
        assert actual.count("\\begin{proof}") == raw.decode().count("\\begin{proof}") == record["proofs"]
        new_scope[record["destination_path"]] = inspect(actual)
    assert sum(len(records) for records in new_scope.values()) == 171
    assert sum(record["complete_proofs"] for records in new_scope.values() for record in records) == 162
    assert sum(record["kind"] == "definition" for records in new_scope.values() for record in records) == 10
    assert sum(record["kind"] == "definition" and not record["complete_proofs"] for records in new_scope.values() for record in records) == 9

    text = lambda ps: "\n".join((ROOT / path).read_text() for path in ps)
    old_text = text(old)
    new_text = text([record["destination_path"] for record in new])
    synchronized = text(paths)
    old_local, new_local, local = refs(old_text), refs(new_text), refs(synchronized)
    assert (len(old_local), len(new_local), len(local)) == (4424, 353, 4731)
    assert new_local == set(load(HERE / "new-local-bindings.json")), "Preserve the exact353 synchronized binding list"
    upstream, historical = refs(synchronized, "upstreamlean"), refs(synchronized, "upstreamunbound")
    assert len(upstream) == 241 and len(historical) == 2 and not local.intersection(external)
    assert historical == set(unbound) and not upstream.intersection(historical)
    assert old_text.count("\\begin{proof}") == 1639
    assert synchronized.count("\\begin{proof}") == 1774

    master = (ROOT / "blueprint/extensions.tex").read_text()
    stems = re.findall(r"\\input\{([^}]+)\}", master)
    full_paths = ["blueprint/" + stem + ".tex" for stem in stems]
    assert len(stems) == len(set(stems)) == 567
    assert all((ROOT / path).is_file() for path in full_paths) and set(paths).issubset(full_paths)
    complete = text(full_paths)
    full_local = refs(complete)
    proofs = re.findall(r"\\begin\{proof\}([\s\S]*?)\\end\{proof\}", complete)
    assert len(proofs) == complete.count("\\begin{proof}") == complete.count("\\end{proof}") == 2245
    assert all(proof.strip() for proof in proofs)
    assert len(full_local) == 5890 and local.issubset(full_local)
    full_labels = re.findall(r"\\label\{([^}]+)\}", complete)
    duplicate_labels = {label: count for label, count in collections.Counter(full_labels).items() if count > 1}
    previous_findings = statement_findings(old_full_paths)
    full_findings = statement_findings(full_paths)
    assert full_findings == previous_findings, "A new strict statement-scope finding was introduced"
    assert len(full_findings) == 36
    added_paths = [path for path in paths if path not in old]
    added_text = text(added_paths)
    added_local = refs(added_text)
    for path in added_paths:
        inspect((ROOT / path).read_text())

    save("complete-synchronized-blueprint-paths.json", paths)
    save("complete-blueprint-local-bindings.json", sorted(local))
    save("all-document-local-bindings.json", sorted(full_local))
    save("blueprint-all-input-source-digests.json", {path: digest((ROOT / path).read_bytes()) for path in ["blueprint/extensions.tex"] + full_paths})
    save("docs-new-statement-proof-scope.json", new_scope)
    save("docs-inherited-statement-scope-findings.json", {
        "status": "INHERITED_STRICT_INSPECTOR_FINDINGS_UNCHANGED_FROM_518_INPUT_PREDECESSOR",
        "all_document_findings": full_findings,
        "synchronized_findings": [record for record in full_findings if record["path"] in paths],
        "new59_scope_findings": [],
        "new49_input_scope_findings": [],
        "definition_proofs_manufactured": 0,
        "interpretation": "Unsupported historical label locations and any historical missing statement proofs are reported verbatim; only the new59 and fixed native395 are claimed to pass strict labelled-statement scope",
    })
    validation = {
        "status": "PASS_RECOVERED59_SOURCE_AND_STATEMENT_SCOPE_AND_FULL_DOCUMENT_PROOF_ENVIRONMENTS",
        "native_accepted_checkpoint": CP,
        "normal_published_revision": REV,
        "source_access": "Pinned-source bytes matched recorded source hashes; no Git command or network access in this docs audit",
        "complete_synchronized_chapters": len(paths),
        "complete_original_proofs": synchronized.count("\\begin{proof}"),
        "distinct_local_bindings": len(local),
        "upstream_only_binding_spellings": len(upstream),
        "explicit_historical_unresolved_bindings": len(historical),
        "distinct_synchronized_references": len(local | upstream | historical),
        "previous_synchronized_chapters": len(old),
        "previous_complete_proofs": old_text.count("\\begin{proof}"),
        "previous_local_bindings": len(old_local),
        "provenance_chapters": len(new),
        "provenance_complete_original_proofs": new_text.count("\\begin{proof}"),
        "provenance_local_bindings": len(new_local),
        "provenance_bindings_overlap_with_previous": len(old_local & new_local),
        "newly_added_synchronized_chapters": len(added_paths),
        "newly_added_original_proofs": added_text.count("\\begin{proof}"),
        "newly_added_binding_spellings": len(added_local - old_local),
        "provenance_labelled_statement_nodes": 171,
        "provenance_labelled_nondefinitions_with_complete_proofs": 161,
        "provenance_labelled_definitions": 10,
        "provenance_labelled_definitions_without_proof": 9,
        "definition_proofs_manufactured": 0,
        "preceding_document_chapter_sources_byte_identical": len(old_full_paths),
        "recovered_chapters_replay_complete_normal_published_source": len(new),
        "all_document_chapters": len(full_paths),
        "all_document_complete_proof_environments": len(proofs),
        "all_document_distinct_local_binding_spellings": len(full_local),
        "all_document_labels": len(full_labels),
        "all_document_duplicate_labels": duplicate_labels,
        "earlier_original_extension_chapters_outside_synchronized_scope": len(full_paths) - len(paths),
        "additional_binding_spellings_outside_synchronized_scope": len(full_local - local),
        "all_inputs_exist_and_are_unique": True,
        "inherited_full_document_strict_statement_scope_findings": len(full_findings),
        "inherited_synchronized_strict_statement_scope_findings": sum(record["path"] in paths for record in full_findings),
        "new_strict_statement_scope_findings": 0,
        "full_document_strict_statement_scope_status": "HAS_36_INHERITED_FINDINGS; see docs-inherited-statement-scope-findings.json",
        "compiled_binding_probe_status": "PENDING_PARENT_PROBE; all binding lists above contain actual source spellings only",
        "axiom_probe_status": "PENDING_PARENT_PROBE",
        "pdf_validation_status": "PENDING_SEPARATE_PREPUBLICATION_PDF_RECEIPT",
        "publication_status": "PENDING_PARENT_SOURCE_EXPRESSION_KERNEL_AND_REVIEW_GATES",
        "input_source_digests_file": "blueprint-all-input-source-digests.json",
        "input_source_digests_sha256": digest((HERE / "blueprint-all-input-source-digests.json").read_bytes()),
        "master_existing_scope_prose": "Updated metadata-only scope and date under docs-master-documentation-contexts.json; all mathematical chapter inputs unchanged",
    }
    save("blueprint-source-scope-validation.json", validation)
    print(json.dumps(validation))


if __name__ == "__main__":
    main()
