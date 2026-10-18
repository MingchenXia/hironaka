"""Replay the complete major395 source increment from ordinary published Git.

Blueprints are synchronized before Lean sources. Only frozen namespace relocation,
the recorded pure imports, and the standard published header affect Lean output.
No compiler, expression exporter, network access, or private ledger is needed.
"""
from pathlib import Path
import argparse
import ast
import hashlib
import json
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REVISION = "bae7068afc70d624cd8563fd4291436195a7f25f"
CHECKPOINT = "8230607eccbe39a30d5cdbd252781cfbe48d4dc8"
BASE = "7f043d57b4052e6f8fc69c4abe4d762114a7666f"
REPAIR = "4f034e0dab92eacb4375ab09a38515b63ccbd7cc"
INVENTORY = "TranscendentalNakamaye/audit/hironaka-subgoals-395-20261018/regular-main-v47-inventory.json"
PREVIOUS = "audit/point-initial-forms-and-global-successor-arrows-20261018"
FROZEN = "audit/local-coefficients-and-curve-overlaps-20261015/verify_incremental_source.py"
HEADER = "/-\nCopyright (c) 2026 Hironaka contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: Hironaka contributors\n-/\n"
FORMAL = [
    "HironakaActualFormalStandardMonomialHS",
    "HironakaActualHomogeneousInitialHS",
    "HironakaActualFiniteInitialGeneration",
    "HironakaActualHolomorphicFibreHS",
    "HironakaActualCoordinateSpecializationHS",
    "HironakaActualTranslatedInitialHS",
]
FORMAL_WHOLE = [FORMAL[i] for i in (1, 2, 3, 4)]
STALK = [
    "HironakaActualWholeStalkHolomorphicPullback",
    "HironakaActualBiholomorphicWholeStalkHS",
    "HironakaActualOpenIntrinsicHS",
    "HironakaActualBlowupOffCentreIntrinsicHS",
]
ADDITIONAL_IMPORTS = {
    "HironakaActualOriginalDerivativeSheaf": ["Hironaka.Support.IterDerivCoordinateMembershipExact"],
    "HironakaActualPointUnitCoordinateChange": ["Hironaka.Support.HolGermSubExact"],
    "HironakaSharpActualCurveGlobalPrefixTowers": ["Hironaka.Support.MarkedTowerTransportEquationsExact"],
}
REPLACEMENTS = {
    "HironakaSharpActualCurveGlobalSuccessorCentreIdeal": (
        "Hironaka.Resolution.HironakaOriginalGlobalPrincipalization",
        "Hironaka.Support.OriginalInvertibleOpenCoverExact",
    ),
    "HironakaActualUnshiftedInitialHSTransfer": (
        "Hironaka.Resolution.HironakaActualTranslatedInitialHS",
        "Hironaka.Support.TranslatedInitialHSOriginalExact",
    ),
    "HironakaActualHomogeneousInitialHS": (
        "Hironaka.Resolution.HironakaActualFormalStandardMonomialHS",
        "Hironaka.Support.FormalStandardMonomialHSComplementExact",
    ),
    "HironakaActualCoordinateSpecializationHS": (
        "Hironaka.Resolution.HironakaSmoothCentreRealDomainActualAmbientHS",
        "Hironaka.Support.GenuineAmbientJetAlgEquivExact",
    ),
    "HironakaActualBiholomorphicWholeStalkHS": (
        "Hironaka.Resolution.HironakaSmoothCentreRealDomainActualAmbientHS",
        "Hironaka.Support.GenuineAmbientJetAlgEquivExact",
    ),
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def show(repository, revision, path):
    return subprocess.check_output(["git", "-C", str(repository), "show", revision + ":" + path])


def bindings(text, macro="lean"):
    return [name.strip() for group in re.findall(r"\\" + macro + r"\{([^}]+)\}", text) for name in group.split(",")]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path("/workspace/archon-nakamaye-main"))
    parser.add_argument("--revision", default=REVISION)
    parser.add_argument("--check", action="store_true", help="verify exact replay without writing any file")
    args = parser.parse_args()
    assert args.revision == REVISION, "The accepted normal published revision is fixed"
    plan = json.loads((HERE / "frozen-major-extraction-plan.json").read_text())
    assert plan["accepted_checkpoint"] == CHECKPOINT
    assert plan["normal_published_revision"] == REVISION
    assert plan["previous_public_main"] == BASE
    assert len(plan["source_modules"]) == len(plan["source_blueprints"]) == 49
    project_tree = subprocess.check_output([
        "git", "-C", str(args.source_root), "rev-parse", REVISION + ":TranscendentalNakamaye"
    ], text=True).strip()
    assert project_tree == plan["normal_published_project_tree"]
    guard_path = ROOT / PREVIOUS / "previous-public-source-digests.json"
    guard = json.loads(guard_path.read_text())
    assert guard["previous_public_main"] == BASE and len(guard["mathematical_sources"]) == 1042
    for path, digest in guard["mathematical_sources"].items():
        assert sha((ROOT / path).read_bytes()) == digest, ("Existing public mathematical source changed", path)

    profiles = [
        FROZEN,
        "scripts/upstream_namespace_map.py",
        "scripts/upstream_blueprint_scope.py",
        "scripts/upstream_blueprint_external_bindings.json",
        "scripts/upstream_blueprint_unbound_bindings.json",
        "scripts/upstream_blueprint_typography.json",
    ]
    profile_hashes = {}
    for path in profiles:
        raw = (ROOT / path).read_bytes()
        assert raw == show(ROOT, REPAIR, path), ("Frozen source profile changed", path)
        profile_hashes[path] = sha(raw)
    sys.path.insert(0, str(ROOT / "scripts"))
    import upstream_namespace_map as names
    from upstream_blueprint_scope import annotate
    names.set_api_modules([f"TranscendentalNakamaye.Pending.HironakaAPI{s}" for s in ("", "2", "3", "4")])
    flat = names.flattened_short()
    fq = re.compile(r"(?<![\w.])(?:Hironaka\.)?(?:Pending\.|FirstPass\.)?(?:" + "|".join(flat) + r")\.(?=[\w«])")
    frozen_source = (ROOT / FROZEN).read_text()
    function = next(node for node in ast.parse(frozen_source).body if isinstance(node, ast.FunctionDef) and node.name == "relocate")
    relocation_env = {"re": re, "names": names, "flat": flat, "fq": fq}
    exec(compile(ast.Module(body=[function], type_ignores=[]), str(ROOT / FROZEN), "exec"), relocation_env)
    relocate = relocation_env["relocate"]

    cache = {}

    def published(path):
        if path not in cache:
            cache[path] = show(args.source_root, REVISION, path)
        return cache[path]

    inventory_raw = published(INVENTORY)
    inventory = json.loads(inventory_raw)
    source_index = {record["module"]: record for record in inventory["source_records"]}
    blueprint_index = {record["path"]: record for record in inventory["blueprint_records"]}
    older_modules = ["TranscendentalNakamaye.Pending." + stem for stem in FORMAL + STALK]
    older_blueprints = {module: [] for module in older_modules}
    for record in inventory["blueprint_records"]:
        raw = published(record["path"])
        assert sha(raw) == record["sha256"], record["path"]
        own_bindings = bindings(raw.decode())
        for module in older_modules:
            if any(name.startswith(module + ".") for name in own_bindings):
                older_blueprints[module].append(record["path"])
    assert all(len(paths) == 1 for paths in older_blueprints.values()), older_blueprints
    old_bp_paths = [older_blueprints[module][0] for module in older_modules]
    assert len(set(old_bp_paths)) == 10
    assert not set(old_bp_paths).intersection(plan["source_blueprints"])
    bp_paths = old_bp_paths + plan["source_blueprints"]
    external = json.loads((ROOT / "scripts/upstream_blueprint_external_bindings.json").read_text())
    unbound = json.loads((ROOT / "scripts/upstream_blueprint_unbound_bindings.json").read_text())
    typography = json.loads((ROOT / "scripts/upstream_blueprint_typography.json").read_text())
    writes = []

    def install(path, output, accepted_before=()):
        path = ROOT / path
        data = output.encode() if isinstance(output, str) else output
        if path.exists() and path.read_bytes() == data:
            return
        if args.check:
            raise AssertionError(("Exact replay mismatch", str(path.relative_to(ROOT))))
        if path.exists():
            assert path.read_bytes() in accepted_before, ("Refuse unexpected existing-file overwrite", path)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        writes.append(str(path.relative_to(ROOT)))

    # Source-facing mathematics is present before any newly synchronized Lean source.
    previous_blueprints = {
        record["destination_path"]
        for record in json.loads((ROOT / PREVIOUS / "blueprint-provenance.json").read_text())
    }
    assert len(previous_blueprints) == 10
    blueprint_records = []
    for source_path in bp_paths:
        raw = published(source_path)
        assert sha(raw) == blueprint_index[source_path]["sha256"]
        output = names.rename_text_names(raw.decode()).replace("\\chapter{", "\\section{")
        destination_path = "blueprint/" + Path(source_path).name
        for adjustment in typography.get(Path(source_path).name, []):
            assert output.count(adjustment["before"]) == 1
            output = output.replace(adjustment["before"], adjustment["after"])
        output = annotate(output, external, unbound)
        before = ()
        if destination_path in previous_blueprints:
            before = (show(ROOT, REPAIR, destination_path),)
        install(destination_path, output, before)
        blueprint_records.append({
            "published_source_revision": REVISION,
            "source_path": source_path,
            "source_sha256": sha(raw),
            "destination_path": destination_path,
            "destination_sha256": sha(output.encode()),
            "cohort": "older_original_producer" if source_path in old_bp_paths else "major395_delta",
            "nodes": len(re.findall(r"\\label\{", output)),
            "proofs": output.count("\\begin{proof}"),
            "bindings": bindings(raw.decode()),
            "local_bindings": bindings(output),
            "upstream_bindings": bindings(output, "upstreamlean"),
            "unbound_upstream_bindings": bindings(output, "upstreamunbound"),
        })

    old_master = show(ROOT, REPAIR, "blueprint/extensions.tex").decode()
    old_inputs = re.findall(r"\\input\{([^}]+)\}", old_master)
    assert len(old_inputs) == 518
    additions = [Path(record["destination_path"]).stem for record in blueprint_records if Path(record["destination_path"]).stem not in old_inputs]
    assert len(additions) == len(set(additions)) == 49
    bibliography = "\\begin{thebibliography}{99}"
    assert old_master.count(bibliography) == 1
    added_input_block = "".join("\\input{" + stem + "}\n" for stem in additions)
    new_master = old_master.replace(bibliography, added_input_block + bibliography)
    append_only_master = new_master
    master_states = [old_master.encode(), new_master.encode()]
    documentation_path = HERE / "docs-master-documentation-contexts.json"
    documentation_contexts = json.loads(documentation_path.read_text()) if documentation_path.exists() else []
    for context in documentation_contexts:
        assert new_master.count(context["before"]) == 1
        new_master = new_master.replace(context["before"], context["after"])
        master_states.append(new_master.encode())
    assert len(re.findall(r"\\input\{", new_master)) == 567
    install("blueprint/extensions.tex", new_master, tuple(master_states))

    whole_modules = plan["source_modules"] + ["TranscendentalNakamaye.Pending." + stem for stem in FORMAL_WHOLE + STALK]
    assert len(whole_modules) == len(set(whole_modules)) == 57
    prior_delta = json.loads((ROOT / PREVIOUS / "provenance.json").read_text())
    prior_modules = {record["source_module"] for record in prior_delta}
    assert len(prior_modules) == 10 and prior_modules.issubset(plan["source_modules"])
    stalk_manifest = json.loads((HERE / "stalk-whole-source-provenance.json").read_text())
    stalk_index = {record["source_module"]: record for record in stalk_manifest}
    records = []
    for module in whole_modules:
        source_path = "TranscendentalNakamaye/" + module.replace(".", "/") + ".lean"
        raw = published(source_path)
        assert source_index[module]["path"] == source_path and source_index[module]["sha256"] == sha(raw)
        destination_module = names.new_mod(module)
        destination_path = destination_module.replace(".", "/") + ".lean"
        assert destination_path not in guard["mathematical_sources"], "Whole-parent copy would overwrite old mathematics"
        initial_output = HEADER + relocate(raw.decode())
        output = initial_output
        stem = module.rsplit(".", 1)[1]
        contexts = []
        if stem in REPLACEMENTS:
            before_module, after_module = REPLACEMENTS[stem]
            before, after = "import " + before_module + "\n", "import " + after_module + "\n"
            assert output.count(before) == 1
            output = output.replace(before, after)
            contexts.append({"before": before, "after": after, "reason": "Import complete original producers from their recovered public Support module; proof and caller typeclass contexts unchanged"})
        additional = ADDITIONAL_IMPORTS.get(stem, [])
        first = re.search(r"^import ", output, re.M)
        assert first
        additional_block = "".join("import " + name + "\n" for name in additional)
        insertion = first.start()
        placement = "before_first_original_import"
        if stem == "HironakaActualOriginalDerivativeSheaf":
            anchor = "import Hironaka.MarkedIdeal.DerivativeIdeal\n"
            assert output.count(anchor) == 1
            insertion = output.index(anchor) + len(anchor)
            placement = "after_original_DerivativeIdeal_import_preserving_repair_checkpoint_order"
        output = output[:insertion] + additional_block + output[insertion:]
        instance_path = HERE / 'original-instance-context-restorations.json'
        original_instances = json.loads(instance_path.read_text()).get(destination_module, []) if instance_path.exists() else []
        for context in original_instances:
            assert output.count(context['before']) == 1
            output = output.replace(context['before'], context['after'], 1)
            contexts.append(context)
        repair_before = None
        transitions = []
        if module in prior_modules:
            repair_before = show(ROOT, REPAIR, destination_path)
            # Every existing unmerged356 file must match its repaired checkpoint or final exact output.
            assert (ROOT / destination_path).read_bytes() in (repair_before, output.encode())
            if stem == "HironakaActualPointExceptionalInitialForm":
                restored = "import Hironaka.Resolution.HironakaActualHomogeneousInitialHS\n"
                assert output.count(restored) == 1 and repair_before == output.replace(restored, "", 1).encode()
                transitions.append({"kind": "restore_original_import", "original_import": restored, "reason": "The complete original HomogeneousInitialHS parent is now recovered"})
            else:
                assert repair_before == output.encode(), ("Unexpected change to an existing unmerged356 file", module)
        if module in stalk_index:
            assert sha((ROOT / destination_path).read_bytes()) == stalk_index[module]["destination_sha256"]
            assert (ROOT / destination_path).read_bytes() == output.encode()
        accepted_context_before = (show(ROOT, '7c808d2b58dc7e7c59d902cf72edd397abb8a47a', destination_path),) if original_instances else ()
        install(destination_path, output, accepted_context_before + (() if repair_before is None else (repair_before,)))
        record = {
            "source_revision": CHECKPOINT,
            "published_source_revision": REVISION,
            "source_module": module,
            "source_path": source_path,
            "source_sha256": sha(raw),
            "whole_original_proof_context_sha256": sha(raw),
            "destination_module": destination_module,
            "destination_path": destination_path,
            "initial_synchronized_destination_sha256": sha(initial_output.encode()),
            "additional_pure_support_imports": additional,
            "additional_pure_support_import_placement": placement if additional else None,
            "additional_pure_support_import_exact_block": additional_block,
            "administrative_elaboration_contexts": contexts,
            "existing_repair_checkpoint": REPAIR if repair_before is not None else None,
            "existing_repair_checkpoint_sha256": sha(repair_before) if repair_before is not None else None,
            "existing_destination_transitions": transitions,
            "destination_sha256": sha(output.encode()),
            "cohort": "major395_delta" if module in plan["source_modules"] else "older_original_producer",
            "proof_edits": False,
        }
        if module in stalk_index:
            record["complete_original_declarations"] = stalk_index[module]["complete_original_declarations"]
            record["prior_stalk_provenance"] = "stalk-whole-source-provenance.json"
        records.append(record)

    old_root = show(ROOT, REPAIR, "Hironaka.lean").decode()
    old_imports = re.findall(r"^import ([\w.]+)$", old_root, re.M)
    root_additions = [names.new_mod(module) for module in plan["source_modules"] if names.new_mod(module) not in old_imports]
    assert len(root_additions) == 43
    marker = old_root.find("/-!")
    assert marker >= 0
    added_import_block = "".join("import " + module + "\n\n" for module in root_additions)
    new_root = old_root[:marker] + added_import_block + old_root[marker:]
    install("Hironaka.lean", new_root, (old_root.encode(),))
    for path, digest in guard["mathematical_sources"].items():
        assert sha((ROOT / path).read_bytes()) == digest, ("Old-source guard failed after sync", path)

    def metadata(name, value):
        if args.check:
            assert json.loads((HERE / name).read_text()) == value, ("Provenance replay mismatch", name)
        else:
            (HERE / name).write_text(json.dumps(value, indent=2) + "\n")

    metadata("provenance.json", records)
    metadata("blueprint-provenance.json", blueprint_records)
    metadata("additional-pure-support-imports.json", {record["destination_module"]: record["additional_pure_support_imports"] for record in records if record["additional_pure_support_imports"]})
    metadata("owned-administrative-contexts.json", {record["destination_module"]: record["administrative_elaboration_contexts"] for record in records if record["administrative_elaboration_contexts"]})
    metadata("new-local-bindings.json", sorted({name for record in blueprint_records for name in record["local_bindings"]}))
    metadata("new-module-targets.json", [record["destination_module"] for record in records])
    metadata("older-blueprint-discovery.json", {"published_source_revision": REVISION, "inventory_path": INVENTORY, "inventory_sha256": sha(inventory_raw), "method": "Unique own original namespace in complete original lean bindings of authoritative v47 blueprint_records", "module_blueprints": {module: paths[0] for module, paths in older_blueprints.items()}})
    metadata("source-document-integration.json", {
        "repair_checkpoint": REPAIR,
        "root": {"path": "Hironaka.lean", "before_sha256": sha(old_root.encode()), "after_sha256": sha(new_root.encode()), "added_imports": root_additions, "exact_inserted_block": added_import_block, "existing_imports_preserved": True},
        "master": {"path": "blueprint/extensions.tex", "before_sha256": sha(old_master.encode()), "append_only_after_sha256": sha(append_only_master.encode()), "after_sha256": sha(new_master.encode()), "before_inputs": 518, "after_inputs": 567, "added_inputs": additions, "exact_inserted_block": added_input_block, "existing_inputs_preserved": True, "documentation_contexts": documentation_contexts},
    })
    metadata("frozen-source-profile-sha256.json", {"profiles": profile_hashes, "relocate_function_source_sha256": sha(ast.get_source_segment(frozen_source, function).encode())})
    metadata("old-public-source-preservation.json", {"status": "PASS_ALL_1042_PREVIOUS_PUBLIC_MATHEMATICAL_SOURCES_BYTE_IDENTICAL", "previous_public_main": BASE, "source_guard_path": str(guard_path.relative_to(ROOT)), "source_guard_sha256": sha(guard_path.read_bytes()), "mathematical_sources": 1042, "kernel_artifacts": "No compiler, kernel replay, or kernel-artifact write occurs in this source-only sync; parent owns separate preservation verification"})
    metadata("source-sync-owned-paths.json", {
        "script": str(Path(__file__).relative_to(ROOT)),
        "all_whole_source_destinations": [record["destination_path"] for record in records],
        "new_whole_source_paths_this_sync": [record["destination_path"] for record in records if record["source_module"] not in prior_modules and record["source_module"] not in stalk_index],
        "changed_existing_unmerged_source_paths": [record["destination_path"] for record in records if record["existing_destination_transitions"]],
        "preserved_existing_source_destinations": [record["destination_path"] for record in records if record["source_module"] in stalk_index or (record["source_module"] in prior_modules and not record["existing_destination_transitions"])],
        "all_blueprint_destinations": [record["destination_path"] for record in blueprint_records],
        "new_blueprint_paths_this_sync": [record["destination_path"] for record in blueprint_records if record["destination_path"] not in previous_blueprints],
        "preserved_existing_blueprints": sorted(previous_blueprints),
        "root_and_master": ["Hironaka.lean", "blueprint/extensions.tex"],
        "audit_metadata": ["provenance.json", "blueprint-provenance.json", "additional-pure-support-imports.json", "owned-administrative-contexts.json", "new-local-bindings.json", "new-module-targets.json", "older-blueprint-discovery.json", "source-document-integration.json", "frozen-source-profile-sha256.json", "old-public-source-preservation.json", "source-sync-owned-paths.json", "old-modules.tsv", "new-modules.tsv", "source-sync-receipt.json", "source-sync-written-paths.json"],
    })
    if not args.check:
        (HERE / "old-modules.tsv").write_text("".join(record["source_module"] + "\t" + record["destination_module"] + "\n" for record in records))
        (HERE / "new-modules.tsv").write_text("".join(record["destination_module"] + "\t" + record["destination_module"] + "\n" for record in records))
    else:
        assert (HERE / "old-modules.tsv").read_text() == "".join(record["source_module"] + "\t" + record["destination_module"] + "\n" for record in records)
        assert (HERE / "new-modules.tsv").read_text() == "".join(record["destination_module"] + "\t" + record["destination_module"] + "\n" for record in records)
    receipt = {
        "status": "PASS_EXACT_PUBLISHED_SOURCE_AND_BLUEPRINT_REPLAY" if args.check else "COPIED_COMPLETE_FROZEN_ORIGINAL_SOURCE_AND_BLUEPRINTS",
        "published_source_revision": REVISION,
        "published_source_project_tree": project_tree,
        "accepted_native_checkpoint": CHECKPOINT,
        "previous_public_main": BASE,
        "repair_checkpoint": REPAIR,
        "private_ledger_required": False,
        "whole_modules": len(records),
        "major395_delta_whole_modules": 49,
        "older_whole_formal_modules": 4,
        "preserved_whole_stalk_modules": 4,
        "blueprint_chapters": len(blueprint_records),
        "complete_original_blueprint_proofs": sum(record["proofs"] for record in blueprint_records),
        "blueprint_nodes": sum(record["nodes"] for record in blueprint_records),
        "local_blueprint_bindings": len({name for record in blueprint_records for name in record["local_bindings"]}),
        "master_new_inputs": len(additions),
        "master_total_inputs": 567,
        "new_root_imports": len(root_additions),
        "old_mathematical_sources_byte_identical": 1042,
        "original_type_or_proof_text_changes": 0,
        "additional_pure_imports": sum(len(record["additional_pure_support_imports"]) for record in records),
        "pure_import_replacements": sum(sum(context.get("kind") != "declaration_local_recovery_of_original_compiled_instance_route" for context in record["administrative_elaboration_contexts"]) for record in records),
        "declaration_local_original_instance_restorations": sum(sum(context.get("kind") == "declaration_local_recovery_of_original_compiled_instance_route" for context in record["administrative_elaboration_contexts"]) for record in records),
        "original_import_restorations": 1,
        "blueprints_written_before_lean_sources": True,
        "source_and_blueprint_paths": [record["destination_path"] for record in records] + [record["destination_path"] for record in blueprint_records],
        "compiled_or_expression_checked_here": False,
        "limitation": "Source replay only; parent owns support completion, strict ALL comparisons, final build, axiom and frozen kernel gates",
    }
    if not args.check:
        (HERE / "source-sync-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
        (HERE / "source-sync-written-paths.json").write_text(json.dumps(writes, indent=2) + "\n")
    print(json.dumps({key: value for key, value in receipt.items() if key != "source_and_blueprint_paths"}))


if __name__ == "__main__":
    main()
