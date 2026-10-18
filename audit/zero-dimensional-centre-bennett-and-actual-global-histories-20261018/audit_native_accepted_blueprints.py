"""Inspect all395 pinned native original blueprint chapters, without Git or Lean."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys

sys.dont_write_bytecode = True
from blueprint_statement_scope import inspect

HERE = Path(__file__).resolve().parent
REV = "bae7068afc70d624cd8563fd4291436195a7f25f"
INVENTORY = "TranscendentalNakamaye/audit/hironaka-subgoals-395-20261018/regular-main-v47-inventory.json"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path, default=Path("/workspace/archon-nakamaye-main"))
    args = parser.parse_args()
    discovery = json.loads((HERE / "older-blueprint-discovery.json").read_text())
    raw_inventory = (args.source_root / INVENTORY).read_bytes()
    assert hashlib.sha256(raw_inventory).hexdigest() == discovery["inventory_sha256"]
    inventory = json.loads(raw_inventory)
    records = inventory["blueprint_records"]
    assert len(records) == 395
    nodes = proofs = definitions = without_proof = nondefinitions = 0
    source_scope = {}
    for record in records:
        raw = (args.source_root / record["path"]).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == record["sha256"], record["path"]
        text = raw.decode()
        scope = inspect(text)
        source_scope[record["path"]] = scope
        nodes += sum(len(row["labels"]) for row in scope)
        blocks = re.findall(r"\\begin\{proof\}([\s\S]*?)\\end\{proof\}", text)
        assert len(blocks) == text.count("\\begin{proof}") == text.count("\\end{proof}")
        assert all(block.strip() for block in blocks)
        proofs += len(blocks)
        definitions += sum(row["kind"] == "definition" for row in scope)
        without_proof += sum(row["kind"] == "definition" and not row["complete_proofs"] for row in scope)
        nondefinitions += sum(row["kind"] != "definition" for row in scope)
    assert (nodes, proofs, definitions) == (1205, 1190, 44)
    receipt = {
        "status": "PASS_ALL395_NATIVE_LABELLED_STATEMENTS_PROOFS_AND_DEFINITIONS",
        "normal_published_revision": REV,
        "accepted_native_source_checkpoint": "8230607eccbe39a30d5cdbd252781cfbe48d4dc8",
        "inventory_path": INVENTORY,
        "inventory_sha256": hashlib.sha256(raw_inventory).hexdigest(),
        "chapters": len(records),
        "labelled_nodes": nodes,
        "complete_nonempty_proof_environments": proofs,
        "labelled_definition_nodes": definitions,
        "labelled_definitions_without_proof": without_proof,
        "labelled_nondefinitions": nondefinitions,
        "every_labelled_nondefinition_has_complete_proof": True,
        "definition_proofs_manufactured": 0,
        "private_ledger_required": False,
        "git_or_network_used_by_this_audit": False,
        "compiled_binding_validation": "PENDING_PARENT; not performed by this text/source audit",
        "scope": "Fixed native395 continuation; public synchronized482 and full567 counts are separate. The public recovery also includes ten older prerequisite blueprints beyond the delta.",
    }
    for name, value in [("accepted-native-395-blueprint-records.json", records), ("docs-native-395-statement-proof-scope.json", source_scope), ("accepted-native-blueprint-scope-validation.json", receipt)]:
        (HERE / name).write_text(json.dumps(value, indent=2) + "\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
