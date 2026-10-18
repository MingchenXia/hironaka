"""Exact, separately versioned owner relocation for three compiler parser roots.

This composes the UNMODIFIED V3 complete Expr DAG with an explicit nominal
profile. It never exports Lean, changes source, or changes the comparator.
Only the three witnessed compiler definitions and five complete Name-valued
subtrees are eligible. All numeric argument expressions are preserved whole.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OLD_MODULE = "TranscendentalNakamaye.Pending.RiemannExtensionThin"
NEW_MODULE = "Hironaka.Analytic.RiemannExtensionThin"
OLD_NAMESPACE = OLD_MODULE
NEW_NAMESPACE = "Hironaka.RiemannExtensionThin"
NATIVE = HERE / "native-full-expressions.jsonl"
REFERENCE = HERE / "public-full-expressions-initial-before-blueprint-binding-recovery.jsonl"
WITNESS = HERE / "parser-generated-owner-witness.json"
COMPARATOR = ROOT / "audit/local-sharp-curves-20261015/compare_full_expr_dag.py"
FROZEN = [
    ROOT / "audit/local-sharp-curves-20261015/CanonicalStandaloneFragmentsV2.lean",
    ROOT / "audit/local-sharp-curves-20261015/CanonicalStandaloneAllV2.lean",
    ROOT / "audit/reduced-basis-curve-comparison-20261015/CanonicalStandaloneAllScopedOwnersV3.lean",
    COMPARATOR,
]
COMPARATOR_SHA = "28bc2ba40004520f5c9f483adf5e2cd2e2491c0de7bb0355ff642b176ca4c063"
V3_SHA = "1679359968f3ee3bef887163f5fe8a2f57df6ff293f30ad8e83825fa72cb3755"
ARITIES = {
    "bvar": (1, 0), "fvar": (1, 0), "mvar": (1, 0), "sort": (1, 0),
    "constant": (2, 0), "application": (0, 2), "lambda": (2, 2),
    "forall": (2, 2), "let": (2, 3), "naturalLiteral": (1, 0),
    "stringLiteral": (1, 0), "metadata": (1, 1), "projection": (2, 1),
}
PATH_EDGES = {
    "application": {"fn": 0, "arg": 1},
    "lambda": {"type": 0, "body": 1},
    "forall": {"type": 0, "body": 1},
    "let": {"type": 0, "value": 1, "body": 2},
    "metadata": {"metadata-body": 0}, "projection": {"projection-body": 0},
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def compact(obj):
    return json.dumps(obj, ensure_ascii=False, separators=(",", ":"), sort_keys=True)


def object_digest(obj):
    return hashlib.sha256(compact(obj).encode()).hexdigest()


def name_components(tree):
    if tree == ["anonymous"]:
        return []
    require(isinstance(tree, list) and len(tree) == 3, "Malformed exact Name tree")
    tag, parent, last = tree
    require((tag == "str" and isinstance(last, str)) or
            (tag == "num" and type(last) is int and last >= 0), "Malformed Name component")
    return name_components(parent) + [(tag, last)]


def name_tree(components):
    result = ["anonymous"]
    for tag, value in components:
        result = [tag, result, value]
    return result


def plain_name(text):
    return name_tree([("str", x) for x in text.split(".")])


def name_string(tree):
    return ".".join(str(x[1]) for x in name_components(tree))


def owner_relocation(tree, encoded_aux=False):
    """Exact private or hygienic owner relocation; every Name.num is retained."""
    parts = name_components(tree)
    old_mod = [("str", x) for x in OLD_MODULE.split(".")]
    new_mod = [("str", x) for x in NEW_MODULE.split(".")]
    old_ns = [("str", x) for x in OLD_NAMESPACE.split(".")]
    new_ns = [("str", x) for x in NEW_NAMESPACE.split(".")]
    if parts[:1 + len(old_mod)] == [("str", "_private")] + old_mod:
        rest = parts[1 + len(old_mod):]
        require(rest[0] == ("num", 0) and rest[1:1 + len(old_ns)] == old_ns,
                "Unexpected original private owner/index/namespace")
        suffix = rest[1 + len(old_ns):]
        require(len(suffix) == 1 and suffix[0][0] == "str", "Unexpected private suffix")
        if encoded_aux:
            old_u = OLD_MODULE.replace(".", "_")
            new_u = NEW_MODULE.replace(".", "_")
            old_n = OLD_NAMESPACE.replace(".", "_")
            new_n = NEW_NAMESPACE.replace(".", "_")
            pairs = {
                f"_aux_{old_u}___unexpand_EuclideanSpace_1":
                    f"_aux_{new_u}___unexpand_EuclideanSpace_1",
                f"_aux_{old_u}___macroRules__private_{old_u}_0_{old_n}_termE_1":
                    f"_aux_{new_u}___macroRules__private_{new_u}_0_{new_n}_termE_1",
            }
            require(suffix[0][1] in pairs, "Unwitnessed encoded auxiliary suffix")
            suffix = [("str", pairs[suffix[0][1]])]
        else:
            require(suffix == [("str", "termE")], "Unwitnessed quoted private kind")
        result = [("str", "_private")] + new_mod + [("num", 0)] + new_ns + suffix
    else:
        require(parts == [("str", "d"), ("str", "_@")] + old_mod +
                [("num", 2577270230), ("str", "_hygCtx"), ("str", "_hyg"), ("num", 6)],
                "Unwitnessed hygienic quoted Name")
        result = [("str", "d"), ("str", "_@")] + new_mod + parts[-4:]
    require([v for t, v in parts if t == "num"] ==
            [v for t, v in result if t == "num"], "A numeric Name component changed")
    return name_tree(result)


def constant(text):
    return {"tag": "constant", "data": [plain_name(text), []], "children": []}


def application(fn, arg):
    return {"tag": "application", "data": [], "children": [fn, arg]}


def expanded(record, index):
    """Complete constructor trees, only for the three small parser records."""
    node = record["fullExprNodes"][index]
    return {"tag": node["tag"], "data": node["data"],
            "children": [expanded(record, i) for i in node["children"]]}


def unapply(tree):
    args = []
    while tree["tag"] == "application":
        fn, arg = tree["children"]
        args.append(arg)
        tree = fn
    return tree, list(reversed(args))


def is_constant(tree, text):
    return tree["tag"] == "constant" and tree["data"][0] == plain_name(text)


def natural_value(tree):
    if tree["tag"] == "naturalLiteral":
        require(type(tree["data"][0]) is int, "Not an actual natural literal")
        return tree["data"][0]
    head, args = unapply(tree)
    require(is_constant(head, "OfNat.ofNat") and len(args) == 3,
            "Unrecognized actual numeric carrier expression")
    require(is_constant(args[0], "Nat") and args[1]["tag"] == "naturalLiteral",
            "Non-Nat numeric carrier")
    ih, ia = unapply(args[2])
    require(is_constant(ih, "instOfNatNat") and ia == [args[1]],
            "Unexpected original OfNat instance expression")
    return args[1]["data"][0]


def decode_quote(tree):
    if is_constant(tree, "Lean.Name.anonymous"):
        return ["anonymous"], []
    head, args = unapply(tree)
    require(len(args) == 2, "Not a whole Name constructor expression")
    prefix, numbers = decode_quote(args[0])
    if is_constant(head, "Lean.Name.mkStr"):
        require(args[1]["tag"] == "stringLiteral", "Name.mkStr argument is not literal")
        return ["str", prefix, args[1]["data"][0]], numbers
    require(is_constant(head, "Lean.Name.mkNum"), "Unknown whole Name constructor")
    number = natural_value(args[1])
    return ["num", prefix, number], numbers + [args[1]]


def reconstruct_quote(tree, original_numeric_expressions):
    """No target Expr is copied: quote the relocated Name, reusing exact Nat terms."""
    numbers = iter(original_numeric_expressions)

    def build(t):
        if t == ["anonymous"]:
            return constant("Lean.Name.anonymous")
        tag, parent, value = t
        prefix = build(parent)
        if tag == "str":
            return application(application(constant("Lean.Name.mkStr"), prefix),
                               {"tag": "stringLiteral", "data": [value], "children": []})
        nat = next(numbers)
        require(natural_value(nat) == value, "Numeric expression changed during relocation")
        return application(application(constant("Lean.Name.mkNum"), prefix), nat)

    result = build(tree)
    require(next(numbers, None) is None, "Unused original numeric argument")
    return result


def at_path(tree, path):
    require(path[0] in ("value", "type"), "Invalid expression root")
    for edge in path[1:]:
        require(edge in PATH_EDGES.get(tree["tag"], {}), "Witness path/constructor mismatch")
        tree = tree["children"][PATH_EDGES[tree["tag"]][edge]]
    return tree


def quoted_names(tree, path="value"):
    """Mirror the actual Lean witness: recognize whole names, never arbitrary strings."""
    try:
        name, _ = decode_quote(tree)
    except ValueError:
        name = None
    if name is not None and name != ["anonymous"]:
        return [(path, name)]
    out = []
    for edge, child in PATH_EDGES.get(tree["tag"], {}).items():
        out.extend(quoted_names(tree["children"][child], path + "/" + edge))
    return out


def validate_record(r):
    nodes = r["fullExprNodes"]
    for i, n in enumerate(nodes):
        require(set(n) == {"tag", "data", "children"} and n["tag"] in ARITIES,
                "Unknown Expr node/field")
        d, c = ARITIES[n["tag"]]
        require(len(n["data"]) == d and len(n["children"]) == c, "Wrong Expr arity")
        require(all(type(k) is int and 0 <= k < i for k in n["children"]), "Invalid DAG")
    roots = [r["typeRoot"], r["valueRoot"]]
    require(all(type(k) is int and 0 <= k < len(nodes) for k in roots), "Missing whole roots")
    seen = set()
    pending = roots[:]
    while pending:
        i = pending.pop()
        if i not in seen:
            seen.add(i)
            pending.extend(nodes[i]["children"])
    require(len(seen) == len(nodes), "Unreachable/discarded Expr nodes")


def selected_records(path):
    selected = {}
    count = 0
    with path.open() as f:
        for line in f:
            count += 1
            # Avoid retaining unrelated full mathematical expression records.
            r = json.loads(line)
            if r["module"] == NEW_MODULE and r["kind"] == "definition":
                validate_record(r)
                require(r["name"] not in selected, "Duplicate generated definition")
                selected[r["name"]] = r
    require(count == 924 and len(selected) == 3, "Unexpected full/parser inventory")
    return selected


def v3_root_tree(original, aux):
    relocated = owner_relocation(original, encoded_aux=aux)
    # V3 already relocates actual owner/namespace; its encoded suffix remains original.
    if aux:
        relocated[-1] = original[-1]
    return relocated


def make_profile():
    require(digest(COMPARATOR) == COMPARATOR_SHA and digest(FROZEN[2]) == V3_SHA,
            "Frozen V3/comparator changed")
    witnesses = json.loads(WITNESS.read_text())
    require(len(witnesses) == 6, "Expected six actual moduleData witnesses")
    require((HERE / "parser-generated-owner-witness-03.log").read_text().strip() ==
            "ACTUAL_PARSER_GENERATED_OWNER_WITNESSES 6", "Missing actual successful witness")
    old = [w for w in witnesses if w["owner"] == OLD_MODULE]
    new = [w for w in witnesses if w["owner"] == NEW_MODULE]
    require(len(old) == len(new) == 3, "Unexpected witness owners")
    native = selected_records(NATIVE)
    public = selected_records(REFERENCE)
    roots = []
    for w in old:
        aux = "._aux_" in w["user_name"]
        actual_new = owner_relocation(w["exact_name_tree"], encoded_aux=aux)
        candidates = [x for x in new if x["exact_name_tree"] == actual_new]
        require(len(candidates) == 1, "No unique actual generated-owner counterpart")
        target = candidates[0]
        require(w["type"] == target["type"] and
                w["is_parser_descriptor"] == target["is_parser_descriptor"], "Generated kind changed")
        old_name = name_string(v3_root_tree(w["exact_name_tree"], aux))
        new_name = name_string(actual_new)
        a, b = native[old_name], public[new_name]
        require(a["exact_name_tree"] == v3_root_tree(w["exact_name_tree"], aux) and
                b["exact_name_tree"] == actual_new, "Actual V3 root-name mismatch")
        require(a["kind"] == b["kind"] == "definition" and a["levelParams"] == b["levelParams"] == [],
                "Wrong compiler definition metadata")
        require(expanded(a, a["typeRoot"]) == expanded(b, b["typeRoot"]), "Generated TYPE differs")
        require(a["fullExprNodes"][a["typeRoot"]]["tag"] == "constant" and
                w["type"] == target["type"], "Invalid actual parser root TYPE")
        av, bv = expanded(a, a["valueRoot"]), expanded(b, b["valueRoot"])
        aq, bq = w["whole_quoted_names"], target["whole_quoted_names"]
        require(quoted_names(av) == [(x["path"], x["exact_name_tree"]) for x in aq] and
                quoted_names(bv) == [(x["path"], x["exact_name_tree"]) for x in bq],
                "Missing/extra/unlisted quoted Name occurrence")
        require(len(aq) == len(bq), "Quoted-name count changed")
        quotes = []
        for x, y in zip(aq, bq):
            require(x["path"] == y["path"], "Actual witness path changed")
            path = x["path"].split("/")
            source, observed = at_path(av, path), at_path(bv, path)
            source_name, numbers = decode_quote(source)
            target_name = owner_relocation(source_name)
            require(source_name == x["exact_name_tree"] and target_name == y["exact_name_tree"],
                    "Quoted Name is not the exact actual owner relocation")
            reconstructed = reconstruct_quote(target_name, numbers)
            require(reconstructed == observed, "Reconstructed whole quote is not actual public Expr")
            _, public_numbers = decode_quote(observed)
            require(numbers == public_numbers, "Whole OfNat/Nat/instance argument expression changed")
            quotes.append({"path": x["path"], "old_name_tree": source_name,
                           "new_name_tree": target_name, "old_subtree_sha256": object_digest(source),
                           "observed_public_subtree_sha256": object_digest(observed),
                           "reconstructed_subtree_sha256": object_digest(reconstructed),
                           "numeric_argument_sha256": [object_digest(t) for t in numbers]})
        roots.append({"actual_original_name_tree": w["exact_name_tree"],
                      "actual_public_name_tree": actual_new,
                      "v3_old_name": old_name, "v4_name": new_name,
                      "v3_old_exact_name_tree": a["exact_name_tree"],
                      "v4_exact_name_tree": actual_new, "actual_lean_type_witness": w["type"],
                      "v3_record_sha256": object_digest(a), "initial_public_record_sha256": object_digest(b),
                      "quotes": quotes})
    require(len(roots) == 3 and sum(len(r["quotes"]) for r in roots) == 5 and
            sum(r["v3_old_name"] != r["v4_name"] for r in roots) == 2,
            "Unexpected exact three-root/five-quote/two-name scope")
    native_source = Path("/workspace/archon-nakamaye/TranscendentalNakamaye/TranscendentalNakamaye/Pending/RiemannExtensionThin.lean")
    public_source = ROOT / "Hironaka/Analytic/RiemannExtensionThin.lean"
    notation = 'local notation "E" => EuclideanSpace ℂ (Fin d)'
    require(native_source.read_text().splitlines().count(notation) ==
            public_source.read_text().splitlines().count(notation) == 1, "Original notation source changed")
    return {"profile_version": 4, "scope": "EXACT_THREE_COMPILER_PARSER_ROOTS_FIVE_WHOLE_QUOTED_NAMES",
            "native_module_owner": OLD_MODULE, "public_module_owner": NEW_MODULE,
            "native_namespace": OLD_NAMESPACE, "public_namespace": NEW_NAMESPACE,
            "raw_native_sha256": digest(NATIVE), "initial_public_sha256": digest(REFERENCE),
            "witness_sha256": digest(WITNESS),
            "witness_source_sha256": digest(HERE / "ParserGeneratedOwnerWitness.lean"),
            "witness_success_log_sha256": digest(HERE / "parser-generated-owner-witness-03.log"),
            "frozen_source_sha256": {str(p.relative_to(ROOT)): digest(p) for p in FROZEN},
            "retained_v3_blocked_report_sha256": digest(HERE / "whole-module-initial-expression-comparison.json"),
            "original_notation_line": notation, "native_source_sha256": digest(native_source),
            "public_source_sha256": digest(public_source), "roots": roots,
            "all_other_records_byte_identical": 921,
            "numeric_erasure": False, "arbitrary_string_replacement": False,
            "alpha_or_defeq_comparison": False, "omitted_roots": 0}


def normalize_record(r, spec):
    require(object_digest(r) == spec["v3_record_sha256"], "Original scoped record changed")
    replacements = {q["path"]: q for q in spec["quotes"]}
    hits = set()

    def transform(tree, path):
        if path in replacements:
            q = replacements[path]
            require(path not in hits, "Duplicate witnessed path")
            hits.add(path)
            actual_name, numbers = decode_quote(tree)
            require(actual_name == q["old_name_tree"] and object_digest(tree) == q["old_subtree_sha256"],
                    "Actual whole quoted Name changed")
            new_name = owner_relocation(actual_name)
            require(new_name == q["new_name_tree"], "Non-owner Name replacement")
            out = reconstruct_quote(new_name, numbers)
            require(object_digest(out) == q["observed_public_subtree_sha256"] ==
                    q["reconstructed_subtree_sha256"], "Reconstructed quote differs")
            return out
        edges = {i: edge for edge, i in PATH_EDGES.get(tree["tag"], {}).items()}
        return {"tag": tree["tag"], "data": tree["data"],
                "children": [transform(ch, path + "/" + edges[i])
                             for i, ch in enumerate(tree["children"])]}

    original_type = expanded(r, r["typeRoot"])
    original_value = expanded(r, r["valueRoot"])
    value = transform(original_value, "value")
    require(hits == set(replacements), "Missing/extra witnessed Name path")
    # Re-intern only complete changed records; all nonnominal node data remain literal.
    nodes, cache = [], {}

    def intern(tree):
        children = [intern(c) for c in tree["children"]]
        key = (tree["tag"], compact(tree["data"]), tuple(children))
        if key not in cache:
            cache[key] = len(nodes)
            nodes.append({"tag": tree["tag"], "data": tree["data"], "children": children})
        return cache[key]

    result = copy.copy(r)
    result["typeRoot"] = intern(original_type)
    result["valueRoot"] = intern(value)
    result["fullExprNodes"] = nodes
    result["name"] = spec["v4_name"]
    result["exact_name_tree"] = spec["v4_exact_name_tree"]
    validate_record(result)
    require(expanded(result, result["typeRoot"]) == original_type, "TYPE altered")
    # This exact structural comparison is the independent unchanged comparator's job too.
    return result


def output_path(text):
    p = Path(text).resolve()
    require(p.parent == HERE and p.name not in {NATIVE.name, REFERENCE.name},
            "Outputs must be distinct task-owned audit files")
    require(p not in FROZEN and p not in (WITNESS, Path(__file__).resolve()), "Protected output path")
    return p


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("freeze-profile", "apply-profile"))
    parser.add_argument("--profile", required=True)
    parser.add_argument("--output")
    parser.add_argument("--receipt")
    args = parser.parse_args()
    profile_file = output_path(args.profile)
    expected = make_profile()
    if args.mode == "freeze-profile":
        require(args.output is None and args.receipt is None, "Unexpected freeze output")
        profile_file.write_text(json.dumps(expected, ensure_ascii=False, indent=2) + "\n")
        print("FROZEN_EXPLICIT_V4_PROFILE", digest(profile_file))
        return
    require(json.loads(profile_file.read_text()) == expected, "Profile differs from exact witnessed scope")
    require(args.output is not None and args.receipt is not None, "Apply output/receipt required")
    output, receipt_file = output_path(args.output), output_path(args.receipt)
    require(len({output, receipt_file, profile_file}) == 3, "Overlapping output paths")
    specs = {r["v3_old_name"]: r for r in expected["roots"]}
    selected_native, selected_public, changed, untouched = [], [], [], 0
    public = selected_records(REFERENCE)
    with NATIVE.open("rb") as src, output.open("wb") as dst:
        for raw in src:
            r = json.loads(raw)
            spec = specs.get(r["name"]) if r["module"] == NEW_MODULE else None
            if spec is None:
                dst.write(raw)  # ALL 921 unrelated records are literally byte-identical.
                untouched += 1
                continue
            require(r["name"] not in changed, "Duplicate scoped compiler root")
            changed.append(r["name"])
            result = normalize_record(r, spec)
            line = json.dumps(result, ensure_ascii=False, separators=(",", ":")) + "\n"
            dst.write(line.encode())
            selected_native.append(result)
            selected_public.append(public[spec["v4_name"]])
    require(set(changed) == set(specs) and untouched == 921, "Changed/unrelated root inventory mismatch")
    old_slice, new_slice = HERE / "parser-v4-three-native.jsonl", HERE / "parser-v4-three-public.jsonl"
    for path, rows in [(old_slice, selected_native), (new_slice, selected_public)]:
        path.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    comparison = HERE / "parser-v4-three-full-expression-comparison.json"
    subprocess.run(["python3", str(COMPARATOR), str(old_slice), str(new_slice), str(comparison)], check=True)
    report = json.loads(comparison.read_text())
    require(report["status"] == "EXACT_ALL_FULL_EXPR_DAG_MATCH" and
            not report["missing"] and not report["native_extras"] and not report["differences"],
            "Three generated full Exprs do not match")
    # Pin frozen sources again after all operations; nothing may mutate them.
    require({str(p.relative_to(ROOT)): digest(p) for p in FROZEN} == expected["frozen_source_sha256"],
            "Frozen source changed during normalization")
    receipt = {"status": "PASS_EXACT_V4_THREE_PARSER_ROOTS_ONLY",
               "profile_sha256": digest(profile_file), "script_sha256": digest(__file__),
               "raw_native_sha256": digest(NATIVE), "normalized_native_sha256": digest(output),
               "initial_public_reference_sha256": digest(REFERENCE),
               "changed_compiler_records": 3, "byte_identical_other_records": untouched,
               "exact_quoted_Name_occurrences": 5, "renamed_generated_root_names": 2,
               "unchanged_comparator_report": str(comparison.relative_to(ROOT)),
               "comparator_report_sha256": digest(comparison),
               "frozen_source_sha256": expected["frozen_source_sha256"],
               "limitation": "Only the three parser definitions are compared here. Full924 final strict comparison, four original instance-context repairs and kernel gates remain root-owned; original V3 BLOCKED evidence is retained."}
    receipt_file.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(receipt, ensure_ascii=False))


if __name__ == "__main__":
    main()
