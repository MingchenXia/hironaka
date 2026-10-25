#!/usr/bin/env python3
"""Reproduce the source-only fixed14/main integration from immutable Git blobs.

No build, cache reuse, kernel/Expr replay, staging, commit, or remote operation.
The previous verification receipts remain immutable historical evidence.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

BASE = "dfce539bb587275734d8c818f186f839d40fb60b"
MAIN = "6e0ec1b397026973570a44769abc1084b938bffd"
FIXED14 = "668ccdac96b962a30f2f12fff2b3f4fbda20ef75"
NATIVE_CURRENT = "c04efdbe221bdf608588adb87f66553951acb75c"
OVERLAP = {"Hironaka.lean", "STATUS.md", "blueprint/extensions.tex"}
AUDIT = Path("audit/phase5-main-integration-20261025")


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def run(root: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=root)


def blob(root: Path, revision: str, path: str) -> bytes:
    return run(root, "show", f"{revision}:{path}")


def changes(root: Path, revision: str) -> set[str]:
    return set(run(root, "diff", "--name-only", BASE, revision).decode().splitlines())


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    root = args.root.resolve()
    assert run(root, "rev-parse", "HEAD").decode().strip() == MAIN
    audit = root / AUDIT
    audit.mkdir(parents=True, exist_ok=True)
    changed = changes(root, FIXED14)
    main_changed = changes(root, MAIN)
    assert len(changed) == 376
    assert changed & main_changed == OVERLAP
    exact = sorted(changed - OVERLAP)
    assert len(exact) == 373

    def emit(path: str, data: bytes) -> None:
        target = root / path
        if args.check:
            assert target.read_bytes() == data, path
        else:
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)

    for path in exact:
        emit(path, blob(root, FIXED14, path))

    merged = {}
    for path in sorted(OVERLAP - {"STATUS.md"}):
        # Git's three-way file merge retains the disjoint original hunks.
        parts = []
        for revision, label in [(MAIN, "main"), (BASE, "base"), (FIXED14, "fixed14")]:
            tmp = audit / f".{Path(path).name}.{label}.input"
            data = blob(root, revision, path)
            if not args.check:
                tmp.write_bytes(data)
            else:
                assert tmp.read_bytes() == data
            parts.append(tmp)
        data = subprocess.check_output(
            ["git", "merge-file", "-p", *(str(p) for p in parts)], cwd=root
        )
        assert b"<<<<<<<" not in data and b">>>>>>>" not in data
        merged[path] = data
        emit(path, data)

    main_status = blob(root, MAIN, "STATUS.md").decode()
    fixed_status = blob(root, FIXED14, "STATUS.md").decode()
    dejong_prefix = main_status.split("## Original complex-analytic scope\n", 1)[0]
    assert fixed_status.startswith("# Current scope\n\n")
    analytic = fixed_status.removeprefix("# Current scope\n\n")
    old_intro = (
        "This table describes the accepted native formalization at\n"
        "[the current native checkpoint](https://github.com/MingchenXia/archon-nakamaye/commit/eef2a7286318c05dda607a2909399937ccaa4c27).\n"
        "The standalone export is recorded separately below; native verification\n"
        "metrics refer to the linked native checkpoint.\n"
    )
    assert analytic.count(old_intro) == 1
    new_intro = (
        "The table below describes the standalone analytic export at the fixed\n"
        "[fourteen-module checkpoint](https://github.com/MingchenXia/hironaka/commit/668ccdac96b962a30f2f12fff2b3f4fbda20ef75),\n"
        "whose native source is\n"
        "[`eef2a728`](https://github.com/MingchenXia/archon-nakamaye/commit/eef2a7286318c05dda607a2909399937ccaa4c27).\n"
        "\n"
        "The separately advanced native repository records five closed original\n"
        "goals (G2, G5, G6, G7 and G9) at\n"
        f"[checkpoint546](https://github.com/MingchenXia/archon-nakamaye/blob/{NATIVE_CURRENT}/TranscendentalNakamaye/audit/hironaka-original-tangent-symbols-20261023/all-nine-continuation-plan.json).\n"
        "Those later native producers are not part of this standalone export;\n"
        "G9 remains open in the exported scope described here.\n"
    )
    analytic = analytic.replace(old_intro, new_intro)
    analytic = analytic.replace(
        "Four original gaps are closed:", "Four original gaps are closed in this export:"
    )
    analytic = analytic.replace(
        "The latest native increment contains 14 independently checked modules,",
        "The fixed native increment underlying this export contains 14 independently checked modules,",
    )
    analytic = analytic.replace(
        "The full build passes 5,707 jobs with zero warnings; all 81 local blueprint\n"
        "bindings resolve. The public axiom check covers 14,001 declarations.",
        "At that standalone checkpoint the full build passed 5,707 jobs with zero\n"
        "warnings; all 81 local blueprint bindings resolved. Its public axiom check\n"
        "covered 14,001 declarations.",
    )
    analytic = analytic.replace(
        "Two complete modules, `HironakaOriginalGlobalOffZero` and",
        "The [source-only integration record](audit/phase5-main-integration-20261025/mechanical-source-verification.json)\n"
        "separately checks this fixed export against the newer de Jong main.\n"
        "A combined build of the reconciled graph is pending; the historical\n"
        "receipts above do not claim that combined validation.\n\n"
        "Two complete modules, `HironakaOriginalGlobalOffZero` and",
    )
    status = (dejong_prefix + "## Standalone complex-analytic scope\n\n" + analytic).encode()
    merged["STATUS.md"] = status
    emit("STATUS.md", status)

    # Preserve the newer main package, vendor bytes, contributor headers,
    # license, README, API and checks exactly. Sparse historical audit entries
    # remain in the main Git index even when not materialized locally.
    preserved = []
    for row in run(root, "ls-tree", "-r", "--name-only", MAIN).decode().splitlines():
        if row in OVERLAP:
            continue
        p = root / row
        if p.exists():
            assert p.is_file(), row
            expected = blob(root, MAIN, row)
            assert p.read_bytes() == expected, row
            preserved.append({"path": row, "sha256": sha(expected)})

    old_receipt_path = "audit/phase5-original-producers-20261021/publication-verification.json"
    old_receipt = json.loads(blob(root, FIXED14, old_receipt_path))
    assert old_receipt["status"] == "PASS_FIXED14_STANDALONE_PUBLICATION_CHECKPOINT"
    assert old_receipt["combined_dejong_main_integration_claimed"] is False
    for name, expected_sha in old_receipt["receipts"].items():
        p = root / "audit/phase5-original-producers-20261021" / name
        assert sha(p.read_bytes()) == expected_sha, str(p)

    root_imports = merged["Hironaka.lean"].decode().splitlines()
    master = merged["blueprint/extensions.tex"].decode().splitlines()
    assert root_imports.count("import Hironaka.DeJong") == 1
    assert master.count("\\input{dejong-alterations}") == 1
    for path in exact:
        if path.startswith("Hironaka/Resolution/") and path.endswith(".lean"):
            module = path.removesuffix(".lean").replace("/", ".")
            assert root_imports.count("import " + module) == 1, module
        if path.startswith("blueprint/") and path.endswith(".tex"):
            name = Path(path).stem
            assert master.count("\\input{" + name + "}") == 1, name
    assert len((root / "README.md").read_text().splitlines()) == 61
    result = {
        "status": "PASS_MECHANICAL_SOURCE_RECONCILIATION_ONLY_COMBINED_BUILD_PENDING",
        "common_base": BASE,
        "standalone_main": MAIN,
        "fixed14_source": FIXED14,
        "separate_native_current_not_exported": NATIVE_CURRENT,
        "fixed14_changed_paths": len(changed),
        "exact_fixed14_nonoverlap_paths": len(exact),
        "whole_math_modules": 14,
        "support_modules": 3,
        "whole_blueprint_chapters": 14,
        "written_proofs": 52,
        "geometric_definitions": 6,
        "explicit_merges": [
            {"path": p, "sha256": sha(b), "method": "manual scope separation" if p == "STATUS.md" else "clean disjoint three-way merge"}
            for p, b in sorted(merged.items())
        ],
        "exact_fixed14_files": [{"path": p, "sha256": sha((root / p).read_bytes())} for p in exact],
        "main_materialized_files_preserved": preserved,
        "historical_receipts_unchanged": True,
        "README_main_bytes_unchanged": True,
        "README_lines": 61,
        "vendor_and_license_main_bytes_unchanged": True,
        "old_kernel_or_expression_replays": 0,
        "new_builds": 0,
        "combined_build_status": "PENDING_RESOURCE_COORDINATION",
        "source_proof_or_type_edits": 0,
        "remote_or_branch_updates": 0,
    }
    dest = audit / "mechanical-source-verification.json"
    data = (json.dumps(result, indent=2) + "\n").encode()
    if args.check:
        assert dest.read_bytes() == data
    else:
        dest.write_bytes(data)
    print(json.dumps({"status": result["status"], "exact_fixed14_files": len(exact), "main_materialized_files_preserved": len(preserved), "receipt_sha256": sha(data), "mode": "check" if args.check else "prepare"}))


if __name__ == "__main__":
    main()
