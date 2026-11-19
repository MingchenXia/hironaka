#!/usr/bin/env python3
"""Verify the normalized de Jong proof import closure."""

import hashlib
import json
import re
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "audit" / "dejong-source.json").read_text())
    expected = manifest["modules"]
    imports = re.compile(r"^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?(\S+)")

    seen = set()
    pending = ["Hironaka.Geometry.Alterations"]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        path = root / (module.replace(".", "/") + ".lean")
        data = path.read_bytes()
        assert hashlib.sha256(data).hexdigest() == expected[module], module
        for line in data.decode().splitlines():
            match = imports.match(line.partition("--")[0])
            if match is None:
                continue
            imported = match[1]
            if imported.startswith("Hironaka."):
                pending.append(imported)
            else:
                assert imported.startswith(("Mathlib.", "Lean.", "Init.")), imported
        seen.add(module)

    assert seen == set(expected), "The source inventory differs from the import closure"
    toolchain = (root / "lean-toolchain").read_text().strip()
    assert toolchain == manifest["lean_toolchain"], toolchain
    packages = json.loads((root / "lake-manifest.json").read_text())["packages"]
    pinned = {pkg["name"]: pkg["rev"] for pkg in packages if pkg["type"] == "git"}
    assert pinned == manifest["dependencies"], "Dependency pins differ"
    print(f"de Jong source check: {len(seen)} exact Hironaka modules; complete import closure")


if __name__ == "__main__":
    main()
