#!/usr/bin/env python3
"""Check the vendored de Jong proof inventory without the original repository."""

import hashlib
import json
import re
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    package = root / "vendor" / "DeJongAlterations"
    manifest = json.loads((package / "SOURCE.json").read_text())
    expected = {}
    for entry in manifest["files"]:
        module = entry["module"]
        assert entry["path"] == module.replace(".", "/") + ".lean", module
        assert module not in expected, f"Duplicate source module: {module}"
        data = (package / entry["path"]).read_bytes()
        assert hashlib.sha256(data).hexdigest() == entry["sha256"], module
        blob = b"blob " + str(len(data)).encode() + b"\0" + data
        assert hashlib.sha1(blob).hexdigest() == entry["git_blob"], module
        assert len(data.splitlines()) == entry["lines"], module
        expected[module] = entry

    actual = {
        p.relative_to(package).with_suffix("").as_posix().replace("/", ".")
        for p in (package / "DeJongAlterations").rglob("*.lean")
    }
    assert actual == set(expected), "Missing or extra vendored proof modules"
    assert len(expected) == manifest["source_modules"]
    assert sum(e["lines"] for e in expected.values()) == manifest["lean_lines"]

    seen, pending = set(), ["DeJongAlterations"]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = package / (module.replace(".", "/") + ".lean")
        for line in path.read_text().splitlines():
            match = re.match(r"\s*(?:public\s+)?import\s+(.+)", line.split("--", 1)[0])
            if not match:
                continue
            for imported in match[1].split():
                if imported.startswith("DeJongAlterations."):
                    pending.append(imported)
                else:
                    assert imported.startswith(("Mathlib.", "Lean.")), imported
    assert seen - {"DeJongAlterations"} == actual, "Proof inventory is not the root import closure"

    root_lock = json.loads((root / "lake-manifest.json").read_text())
    vendor_lock = json.loads((package / "lake-manifest.json").read_text())
    root_pins = {p["name"]: p["rev"] for p in root_lock["packages"] if p["type"] == "git"}
    vendor_pins = {p["name"]: p["rev"] for p in vendor_lock["packages"] if p["type"] == "git"}
    assert root_pins == vendor_pins, "Root and vendored dependency pins differ"
    assert (root / "lean-toolchain").read_text().strip() == (package / "lean-toolchain").read_text().strip()
    print(f"de Jong source check: {len(expected)} exact proof modules; complete import closure; dependency pins match")


if __name__ == "__main__":
    main()
