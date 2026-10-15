"""Fingerprint every local source and every kernel-replayed olean data part."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("output", type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
sources = sorted((root / "Hironaka").rglob("*.lean")) + [root / "Hironaka.lean"]
artifacts = []
for source in sources:
    module = source.relative_to(root).with_suffix("")
    olean = root / ".lake/build/lib/lean" / module.with_suffix(".olean")
    assert olean.is_file(), olean
    artifacts.append(olean)
    for suffix in (".server", ".private"):
        part = Path(str(olean) + suffix)
        if part.exists():
            artifacts.append(part)


def digest(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


report = {
    "mathematical_modules_including_root": len(sources),
    "kernel_data_parts": len(artifacts),
    "sources": {str(p.relative_to(root)): digest(p) for p in sources},
    "compiled_kernel_data_parts": {str(p.relative_to(root)): digest(p) for p in artifacts},
}
args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
print(json.dumps({k: v for k, v in report.items() if not isinstance(v, dict)}))
