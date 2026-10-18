"""Prepare the full567-input PDF in bounded foreground TeX passes only."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
OUT = HERE / "blueprint-pdf-build"
STAGE = HERE / "blueprint-pdf-source"


def main():
    OUT.mkdir(exist_ok=True)
    STAGE.mkdir(exist_ok=True)
    digests = json.loads((HERE / "blueprint-all-input-source-digests.json").read_text())
    contexts_path = HERE / "docs-render-typography-contexts.json"
    contexts = json.loads(contexts_path.read_text()) if contexts_path.exists() else []
    source_records = []
    for path, expected in digests.items():
        raw = (ROOT / path).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == expected, path
        output = raw.decode()
        applied = [context for context in contexts if context["source_path"] == path]
        for context in applied:
            assert context["source_sha256"] == expected
            assert output.count(context["before"]) == 1
            output = output.replace(context["before"], context["after"])
        staged = STAGE / Path(path).name
        staged.write_text(output)
        source_records.append({"public_source_path": path, "public_source_sha256": expected, "render_source_path": str(staged.relative_to(HERE)), "render_source_sha256": hashlib.sha256(staged.read_bytes()).hexdigest(), "explicit_render_only_contexts": applied})
    (HERE / "docs-render-source-provenance.json").write_text(json.dumps(source_records, indent=2) + "\n")
    env = os.environ.copy()
    env["SOURCE_DATE_EPOCH"] = "1792281600"
    env["FORCE_SOURCE_DATE"] = "1"
    for number in range(1, 4):
        stdout = HERE / f"blueprint-pass-{number}.stdout.log"
        with stdout.open("w") as stream:
            result = subprocess.run([
                "pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-recorder",
                "-output-directory", str(OUT), "extensions.tex",
            ], cwd=STAGE, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=180)
        if (OUT / "extensions.log").exists():
            shutil.copyfile(OUT / "extensions.log", HERE / f"blueprint-pass-{number}.log")
        if result.returncode:
            shutil.copyfile(ROOT / "blueprint/extensions.tex", HERE / f"docs-failed-pass-{number}-master-original.tex")
            (HERE / f"docs-failed-pass-{number}-source-digests.json").write_text(json.dumps(digests, indent=2) + "\n")
            raise SystemExit(f"TeX pass{number} failed with exit{result.returncode}; raw logs and original master preserved; no source was edited")
        print("LATEX_PASS", number, "COMPLETE", flush=True)
    for path, expected in digests.items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == expected, path


if __name__ == "__main__":
    main()
