#!/usr/bin/env bash
set -euo pipefail
[[ "${GITHUB_REPOSITORY:-}" == MingchenXia/hironaka ]] || { echo 'Wrong destination repository'; exit 1; }
[[ "${RUNNER_OS:-}" == Linux ]] || { echo 'Linux runner required'; exit 1; }
[[ "${SOURCE_REF:-}" =~ ^[0-9a-f]{40}$ ]] || { echo 'Exact 40-character source commit required'; exit 1; }
[[ "${DRAFT_TAG:-}" =~ ^[a-zA-Z0-9][a-zA-Z0-9_./+-]*$ ]] || { echo 'Explicit safe draft tag required'; exit 1; }
[[ "${INITIAL_FREE_GIB:-}" =~ ^[0-9]+$ ]] || { echo 'Integer capacity guard required'; exit 1; }
if [[ "${RUNNER_ENVIRONMENT:-}" == github-hosted ]]; then
  # Supported cleanup of unused software on this disposable runner. No mount,
  # partition, swap, TLS, runner-agent, or whole toolcache modifications.
  sudo rm -rf -- /usr/share/dotnet /usr/local/lib/android /opt/ghc \
    /usr/local/share/boost /opt/hostedtoolcache/CodeQL /usr/local/swift
  if command -v docker >/dev/null 2>&1; then sudo docker system prune --all --force; fi
  sudo apt-get update -qq
  sudo apt-get install --no-install-recommends -y zstd python3 git curl ca-certificates
fi
for tool in python3 git curl zstd tar gh; do
  command -v "$tool" >/dev/null || { echo "Required preinstalled tool missing: $tool"; exit 1; }
done
python3 - <<'PY'
import os, shutil, sys
if sys.version_info < (3, 12):
    raise SystemExit('Python 3.12+ required for safe release extraction')
need = int(os.environ['INITIAL_FREE_GIB']) * 1024**3
workspace = os.environ['GITHUB_WORKSPACE']
free = shutil.disk_usage(workspace).free
print(f'Measured workspace free bytes: {free}; required: {need}', flush=True)
if free < need:
    raise SystemExit('Insufficient runner disk; select an existing larger runner. Nothing built or uploaded.')
PY
