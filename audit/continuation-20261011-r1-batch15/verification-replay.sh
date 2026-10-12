#!/usr/bin/env bash
set -euo pipefail
source /workspace/.cloud-onboarding/tn/env.sh
cd /workspace/hironaka
task_audit=audit/continuation-20261011-r1-batch15
flock /workspace/.cloud-onboarding/tn/build.lock lake build
for task_check in CheckAllNewAxioms CheckAllLibraryAxioms CheckWholeTypeOpaqueCone; do
 flock /workspace/.cloud-onboarding/tn/build.lock lake env lean "$task_audit/$task_check.lean"
done
