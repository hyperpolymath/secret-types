#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# The pinned Scorecard reusable requires these grants on the calling job.
# A job permissions map replaces the workflow map; top-level actions: read
# alone cannot satisfy the callee. Exercise the YAML map and negative controls.
set -euo pipefail
yq --version 2>&1 | grep -q mikefarah || { echo 'FAIL: Mike Farah yq required' >&2; exit 2; }
repo=$(git rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
wf="$repo/.github/workflows/scorecard.yml"
fail() { echo "FAIL: $*" >&2; exit 1; }
check() {
    local workflow="$1"
    yq -e '
      .jobs.scorecard.uses == "metadatastician/standards/.github/workflows/scorecard-reusable.yml@46ee18323305d5b36e2eef936e47dd54c39ea736" and
      (.jobs.scorecard.permissions | length) == 4 and
      .jobs.scorecard.permissions.actions == "read" and
      .jobs.scorecard.permissions.contents == "read" and
      .jobs.scorecard.permissions."security-events" == "write" and
      .jobs.scorecard.permissions."id-token" == "write"
    ' "$workflow" >/dev/null 2>&1
}
check "$wf" || fail 'calling job does not satisfy its pinned reusable contract'
echo 'PASS: Scorecard keeps the pinned reconciliation workflow and exact job grants'

yq 'del(.jobs.scorecard.permissions.actions)' "$wf" > "$work/top-level-only.yml"
if check "$work/top-level-only.yml"; then fail 'top-level actions grant hid the missing job grant'; fi
yq '.jobs.scorecard.permissions.actions = "write"' "$wf" > "$work/overgrant.yml"
if check "$work/overgrant.yml"; then fail 'unneeded actions: write was accepted'; fi
yq '.jobs.scorecard.permissions."security-events" = "read"' "$wf" > "$work/no-upload.yml"
if check "$work/no-upload.yml"; then fail 'missing SARIF upload permission was accepted'; fi
yq '.jobs.scorecard.uses = "hyperpolymath/rsr-template-repo/.github/workflows/scorecard.yml@e67ee0013777509a198977b840c0f0fabfa8ce75"' "$wf" > "$work/changed-reusable.yml"
if check "$work/changed-reusable.yml"; then fail 'replacement reusable escaped the reconciliation contract'; fi
echo 'PASS: missing or excessive grants and a replacement reusable fail the contract'
