#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# grade-receipt.sh [--check]
#
# Writes (or checks) verification/receipts/agda_praxis.deed: the machine record
# of this repository's Agda claims, each with its Proof Witness Grade.
#
#   Proof Witness Grades: standards/3-practice/PROOF-POLICY.adoc §8 (owner
#   ruling 2026-11-04).  PWG-3: the Agda proof is PROVEN under the §2.1
#   invocation and no Rocq or Lean leg counts yet.  The record carries the
#   §8.5 fields: pwg, foundation-diverse, and for each leg its route, its §5
#   token and its §2.2 correspondence state.  A grade is derived, never
#   asserted (§8.4): it is computed below from the legs, not typed in.
#
# The receipt is DERIVED from the tree, never typed by hand, except for the
# claim list below, which is cross-checked against the claim IDs in
# PROOF-STATUS.adoc in both directions.  That makes two drifts impossible:
#   * a module added or changed without the receipt following it, and
#   * a claim added to PROOF-STATUS.adoc without a ledger token and its legs.
#
# What the receipt deliberately does NOT do: it does not run Agda.  It records
# the gate, the flags and the pinned versions; the gate itself runs in CI
# (.github/workflows/proofs.yml) and its log is the execution evidence.  A
# receipt is a statement about which gate produced which result, not a
# substitute for the result — standards/3-practice/PROOF-POLICY.adoc §2.3.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
. scripts/proof-flags.sh

out=verification/receipts/agda_praxis.deed
mode=
commit_override=
while (( $# )); do
  case "$1" in
    --write|--check) mode="$1" ;;
    --commit)        commit_override="${2:-}"; shift ;;
    -h|--help)
      printf 'usage: %s [--write|--check] [--commit <sha>]\n' "${0##*/}"
      printf '  --commit records a specific revision instead of HEAD (CI does this,\n'
      printf '           because a committed receipt can only name its parent)\n'
      exit 0 ;;
    *) printf 'unknown argument: %s\n' "$1" >&2; exit 2 ;;
  esac
  shift
done

# ── The claim list ────────────────────────────────────────────────────────────
# id | ledger token (README-EXPLAINME-STANDARD §5 vocabulary) | kind |
# Rocq route | Rocq §2.2 state | Lean route | Lean §2.2 state.
# Tokens are the closed vocabulary: proven | proven-with-postulates | tested-only
# | argued | open.  Kind is theorem (graded, PROOF-POLICY §8.1) or
# demonstration (a checked example, below the ladder: `ungraded`).  Leg routes
# are PROOF-POLICY §2 and §8.5: transported | re-proved | waived | unavailable.
# States are §2.2: AGDA-VERIFIED | COQ-CHECKED | LEAN-CHECKED | BRIDGE-PENDING
# | RECONCILED | COUNTEREXAMPLE | QUARANTINED.  Only RECONCILED counts (§8.2).
claims() {
  cat <<'ROWS'
N-1|proven|theorem|unavailable|AGDA-VERIFIED|unavailable|AGDA-VERIFIED
N-2|proven|theorem|unavailable|AGDA-VERIFIED|unavailable|AGDA-VERIFIED
N-3|proven|theorem|unavailable|AGDA-VERIFIED|unavailable|AGDA-VERIFIED
N-4|tested-only|demonstration|n/a|n/a|n/a|n/a
N-5|tested-only|demonstration|n/a|n/a|n/a|n/a
N-6|tested-only|demonstration|n/a|n/a|n/a|n/a
N-7|proven|theorem|unavailable|AGDA-VERIFIED|unavailable|AGDA-VERIFIED
N-8|proven|theorem|unavailable|AGDA-VERIFIED|unavailable|AGDA-VERIFIED
N-9|proven|theorem|unavailable|AGDA-VERIFIED|unavailable|AGDA-VERIFIED
ROWS
}

# PROOF-POLICY §8.2: derive the grade from the Agda token and the legs.  A leg
# counts only when it is RECONCILED (§2.2); none exists yet, so no leg counts.
# Print the PWG for one claim row's token, kind and two legs' §2.2 states.
pwg_of() {
  local token="$1" kind="$2" coq_state="$3" lean_state="$4" counted=0
  [[ "$kind" == theorem ]] || { printf 'ungraded'; return; }
  [[ "$token" == proven || "$token" == proven-with-postulates ]] || { printf 'ungraded'; return; }
  # A leg counts on its §2.2 state, never on its route: a transported or
  # re-proved leg still BRIDGE-PENDING does not count.
  [[ "$coq_state" == RECONCILED ]] && counted=$((counted + 1))
  [[ "$lean_state" == RECONCILED ]] && counted=$((counted + 1))
  case "$counted" in 0) printf '3' ;; 1) printf '2i' ;; 2) printf '2ii' ;; esac
}

# ── Derived facts ─────────────────────────────────────────────────────────────
repo="hyperpolymath/secret-types"
source_commit="${commit_override:-$(git rev-parse --short=12 HEAD 2>/dev/null || printf 'unknown')}"
agda_version="$(proof_agda_pin)"
agda_from="$(proof_agda_provenance)"
flag_line="$(proof_flags_line)"
# The standards commit this receipt reads PROOF-POLICY at (section 7 asks a
# gate to cite the policy by repository, path and full 40-character commit).
policy_commit="9bdf864cc7f2c8e24b4df84bf00d04158eee3ad5"

# Print the Agda module paths under src/SecretTypes in sorted order.
modules() { find src/SecretTypes -name '*.agda' | LC_ALL=C sort; }
# Print the Agda rejection fixture paths under tests/reject in sorted order.
fixtures() { find tests/reject -name '*.agda' | LC_ALL=C sort; }

# Print matching escape-hatch lines with paths and line numbers from Agda files
# in the gated trees. Suppress grep errors and return success even with no hits.
escape_hits() {
  grep -rn --include='*.agda' -E \
    '(^|[^A-Za-z])(postulate|believe_me|trustMe|sorry|Admitted)([^A-Za-z]|$)|{-# *(TERMINATING|NON_TERMINATING) *#-}|--type-in-type' \
    src/SecretTypes tests 2>/dev/null || true
}

# The claim list and PROOF-STATUS.adoc must name exactly the same claims.
# PROOF-STATUS is the human record; this receipt is the machine one; a claim in
# one and not the other is drift, in either direction.
# Exit with an error if claim IDs cannot be read or differ.
check_claim_ids() {
  local decl doc
  decl="$(claims | cut -d'|' -f1 | LC_ALL=C sort)"
  doc="$(grep -oE '^\| N-[0-9]+ ' PROOF-STATUS.adoc | tr -d '| ' | LC_ALL=C sort -u || true)"
  if [[ -z "$doc" ]]; then
    echo 'ERROR: no claim ids found in PROOF-STATUS.adoc; the table layout changed' >&2
    exit 1
  fi
  if [[ "$decl" != "$doc" ]]; then
    echo 'ERROR: claim ids differ between this receipt and PROOF-STATUS.adoc' >&2
    diff <(printf '%s\n' "$doc") <(printf '%s\n' "$decl") \
      | sed 's/^</  only in PROOF-STATUS.adoc:/; s/^>/  only in grade-receipt.sh:/' >&2
    exit 1
  fi
}

# Print the derived receipt, including claim rows, module hashes and fixtures.
emit() {
  printf ';; SPDX-License-Identifier: CC-BY-SA-4.0\n'
  printf ';; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)\n'
  printf ';; GENERATED by scripts/grade-receipt.sh; regenerate with --write, check with --check.\n'
  printf ';; This describes the gate and tree; the CI log is the execution evidence.\n'
  printf '(praxis-deed\n  :schema-version "1.0.0"\n  :canonical-name "secret-types-agda-receipt"\n'
  printf '  (identity\n    :project "secret-types"\n    :name "Agda verification receipt with Proof Witness Grades"\n'
  printf '    :repository "%s"\n    :repo-uuid #u5"github.com/%s"\n' "$repo" "$repo"
  printf '    :uuid-source "uuid5(URL, github.com/%s)"\n' "$repo"
  printf '    :uuid-note "F-1 remains open: template mint-path cause and local scaffolding sweep; see docs/reports/audit/consistency-audit-2026-11-01.adoc"\n'
  printf '    :kind "theory"\n    :source-commit "%s")\n' "$source_commit"
  printf '  (prover\n    :tool "agda"\n    :version "%s"\n    :provenance "%s"\n' "$agda_version" "$agda_from"
  printf '    :library "none (--no-libraries; Agda builtins only)"\n    :flags "%s"\n' "$flag_line"
  printf '    :flags-source "scripts/proof-flags.sh"\n'
  printf '    :flags-note "One definition, read by the gate and by this receipt; the receipt cannot describe a gate that did not run")\n'
  printf '  (conformance\n    :policy "standards/3-practice/PROOF-POLICY.adoc"\n'
  printf '    :policy-repository "hyperpolymath/standards"\n    :policy-commit "%s"\n' "$policy_commit"
  printf '    :policy-revision "owner ruling 2026-10-26; section 2.1 dated 2026-11-01; section 8 (PWG) 2026-11-04"\n'
  printf '    :canonical-invocation "agda --safe --without-K --cubical-compatible"\n'
  printf '    :cubical-compatible "in-force"\n    :flag-control "tests/flag-control/IndexedMatch.agda"\n'
  printf '    :closed-waiver "W-1, docs/proof-debt.adoc#waivers"\n'
  printf '    :stronger-than-canonical ("--no-libraries" "--ignore-interfaces" "--double-check" "-W error"))\n'
  printf '  (gate\n    :command "bash scripts/check.sh"\n    :laws-certificate "bash scripts/minimal-laws.sh"\n'
  printf '    :ci ".github/workflows/proofs.yml"\n    :module-count %s\n    :reject-fixture-count %s)\n' "$(modules | wc -l | tr -d ' ')" "$(fixtures | wc -l | tr -d ' ')"
  printf '  (trust-base\n    :postulates %s\n    :escape-hatches %s\n' "$(grep -rlw --include='*.agda' postulate src/SecretTypes tests 2>/dev/null | wc -l | tr -d ' ')" "$(escape_hits | wc -l | tr -d ' ')"
  printf '    :library-dependencies 0\n    :axioms-assumed 0\n'
  printf '    :note "A non-zero count above fails the gate; the receipt is only meaningful while all four are zero")\n'
  printf '  ; PROOF-POLICY section 8: grades apply to theory theorems; demonstrations are ungraded.\n'
  printf '  ; Rocq and Lean legs are unavailable: no transport or hand re-proof exists yet, so no leg counts.\n'
  printf '  (claims\n'
  while IFS='|' read -r id token kind coq coq_state lean lean_state; do
    if [[ "$kind" == theorem ]]; then
      printf '    (claim :id "%s" :token "%s" :kind "%s" :pwg "%s" :foundation-diverse #f\n' "$id" "$token" "$kind" "$(pwg_of "$token" "$kind" "$coq_state" "$lean_state")"
      printf '      (leg :prover "rocq" :route "%s" :token "open" :state "%s" :receipts ())\n' "$coq" "$coq_state"
      printf '      (leg :prover "lean" :route "%s" :token "open" :state "%s" :receipts ()))\n' "$lean" "$lean_state"
    else
      printf '    (claim :id "%s" :token "%s" :kind "%s" :pwg "%s")\n' "$id" "$token" "$kind" "$(pwg_of "$token" "$kind" "$coq_state" "$lean_state")"
    fi
  done < <(claims)
  printf '  )\n  ; Every module hash is checked against the current tree.\n  (modules\n'
  while read -r m; do
    printf '    (module :path "%s" :sha256 "%s")\n' "$m" "$(sha256sum "$m" | cut -d' ' -f1)"
  done < <(modules)
  printf '  )\n  (fixtures\n'
  while read -r f; do
    printf '    (fixture :path "%s")\n' "$f"
  done < <(fixtures)
  printf '  )\n)\n'
}

check_claim_ids

case "$mode" in
  --write|"")
    mkdir -p "$(dirname "$out")"
    emit > "$out"
    printf 'WROTE %s (source-commit %s)\n' "$out" "$source_commit"
    ;;
  --check)
    tmp="$(mktemp)"; trap 'rm -f "$tmp"' EXIT
    emit > "$tmp"
    # The source-commit line is expected to differ: a receipt is committed by
    # the change that produces it and so records its parent.  Everything else
    # must match byte for byte, including every module sha256.
    # Print the receipt file in $1 without its source-commit line.
    filter() { grep -v '^    :source-commit ' "$1"; }
    if ! diff -u <(filter "$out") <(filter "$tmp") > /tmp/receipt-diff.$$ 2>&1; then
      echo 'ERROR: verification receipt does not match the tree:' >&2
      sed -n '1,60p' /tmp/receipt-diff.$$ >&2
      rm -f /tmp/receipt-diff.$$
      echo 'Regenerate with: bash scripts/grade-receipt.sh --write' >&2
      exit 1
    fi
    rm -f /tmp/receipt-diff.$$
    echo "PASS: verification receipt matches the tree ($(modules | wc -l | tr -d ' ') modules, all sha256 verified)"
    ;;
  *)
    echo "usage: ${0##*/} [--write|--check]" >&2
    exit 2
    ;;
esac
