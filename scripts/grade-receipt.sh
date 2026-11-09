#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# grade-receipt.sh [--check]
#
# Writes (or checks) verification/receipts/agda-pwg_praxis.deed: the machine
# record of this repository's Agda claims and their Proof Witness Grades
# (standards/3-practice/PROOF-POLICY.adoc §8, owner ruling 2026-11-04).
#
#   PWG-3 (§8.2): the Agda proof is PROVEN under the canonical §2.1 invocation
#   (agda --safe --without-K --cubical-compatible, here with stronger flags
#   besides).  PWG-2ii: PWG-3, and both the Rocq and the Lean leg count:
#   kernel-checked (scripts/check-legs.sh, no axioms) and RECONCILED against
#   the Agda statement (verification/legs/README.adoc).  Not PWG-1: that needs
#   a per-commit receipt of each checker's observed result, which this file
#   is not (see below).
#
# The receipt is DERIVED from the tree, never typed by hand, except for the
# claim list below, which is cross-checked against the claim IDs in
# PROOF-STATUS.adoc in both directions.  That makes two drifts impossible:
#   * a module added or changed without the receipt following it, and
#   * a claim added to PROOF-STATUS.adoc without a ledger token and a grade.
#
# What the receipt deliberately does NOT do: it does not run Agda.  It records
# the gate, the flags and the pinned versions; the gate itself runs in CI
# (.github/workflows/proofs.yml) and its log is the execution evidence.  A
# receipt is a statement about which gate produced which result, not a
# substitute for the result — standards/3-practice/PROOF-POLICY.adoc §2.3.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
. scripts/proof-flags.sh

out=verification/receipts/agda-pwg_praxis.deed
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
# id | ledger token (README-EXPLAINME-STANDARD §5 vocabulary) | PWG (PROOF-POLICY
# §8.5: 3 | 2i | 2ii | 1 | ungraded; n/a for a checked demonstration, which
# is not a theory theorem and so not on the ladder, §8.1) | Rocq leg (§2) | Lean leg.
# Tokens are the closed vocabulary: proven | proven-with-postulates | tested-only
# | argued | open.  Legs are: transported | re-proved | unavailable.
claims() {
  cat <<'ROWS'
N-1|proven|2ii|re-proved|re-proved
N-2|proven|2ii|re-proved|re-proved
N-3|proven|2ii|re-proved|re-proved
N-4|tested-only|n/a|n/a|n/a
N-5|tested-only|n/a|n/a|n/a
N-6|tested-only|n/a|n/a|n/a
N-7|proven|2ii|re-proved|re-proved
N-8|proven|2ii|re-proved|re-proved
N-9|proven|2ii|re-proved|re-proved
ROWS
}

# ── Derived facts ─────────────────────────────────────────────────────────────
repo="hyperpolymath/secret-types"
source_commit="${commit_override:-$(git rev-parse --short=12 HEAD 2>/dev/null || printf 'unknown')}"
agda_version="$(proof_agda_pin)"
agda_from="$(proof_agda_provenance)"
flag_line="$(proof_flags_line)"

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

# The leg sources, in sorted order: everything a leg's kernel reads.
leg_sources() {
  find verification/legs/rocq -name '*.v' | LC_ALL=C sort
  find verification/legs/lean -name '*.lean' -not -path '*/.lake/*' | LC_ALL=C sort
  printf '%s\n' verification/legs/lean/lakefile.toml verification/legs/lean/lean-toolchain
}

# Print the (legs) block: per leg, the pinned checker, its invocation, the
# axiom check, and the sha256 of every input.  The pins are read from
# scripts/check-legs.sh, the one place the gate takes them from.
emit_legs() {
  local coq lean
  coq="$(sed -n 's/^COQ_VERSION=\(.*\)$/\1/p' scripts/check-legs.sh)"
  lean="$(sed -n 's/^LEAN_VERSION=\(.*\)$/\1/p' scripts/check-legs.sh)"
  printf '  (legs\n    :gate "bash scripts/check-legs.sh"\n    :ci ".github/workflows/proofs.yml (job legs)"\n'
  printf '    :correspondence "verification/legs/README.adoc"\n'
  printf '    :route "re-proved"\n'
  printf '    :route-reason "Agda2Dedukti is an Agda backend pinned to a fork (b026db1, GHC 8.10) and cannot run on Agda %s; no released Dedukti/Lambdapi exporter to Lean 4, and no pinned route to Rocq"\n' "$agda_version"
  printf '    :state "RECONCILED"\n'
  printf '    :review "statement comparison written by Claude Code; provisional until owner review (estate doctrine 4)"\n'
  printf '    (leg :prover "rocq" :checker "coqc" :version "%s" :invocation "coqc -q SecretTypes.v (in verification/legs/rocq)" :libraries "none (no Require)" :axioms "none (Print Assumptions: Closed under the global context)")\n' "$coq"
  printf '    (leg :prover "lean" :checker "lean" :version "%s" :invocation "lake build; lake env lean Axioms.lean (in verification/legs/lean)" :libraries "none (lakefile has no require; no Mathlib)" :axioms "none (#print axioms: does not depend on any axioms)")\n' "$lean"
  printf '    (inputs\n'
  while read -r p; do
    printf '      (input :path "%s" :sha256 "%s")\n' "$p" "$(sha256sum "$p" | cut -d' ' -f1)"
  done < <(leg_sources)
  printf '    ))\n'
}

# Print the derived receipt, including claim rows, module hashes and fixtures.
emit() {
  printf ';; SPDX-License-Identifier: CC-BY-SA-4.0\n'
  printf ';; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)\n'
  printf ';; GENERATED by scripts/grade-receipt.sh; regenerate with --write, check with --check.\n'
  printf ';; This describes the gate and tree; the CI log is the execution evidence.\n'
  printf '(praxis-deed\n  :schema-version "1.0.0"\n  :canonical-name "secret-types-agda-pwg-receipt"\n'
  printf '  (identity\n    :project "secret-types"\n    :name "agda verification receipt (Proof Witness Grades)"\n'
  printf '    :repository "%s"\n    :repo-uuid #u5"github.com/%s"\n' "$repo" "$repo"
  printf '    :uuid-source "uuid5(URL, github.com/%s)"\n' "$repo"
  printf '    :uuid-note "F-1 remains open: template mint-path cause and local scaffolding sweep; see docs/reports/audit/consistency-audit-2026-11-01.adoc"\n'
  printf '    :kind "theory"\n    :source-commit "%s")\n' "$source_commit"
  printf '  (prover\n    :tool "agda"\n    :version "%s"\n    :provenance "%s"\n' "$agda_version" "$agda_from"
  printf '    :library "none (--no-libraries; Agda builtins only)"\n    :flags "%s"\n' "$flag_line"
  printf '    :flags-source "scripts/proof-flags.sh"\n'
  printf '    :flags-note "One definition, read by the gate and by this receipt; the receipt cannot describe a gate that did not run")\n'
  printf '  (conformance\n    :policy "standards/3-practice/PROOF-POLICY.adoc"\n'
  printf '    :policy-revision "owner ruling 2026-10-26; section 2.1 dated 2026-11-01; section 8 (PWG) dated 2026-11-04"\n'
  printf '    :canonical-invocation "agda --safe --without-K --cubical-compatible"\n'
  printf '    :cubical-compatible "met"\n    :met-since "2026-11-09; W-1 closed, docs/proof-debt.adoc#waivers"\n'
  printf '    :stronger-than-canonical ("--no-libraries" "--ignore-interfaces" "--double-check" "-W error"))\n'
  printf '  (gate\n    :command "bash scripts/check.sh"\n    :laws-certificate "bash scripts/minimal-laws.sh"\n'
  printf '    :ci ".github/workflows/proofs.yml"\n    :module-count %s\n    :reject-fixture-count %s)\n' "$(modules | wc -l | tr -d ' ')" "$(fixtures | wc -l | tr -d ' ')"
  printf '  (trust-base\n    :postulates %s\n    :escape-hatches %s\n' "$(grep -rlw --include='*.agda' postulate src/SecretTypes tests 2>/dev/null | wc -l | tr -d ' ')" "$(escape_hits | wc -l | tr -d ' ')"
  printf '    :library-dependencies 0\n    :axioms-assumed 0\n'
  printf '    :note "A non-zero count above fails the gate; the receipt is only meaningful while all four are zero")\n'
  printf '  ; PWGs apply to theory theorems (PROOF-POLICY section 8.1); refusal fixtures and leak witnesses are n/a.\n'
  printf '  ; Rocq and Lean legs: re-proved by hand (Agda2Dedukti cannot run on the pinned Agda), RECONCILED in verification/legs/README.adoc.\n'
  emit_legs
  printf '  (claims\n'
  while IFS='|' read -r id token grade coq lean; do
    printf '    (claim :id "%s" :token "%s" :pwg "%s" :coq-leg "%s" :lean-leg "%s")\n' "$id" "$token" "$grade" "$coq" "$lean"
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

# A leg counted for a claim must have a row in the correspondence record, and a
# claim with a correspondence row must count its legs: the grade is derived
# from the §2.2 record, not typed beside it (PROOF-POLICY §8.4).
check_leg_records() {
  local rec=verification/legs/README.adoc counted recorded
  counted="$(claims | awk -F'|' '$4=="re-proved"||$5=="re-proved"{print $1}' | LC_ALL=C sort)"
  recorded="$(grep -oE '^\| N-[0-9]+$' "$rec" 2>/dev/null | tr -d '| ' | LC_ALL=C sort -u || true)"
  if [[ "$counted" != "$recorded" ]]; then
    echo "ERROR: claims with a counted leg differ from the rows of $rec" >&2
    diff <(printf '%s\n' "$recorded") <(printf '%s\n' "$counted") \
      | grep -E '^[<>]' | sed "s|^<|  only in $rec:|; s/^>/  only in grade-receipt.sh:/" >&2
    exit 1
  fi
}

check_claim_ids
check_leg_records

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
