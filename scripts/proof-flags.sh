#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# The canonical Agda flag set for this repository — ONE definition, used by
# scripts/check.sh, scripts/minimal-laws.sh and scripts/grade-receipt.sh.
#
# Why this file exists: a flag set that is written out in three places drifts,
# and a drifted flag set means the receipt describes a gate that did not run.
# The receipt records these exact flags, so the gate and the receipt cannot
# disagree.
#
# Conformance: standards/3-practice/PROOF-POLICY.adoc §2.1 (2026-11-01) sets
#   agda --safe --without-K --cubical-compatible <module.agda>
# as the estate default for first-party Agda theory entrypoints.  Every flag
# below is that default, or strictly stronger:
#
#   --safe               policy default.  No postulates, no --type-in-type,
#                        no termination pragmas, no unsafe features.
#   --without-K          policy default.  No UIP, no Streicher K.  (Implied by
#                        --cubical-compatible; kept explicit so the intent
#                        survives a future flag change.)
#   --cubical-compatible WAIVED, not dropped silently.  PROOF-POLICY §2.1
#                        (2026-11-01) names it; this development cannot meet it
#                        yet.  Evidence and the two arms are in
#                        docs/proof-debt.adoc#waivers and PROOF-STATUS.adoc
#                        "Grade and the independent-witness legs".  The short
#                        version: every clause matching on `_⊑_` is an indexed
#                        match, which Cubical Agda does not support
#                        (-WUnsupportedIndexedMatch), and -W error makes that
#                        fatal.  Suppressing the warning would be a green gate
#                        over a weakened check, so the flag is absent and the
#                        gap is recorded instead.
#   --no-libraries       stronger.  Builtins only; no Agda standard library and
#                        no sibling repository is on the path.  The policy's
#                        "no Mathlib" rule (PROOF-POLICY §2) is the Lean form of
#                        this; --no-libraries makes the Agda form checkable.
#   --ignore-interfaces  stronger.  A stale .agdai can never stand in for a
#                        proof: every module is re-typechecked from source.
#   --double-check       stronger.  The kernel re-verifies every term the
#                        typechecker produced.
#   -W error             stronger.  A warning is a failure, so a deprecation or
#                        a coverage warning cannot be absorbed silently.
#
# Dropping or weakening any flag requires a recorded owner decision and a new
# receipt; the receipt's [prover] block is generated from this file, so the two
# cannot disagree.
#
# Relation to the per-module pragmas: each module declares
#   {-# OPTIONS --safe --without-K #-}
# which are inherent to the source, not properties of the invocation.  The
# canonical invocation ADDS the rest, so a module checked by hand is weaker than
# the same module checked by the gate.  That asymmetry is deliberate: the gate is
# the only place a claim may come from, and PROOF-STATUS names the gate.

proof_flags() {
  printf '%s\n' \
    --safe \
    --without-K \
    --no-libraries \
    --ignore-interfaces \
    --double-check \
    -W error
}

# The flags as one line, for prose records and receipts.
proof_flags_line() {
  proof_flags | paste -sd ' ' -
}

# The exact Agda version this repository pins.  Debian 13's agda-bin package;
# keep in step with .github/workflows/proofs.yml.
proof_agda_pin() {
  printf '%s\n' '2.6.4.3'
}

# Human-readable summary of what the pin includes.
proof_agda_provenance() {
  printf '%s\n' 'Debian 13 agda-bin=2.6.4.3-1+b2'
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  case "${1:-flags}" in
    flags)      proof_flags ;;
    line)       proof_flags_line ;;
    version)    proof_agda_pin ;;
    provenance) proof_agda_provenance ;;
    *)
      printf 'usage: %s [flags|line|version|provenance]\n' "${0##*/}" >&2
      exit 2
      ;;
  esac
fi
