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
# below is that default, or strictly stronger; all three default flags are in
# force:
#
#   --safe               policy default.  No postulates, no --type-in-type,
#                        no termination pragmas, no unsafe features.
#   --without-K          policy default.  No UIP, no Streicher K.  (Implied by
#                        --cubical-compatible; kept explicit so the intent
#                        survives a future flag change.)
#   --cubical-compatible policy default.  In force since W-1 closed: the last
#                        clauses that needed constructor injectivity (matching
#                        `refl` against `exec … ≡ just t`) now read the result
#                        through Prelude.just-inj, which matches nothing.  The
#                        gate does NOT suppress -WUnsupportedIndexedMatch, and
#                        -W error makes any return of such a clause fatal: a
#                        planted `refl` match fails the gate (exit 42).
#                        History: docs/proof-debt.adoc#waivers, W-1 (closed).
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

# Print the canonical Agda arguments, one per line, including both parts of -W error.
proof_flags() {
  printf '%s\n' \
    --safe \
    --without-K \
    --cubical-compatible \
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

# The graded root: the one module the gate checks and whose import cone holds
# every theorem.  scripts/check.sh, scripts/check-trusted-base.sh and the
# receipt read it from here.
proof_agda_root() {
  printf '%s\n' 'src/SecretTypes/All.agda'
}

# The gate's Agda invocation, as one line: what scripts/check.sh runs on the
# graded root, and what a receipt records as its :invocation.
proof_agda_invocation() {
  printf 'agda %s -i src %s\n' "$(proof_flags_line)" "$(proof_agda_root)"
}

# The prover's trusted base (PROOF-POLICY §8.4): every postulate in a
# prover-supplied module of the graded root's import cone, as
# module|name|binding.  scripts/check-trusted-base.sh checks that this exact
# list is what the cone holds; the receipt writes it as (trusted-base ...).
# A prover pin bump can change it; then the gate fails until this list is
# updated and the receipt is earned again.
proof_trusted_base() {
  printf '%s\n' \
    'Agda.Primitive|Level|BUILTIN LEVEL' \
    'Agda.Primitive|lzero|BUILTIN LEVELZERO' \
    'Agda.Primitive|lsuc|BUILTIN LEVELSUC' \
    'Agda.Primitive|_⊔_|BUILTIN LEVELMAX'
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  case "${1:-flags}" in
    flags)      proof_flags ;;
    line)       proof_flags_line ;;
    version)    proof_agda_pin ;;
    provenance) proof_agda_provenance ;;
    root)       proof_agda_root ;;
    invocation) proof_agda_invocation ;;
    trusted-base) proof_trusted_base ;;
    *)
      printf 'usage: %s [flags|line|version|provenance|root|invocation|trusted-base]\n' "${0##*/}" >&2
      exit 2
      ;;
  esac
fi
