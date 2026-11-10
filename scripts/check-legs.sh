#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# check-legs.sh — the Rocq and Lean recheck legs (PROOF-POLICY §2).
#
# Checks verification/legs/rocq (Coq, prelude only) and verification/legs/lean
# (Lean core only, no Mathlib, no `require`), then refuses any axiom:
#   * every `Print Assumptions` line must read "Closed under the global context";
#   * every `#print axioms` line must read "does not depend on any axioms".
# A leg that does not check, or that rests on an axiom, fails this gate: a
# witness with axioms would have to be recorded PROVEN-WITH-AXIOMS and the
# receipt says it is not (PROOF-POLICY §8.4).
#
# Pins: COQ_VERSION and LEAN_VERSION below, fixed (no environment override);
# scripts/grade-receipt.sh reads them from here into the receipt.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"

COQ_VERSION=8.18.0
LEAN_VERSION=4.24.0
fail=0

got="$(coqc --version | sed -n 's/^The Coq Proof Assistant, version \([0-9.]*\).*/\1/p')"
[[ "$got" == "$COQ_VERSION" ]] || { echo "ERROR: expected Coq $COQ_VERSION, found '${got:-none}'" >&2; exit 2; }
got="$(lean --version | sed -n 's/^Lean (version \([0-9.]*\),.*/\1/p')"
[[ "$got" == "$LEAN_VERSION" ]] || { echo "ERROR: expected Lean $LEAN_VERSION, found '${got:-none}'" >&2; exit 2; }

# The Lean leg may not depend on anything: no `require` in the lakefile.
if grep -nE '^\s*\[\[require\]\]|^\s*require\b' verification/legs/lean/lakefile.toml; then
  echo 'FAIL: the Lean leg declares a dependency (no Mathlib, no libraries)' >&2; fail=1
fi
# The Rocq leg may not load the standard library.
if grep -nE '^\s*(From\s+\S+\s+)?Require\b' verification/legs/rocq/*.v; then
  echo 'FAIL: the Rocq leg loads a library (prelude only)' >&2; fail=1
fi
# No escape hatches in either leg.
if grep -nE '\b(sorry|admit|Admitted|Axiom|Parameter|axiom)\b' verification/legs/rocq/*.v verification/legs/lean/SecretTypes/*.lean; then
  echo 'FAIL: an escape hatch in a leg' >&2; fail=1
fi

rocq_out="$(cd verification/legs/rocq && coqc -q SecretTypes.v 2>&1)" || { echo "$rocq_out" >&2; echo 'FAIL: the Rocq leg does not check' >&2; exit 1; }
n_closed="$(grep -c '^Closed under the global context$' <<< "$rocq_out" || true)"
n_print="$(grep -c '^Print Assumptions ' verification/legs/rocq/SecretTypes.v)"
if [[ "$n_closed" != "$n_print" ]] || grep -vq '^Closed under the global context$' <<< "$rocq_out"; then
  echo "$rocq_out" >&2; echo "FAIL: the Rocq leg rests on an axiom ($n_closed of $n_print closed)" >&2; fail=1
else
  echo "PASS: Rocq leg (Coq $COQ_VERSION), $n_print theorems closed under the global context"
fi

lean_out="$(cd verification/legs/lean && lake build >/dev/null && lake env lean Axioms.lean 2>&1)" \
  || { echo "$lean_out" >&2; echo 'FAIL: the Lean leg does not check' >&2; exit 1; }
n_free="$(grep -c 'does not depend on any axioms$' <<< "$lean_out" || true)"
n_ax="$(grep -c '^#print axioms ' verification/legs/lean/Axioms.lean)"
if [[ "$n_free" != "$n_ax" ]] || grep -vq 'does not depend on any axioms$' <<< "$lean_out"; then
  echo "$lean_out" >&2; echo "FAIL: the Lean leg rests on an axiom ($n_free of $n_ax free)" >&2; fail=1
else
  echo "PASS: Lean leg (Lean $LEAN_VERSION, core only), $n_ax theorems depend on no axioms"
fi

(( fail == 0 )) || exit 1
echo 'PASS: both recheck legs'
