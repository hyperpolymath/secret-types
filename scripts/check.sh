#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Core proofs plus expected rejections.  Pattern: residual-evidence-types,
# choreographic-types.
#
# Every check runs with --ignore-interfaces (no stale .agdai can stand in for
# a proof), --double-check (the kernel re-verifies every term) and -W error
# (a warning is a failure).  The development uses Agda builtins only.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"
prover="${AGDA:-agda}"
expected_version="${AGDA_VERSION:-2.6.4.3}"

version="$("$prover" --version)"
echo "$version"
if [ "$version" != "Agda version $expected_version" ]; then
  echo "ERROR: expected 'Agda version $expected_version' (the Debian pin); set AGDA_VERSION to check with another" >&2
  exit 1
fi

# 0. Trusted base: nothing under src/SecretTypes or tests may postulate.
if stray="$(grep -rlw --include='*.agda' postulate src/SecretTypes tests)"; then
  echo "ERROR: postulate in the trusted base:" >&2
  echo "$stray" >&2
  exit 1
fi
echo 'PASS: trusted base (no postulates under src/SecretTypes or tests)'

flags=(--safe --without-K --no-libraries --ignore-interfaces --double-check -W error -i src)
"$prover" "${flags[@]}" src/SecretTypes/All.agda
echo 'PASS: core proofs (SecretTypes.All, builtins only)'

# Expected rejections: each fixture must fail AT its `invalid` declaration
# with a type mismatch, never for a missing import or a parse error.
mkdir -p _build/check-logs
shopt -s nullglob
rejects=(tests/reject/*.agda)
shopt -u nullglob
if (( ${#rejects[@]} == 0 )); then
  echo 'ERROR: no expected-rejection modules found under tests/reject' >&2
  exit 1
fi
for file in "${rejects[@]}"; do
  name="$(basename -- "$file" .agda)"
  log="_build/check-logs/$name.log"
  if "$prover" "${flags[@]}" -i tests/reject "$file" >"$log" 2>&1; then
    cat "$log"
    echo "ERROR: invalid proof accepted: $name" >&2
    exit 1
  fi
  invalid_line="$(grep -nE '^invalid ' "$file" | head -1 | cut -d: -f1)"
  diag_line="$(grep -oE "/$name\.agda:[0-9]+,[0-9]+" "$log" | head -1 | sed -E 's/.*:([0-9]+),.*/\1/')"
  if [ -z "$invalid_line" ] || [ -z "$diag_line" ] || [ "$diag_line" -lt "$invalid_line" ] ||
     ! grep -q 'when checking that' "$log" ||
     grep -Eq 'Not in scope|Failed to find|Unsolved|Parse error' "$log"; then
    cat "$log"
    echo "ERROR: unexpected failure while checking $name" >&2
    exit 1
  fi
  echo "PASS: rejected $name at its invalid declaration"
done
echo "PASS: core proofs and all ${#rejects[@]} expected rejections"
