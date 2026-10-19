#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Certifies which laws generic TINI depends on (PROOF-STATUS N-6).
# Pattern: choreographic-types scripts/minimal-laws.sh (K-4).
#
#  1. Sufficiency: SecretTypes.Noninterference.Generic typechecks against
#     tests/minimal-laws, a SecretTypes.Lattice.Record whose Lattice has only
#     ⊔-upper₁ and ⊔-upper₂ and whose Observer has only down-closure.  If this
#     passes, the proof uses no other law: not ⊑-trans, not decidability, not
#     ⊥ ⊑ x, reflexivity, antisymmetry, leastness of ⊔ or a top.
#  2. No drift: every field line of that record appears verbatim in the real
#     one, and the real Lattice adds exactly ⊑-trans (used only by
#     `principal`).
#  3. Negative control: deleting any one census field makes step 1 fail,
#     and fail on that field.
# That each census law is also semantically necessary (drop it and a
# well-typed program leaks) is SecretTypes.Countermodels, in the core gate.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL="${LC_ALL:-C.UTF-8}"
prover="${AGDA:-agda}"
real=src/SecretTypes/Lattice/Record.agda
minimal=tests/minimal-laws/SecretTypes/Lattice/Record.agda
census=(⊔-upper₁ ⊔-upper₂ sees-↓)
flags=(--safe --without-K --no-libraries --ignore-interfaces --double-check -W error)
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT

# fields <file> <record>: the field declaration lines of one record.
fields() {
  local file="$1" rec="$2"
  awk -v rec="$rec" '
    $0 ~ "^record " rec " " { inrec = 1; next }
    inrec && /^[^ ]/        { inrec = 0 }
    inrec && /^  field$/    { infield = 1; next }
    inrec && infield && /^    [^ ]+ +: / { print; next }
    inrec && infield        { infield = 0 }
  ' "$file"
}

# stage <record file>: a copy of src/SecretTypes with that Lattice.Record.
stage() {
  local record="$1"
  rm -rf "$tmp/src"; mkdir -p "$tmp/src"
  (cd src && find SecretTypes -name '*.agda' -exec cp --parents {} "$tmp/src" \;)
  cp "$record" "$tmp/src/SecretTypes/Lattice/Record.agda"
}

# 2. No drift.
for rec in Lattice Observer; do
  if [ -z "$(fields "$minimal" "$rec")" ]; then
    echo "ERROR: no fields of $rec found in $minimal" >&2; exit 1
  fi
  if missing="$(fields "$minimal" "$rec" | grep -vxF -f <(fields "$real" "$rec"))"; then
    echo "ERROR: census field(s) of $rec not declared verbatim in $real:" >&2
    echo "$missing" >&2; exit 1
  fi
done
extra="$(fields "$real" Lattice | grep -vxF -f <(fields "$minimal" Lattice) | awk '{print $1}' | tr '\n' ' ')"
if [ "$extra" != "⊑-trans " ]; then
  echo "ERROR: the real Lattice should add exactly ⊑-trans to the census, adds: ${extra:-nothing}" >&2
  exit 1
fi
if [ "$(fields "$real" Observer)" != "$(fields "$minimal" Observer)" ]; then
  echo "ERROR: the real Observer differs from the census Observer" >&2; exit 1
fi
echo 'PASS: census record matches the real record (which adds only ⊑-trans)'

# 1. Sufficiency.
stage "$minimal"
"$prover" "${flags[@]}" -i "$tmp/src" "$tmp/src/SecretTypes/Noninterference/Generic.agda"
echo "PASS: generic TINI typechecks with only ${census[*]}"

# 3. Negative control: each census field is used.
for law in "${census[@]}"; do
  ablated="$tmp/ablated.agda"
  grep -v -E "^    $law +: " "$minimal" > "$ablated"
  if cmp -s "$ablated" "$minimal"; then
    echo "ERROR: could not remove $law from $minimal" >&2; exit 1
  fi
  stage "$ablated"
  log="$tmp/$law.log"
  if "$prover" "${flags[@]}" -i "$tmp/src" "$tmp/src/SecretTypes/Noninterference/Generic.agda" >"$log" 2>&1; then
    cat "$log"
    echo "ERROR: generic TINI still typechecks without $law: the census over-claims" >&2
    exit 1
  fi
  if ! grep -q 'Not in scope' "$log" || ! grep -qF "$law" "$log"; then
    cat "$log"
    echo "ERROR: removing $law failed for another reason" >&2
    exit 1
  fi
  echo "PASS: without $law generic TINI is refused (Not in scope: $law)"
done
echo "PASS: minimal-laws certificate (${#census[@]} laws, each needed)"
