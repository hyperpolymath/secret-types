#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# check-trusted-base.sh: the prover's trusted base (PROOF-POLICY §8.4).
#
# The import cone of the graded root (scripts/proof-flags.sh, proof_agda_root)
# includes modules that Agda supplies, such as Agda.Primitive.  Some of them
# declare primitives by postulate, and --safe accepts them.  Such a postulate
# is admissible only if the receipt lists it by name with its binding, and the
# gate checks that exact list.  This script is that check:
#   1. run the scanner's controls (tests/trusted-base), so a scanner that
#      stops finding postulates fails here first;
#   2. ask Agda for the cone (--dependency-graph, the gate's own flags);
#   3. scan every prover-supplied module of the cone;
#   4. compare the result, as a set, with proof_trusted_base.
# Any difference fails.  A prover pin bump that changes the list fails here
# until proof_trusted_base is updated and the receipt is earned again.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL=C
. scripts/proof-flags.sh
prover="${AGDA:-agda}"
scan=scripts/scan-agda-postulates.awk
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT

# 1. Controls.  Positive and comment-only fixtures must give their expected
# lists; the refusal fixtures must be refused (exit 3), never passed.
for f in tests/trusted-base/*.txt; do
  name="$(basename -- "$f" .txt)"
  set +e; awk -v "module=Fixture.$name" -f "$scan" "$f" > "$work/$name.out" 2> "$work/$name.err"; rc=$?; set -e
  if [[ -f "tests/trusted-base/$name.expected" ]]; then
    if (( rc != 0 )) || ! diff -u "tests/trusted-base/$name.expected" "$work/$name.out"; then
      cat "$work/$name.err" >&2
      echo "FAIL: scanner control $name (rc=$rc)" >&2; exit 1
    fi
  elif (( rc != 3 )); then
    cat "$work/$name.out" >&2
    echo "FAIL: scanner control $name was not refused (rc=$rc)" >&2; exit 1
  fi
done
echo "PASS: scanner controls ($(ls tests/trusted-base/*.txt | wc -l | tr -d ' ') fixtures)"

# 2. The cone, as Agda reports it under the gate's flags.
mapfile -t flags < <(proof_flags)
"$prover" "${flags[@]}" -i src --dependency-graph="$work/cone.dot" "$(proof_agda_root)" > "$work/agda.log" 2>&1 \
  || { cat "$work/agda.log" >&2; echo 'FAIL: agda could not produce the dependency graph' >&2; exit 1; }
mapfile -t cone < <(sed -n 's/.*label="\([^"]*\)".*/\1/p' "$work/cone.dot" | sort -u)
(( ${#cone[@]} > 0 )) || { echo 'FAIL: empty dependency graph' >&2; exit 1; }
agda_dir="$("$prover" --print-agda-dir)"

# The repository's part of the cone is the Agda input set of the receipt
# (PROOF-POLICY §8.5.1).  scripts/grade-receipt.sh computes it by a text scan
# of import statements; it must be exactly the set Agda reports.
for m in "${cone[@]}"; do
  rel="src/${m//.//}.agda"
  [[ -f "$rel" ]] && printf '%s\n' "$rel"
done | LC_ALL=C sort > "$work/cone-repo"
bash scripts/grade-receipt.sh --inputs agda > "$work/cone-scan"
if ! diff -u "$work/cone-repo" "$work/cone-scan"; then
  echo 'FAIL: the Agda input set of scripts/grade-receipt.sh differs from the cone agda --dependency-graph reports' >&2
  exit 1
fi
echo "PASS: Agda input set ($(wc -l < "$work/cone-repo" | tr -d ' ') repository modules) equals the cone Agda reports"

# 3. Scan the prover-supplied modules.  Every module of the cone is either the
# development's (under src/) or Agda's (under the prover's lib/prim); a module
# in neither place fails, so nothing in the cone goes unscanned.
supplied=0
: > "$work/found"
for m in "${cone[@]}"; do
  rel="${m//.//}.agda"
  if [[ -f "src/$rel" ]]; then continue; fi
  path="$agda_dir/lib/prim/$rel"
  [[ -f "$path" ]] || { echo "FAIL: module $m of the cone is neither under src/ nor under $agda_dir/lib/prim" >&2; exit 1; }
  supplied=$((supplied + 1))
  awk -v "module=$m" -f "$scan" "$path" >> "$work/found"
done

# 4. Compare with the declared list.
sort -u "$work/found" > "$work/found.sorted"
proof_trusted_base | sort -u > "$work/declared.sorted"
if ! diff -u "$work/declared.sorted" "$work/found.sorted" > "$work/diff"; then
  cat "$work/diff" >&2
  echo 'FAIL: the prover-supplied postulates of the cone differ from proof_trusted_base (scripts/proof-flags.sh)' >&2
  exit 1
fi
echo "PASS: trusted base: $(wc -l < "$work/found.sorted" | tr -d ' ') prover postulates in $supplied prover-supplied modules of the cone, each BUILTIN-bound and listed; no other postulate"
