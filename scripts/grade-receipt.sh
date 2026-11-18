#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# grade-receipt.sh: the proof receipt of this repository,
# verification/receipts/agda_praxis.deed, in the shape of
# standards/3-practice/PROOF-POLICY.adoc §8.5.1 and §8.5.2 (profile
# proof-receipt), with the git checks of §8.5.3.
#
# This script holds what is this repository's: the three ledgers below, the
# header of the receipt, and the hooks that name each leg's invocation and
# inputs.  The generator and gate are standards' scripts/proof-receipt.sh,
# fetched with the reader, the reference digest and the shared git checker at
# ONE pinned standards commit, each file checked against its sha256.
#
#   --fetch-reader       fetch the four pinned standards files into _build/
#   --write | --check | --digest P | --inputs P | --run-row P ... | --emit-run ROWS --out FILE
#                        the modes of proof-receipt.sh (see its header)
#
# What is derived and what is typed.  Three lists are typed in this file: the
# claim list (cross-checked against PROOF-STATUS.adoc and
# verification/legs/README.adoc), the run ledger (each row copied from the CI
# log that printed it) and the echo ledger (history rewrites).  Everything else
# is read from the one definition the gate also reads: the flags, the root, the
# invocation and the trusted base from scripts/proof-flags.sh; the leg
# invocations and pins from scripts/check-legs.sh.  Every digest is a git fact.
# The grade is never typed: the generator derives it under §8.2 and §8.5.2 and
# the pinned reader derives it again, refusing a receipt whose :pwg its legs
# and receipts do not support (§8.4).
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL=C.UTF-8
. scripts/proof-flags.sh

RECEIPT_OUT=verification/receipts/agda_praxis.deed
RECEIPT_REPOSITORY="hyperpolymath/secret-types"
RECEIPT_DEFAULT_BRANCH=main
RECEIPT_CANONICAL_NAME="secret-types-proof-receipt"
RECEIPT_SCRIPT=scripts/grade-receipt.sh

# The pinned standard, all at one standards commit, each file with its
# sha256: the generator (scripts/proof-receipt.sh), the reader readProofReceipt
# (1-formats/deed/tools/deed_lint.js), the reference digest
# (scripts/proof-inputs-sha256.sh) and the shared git checker of §8.5.3
# (scripts/check-proof-receipt.sh).  They keep the standards layout under
# _build/standards, because the checker finds the reader and the digest
# script by their paths.  Mathesis pins the same reader and runs the same
# checker.
RECEIPT_STANDARDS_COMMIT="${RECEIPT_STANDARDS_COMMIT_OVERRIDE:-4813fa1092a38a6782e722ede5b09ce79e92fba3}"
GENERATOR_SHA256=47e9e5596e69574440260e4372c4b400f6c5f97192ff04292a59bffc4c215fe8
READER_SHA256=29278b46654bdee70e8e1ff4a7ff8cb810e04b618c9ca1520a6979d6c4c91f18
DIGEST_SHA256=dfc6dde01a3a79df638eebe4cad0eae584d8f17280077e149174c0667e9508f4
CHECKER_SHA256=f2375747238464535d1b4a61f658f07cb2f8504c69bfb1812311c79429a4e23e
RECEIPT_STD="${RECEIPT_STD_OVERRIDE:-_build/standards}"

pinned_files() {
  printf '%s %s\n' scripts/proof-receipt.sh "$GENERATOR_SHA256" \
    1-formats/deed/tools/deed_lint.js "$READER_SHA256" \
    scripts/proof-inputs-sha256.sh "$DIGEST_SHA256" \
    scripts/check-proof-receipt.sh "$CHECKER_SHA256"
}
fetch_pinned() {
  local path sum dest raw="https://raw.githubusercontent.com/metadatastician/standards/$RECEIPT_STANDARDS_COMMIT"
  while read -r path sum; do
    dest="$RECEIPT_STD/$path"; mkdir -p "$(dirname "$dest")"
    curl --proto '=https' --tlsv1.2 -fsSL "$raw/$path" -o "$dest.tmp"
    echo "$sum  $dest.tmp" | sha256sum --check --strict >/dev/null || { rm -f "$dest.tmp"; printf 'ERROR: the fetched %s does not match its pinned sha256\n' "$path" >&2; exit 1; }
    mv "$dest.tmp" "$dest"; printf 'FETCHED %s (standards %s) to %s\n' "$path" "${RECEIPT_STANDARDS_COMMIT:0:12}" "$dest"
  done < <(pinned_files)
}
check_pinned() {
  local path sum
  while read -r path sum; do
    [[ -f "$RECEIPT_STD/$path" ]] || { printf 'ERROR: the pinned %s is missing: run bash %s --fetch-reader\n' "$path" "$RECEIPT_SCRIPT" >&2; exit 1; }
    [[ "$(sha256sum "$RECEIPT_STD/$path" | cut -d' ' -f1)" == "$sum" ]] || { printf 'ERROR: %s is not the pinned file (sha256 differs)\n' "$RECEIPT_STD/$path" >&2; exit 1; }
  done < <(pinned_files)
}

# ── The claim list ────────────────────────────────────────────────────────────
# id | §5 token of the Agda proof | kind | Rocq route | Rocq §2.2 state |
# Lean route | Lean §2.2 state | Rocq reason | Lean reason.  A waived or
# unavailable leg carries a reason and no token, state or receipt (§8.5.1);
# the reason columns stay empty for any other route.  Kind is theorem
# (graded, §8.1) or demonstration (a checked example; §8.1 grades theorems
# only, so a demonstration has no claim in the receipt).  Routes: transported
# | re-proved | waived | unavailable.  States: §2.2; only RECONCILED counts.
receipt_claims() {
  cat <<'ROWS'
N-1|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
N-2|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
N-3|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
N-4|tested-only|demonstration|n/a|n/a|n/a|n/a||
N-5|tested-only|demonstration|n/a|n/a|n/a|n/a||
N-6|tested-only|demonstration|n/a|n/a|n/a|n/a||
N-7|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
N-8|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
N-9|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED||
ROWS
}

# ── The run ledger ────────────────────────────────────────────────────────────
# One row per checker run, copied from the log of the run that printed it
# (the receipt job of .github/workflows/proofs.yml prints the rows of its own
# run).  One run of a leg checks every theorem, so each row is a receipt of
# that leg for every claim.
# prover | run | commit (40 hex) | checker | invocation | inputs sha256 |
# what the run reported | state (current|superseded|regressed) | reason |
# axioms
# The inputs sha256 of a current row is the §8.5.1 digest at the row's
# commit; --check computes it again with the reference script (§8.5.3).  A
# row that is not current keeps the digest its run printed, which may predate
# §8.5.1, and the receipt does not state it.  The axioms column lists each
# axiom the checker reported as name:disposition, comma-separated; it is
# empty when the checker reported none, and the gates fail on any axiom.
# An Agda row then carries an imports field (empty here: this repository
# imports no other) and the sha256 of the trusted base the run checked
# (PROOF-POLICY 8.4), which --run-row writes.  The current Agda row was
# recorded before the shared generator wrote that field.  Its value is the
# sha256 of proof_trusted_base in scripts/proof-flags.sh at the run's own
# commit 7dfeab2, the list the run's trusted-base gate checked the cone
# against (its reported column); that list is unchanged since.
receipt_runs() {
  cat <<'ROWS'
agda|https://github.com/hyperpolymath/secret-types/actions/runs/43455458225/attempts/1|7dfeab2dc13142fac476ee9c698cf009deb709c9|Agda version 2.6.4.3 (Debian 13 agda-bin=2.6.4.3-1+b2, container debian:13-slim)|agda --safe --without-K --cubical-compatible --no-libraries --ignore-interfaces --double-check -W error -i src src/SecretTypes/All.agda|96b2f0237fcc31a0ab60cc6952edbe4e9c1b3ca5f267d79bf6491f81432b0c9e|--safe; trusted base (no postulates under src/SecretTypes or tests); trusted base: 4 prover postulates in 6 prover-supplied modules of the cone, each BUILTIN-bound and listed; no other postulate|current||||0c1f64c3c7f0a26cbc92595168858485a9883f6196d287497dcc805faf5c58eb
rocq|https://github.com/hyperpolymath/secret-types/actions/runs/43455458225/attempts/1|7dfeab2dc13142fac476ee9c698cf009deb709c9|The Coq Proof Assistant, version 8.18.0 (Ubuntu 24.04 coq=8.18.0+dfsg-1build2)|coqc -q SecretTypes.v (in verification/legs/rocq)|4c96fb9c7d22685ae08d71fc2f200e394e93f07711b2b0619d2a154dbd19bc60|Rocq leg (Coq 8.18.0), 11 theorems closed under the global context|current||
lean|https://github.com/hyperpolymath/secret-types/actions/runs/43455458225/attempts/1|7dfeab2dc13142fac476ee9c698cf009deb709c9|Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release) (release tarball, sha256 b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec)|lake build; lake env lean Axioms.lean (in verification/legs/lean)|7ed75659e1520a28b949c7b004609485605f1b9e017b810352be4285390a13d6|Lean leg (Lean 4.24.0, core only), 11 theorems depend on no axioms|current||
agda|https://github.com/hyperpolymath/secret-types/actions/runs/43448301280/attempts/1|88a763ac6101b8d9e59c71caa6959abb4bffe4bd|Agda version 2.6.4.3 (Debian 13 agda-bin=2.6.4.3-1+b2, container debian:13-slim)|agda --safe --without-K --cubical-compatible --no-libraries --ignore-interfaces --double-check -W error -i src src/SecretTypes/All.agda|a0a8d66d74bf9deb5beeba6739c377290ce7399cf8ef60dc6214da211d086cb4|--safe; trusted base (no postulates under src/SecretTypes or tests); trusted base: 4 prover postulates in 6 prover-supplied modules of the cone, each BUILTIN-bound and listed; no other postulate|superseded|the inputs of the Agda leg changed after this run (scanner hardening from review); the CI run of the hardened commit replaces it|
rocq|https://github.com/hyperpolymath/secret-types/actions/runs/43448301280/attempts/1|88a763ac6101b8d9e59c71caa6959abb4bffe4bd|The Coq Proof Assistant, version 8.18.0 (Ubuntu 24.04 coq=8.18.0+dfsg-1build2)|coqc -q SecretTypes.v (in verification/legs/rocq)|88cee666f75f94eea702abe967a25c10d3958988012da1300847c5c0a1372129|Rocq leg (Coq 8.18.0), 11 theorems closed under the global context|superseded|replaced by the later run https://github.com/hyperpolymath/secret-types/actions/runs/43455458225/attempts/1|
lean|https://github.com/hyperpolymath/secret-types/actions/runs/43448301280/attempts/1|88a763ac6101b8d9e59c71caa6959abb4bffe4bd|Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release) (release tarball, sha256 b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec)|lake build; lake env lean Axioms.lean (in verification/legs/lean)|d30ae3c6563e34c78ef98de43d52e9eebcedac1714c8e2be06c413871c6ac6ac|Lean leg (Lean 4.24.0, core only), 11 theorems depend on no axioms|superseded|replaced by the later run https://github.com/hyperpolymath/secret-types/actions/runs/43455458225/attempts/1|
agda|local run, 2026-11-12, Claude Code cloud container (Ubuntu 24.04)|eaa7e975ca7beb0a304c39704cc9bc6d88d46b83|Agda version 2.6.4.3 (Debian 13 agda-bin=2.6.4.3-1+b2, .deb unpacked on Ubuntu 24.04)|agda --safe --without-K --cubical-compatible --no-libraries --ignore-interfaces --double-check -W error -i src src/SecretTypes/All.agda|22d8e74d66d65909af1862a92d10ce8d460a2012f392ec604b759c4fb2fcd72d|--safe; trusted base (no postulates under src/SecretTypes or tests); the import cone was not yet gated at this commit|superseded|local run outside CI, kept as lineage only; replaced by the CI run https://github.com/hyperpolymath/secret-types/actions/runs/43448301280/attempts/1|
rocq|local run, 2026-11-12, Claude Code cloud container (Ubuntu 24.04)|eaa7e975ca7beb0a304c39704cc9bc6d88d46b83|The Coq Proof Assistant, version 8.18.0 (Ubuntu 24.04 coq=8.18.0+dfsg-1build2)|coqc -q SecretTypes.v (in verification/legs/rocq)|8cdb209c928d2c63a73366e9c11d51ad2a799fd123d8a2c51379a4ca666b4b24|Rocq leg (Coq 8.18.0), 11 theorems closed under the global context|superseded|local run outside CI, kept as lineage only; replaced by the CI run https://github.com/hyperpolymath/secret-types/actions/runs/43448301280/attempts/1|
lean|local run, 2026-11-12, Claude Code cloud container (Ubuntu 24.04)|eaa7e975ca7beb0a304c39704cc9bc6d88d46b83|Lean (version 4.24.0, x86_64-unknown-linux-gnu, commit 797c613eb9b6d4ec95db23e3e00af9ac6657f24b, Release) (release tarball, sha256 b14f5e5159219dd1a1956c3b806813319f5e94ccd5bdfd56f54520609a5bb5ec)|lake build; lake env lean Axioms.lean (in verification/legs/lean)|a4616dcb6de917279eab73cf53d6ac39584a09c71a22ff3624b825c61638dc96|Lean leg (Lean 4.24.0, core only), 11 theorems depend on no axioms|superseded|local run outside CI, kept as lineage only; replaced by the CI run https://github.com/hyperpolymath/secret-types/actions/runs/43448301280/attempts/1|
ROWS
}

# ── The echo ledger (§8.5.2) ──────────────────────────────────────────────────
# One row per history rewrite of a commit that a receipt names: the commit
# before the rewrite (source), the commit on the default branch that replaced
# it (image), the witness, and the forge reference that keeps the source
# reachable.  The witness digests are not typed: --write and --check compute
# them at both commits and refuse the row unless they are equal.
# source (40 hex) | image (40 hex) | witness (inputs-sha256) | fetch ref
receipt_echoes() {
  cat <<'ROWS'
7dfeab2dc13142fac476ee9c698cf009deb709c9|292d566a81a9bafcd6bdf7f3caab7fc2ebad36bd|inputs-sha256|refs/pull/40/head
ROWS
}


# ── Hooks of the generator ───────────────────────────────────────────────────
receipt_header() {
  printf ';; SPDX-License-Identifier: CC-BY-SA-4.0\n'
  printf ';; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)\n'
  printf ';; The proof receipt of secret-types (PROOF-POLICY §8.5.1, §8.5.2).\n'
  printf ';; GENERATED by scripts/grade-receipt.sh: regenerate with --write, check with --check.\n'
  printf ';; Each (receipt ...) is a row of the run ledger in that script, copied from\n'
  printf ';; the CI log that printed it.  Every digest is computed from git objects and\n'
  printf ';; checked with the reference script of the standard.  The grade is derived,\n'
  printf ';; never typed:\n'
  printf ';;   bun deed_lint.js --proof-receipt-json verification/receipts/agda_praxis.deed\n'
  printf ';; with the reader at standards %s.\n' "$RECEIPT_STANDARDS_COMMIT"
  printf ';; Demonstrations N-4, N-5 and N-6 are not theorems (§8.1) and have no claim here.\n'
  printf ';; The trusted base is what scripts/check-trusted-base.sh finds in the\n'
  printf ';; prover-supplied modules of the import cone of %s.\n' "$(proof_agda_root)"
}
receipt_trusted_base() { proof_trusted_base; }
# The legs' invocations, read from their one definition.
legvar() { local name="$1"; sed -n "s/^$name='\\{0,1\\}\\([^']*\\)'\\{0,1\\}\$/\\1/p" scripts/check-legs.sh; }
receipt_invocation() {
  case "$1" in
    agda) proof_agda_invocation ;;
    rocq) printf '%s (in %s)\n' "$(legvar ROCQ_INVOCATION)" "$(legvar ROCQ_DIR)" ;;
    lean) printf '%s; %s (in %s)\n' "$(legvar LEAN_BUILD)" "$(legvar LEAN_AXIOMS)" "$(legvar LEAN_DIR)" ;;
    *) receipt_die "unknown prover: $1" ;;
  esac
}
# The input set of one leg (§8.5.1): Agda, the cone of the graded root under
# src (scripts/check-trusted-base.sh checks the scan against
# agda --dependency-graph); Rocq, the file the invocation compiles; Lean, every
# tracked .lean file of the leg and the lakefile, toolchain and manifest that
# exist.
receipt_inputs() {
  local dir
  case "$1" in
    agda) receipt_agda_cone "$(proof_agda_root)" src ;;
    rocq) dir="$(legvar ROCQ_DIR)"; printf '%s/%s\n' "$dir" "$(legvar ROCQ_INVOCATION | awk '{print $NF}')" ;;
    lean) dir="$(legvar LEAN_DIR)"
          git ls-files -- "$dir" | grep -E '(\.lean|/lakefile\.(lean|toml)|/lean-toolchain|/lake-manifest\.json)$' ;;
    *) receipt_die "unknown prover: $1" ;;
  esac
}
receipt_status_ids() { grep -oE '^\| N-[0-9]+ ' PROOF-STATUS.adoc | tr -d '| ' || true; }
receipt_recorded_legs() { grep -oE '^\| N-[0-9]+$' verification/legs/README.adoc 2>/dev/null | tr -d '| ' || true; }

case "${1:-}" in
  -h|--help) sed -n '5,19p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
  --fetch-reader) fetch_pinned; exit 0 ;;
esac
check_pinned
. "$RECEIPT_STD/scripts/proof-receipt.sh"
receipt_main "$@"
