#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# grade-receipt.sh: the proof receipt of this repository,
# verification/receipts/agda_praxis.deed, in the shape of
# standards/3-practice/PROOF-POLICY.adoc §8.5.1 and §8.5.2 (profile
# proof-receipt), with the git checks of §8.5.3.
#
#   --write              write the receipt from the tree and the ledgers
#   --check              regenerate it, refuse any difference, do the git
#                        checks of §8.5.3, check that each current receipt
#                        still describes the tree, and run the pinned reader
#                        with a negative control
#   --digest PROVER      print the §8.5.1 inputs digest of one leg (agda|rocq|lean)
#   --inputs PROVER      print the §8.5.1 input set of one leg, one path a line
#   --run-row PROVER --run URL --commit SHA --checker TEXT --reported TEXT
#                        print one ledger row for a run that just passed
#   --emit-run ROWS --out FILE
#                        write a receipt for the run whose rows are in ROWS:
#                        they become current, and the earlier current receipts
#                        of the same legs become superseded (CI does this)
#   --fetch-reader       fetch the pinned reader and the pinned reference
#                        digest script into _build/ and check both
#
# What is derived and what is typed.  Three lists are typed in this file: the
# claim list (cross-checked against PROOF-STATUS.adoc and
# verification/legs/README.adoc), the run ledger (each row copied from the CI
# log that printed it) and the echo ledger (history rewrites).  Everything else
# is read from the one definition the gate also reads: the flags, the root, the
# invocation and the trusted base from scripts/proof-flags.sh; the leg
# invocations and pins from scripts/check-legs.sh.  Every digest is a git fact:
# this script computes it, and the pinned reference script of the standard
# checks it.  The grade is never typed: it is derived here under §8.2 and
# §8.5.2 and derived again by the pinned reader, which refuses a receipt whose
# :pwg its legs and receipts do not support (§8.4).
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL=C.UTF-8
. scripts/proof-flags.sh

out=verification/receipts/agda_praxis.deed
repo="hyperpolymath/secret-types"
default_branch=main

# The pinned standard: readProofReceipt in 1-formats/deed/tools/deed_lint.js
# (PROOF-POLICY §8.5.1 to §8.5.3) and the reference digest
# scripts/proof-inputs-sha256.sh, both at one standards commit, each with its
# sha256.  Mathesis pins the same reader.
STANDARDS_COMMIT=d9b03a30e9570e1ffc05f16a580ab0f7a7e6fec6
READER_SHA256=c06de71c26dca57e81c17dbe4998ec99dd73035e773f7b6f92b819e96559853a
DIGEST_SHA256=dfc6dde01a3a79df638eebe4cad0eae584d8f17280077e149174c0667e9508f4
STANDARDS_RAW="https://raw.githubusercontent.com/metadatastician/standards/$STANDARDS_COMMIT"
reader="${DEED_LINT:-_build/deed_lint.js}"
digest_script="${PROOF_INPUTS_SHA256:-_build/proof-inputs-sha256.sh}"

# ── The claim list ────────────────────────────────────────────────────────────
# id | §5 token of the Agda proof | kind | Rocq route | Rocq §2.2 state |
# Lean route | Lean §2.2 state | Rocq reason | Lean reason.  A waived or
# unavailable leg carries a reason and no token, state or receipt (§8.5.1);
# the reason columns stay empty for any other route.  Kind is theorem
# (graded, §8.1) or demonstration (a checked example; §8.1 grades theorems
# only, so a demonstration has no claim in the receipt).  Routes: transported
# | re-proved | waived | unavailable.  States: §2.2; only RECONCILED counts.
claims() {
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
runs() {
  cat <<'ROWS'
agda|https://github.com/hyperpolymath/secret-types/actions/runs/43455458225/attempts/1|7dfeab2dc13142fac476ee9c698cf009deb709c9|Agda version 2.6.4.3 (Debian 13 agda-bin=2.6.4.3-1+b2, container debian:13-slim)|agda --safe --without-K --cubical-compatible --no-libraries --ignore-interfaces --double-check -W error -i src src/SecretTypes/All.agda|96b2f0237fcc31a0ab60cc6952edbe4e9c1b3ca5f267d79bf6491f81432b0c9e|--safe; trusted base (no postulates under src/SecretTypes or tests); trusted base: 4 prover postulates in 6 prover-supplied modules of the cone, each BUILTIN-bound and listed; no other postulate|current||
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
echoes() {
  cat <<'ROWS'
7dfeab2dc13142fac476ee9c698cf009deb709c9|292d566a81a9bafcd6bdf7f3caab7fc2ebad36bd|inputs-sha256|refs/pull/40/head
ROWS
}

die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }

# ── Inputs of each leg (§8.5.1) ───────────────────────────────────────────────
# The legs' invocations, read from their one definition.
legvar() { local name="$1"; sed -n "s/^$name='\\{0,1\\}\\([^']*\\)'\\{0,1\\}\$/\\1/p" scripts/check-legs.sh; }
invocation() {
  local prover="$1"
  case "$prover" in
    agda) proof_agda_invocation ;;
    rocq) printf '%s (in %s)\n' "$(legvar ROCQ_INVOCATION)" "$(legvar ROCQ_DIR)" ;;
    lean) printf '%s; %s (in %s)\n' "$(legvar LEAN_BUILD)" "$(legvar LEAN_AXIOMS)" "$(legvar LEAN_DIR)" ;;
    *) die "unknown prover: $prover" ;;
  esac
}

# The Agda cone: the graded root and every module of the repository that it
# imports, directly or not (include path src, as the invocation says).  A text
# scan of import statements; scripts/check-trusted-base.sh checks it against
# agda --dependency-graph on every gate run, so a scan that drifts from Agda
# fails there.  Modules supplied with the prover are not in the input set.
agda_cone() {
  local f m p
  local -A seen=()
  local -a queue=("$(proof_agda_root)")
  while (( ${#queue[@]} )); do
    f="${queue[0]}"; queue=("${queue[@]:1}")
    [[ -z "${seen[$f]:-}" ]] || continue
    seen[$f]=1
    printf '%s\n' "$f"
    while read -r m; do
      p="src/${m//.//}.agda"
      [[ -f "$p" ]] && queue+=("$p")
    done < <(sed -e 's/--.*$//' "$f" | grep -oE '(^|[[:space:];])import[[:space:]]+[A-Za-z0-9_.]+' | awk '{print $NF}')
  done
}
# The input set of one leg, as paths of files that git tracks, sorted:
# Agda, the cone; Rocq, the file the invocation compiles; Lean, every tracked
# .lean file of the leg (Axioms.lean imports the library, which imports the
# rest) and the lakefile, toolchain and manifest that exist.
inputs() {
  local prover="$1" dir
  case "$prover" in
    agda) agda_cone ;;
    rocq) dir="$(legvar ROCQ_DIR)"; printf '%s/%s\n' "$dir" "$(legvar ROCQ_INVOCATION | awk '{print $NF}')" ;;
    lean) dir="$(legvar LEAN_DIR)"
          git ls-files -- "$dir" | grep -E '(\.lean|/lakefile\.(lean|toml)|/lean-toolchain|/lake-manifest\.json)$' ;;
    *) die "unknown prover: $prover" ;;
  esac | LC_ALL=C sort -u
}
# The §8.5.1 digest of a leg's inputs in the working tree: the SHA-256 of the
# sorted "sha256  path" manifest.  On a clean checkout this is the reference
# digest at HEAD; --check confirms that with the reference script.
digest() {
  local prover="$1" paths
  paths="$(inputs "$prover")"
  [[ -n "$paths" ]] || die "the $prover leg has no inputs"
  while read -r p; do git ls-files --error-unmatch -- "$p" >/dev/null 2>&1 || die "$p is not tracked by git"; done <<< "$paths"
  printf '%s\n' "$paths" | xargs -d '\n' sha256sum -- | sha256sum | cut -d' ' -f1
}
# The reference digest (the pinned standard script) of a leg's inputs at a
# commit, over the input set of the working tree.  If a file of that set is
# missing at the commit, the script fails and so does the gate.  Equal bytes
# of the whole set at two commits mean an equal set: the cone is fixed by the
# contents of its own files, and the other legs' sets are fixed by name.
ref_digest() {
  local commit="$1" prover="$2"
  check_pinned "$digest_script" "$DIGEST_SHA256" 'reference digest script'
  mapfile -t paths < <(inputs "$prover")
  bash "$digest_script" "$commit" "${paths[@]}"
}
check_pinned() {
  local file="$1" sum="$2" what="$3"
  [[ -f "$file" ]] || die "the pinned $what is missing at $file: run bash scripts/grade-receipt.sh --fetch-reader"
  [[ "$(sha256sum "$file" | cut -d' ' -f1)" == "$sum" ]] || die "$file is not the pinned $what (sha256 differs)"
}
# Make a commit available, fetching the forge reference that keeps it.
ensure_commit() {
  local commit="$1" ref="${2:-}"
  git cat-file -e "$commit^{commit}" 2>/dev/null && return 0
  [[ -n "$ref" ]] || die "commit $commit is not here and has no fetch reference"
  git fetch -q origin "+$ref:refs/remotes/origin/receipt-fetch/${commit:0:12}" \
    || die "cannot fetch $ref for commit $commit"
  git cat-file -e "$commit^{commit}" 2>/dev/null || die "$ref does not hold commit $commit"
}
echo_ref() { local c="$1"; echoes | awk -F'|' -v c="$c" '$1==c{print $4}'; }

# ── Ledger rows ───────────────────────────────────────────────────────────────
# Validate one row; print nothing.  A field may not hold " or \ (deed strings)
# and may not be empty, except the reason of a current receipt and the axioms.
check_row() {
  local row="$1" prover run commit checker inv dig said state reason axioms a
  IFS='|' read -r prover run commit checker inv dig said state reason axioms <<< "$row"
  [[ "$(tr -cd '|' <<< "$row" | wc -c)" == 9 ]] || die "a ledger row needs 10 fields: $row"
  [[ "$row" != *'"'* && "$row" != *'\'* ]] || die "a ledger row holds a quote or backslash: $row"
  [[ "$prover" =~ ^(agda|rocq|lean)$ ]] || die "unknown prover in row: $row"
  [[ "$commit" =~ ^[0-9a-f]{40}$ ]] || die "a row's commit must be 40 lowercase hex: $row"
  [[ "$dig" =~ ^[0-9a-f]{64}$ ]] || die "a row's inputs digest must be a sha256: $row"
  [[ -n "$run" && -n "$checker" && -n "$inv" && -n "$said" ]] || die "an empty field in row: $row"
  case "$state" in
    current) [[ -z "$reason" ]] || die "a current row carries no reason: $row" ;;
    superseded|regressed) [[ -n "$reason" ]] || die "a $state row needs a reason: $row" ;;
    *) die "unknown receipt state in row: $row" ;;
  esac
  if [[ -n "$axioms" ]]; then
    IFS=',' read -ra a <<< "$axioms"
    for x in "${a[@]}"; do [[ "$x" =~ ^[^:]+:(c|b|debt)$ ]] || die "an axiom must be name:c, name:b or name:debt: $row"; done
  fi
}
check_echo() {
  local row="$1" src img wit ref
  IFS='|' read -r src img wit ref <<< "$row"
  [[ "$src" =~ ^[0-9a-f]{40}$ && "$img" =~ ^[0-9a-f]{40}$ ]] || die "an echo needs two 40-hex commits: $row"
  [[ "$src" != "$img" ]] || die "an echo joins a commit to itself: $row"
  [[ "$wit" == inputs-sha256 ]] || die "this gate writes the inputs-sha256 witness only: $row"
  [[ "$ref" =~ ^refs/ ]] || die "an echo needs the forge reference that keeps its source: $row"
}

# The ledger in force: runs(), plus the rows of $extra (a file) as current;
# an earlier current row of a prover that $extra covers becomes superseded.
extra=
ledger() {
  local row prover run state
  local -A replaced=()
  if [[ -n "$extra" ]]; then
    while IFS= read -r row; do
      [[ -n "$row" ]] || continue
      IFS='|' read -r prover run _ <<< "$row"
      replaced[$prover]="$run"
      printf '%s\n' "$row"
    done < "$extra"
  fi
  while IFS= read -r row; do
    [[ -n "$row" ]] || continue
    IFS='|' read -r prover _ _ _ _ _ _ state _ <<< "$row"
    if [[ "$state" == current && -n "${replaced[$prover]:-}" ]]; then
      printf '%s|superseded|replaced by the later run %s|%s\n' "$(cut -d'|' -f1-7 <<< "$row")" "${replaced[$prover]}" "$(cut -d'|' -f10 <<< "$row")"
    else
      printf '%s\n' "$row"
    fi
  done < <(runs)
}

# ── Grade (§8.2 and §8.5.2, the same rules as readProofReceipt) ───────────────
has_current() { local prover="$1"; awk -F'|' -v p="$prover" '$1==p && $8=="current"{f=1} END{exit !f}' "$ledger_file"; }
current_field() { local prover="$1" field="$2"; awk -F'|' -v p="$prover" -v f="$field" '$1==p && $8=="current"{print $f}' "$ledger_file"; }
canonical() {
  local w=" $1 "
  [[ "$w" == *' --safe '* && "$w" == *' --without-K '* ]] && [[ "$w" == *' --cubical-compatible '* || "$w" == *' --cubical '* ]]
}
# A leg's witness counts only if every axiom its current receipt reports has
# disposition c (§8.4).
axioms_ok() { local prover="$1"; [[ ",$(current_field "$prover" 10)," != *':b,'* && ",$(current_field "$prover" 10)," != *':debt,'* ]]; }
# §8.5.2: the leg's current receipt describes the :source-commit when its
# commit is that commit, or an echo chain leads there and every link's digest
# for this prover equals the receipt's digest.
describes_source() {
  local prover="$1" c d img
  c="$(current_field "$prover" 3)"; d="$(current_field "$prover" 6)"
  while :; do
    [[ "$c" != "$source_commit" ]] || return 0
    img="$(awk -F'|' -v c="$c" '$1==c{print $2}' "$echo_file")"
    [[ -n "$img" ]] || return 1
    [[ "$(awk -F'|' -v c="$c" -v p="$prover" '$1==c && $2==p{print $3}' "$echo_digest_file")" == "$d" ]] || return 1
    c="$img"
  done
}
pwg_of() {
  local token="$1" coq_route="$2" coq_state="$3" lean_route="$4" lean_state="$5" n=0 p
  [[ "$token" == proven || "$token" == proven-with-postulates ]] || { printf 'ungraded'; return; }
  has_current agda && axioms_ok agda && canonical "$(current_field agda 5)" || { printf 'ungraded'; return; }
  for p in rocq lean; do
    local route state
    if [[ $p == rocq ]]; then route="$coq_route" state="$coq_state"; else route="$lean_route" state="$lean_state"; fi
    [[ "$route" == transported || "$route" == re-proved ]] && [[ "$state" == RECONCILED ]] && has_current "$p" && axioms_ok "$p" && n=$((n + 1))
  done
  case "$n" in
    0) printf 'PWG-3' ;;
    1) printf 'PWG-2i' ;;
    2) if describes_source agda && describes_source rocq && describes_source lean; then printf 'PWG-1'; else printf 'PWG-2ii'; fi ;;
    *) die "unexpected recheck count: $n" ;;
  esac
}

# ── Emit ──────────────────────────────────────────────────────────────────────
emit_axioms() {
  local list="$1" x
  if [[ -z "$list" ]]; then printf '               (axioms))\n'; return; fi
  printf '               (axioms'
  IFS=',' read -ra a <<< "$list"
  for x in "${a[@]}"; do printf '\n                 (axiom :name "%s" :disposition %s)' "${x%:*}" "${x##*:}"; done
  printf '))\n'
}
emit_receipts() {
  local prover="$1" row p run commit checker inv dig said state reason axioms
  # Current first, then the lineage in ledger order.
  for want in current other; do
    while IFS= read -r row; do
      IFS='|' read -r p run commit checker inv dig said state reason axioms <<< "$row"
      [[ "$p" == "$prover" ]] || continue
      if [[ $want == current ]]; then [[ $state == current ]] || continue; else [[ $state != current ]] || continue; fi
      printf '      ; the run reported: %s\n' "$said"
      printf '      (receipt :run "%s"\n' "$run"
      printf '               :commit "%s"\n' "$commit"
      printf '               :checker "%s"\n' "$checker"
      printf '               :invocation "%s"\n' "$inv"
      if [[ $state == current ]]; then
        printf '               :inputs-sha256 "%s"\n' "$dig"
        printf '               :state current\n'
        emit_axioms "$axioms"
      else
        printf '               :state %s\n               :reason "%s")\n' "$state" "$reason"
      fi
    done < "$ledger_file"
  done
}
emit_echoes() {
  local src img wit ref p
  while IFS='|' read -r src img wit ref; do
    printf '  ; %s was rewritten into %s on %s; %s keeps it.\n' "${src:0:12}" "${img:0:12}" "$default_branch" "$ref"
    printf '  (echo :source "%s" :image "%s" :witness %s' "$src" "$img" "$wit"
    for p in agda rocq lean; do
      printf '\n    (inputs :prover %s :sha256 "%s")' "$p" "$(awk -F'|' -v c="$src" -v p="$p" '$1==c && $2==p{print $3}' "$echo_digest_file")"
    done
    printf ')\n'
  done < "$echo_file"
}
emit() {
  local id token kind coq coq_state lean lean_state coq_reason lean_reason m name binding
  printf ';; SPDX-License-Identifier: CC-BY-SA-4.0\n'
  printf ';; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)\n'
  printf ';; The proof receipt of secret-types (PROOF-POLICY §8.5.1, §8.5.2).\n'
  printf ';; GENERATED by scripts/grade-receipt.sh: regenerate with --write, check with --check.\n'
  printf ';; Each (receipt ...) is a row of the run ledger in that script, copied from\n'
  printf ';; the CI log that printed it.  Every digest is computed from git objects and\n'
  printf ';; checked with the reference script of the standard.  The grade is derived,\n'
  printf ';; never typed:\n'
  printf ';;   bun deed_lint.js --proof-receipt-json verification/receipts/agda_praxis.deed\n'
  printf ';; with the reader at standards %s.\n' "$STANDARDS_COMMIT"
  printf ';; Demonstrations N-4, N-5 and N-6 are not theorems (§8.1) and have no claim here.\n'
  printf ';; The trusted base is what scripts/check-trusted-base.sh finds in the\n'
  printf ';; prover-supplied modules of the import cone of %s.\n' "$(proof_agda_root)"
  printf '(praxis-deed\n'
  printf '  :schema-version "1.0.0"\n'
  printf '  :canonical-name "secret-types-proof-receipt"\n'
  printf '  :profile proof-receipt\n'
  printf '  :repository "%s"\n' "$repo"
  printf '  :source-commit "%s"\n' "$source_commit"
  printf '  (trusted-base'
  while IFS='|' read -r m name binding; do
    printf '\n    (primitive :prover agda :module "%s" :name "%s" :binding "%s")' "$m" "$name" "$binding"
  done < <(proof_trusted_base)
  printf ')\n'
  emit_echoes
  while IFS='|' read -r id token kind coq coq_state lean lean_state coq_reason lean_reason; do
    [[ "$kind" == theorem ]] || continue
    printf '  (claim :id "%s" :pwg %s :foundation-diverse #f\n' "$id" "$(pwg_of "$token" "$coq" "$coq_state" "$lean" "$lean_state")"
    printf '    (leg :prover agda :route source :token %s :state AGDA-VERIFIED' "$token"
    if has_any agda; then printf '\n'; emit_receipts agda | sed '$ s/$/)/'; else printf ')\n'; fi
    emit_leg rocq "$coq" "$coq_state" "$coq_reason" ')'
    emit_leg lean "$lean" "$lean_state" "$lean_reason" '))'
  done < <(claims)
  printf ')\n'
}
# Print one recheck leg, then $5 (the closing parentheses).  A waived or
# unavailable leg carries only its reason (§8.5.1); a transported or
# re-proved leg carries its token, its §2.2 state and its receipts.
emit_leg() {
  local prover="$1" route="$2" state="$3" reason="$4" close="$5"
  case "$route" in
    waived|unavailable)
      [[ -n "$reason" && "$reason" != *'"'* ]] || die "a $route $prover leg needs a reason without a quote"
      printf '    (leg :prover %s :route %s :reason "%s"%s\n' "$prover" "$route" "$reason" "$close" ;;
    transported|re-proved)
      printf '    (leg :prover %s :route %s :token %s :state %s' "$prover" "$route" "$(leg_token "$state")" "$state"
      if has_any "$prover"; then printf '\n'; emit_receipts "$prover" | sed "\$ s/\$/$close/"; else printf '%s\n' "$close"; fi ;;
    *) die "unknown route for the $prover leg: $route" ;;
  esac
}
has_any() { local prover="$1"; awk -F'|' -v p="$prover" '$1==p{f=1} END{exit !f}' "$ledger_file"; }
# A leg's §5 token: a RECONCILED re-proof is kernel-checked with no axiom
# (scripts/check-legs.sh refuses any), so it is proven; any other state is open.
leg_token() { local state="$1"; [[ "$state" == RECONCILED ]] && printf 'proven' || printf 'open'; }

# ── Cross-checks of the typed claim list ──────────────────────────────────────
check_claim_ids() {
  local decl doc
  decl="$(claims | cut -d'|' -f1 | LC_ALL=C sort)"
  doc="$(grep -oE '^\| N-[0-9]+ ' PROOF-STATUS.adoc | tr -d '| ' | LC_ALL=C sort -u || true)"
  [[ -n "$doc" ]] || die 'no claim ids found in PROOF-STATUS.adoc; the table layout changed'
  if [[ "$decl" != "$doc" ]]; then
    diff <(printf '%s\n' "$doc") <(printf '%s\n' "$decl") \
      | sed 's/^</  only in PROOF-STATUS.adoc:/; s/^>/  only in grade-receipt.sh:/' >&2
    die 'claim ids differ between this receipt and PROOF-STATUS.adoc'
  fi
}
check_leg_records() {
  local rec=verification/legs/README.adoc counted recorded
  counted="$(claims | awk -F'|' '$5=="RECONCILED"||$7=="RECONCILED"{print $1}' | LC_ALL=C sort)"
  recorded="$(grep -oE '^\| N-[0-9]+$' "$rec" 2>/dev/null | tr -d '| ' | LC_ALL=C sort -u || true)"
  if [[ "$counted" != "$recorded" ]]; then
    diff <(printf '%s\n' "$recorded") <(printf '%s\n' "$counted") \
      | grep -E '^[<>]' | sed "s|^<|  only in $rec:|; s/^>/  only in grade-receipt.sh:/" >&2
    die "claims with a RECONCILED leg differ from the rows of $rec"
  fi
}

# Prepare $ledger_file, $echo_file, $echo_digest_file and $source_commit.  The
# current receipts must name one commit; the :source-commit is the end of the
# echo chain from it (§8.5.2), or that commit if it has no echo.  With no
# current receipt it is $fallback_commit (nothing is graded then).  Each echo
# link's witness digests are computed at its source and at its image with the
# reference script, and must be equal (§8.5.3, check 3).
prepare() {
  ledger_file="$(mktemp)"; echo_file="$(mktemp)"; echo_digest_file="$(mktemp)"
  tmpfiles+=("$ledger_file" "$echo_file" "$echo_digest_file")
  ledger > "$ledger_file"
  echoes | grep . > "$echo_file" || true
  local row p commits src img wit ref a b
  while IFS= read -r row; do check_row "$row"; done < "$ledger_file"
  while IFS= read -r row; do check_echo "$row"; done < "$echo_file"
  [[ "$(cut -d'|' -f1 "$echo_file" | sort | uniq -d | wc -l)" == 0 ]] || die 'an echo source has two images'
  commits="$(awk -F'|' '$8=="current"{print $3}' "$ledger_file" | sort -u)"
  [[ "$(grep -c . <<< "$commits" || true)" -le 1 ]] || die "the current receipts name different commits: $(tr '\n' ' ' <<< "$commits")"
  for p in agda rocq lean; do
    [[ "$(awk -F'|' -v p="$p" '$1==p && $8=="current"' "$ledger_file" | wc -l)" -le 1 ]] || die "the $p leg has more than one current row"
  done
  while IFS='|' read -r src img wit ref; do
    ensure_commit "$src" "$ref"; ensure_commit "$img" "refs/heads/$default_branch"
    for p in agda rocq lean; do
      a="$(ref_digest "$src" "$p")" || die "cannot compute the $p digest at $src"
      b="$(ref_digest "$img" "$p")" || die "cannot compute the $p digest at $img"
      [[ "$a" == "$b" ]] || die "echo $src -> $img: the $p inputs differ ($a at the source, $b at the image)"
      printf '%s|%s|%s\n' "$src" "$p" "$a" >> "$echo_digest_file"
    done
  done < "$echo_file"
  source_commit="${commits:-$fallback_commit}"
  local steps=0 next
  while next="$(awk -F'|' -v c="$source_commit" '$1==c{print $2}' "$echo_file")" && [[ -n "$next" ]]; do
    source_commit="$next"; steps=$((steps + 1))
    (( steps < 64 )) || die 'the echoes form a cycle'
  done
  [[ "$source_commit" =~ ^[0-9a-f]{40}$ ]] || die "no 40-hex source commit (got '${source_commit}')"
}

# §8.5.3, checks 1 and 2: the :source-commit is on the default branch, and
# each current receipt's :inputs-sha256 is the reference digest at its commit.
check_git_facts() {
  local p c want got base
  base="refs/remotes/origin/$default_branch"
  git rev-parse -q --verify "$base" >/dev/null || base="refs/heads/$default_branch"
  git merge-base --is-ancestor "$source_commit" "$base" \
    || die "the :source-commit $source_commit is not on $default_branch ($base)"
  for p in agda rocq lean; do
    has_current "$p" || continue
    c="$(current_field "$p" 3)"; want="$(current_field "$p" 6)"
    ensure_commit "$c" "$(echo_ref "$c")"
    got="$(ref_digest "$c" "$p")" || die "cannot compute the $p digest at $c"
    [[ "$want" == "$got" ]] || die "the $p receipt records inputs $want, but the reference digest at $c is $got"
  done
  printf 'PASS: git facts (source-commit %s on %s; each current inputs digest matches the reference script at its commit; each echo witness equal at source and image)\n' "${source_commit:0:12}" "$default_branch"
}

# Each current receipt must still describe the tree: its inputs digest is the
# digest of the inputs now, and the reference script agrees.  Otherwise the
# grade cannot be carried forward (§8.4, regression drops the grade): record a
# new run, or mark the row superseded or regressed with its reason.
check_currency() {
  local p want got
  for p in agda rocq lean; do
    has_current "$p" || continue
    want="$(current_field "$p" 6)"; got="$(digest "$p")"
    [[ "$want" == "$got" ]] || die "the $p inputs changed since run $(current_field "$p" 2) (recorded $want, now $got): record a new CI run, or mark that row superseded or regressed"
  done
}

# Run the pinned reader on $1 and print each claim's derived grade.  Then the
# negative control: the same receipt with one claim's :pwg changed must be
# refused, so a reader that stopped deriving grades cannot pass this gate.
read_with_reader() {
  local file="$1" json first wrong ctl err
  command -v bun >/dev/null || die 'bun is needed to run the pinned reader'
  check_pinned "$reader" "$READER_SHA256" 'reader'
  json="$(bun "$reader" --proof-receipt-json "$file")" || die "the pinned reader refused $file"
  printf 'PASS: the pinned reader (standards %s) accepts %s\n' "${STANDARDS_COMMIT:0:12}" "$file"
  grep -oE '"source_commit":"[0-9a-f]{40}"' <<< "$json" | sed 's/"source_commit":"\(.*\)"/  source-commit \1/'
  grep -oE '"id":"[^"]*","pwg":"[^"]*","foundation_diverse":(true|false)' <<< "$json" \
    | sed -E 's/"id":"([^"]*)","pwg":"([^"]*)","foundation_diverse":(.*)/  \1  \2  foundation-diverse \3/'
  first="$(grep -m1 -oE ':pwg [A-Za-z0-9-]+' "$file" | cut -d' ' -f2)"
  case "$first" in PWG-1) wrong=PWG-2ii ;; *) wrong=PWG-1 ;; esac
  ctl="$(mktemp -d)"; tmpfiles+=("$ctl")
  awk -v w="$wrong" '!done && /:pwg /{sub(/:pwg [A-Za-z0-9-]+/, ":pwg " w); done=1} {print}' "$file" > "$ctl/control_praxis.deed"
  if err="$(bun "$reader" --proof-receipt-json "$ctl/control_praxis.deed" 2>&1)"; then
    die "negative control: the reader accepted a receipt whose first claim records :pwg $wrong"
  fi
  grep -q 'records :pwg' <<< "$err" || { printf '%s\n' "$err" >&2; die 'negative control: refused for another reason than the grade'; }
  printf 'PASS: negative control (the first claim recorded as :pwg %s is refused: its legs support %s)\n' "$wrong" "$first"
}

fetch_pinned() {
  local path="$1" sum="$2" dest="$3"
  mkdir -p "$(dirname "$dest")"
  curl --proto '=https' --tlsv1.2 -fsSL "$STANDARDS_RAW/$path" -o "$dest.tmp"
  echo "$sum  $dest.tmp" | sha256sum --check --strict >/dev/null || { rm -f "$dest.tmp"; die "the fetched $path does not match its pinned sha256"; }
  mv "$dest.tmp" "$dest"; printf 'FETCHED %s (standards %s) to %s\n' "$path" "${STANDARDS_COMMIT:0:12}" "$dest"
}

tmpfiles=()
cleanup() { (( ${#tmpfiles[@]} )) && rm -rf "${tmpfiles[@]}"; return 0; }
trap cleanup EXIT

mode=--write; fallback_commit=; target="$out"
r_prover=; r_run=; r_commit=; r_checker=; r_reported=
while (( $# )); do
  case "$1" in
    --write|--check|--fetch-reader) mode="$1" ;;
    --digest)   mode=--digest; r_prover="${2:-}"; shift ;;
    --inputs)   mode=--inputs; r_prover="${2:-}"; shift ;;
    --run-row)  mode=--run-row; r_prover="${2:-}"; shift ;;
    --emit-run) mode=--emit-run; extra="${2:-}"; shift ;;
    --out)      target="${2:-}"; shift ;;
    --commit)   fallback_commit="${2:-}"; r_commit="${2:-}"; shift ;;
    --run)      r_run="${2:-}"; shift ;;
    --checker)  r_checker="${2:-}"; shift ;;
    --reported) r_reported="${2:-}"; shift ;;
    -h|--help)  sed -n '5,25p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) printf 'unknown argument: %s\n' "$1" >&2; exit 2 ;;
  esac
  shift
done

case "$mode" in
  --digest) digest "$r_prover" ;;
  --inputs) inputs "$r_prover" ;;
  --run-row)
    # A run that passed its gate reported no axiom: every gate fails on one.
    row="$r_prover|$r_run|$r_commit|$r_checker|$(invocation "$r_prover")|$(digest "$r_prover")|$r_reported|current||"
    check_row "$row"; printf '%s\n' "$row" ;;
  --fetch-reader)
    fetch_pinned 1-formats/deed/tools/deed_lint.js "$READER_SHA256" "$reader"
    fetch_pinned scripts/proof-inputs-sha256.sh "$DIGEST_SHA256" "$digest_script" ;;
  --write|--emit-run)
    check_claim_ids; check_leg_records
    [[ -n "$fallback_commit" ]] || fallback_commit="$(git rev-parse HEAD)"
    [[ "$mode" == --write || -f "$extra" ]] || die "--emit-run needs a rows file"
    prepare
    # A run's receipt must describe the tree it was emitted from.
    if [[ "$mode" == --emit-run ]]; then check_currency; fi
    mkdir -p "$(dirname "$target")"
    emit > "$target"
    printf 'WROTE %s (source-commit %s)\n' "$target" "$source_commit"
    if [[ "$mode" == --emit-run ]]; then
      read_with_reader "$target"
      printf 'To record this run, add these rows to runs() in scripts/grade-receipt.sh:\n'
      sed 's/^/  /' "$extra"
    fi ;;
  --check)
    check_claim_ids; check_leg_records
    [[ -f "$out" ]] || die "$out is missing"
    fallback_commit="$(sed -n 's/^  :source-commit "\([0-9a-f]*\)"$/\1/p' "$out")"
    prepare
    check_git_facts
    check_currency
    tmp="$(mktemp)"; tmpfiles+=("$tmp")
    emit > "$tmp"
    if ! diff -u "$out" "$tmp" >&2; then
      die 'the receipt does not match the tree and the ledgers: regenerate with bash scripts/grade-receipt.sh --write'
    fi
    printf 'PASS: %s matches the tree and the ledgers (source-commit %s)\n' "$out" "$source_commit"
    read_with_reader "$out" ;;
  *) die "unknown mode: $mode" ;;
esac
