#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# grade-receipt.sh: the proof receipt of this repository,
# verification/receipts/agda_praxis.deed, in the shape of
# standards/3-practice/PROOF-POLICY.adoc §8.5.1 (profile proof-receipt).
#
#   --write              write the receipt from the tree and the run ledger
#   --check              regenerate it, refuse any difference, check that each
#                        current receipt still describes the tree, and run the
#                        pinned reader with a negative control
#   --digest PROVER      print the inputs digest of one leg (agda|rocq|lean)
#   --run-row PROVER --run URL --commit SHA --checker TEXT --axioms TEXT
#                        print one ledger row for a run that just passed
#   --emit-run ROWS --out FILE
#                        write a receipt for the run whose rows are in ROWS:
#                        they become current, and the earlier current receipts
#                        of the same legs become superseded (CI does this)
#   --fetch-reader       fetch the pinned reader into _build/ and check it
#
# What is derived and what is typed.  Two lists are typed in this file: the
# claim list (cross-checked against PROOF-STATUS.adoc and
# verification/legs/README.adoc) and the run ledger (each row copied from the
# CI log that printed it).  Everything else is read from the one definition
# the gate also reads: the flags, the root, the invocation and the trusted
# base from scripts/proof-flags.sh; the leg invocations and pins from
# scripts/check-legs.sh.  The grade is never typed: it is derived here under
# §8.2 and derived again by the pinned reader, which refuses a receipt whose
# :pwg its legs and receipts do not support (§8.4).
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
export LC_ALL=C.UTF-8
. scripts/proof-flags.sh

out=verification/receipts/agda_praxis.deed
repo="hyperpolymath/secret-types"

# The pinned reader: readProofReceipt in standards 1-formats/deed/tools/deed_lint.js
# (PROOF-POLICY §8.5.1), at the commit and sha256 that Mathesis also pins.
READER_COMMIT=be39f900665fb7c042c05d1165da018adc1860f4
READER_SHA256=f7e2b91905f0d99e5cabab59385073afb695be8b9f2d0591257a6a6fd62e25e3
READER_URL="https://raw.githubusercontent.com/metadatastician/standards/$READER_COMMIT/1-formats/deed/tools/deed_lint.js"
reader="${DEED_LINT:-_build/deed_lint.js}"

# ── The claim list ────────────────────────────────────────────────────────────
# id | §5 token of the Agda proof | kind | Rocq route | Rocq §2.2 state |
# Lean route | Lean §2.2 state.  Kind is theorem (graded, §8.1) or
# demonstration (a checked example; §8.1 grades theorems only, so a
# demonstration has no claim in the receipt).  Routes: transported | re-proved
# | waived | unavailable.  States: §2.2; only RECONCILED counts (§8.2).
claims() {
  cat <<'ROWS'
N-1|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED
N-2|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED
N-3|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED
N-4|tested-only|demonstration|n/a|n/a|n/a|n/a
N-5|tested-only|demonstration|n/a|n/a|n/a|n/a
N-6|tested-only|demonstration|n/a|n/a|n/a|n/a
N-7|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED
N-8|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED
N-9|proven|theorem|re-proved|RECONCILED|re-proved|RECONCILED
ROWS
}

# ── The run ledger ────────────────────────────────────────────────────────────
# One row per checker run, copied from the log of the run that printed it
# (the receipt job of .github/workflows/proofs.yml prints the rows of its own
# run).  One run of a leg checks every theorem, so each row is a receipt of
# that leg for every claim.
# prover | run | commit (40 hex) | checker | invocation | inputs sha256 |
# axioms reported | state (current|superseded|regressed) | reason
runs() {
  cat <<'ROWS'
ROWS
}

die() { printf 'ERROR: %s\n' "$*" >&2; exit 1; }

# ── Inputs of each leg ────────────────────────────────────────────────────────
# Every file a leg's checker or gate reads.  A current receipt describes the
# tree only while the digest of these files is the digest its run recorded.
inputs() {
  case "$1" in
    agda)
      { find src/SecretTypes -name '*.agda'
        find tests/reject tests/flag-control tests/trusted-base -type f
        printf '%s\n' scripts/proof-flags.sh scripts/check.sh scripts/check-trusted-base.sh scripts/scan-agda-postulates.awk
      } ;;
    rocq)
      { find verification/legs/rocq -name '*.v'; printf '%s\n' scripts/check-legs.sh; } ;;
    lean)
      { find verification/legs/lean \( -name '*.lean' -o -name lakefile.toml -o -name lean-toolchain \) -not -path '*/.lake/*'
        printf '%s\n' scripts/check-legs.sh; } ;;
    *) die "unknown prover: $1" ;;
  esac | while read -r p; do [[ -f "$p" ]] && printf '%s\n' "$p"; done | LC_ALL=C sort -u
}
# The digest of a leg's inputs: sha256 of the sorted "sha256  path" listing.
digest() { inputs "$1" | xargs -d '\n' sha256sum | sha256sum | cut -d' ' -f1; }

# The invocation each leg's gate runs, read from its one definition.
legvar() { sed -n "s/^$1='\\{0,1\\}\\([^']*\\)'\\{0,1\\}\$/\\1/p" scripts/check-legs.sh; }
invocation() {
  case "$1" in
    agda) proof_agda_invocation ;;
    rocq) printf '%s (in %s)\n' "$(legvar ROCQ_INVOCATION)" "$(legvar ROCQ_DIR)" ;;
    lean) printf '%s; %s (in %s)\n' "$(legvar LEAN_BUILD)" "$(legvar LEAN_AXIOMS)" "$(legvar LEAN_DIR)" ;;
  esac
}

# ── Ledger rows ───────────────────────────────────────────────────────────────
# Validate one row; print nothing.  A field may not hold " or \ (deed strings)
# and may not be empty, except the reason of a current receipt.
check_row() {
  local row="$1" prover run commit checker inv dig ax state reason
  IFS='|' read -r prover run commit checker inv dig ax state reason <<< "$row"
  [[ "$(tr -cd '|' <<< "$row" | wc -c)" == 8 ]] || die "a ledger row needs 9 fields: $row"
  [[ "$row" != *'"'* && "$row" != *'\'* ]] || die "a ledger row holds a quote or backslash: $row"
  [[ "$prover" =~ ^(agda|rocq|lean)$ ]] || die "unknown prover in row: $row"
  [[ "$commit" =~ ^[0-9a-f]{40}$ ]] || die "a row's commit must be 40 lowercase hex: $row"
  [[ "$dig" =~ ^[0-9a-f]{64}$ ]] || die "a row's inputs digest must be a sha256: $row"
  [[ -n "$run" && -n "$checker" && -n "$inv" && -n "$ax" ]] || die "an empty field in row: $row"
  case "$state" in
    current) [[ -z "$reason" ]] || die "a current row carries no reason: $row" ;;
    superseded|regressed) [[ -n "$reason" ]] || die "a $state row needs a reason: $row" ;;
    *) die "unknown receipt state in row: $row" ;;
  esac
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
      printf '%s|superseded|replaced by the later run %s\n' "$(cut -d'|' -f1-7 <<< "$row")" "${replaced[$prover]}"
    else
      printf '%s\n' "$row"
    fi
  done < <(runs)
}

# ── Grade (§8.2, the same rules as readProofReceipt) ──────────────────────────
has_current() { awk -F'|' -v p="$1" '$1==p && $8=="current"{f=1} END{exit !f}' "$ledger_file"; }
current_field() { awk -F'|' -v p="$1" -v f="$2" '$1==p && $8=="current"{print $f}' "$ledger_file"; }
canonical() {
  local w=" $1 "
  [[ "$w" == *' --safe '* && "$w" == *' --without-K '* ]] && [[ "$w" == *' --cubical-compatible '* || "$w" == *' --cubical '* ]]
}
pwg_of() {
  local token="$1" coq_route="$2" coq_state="$3" lean_route="$4" lean_state="$5" n=0 p
  [[ "$token" == proven || "$token" == proven-with-postulates ]] || { printf 'ungraded'; return; }
  has_current agda && canonical "$(current_field agda 5)" || { printf 'ungraded'; return; }
  for p in rocq lean; do
    local route state
    if [[ $p == rocq ]]; then route="$coq_route" state="$coq_state"; else route="$lean_route" state="$lean_state"; fi
    [[ "$route" == transported || "$route" == re-proved ]] && [[ "$state" == RECONCILED ]] && has_current "$p" && n=$((n + 1))
  done
  case "$n" in
    0) printf 'PWG-3' ;;
    1) printf 'PWG-2i' ;;
    2) if [[ "$(current_field agda 3)" == "$source_commit" && "$(current_field rocq 3)" == "$source_commit" \
              && "$(current_field lean 3)" == "$source_commit" ]]; then printf 'PWG-1'; else printf 'PWG-2ii'; fi ;;
  esac
}

# ── Emit ──────────────────────────────────────────────────────────────────────
emit_receipts() {
  local prover="$1" row p run commit checker inv dig ax state reason
  # Current first, then the lineage in ledger order.
  for want in current other; do
    while IFS= read -r row; do
      IFS='|' read -r p run commit checker inv dig ax state reason <<< "$row"
      [[ "$p" == "$prover" ]] || continue
      if [[ $want == current ]]; then [[ $state == current ]] || continue; else [[ $state != current ]] || continue; fi
      printf '      ; inputs sha256 %s (bash scripts/grade-receipt.sh --digest %s)\n' "$dig" "$prover"
      printf '      ; axioms reported: %s\n' "$ax"
      printf '      (receipt :run "%s"\n' "$run"
      printf '               :commit "%s"\n' "$commit"
      printf '               :checker "%s"\n' "$checker"
      printf '               :invocation "%s"\n' "$inv"
      if [[ $state == current ]]; then
        printf '               :state current)\n'
      else
        printf '               :state %s\n               :reason "%s")\n' "$state" "$reason"
      fi
    done < "$ledger_file"
  done
}

emit() {
  local id token kind coq coq_state lean lean_state m name binding
  printf ';; SPDX-License-Identifier: CC-BY-SA-4.0\n'
  printf ';; SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)\n'
  printf ';; The proof receipt of secret-types (PROOF-POLICY §8.5.1).\n'
  printf ';; GENERATED by scripts/grade-receipt.sh: regenerate with --write, check with --check.\n'
  printf ';; Each (receipt ...) is a row of the run ledger in that script, copied from\n'
  printf ';; the CI log that printed it.  The grade is derived, never typed:\n'
  printf ';;   bun deed_lint.js --proof-receipt-json verification/receipts/agda_praxis.deed\n'
  printf ';; with the reader at standards %s.\n' "$READER_COMMIT"
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
  while IFS='|' read -r id token kind coq coq_state lean lean_state; do
    [[ "$kind" == theorem ]] || continue
    printf '  (claim :id "%s" :pwg %s :foundation-diverse #f\n' "$id" "$(pwg_of "$token" "$coq" "$coq_state" "$lean" "$lean_state")"
    printf '    (leg :prover agda :route source :token %s :state AGDA-VERIFIED' "$token"
    has_any agda && { printf '\n'; emit_receipts agda | sed '$ s/$/)/'; } || printf ')\n'
    printf '    (leg :prover rocq :route %s :token %s :state %s' "$coq" "$(leg_token "$coq_state")" "$coq_state"
    has_any rocq && { printf '\n'; emit_receipts rocq | sed '$ s/$/)/'; } || printf ')\n'
    printf '    (leg :prover lean :route %s :token %s :state %s' "$lean" "$(leg_token "$lean_state")" "$lean_state"
    has_any lean && { printf '\n'; emit_receipts lean | sed '$ s/$/))/'; } || printf '))\n'
  done < <(claims)
  printf ')\n'
}
has_any() { awk -F'|' -v p="$1" '$1==p{f=1} END{exit !f}' "$ledger_file"; }
# A leg's §5 token: a RECONCILED re-proof is kernel-checked with no axiom
# (scripts/check-legs.sh refuses any), so it is proven; any other state is open.
leg_token() { [[ "$1" == RECONCILED ]] && printf 'proven' || printf 'open'; }

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

# Prepare $ledger_file and $source_commit.  The source commit is the commit of
# the current receipts, which must agree; with no current receipt it is
# $fallback_commit (nothing is graded then, so nothing rests on it).
prepare() {
  ledger_file="$(mktemp)"; tmpfiles+=("$ledger_file")
  ledger > "$ledger_file"
  local row
  while IFS= read -r row; do check_row "$row"; done < "$ledger_file"
  local commits
  commits="$(awk -F'|' '$8=="current"{print $3}' "$ledger_file" | sort -u)"
  [[ "$(grep -c . <<< "$commits" || true)" -le 1 ]] || die "the current receipts name different commits: $(tr '\n' ' ' <<< "$commits")"
  local p
  for p in agda rocq lean; do
    [[ "$(awk -F'|' -v p="$p" '$1==p && $8=="current"' "$ledger_file" | wc -l)" -le 1 ]] || die "the $p leg has more than one current row"
  done
  source_commit="${commits:-$fallback_commit}"
  [[ "$source_commit" =~ ^[0-9a-f]{40}$ ]] || die "no 40-hex source commit (got '${source_commit}')"
}

# Each current receipt must still describe the tree: its inputs digest is the
# digest of the inputs now.  Otherwise the grade cannot be carried forward
# (§8.4, regression drops the grade): record a new run, or mark the row
# superseded or regressed with its reason.
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
  [[ -f "$reader" ]] || die "the pinned reader is missing at $reader: run bash scripts/grade-receipt.sh --fetch-reader"
  [[ "$(sha256sum "$reader" | cut -d' ' -f1)" == "$READER_SHA256" ]] || die "$reader is not the pinned reader (sha256 differs)"
  json="$(bun "$reader" --proof-receipt-json "$file")" || die "the pinned reader refused $file"
  printf 'PASS: the pinned reader (standards %s) accepts %s\n' "${READER_COMMIT:0:12}" "$file"
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

tmpfiles=()
cleanup() { (( ${#tmpfiles[@]} )) && rm -rf "${tmpfiles[@]}"; return 0; }
trap cleanup EXIT

mode=--write; fallback_commit=; target="$out"
r_prover=; r_run=; r_commit=; r_checker=; r_axioms=
while (( $# )); do
  case "$1" in
    --write|--check|--fetch-reader) mode="$1" ;;
    --digest)   mode=--digest; r_prover="${2:-}"; shift ;;
    --run-row)  mode=--run-row; r_prover="${2:-}"; shift ;;
    --emit-run) mode=--emit-run; extra="${2:-}"; shift ;;
    --out)      target="${2:-}"; shift ;;
    --commit)   fallback_commit="${2:-}"; r_commit="${2:-}"; shift ;;
    --run)      r_run="${2:-}"; shift ;;
    --checker)  r_checker="${2:-}"; shift ;;
    --axioms)   r_axioms="${2:-}"; shift ;;
    -h|--help)  sed -n '5,22p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) printf 'unknown argument: %s\n' "$1" >&2; exit 2 ;;
  esac
  shift
done

case "$mode" in
  --digest) digest "$r_prover" ;;
  --run-row)
    row="$r_prover|$r_run|$r_commit|$r_checker|$(invocation "$r_prover")|$(digest "$r_prover")|$r_axioms|current|"
    check_row "$row"; printf '%s\n' "$row" ;;
  --fetch-reader)
    mkdir -p "$(dirname "$reader")"
    curl --proto '=https' --tlsv1.2 -fsSL "$READER_URL" -o "$reader.tmp"
    echo "$READER_SHA256  $reader.tmp" | sha256sum --check --strict >/dev/null || { rm -f "$reader.tmp"; die 'the fetched reader does not match its pinned sha256'; }
    mv "$reader.tmp" "$reader"; printf 'FETCHED the pinned reader to %s\n' "$reader" ;;
  --write|--emit-run)
    check_claim_ids; check_leg_records
    [[ -n "$fallback_commit" ]] || fallback_commit="$(git rev-parse HEAD)"
    [[ "$mode" == --write || -f "$extra" ]] || die "--emit-run needs a rows file"
    prepare
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
    check_currency
    tmp="$(mktemp)"; tmpfiles+=("$tmp")
    emit > "$tmp"
    if ! diff -u "$out" "$tmp" >&2; then
      die 'the receipt does not match the tree and the run ledger: regenerate with bash scripts/grade-receipt.sh --write'
    fi
    printf 'PASS: %s matches the tree and the run ledger (source-commit %s)\n' "$out" "$source_commit"
    read_with_reader "$out" ;;
esac
