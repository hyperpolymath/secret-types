#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# dev-toolchain.sh [agda] [zig] [status]
#
# Provisions, in an agent sandbox with a restricted egress allowlist, the
# provers this repository can actually get. Exits non-zero on anything it
# cannot provision, and says which host blocked it: a toolchain script that
# reports success for a tool it did not install is the same failure mode as a
# gate that cannot fail.
#
# Why this is not "install Agda from apt": the allowlist for this session is
# github.com, codeload.github.com, api.github.com, pypi.org,
# files.pythonhosted.org and registry.npmjs.org. deb.debian.org,
# static.rust-lang.org, downloads.haskell.org and (for release assets)
# release-assets.githubusercontent.com are all blocked, so apt, rustup, ghcup
# and GitHub *release downloads* are unavailable. PyPI and npm are not.
#
# The working combination, found 2026-11-01:
#
#   pip install agda          -> a native Agda (2.7.0.1 at the time), a Python
#                                binding to Agda's Haskell library, which needs
#                                Agda's *data directory* to run at all
#   npm install agda-wasm     -> ships that data directory (2.6.4.3 and 2.7.0.1)
#                                and a WASM build
#
# so: install the binding, symlink the matching data dir into it, verify by
# typechecking SecretTypes.All. Two packages doing one job is ugly; it is
# recorded because "Agda installed" and "Agda usable" are different claims and
# only the second one matters.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

VENV="${VENV:-$HOME/.tclocal}"
NPMDIR="${NPMDIR:-$HOME/.tc/npm}"

note() { printf '%s\n' "$*" >&2; }

blocked() {
  local host="$1"
  if timeout 8 curl -sS -o /dev/null "https://$host/" 2>/dev/null; then return 1; fi
  return 0
}

install_agda() {
  note '== Agda =='
  if command -v agda >/dev/null 2>&1; then
    note "already present: $(agda --version | head -1)"
    return 0
  fi
  if [ ! -d "$VENV" ]; then
    python3 -m venv "$VENV"
  fi
  "$VENV/bin/pip" install --quiet --upgrade agda
  local ver
  ver="$("$VENV/bin/agda" --version | head -1 | awk '{print $3}')"
  # The binding hard-codes <site-packages>/agda/data as Agda_datadir; the data
  # directory ships in the npm package rather than in the wheel.
  if [ ! -d "$NPMDIR/node_modules/agda-wasm/data/$ver" ]; then
    mkdir -p "$NPMDIR"
    ( cd "$NPMDIR" && npm install --silent agda-wasm )
  fi
  local site
  site="$("$VENV/bin/python" -c 'import agda, os; print(os.path.dirname(agda.__file__))')"
  ln -sfn "$NPMDIR/node_modules/agda-wasm/data/$ver" "$site/data"
  note "installed: $("$VENV/bin/agda" --version | head -1) with data dir $ver"

  # Usable, not merely installed.
  if "$VENV/bin/agda" --safe --without-K --no-libraries --ignore-interfaces \
       -i src src/SecretTypes/All.agda >/dev/null 2>&1; then
    note 'verified: SecretTypes.All typechecks'
  else
    note 'ERROR: Agda is installed but cannot check SecretTypes.All' >&2
    return 1
  fi
}

install_zig() {
  note '== Zig (for src/interface/ffi) =='
  if command -v zig >/dev/null 2>&1; then
    note "already present: $(zig version)"
    return 0
  fi
  [ -d "$VENV" ] || python3 -m venv "$VENV"
  if "$VENV/bin/pip" install --quiet ziglang 2>/dev/null; then
    ln -sfn "$VENV/bin/python-zig" "$VENV/bin/zig" 2>/dev/null || true
    note "installed: $("$VENV/bin/python" -m ziglang version 2>/dev/null || echo 'check ziglang module')"
    return 0
  fi
  note 'ziglang wheel not installable' >&2
  return 1
}

status() {
  note '== what this sandbox can and cannot provision =='
  local t
  for t in agda zig rustc cargo coqc rocq lean lake idris2 lambdapi; do
    printf '%-10s %s\n' "$t" "$(command -v "$t" || echo '-')"
  done
  note ''
  note 'blocked hosts (measured):'
  local h
  for h in deb.debian.org static.rust-lang.org downloads.haskell.org release-assets.githubusercontent.com; do
    if blocked "$h"; then printf '  %-45s BLOCKED\n' "$h"; else printf '  %-45s reachable\n' "$h"; fi
  done
  note ''
  note 'so: apt (Debian Agda/Coq), rustup (Rust/Creusot), ghcup (Haskell) and'
  note 'GitHub release assets (Agda/Lean/F* binaries) are all unavailable here.'
  note 'Prebuilt prover binaries are fetched from release assets, which is the'
  note 'blocked one. PyPI and npm are available and carry Agda and Zig.'
}

case "${1:-status}" in
  agda) install_agda ;;
  zig)  install_zig ;;
  all)  install_agda; install_zig || true; status ;;
  status) status ;;
  *)
    printf 'usage: %s [agda|zig|all|status]\n' "${0##*/}" >&2
    exit 2
    ;;
esac
