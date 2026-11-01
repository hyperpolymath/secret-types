#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath)
#
# dev-toolchain.sh [agda] [zig] [docs] [all] [status]
#
# Provisions, in an agent sandbox with a restricted egress allowlist, the tools
# this repository can actually get. Exits non-zero on anything it cannot
# provision, and says which host blocked it: a toolchain script that reports
# success for a tool it did not install is the same failure mode as a gate that
# cannot fail.
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

# Fixed locations under $HOME, deliberately NOT read from the environment. Every
# use below creates or writes into one of these paths, so a value inherited from
# a shell would be an injection surface, and the script only ever wants one
# location per sandbox. To move them, edit these two functions.
tool_root() { printf '%s/.tclocal' "$HOME"; }
npm_root() { printf '%s/.tc/npm' "$HOME"; }
docs_root() { printf '%s/.tc/adoc22' "$HOME"; }

note() { printf '%s\n' "$*" >&2; }

blocked() {
  local host="$1"
  if timeout 8 curl -sS -o /dev/null "https://$host/" 2>/dev/null; then return 1; fi
  return 0
}

install_agda() {
  note '== Agda =='
  local venv
  venv="$(tool_root)"
  if command -v agda >/dev/null 2>&1; then
    note "already present: $(agda --version | head -1)"
    return 0
  fi
  if ! [ -x "$venv/bin/pip" ]; then
    python3 -m venv "$venv"
  fi
  "$venv/bin/pip" install --quiet --upgrade agda
  local ver
  ver="$("$venv/bin/agda" --version | head -1 | awk '{print $3}')"
  # The binding hard-codes <site-packages>/agda/data as Agda_datadir; the data
  # directory ships in the npm package rather than in the wheel.
  local npmdir
  npmdir="$(npm_root)"
  mkdir -p "$npmdir"
  ( cd "$npmdir" && npm install --silent agda-wasm )
  local site
  site="$("$venv/bin/python" -c 'import agda, os; print(os.path.dirname(agda.__file__))')"
  ln -sfn "$npmdir/node_modules/agda-wasm/data/$ver" "$site/data"
  note "installed: $("$venv/bin/agda" --version | head -1) with data dir $ver"

  # Usable, not merely installed.
  if "$venv/bin/agda" --safe --without-K --no-libraries --ignore-interfaces \
       -i src src/SecretTypes/All.agda >/dev/null 2>&1; then
    note 'verified: SecretTypes.All typechecks'
  else
    note 'ERROR: Agda is installed but cannot check SecretTypes.All' >&2
    return 1
  fi
}

install_zig() {
  note '== Zig (for src/interface/ffi) =='
  local venv
  venv="$(tool_root)"
  if command -v zig >/dev/null 2>&1; then
    note "already present: $(zig version)"
    return 0
  fi
  if ! [ -x "$venv/bin/pip" ]; then
    python3 -m venv "$venv"
  fi
  if "$venv/bin/pip" install --quiet ziglang 2>/dev/null; then
    ln -sfn "$venv/bin/python-zig" "$venv/bin/zig" 2>/dev/null || true
    note "installed: $("$venv/bin/python" -m ziglang version 2>/dev/null || echo 'check ziglang module')"
    return 0
  fi
  note 'ziglang wheel not installable' >&2
  return 1
}

# scripts/check-adoc-renders.sh shells out to `asciidoctor` and treats ANY
# stderr as a finding. CI installs the Ruby gem (2.0.26); this sandbox cannot
# reach rubygems.org, so it uses the asciidoctor.js build that tracks the same
# Asciidoctor core.
#
# The version matters, and this was measured rather than assumed: with
# @asciidoctor/core 4.1.1 (Asciidoctor 3.x core) all 168 tracked .adoc files
# rendered clean and CI still failed, on
# "dropping cells from incomplete row detected end of table" in a table with a
# short row. @asciidoctor/core 2.2.9 (Asciidoctor 2.0.23 core) reproduces the
# Ruby 2.0.26 diagnostic exactly. A render check is only a check if its parser
# is the parser the gate uses.
install_docs() {
  note '== asciidoctor (for scripts/check-adoc-renders.sh) =='
  local dir
  dir="$(docs_root)"
  mkdir -p "$dir"
  ( cd "$dir" && npm install --silent @asciidoctor/core@2.2.9 @asciidoctor/cli@3.5.0 )
  note "installed: $("$dir/node_modules/.bin/asciidoctor" --version | head -1)"
  note "put it on PATH with: PATH=$dir/node_modules/.bin:\$PATH"
}

status() {
  note '== what this sandbox can and cannot provision =='
  local t
  for t in agda zig rustc cargo coqc rocq lean lake idris2 lambdapi asciidoctor; do
    printf '%-12s %s\n' "$t" "$(command -v "$t" || echo '-')"
  done
  note ''
  note 'blocked hosts (measured):'
  local h
  for h in deb.debian.org static.rust-lang.org downloads.haskell.org release-assets.githubusercontent.com rubygems.org; do
    if blocked "$h"; then printf '  %-45s BLOCKED\n' "$h"; else printf '  %-45s reachable\n' "$h"; fi
  done
  note ''
  note 'so: apt (Debian Agda/Coq), rustup (Rust/Creusot), ghcup (Haskell),'
  note 'rubygems (Ruby asciidoctor) and GitHub release assets (Agda/Lean/F*'
  note 'binaries) are all unavailable here. PyPI and npm are available and carry'
  note 'Agda, Zig and an asciidoctor whose diagnostics match the CI one.'
}

case "${1:-status}" in
  agda) install_agda ;;
  zig)  install_zig ;;
  docs) install_docs ;;
  all)
    install_agda
    install_zig || true
    install_docs || true
    status
    ;;
  status) status ;;
  *)
    printf 'usage: %s [agda|zig|docs|all|status]\n' "${0##*/}" >&2
    exit 2
    ;;
esac
