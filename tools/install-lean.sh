#!/bin/sh
# Install Lean 4 (core only, no Mathlib) via the official installer, elan.
#
# The environment's network settings must allow:
#   raw.githubusercontent.com   (installer script)
#   release.lean-lang.org       (toolchain lookup)
#   releases.lean-lang.org      (toolchain download; redirects to GitHub)
#   release-assets.githubusercontent.com, objects.githubusercontent.com
set -eu
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain none
cd "$(dirname "$0")/.."
"$HOME/.elan/bin/lean" --version
