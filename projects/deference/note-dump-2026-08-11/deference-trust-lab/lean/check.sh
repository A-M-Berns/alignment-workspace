#!/usr/bin/env bash
# Kernel-check a Lean file in this lab against the prebuilt Mathlib in ../../lean-deference.
#
# Usage:
#   bash deference-trust-lab/lean/check.sh <ABSOLUTE-path-to-file.lean>
#
# Runs `lake env lean <file>` from the lean-deference project (read-only use: `lake env` only
# sets LEAN_PATH and runs lean; it does not build or modify that project). The file may
# `import Mathlib` submodules (do NOT `import Mathlib` wholesale — ~10 min load).
#
# SERIALIZED: this machine has ~7 GB RAM and each Lean compile uses ~1-3 GB. An flock lock makes
# concurrent invocations run ONE AT A TIME, so many verifier agents can call this freely without
# OOM. (Each waits up to 30 min for the lock.)
#
# Exit 0 + no output  => the file type-checks with no errors/sorries.
# Put `#print axioms yourTheorem` lines in the file for an axiom report; `sorryAx` in the output
# means the theorem depends on a sorry (NOT verified). A clean proof prints only
# `[propext, Classical.choice, Quot.sound]` (or a subset).
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
LEANDIR="${LEANDIR:-$(cd "$(dirname "$0")/../../lean-deference" && pwd)}"  # or set LEANDIR to your lean-deference checkout
LOCK="/tmp/dtlab-lean.lock"
if [ $# -lt 1 ]; then echo "usage: check.sh <abs-path-to.lean>"; exit 2; fi
FILE="$1"
case "$FILE" in
  /*) : ;;
  *) echo "ERROR: pass an ABSOLUTE path (got: $FILE)"; exit 2 ;;
esac
# Acquire the serialization lock (fd 9), wait up to 1800s, then compile.
exec 9>"$LOCK"
if ! flock -w 1800 9; then
  echo "ERROR: timed out waiting for the Lean serialization lock ($LOCK)"; exit 3
fi
cd "$LEANDIR"
exec lake env lean "$FILE"
