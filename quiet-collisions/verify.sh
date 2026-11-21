#!/bin/sh
# Check every Lean proof (core library only, no Mathlib) and run the
# independent Python checks. Needs Lean 4.15.0 and Python 3 on the PATH.
set -eu
cd "$(dirname "$0")"
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
lean --version
for f in FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery CollisionCircuit SilentRoom; do
  echo "== $f"
  LEAN_PATH="$build" lean -o "$build/$f.olean" "lean/$f.lean"
done
echo "== RingCracks"
LEAN_PATH="$build" lean lean/RingCracks.lean
echo "== Python checks"
python3 -B checks/quiet_cut_runs.py
