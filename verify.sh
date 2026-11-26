#!/bin/sh
# Check everything in this repository: Lean proofs (core library only, no Mathlib), the
# comparator check, and the independent Python checks. Needs Lean 4.15.0, Python 3 and NumPy.
set -eu
cd "$(dirname "$0")"
fail() { echo "FAIL: $*" >&2; exit 1; }
MODULES="ChallengeDefs Challenge FrozenShells FreezeMovies CandyKnots CollisionLaw MaskRecovery \
CollisionCircuit SilentRoom RingCracks DegreeDivisibility CubePermutation GroupedRing \
ExactCollisionMinimum RectangularCollisionMinimum Solution"

echo "== 1. Lean version"
lean --version | grep -q 'version 4\.15\.0' || fail "need Lean 4.15.0, found: $(lean --version)"
lean --version

echo "== 2. SHA-256 checksums"
if command -v sha256sum >/dev/null 2>&1; then (cd lean && sha256sum -c --quiet SHA256SUMS) || fail "checksum mismatch"
else (cd lean && shasum -a 256 -c --quiet SHA256SUMS) || fail "checksum mismatch"; fi
echo "all $(wc -l < lean/SHA256SUMS | tr -d ' ') files OK"

echo "== 3. Forbidden tokens outside comments"
for f in lean/*.lean; do
  [ "$f" = lean/Challenge.lean ] && continue
  hits=$(python3 tools/strip_comments.py "$f" | grep -n -E \
    '(^|[^A-Za-z0-9_.])(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque)([^A-Za-z0-9_]|$)' || true)
  [ -z "$hits" ] || { echo "$hits"; fail "forbidden token in $f"; }
done
echo "no sorry/admit/axiom/native_decide in any proof or definition file"

echo "== 4. Compile"
build=$(mktemp -d "${TMPDIR:-/tmp}/qc.XXXXXX")
trap 'rm -rf "$build"' EXIT
for m in $MODULES; do
  LEAN_PATH="$build" lean -o "$build/$m.olean" "lean/$m.lean" > "$build/$m.log" 2>&1 \
    || { cat "$build/$m.log"; fail "$m did not compile"; }
  if [ "$m" != Challenge ] && grep -q -E 'error|declaration uses .sorry.' "$build/$m.log"; then
    cat "$build/$m.log"; fail "$m reported errors"; fi
  echo "$m: ok"
done

echo "== 5. Comparator: Solution proves exactly the statements in Challenge"
LEAN_PATH="$build" lean/check_comparator.sh > "$build/cmp.out" 2>&1 || { cat "$build/cmp.out"; fail "comparator check failed"; }
cat "$build/cmp.out"

echo "== 6. Axioms reported by the proof files"
cat "$build"/*.log | grep 'depends on axioms' > "$build/axioms.txt" || true
cat "$build/axioms.txt"
n=$(wc -l < "$build/axioms.txt" | tr -d ' ')
[ "$n" -gt 0 ] || fail "no axiom reports found"
bad=$(grep -v -E "depends on axioms: \[(propext|Quot.sound|Classical.choice)(, (propext|Quot.sound|Classical.choice))*\]" "$build/axioms.txt" || true)
[ -z "$bad" ] || { echo "$bad"; fail "a theorem uses an axiom outside propext, Quot.sound, Classical.choice"; }
echo "$n theorems, all on Lean's standard axioms only"

echo "== 7. Independent Python checks"
python3 -B checks/quiet_cut_runs.py
python3 -B checks/rect_exhaustive.py

echo "== ALL CHECKS PASSED"
