#!/usr/bin/env bash
# check_comparator.sh: check that Solution.lean proves exactly the statements in Challenge.lean.
#
# 1. Audits the trusted files: ChallengeDefs.lean has no imports, Challenge.lean imports only
#    ChallengeDefs, and no proof file contains sorry/admit/axiom/native_decide outside comments.
# 2. Loads the compiled Challenge and Solution modules and, for every theorem in config.json,
#    checks that the two statements are identical, that every definition they depend on is
#    identical, and that the proof uses only the permitted axioms.
#
# Needs compiled .olean files: run `lake build` first, or set LEAN_PATH to a build directory.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cd "$SCRIPT_DIR"

echo "=== [1/2] Auditing the trusted files ==="
python3 - <<'PY'
import pathlib, re, sys
sys.path.insert(0, str(pathlib.Path("../tools").resolve()))
from strip_comments import code_only
def imports(p):
    return re.findall(r'^\s*import\s+(\S+)', code_only(pathlib.Path(p).read_text()), re.M)
assert imports("ChallengeDefs.lean") == [], "ChallengeDefs.lean must have no imports"
assert imports("Challenge.lean") == ["ChallengeDefs"], "Challenge.lean must import only ChallengeDefs"
bad = re.compile(r'(?<![\w.])(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque)(?![\w])')
for p in sorted(str(q) for q in pathlib.Path(".").glob("*.lean") if q.name != "Challenge.lean"):
    hits = bad.findall(code_only(pathlib.Path(p).read_text()))
    assert not hits, f"disallowed tokens in {p}: {hits}"
print("PASS: trusted files import nothing else; no sorry/admit/axiom/native_decide in proof files.")
PY

if [ -z "${LEAN_PATH:-}" ]; then
  if [ -f "../.lake/build/lib/Solution.olean" ]; then
    export LEAN_PATH="$SCRIPT_DIR/../.lake/build/lib"
  else
    echo "No compiled modules found: run 'lake build' in the repository root first." >&2
    exit 1
  fi
fi

echo "=== [2/2] Comparing statements, definitions and axioms ==="
TMP_CHECK="$(mktemp "${TMPDIR:-/tmp}/qc_cmp_XXXXXX")"
mv "$TMP_CHECK" "$TMP_CHECK.lean"; TMP_CHECK="$TMP_CHECK.lean"
trap 'rm -f "$TMP_CHECK"' EXIT
cat > "$TMP_CHECK" <<'LEAN'
import Lean

open Lean

def collectTypeConsts (env : Environment) (roots : List Name) : NameSet :=
  Id.run do
    let mut visited : NameSet := {}
    let mut work : List Name := roots
    while !work.isEmpty do
      let n :: rest := work | break
      work := rest
      if visited.contains n then continue
      visited := visited.insert n
      if let some ci := env.find? n then
        for c in ci.type.getUsedConstants do
          if !visited.contains c then work := c :: work
        if let some v := ci.value? then
          match ci with
          | .thmInfo _ => pure ()
          | _ =>
            for c in v.getUsedConstants do
              if !visited.contains c then work := c :: work
    return visited

def quotKindEq : QuotKind → QuotKind → Bool
  | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
  | _, _ => false

def constDeclEq (a b : ConstantInfo) : Bool :=
  match a, b with
  | .defnInfo x, .defnInfo y =>
      x.levelParams == y.levelParams && x.type == y.type && x.value == y.value
  | .axiomInfo x, .axiomInfo y =>
      x.levelParams == y.levelParams && x.type == y.type
  | .inductInfo x, .inductInfo y =>
      x.levelParams == y.levelParams && x.type == y.type &&
      x.numParams == y.numParams && x.numIndices == y.numIndices &&
      x.ctors == y.ctors
  | .ctorInfo x, .ctorInfo y =>
      x.levelParams == y.levelParams && x.type == y.type &&
      x.induct == y.induct && x.cidx == y.cidx && x.numParams == y.numParams && x.numFields == y.numFields
  | .recInfo x, .recInfo y =>
      x.levelParams == y.levelParams && x.type == y.type &&
      x.numParams == y.numParams && x.numIndices == y.numIndices && x.numMotives == y.numMotives
  | .quotInfo x, .quotInfo y =>
      x.levelParams == y.levelParams && x.type == y.type && quotKindEq x.kind y.kind
  | .opaqueInfo x, .opaqueInfo y =>
      x.levelParams == y.levelParams && x.type == y.type && x.value == y.value
  | .thmInfo x, .thmInfo y =>
      x.levelParams == y.levelParams && x.type == y.type
  | _, _ => false

structure Cfg where
  challenge_module : String
  solution_module : String
  theorem_names : Array String
  permitted_axioms : Array String
  deriving FromJson

def main (args : List String) : IO Unit := do
  let cfgPath := args[0]?.getD "config.json"
  let txt ← IO.FS.readFile cfgPath
  let cfg : Cfg ← IO.ofExcept <| (Json.parse txt >>= fromJson?)
  initSearchPath (← findSysroot)
  let envC ← importModules #[{ module := cfg.challenge_module.toName }] {} (trustLevel := 0)
  let envS ← importModules #[{ module := cfg.solution_module.toName }] {} (trustLevel := 0)
  let allowed : NameSet := cfg.permitted_axioms.foldl (fun s a => s.insert a.toName) {}
  let mut rootTypes : List Name := []
  for thmStr in cfg.theorem_names do
    let nm := thmStr.toName
    let some (.thmInfo ciC) := envC.find? nm
      | throw <| IO.userError s!"Missing theorem in {cfg.challenge_module}: {nm}"
    let some (.thmInfo ciS) := envS.find? nm
      | throw <| IO.userError s!"Missing theorem in {cfg.solution_module}: {nm}"
    if ciC.levelParams != ciS.levelParams || ciC.type != ciS.type then
      throw <| IO.userError s!"Statement MISMATCH for {nm}"
    for c in ciC.type.getUsedConstants do
      rootTypes := c :: rootTypes
    let (_, st) := (CollectAxioms.collect nm).run envS {}
    for ax in st.axioms do
      if !allowed.contains ax then
        throw <| IO.userError s!"Disallowed axiom {ax} in {nm}"
    IO.println s!"[ok] {nm}  axioms={st.axioms.toList}"
  let depConsts := collectTypeConsts envC rootTypes
  let mut checked := 0
  for c in depConsts do
    let some a := envC.find? c
      | throw <| IO.userError s!"Missing dep {c} in Challenge"
    let some b := envS.find? c
      | throw <| IO.userError s!"Missing dep {c} in Solution"
    if !constDeclEq a b then
      throw <| IO.userError s!"Definition MISMATCH on transitive dependency {c}"
    checked := checked + 1
  IO.println s!"PASS: all {cfg.theorem_names.size} theorems match Challenge.lean ({checked} definitions identical; axioms within the permitted list)."
LEAN

lean --run "$TMP_CHECK" config.json
