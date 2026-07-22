/-
gen_extern_census.lean — the extern census via a pin-verified environment walk
(bead franken_lean-53v; plan Appendix C; Rule D5/D8-2: derived, never remembered).

Run by the PINNED Reference binary (located and commit-verified by
gen_extern_census.sh — the fixture-mine capacity of the Oracle-Only Law). The
walk imports the full `Lean` closure (which transitively contains `Init` and
`Std`) and emits, sorted by name for determinism:

  1. one row per `@[extern]` constant — the seed of Golem's intrinsic table
     (plan §11.4): name, kind, defining module, forall-arity of the declared
     type, universe-parameter count, and the encoded extern entries;
  2. a per-root-namespace × kind summary of the ENTIRE reachable constant
     surface — the builtin-census totality baseline the full Mirror-partition
     census (follow-up slice) must reconcile against.

Output is line-oriented, tab-separated, no timestamps, no absolute paths.
-/
import Lean
open Lean

def entryRepr : ExternEntry → String
  | .adhoc backend => s!"adhoc:{backend}"
  | .inline backend pattern => s!"inline:{backend}:{pattern}"
  | .standard backend fn => s!"standard:{backend}:{fn}"
  | .opaque => "opaque"

def kindRepr : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "defn"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- Root namespace component of a name, or `<anonymous-root>` for single-component names. -/
def rootOf (n : Name) : String :=
  match n.getRoot with
  | .anonymous => "<anonymous-root>"
  | root => toString root

def main : IO Unit := do
  let env ← importModules #[{module := `Lean}] {} (trustLevel := 1024)
  -- Lane 1: the extern census.
  let mut externRows : Array (String × String) := #[]
  -- Lane 2: totality summary, root namespace × kind → count.
  let mut summary : Std.TreeMap String Nat := {}
  let mut total := 0
  for (name, ci) in env.constants.toList do
    total := total + 1
    let kind := kindRepr ci
    let summaryKey := s!"{rootOf name}\t{kind}"
    summary := summary.insert summaryKey (summary.getD summaryKey 0 + 1)
    if let some data := Lean.externAttr.getParam? env name then
      let modName := match env.getModuleIdxFor? name with
        | some idx => toString env.header.moduleNames[idx.toNat]!
        | none => "<current>"
      let entries := ";".intercalate (data.entries.map entryRepr)
      let key := toString name
      externRows := externRows.push
        (key, s!"extern\t{key}\t{kind}\t{modName}\t{ci.type.getForallArity}\t{ci.levelParams.length}\t{entries}")
  let sorted := externRows.qsort (fun a b => a.1 < b.1)
  IO.println s!"extern_count\t{sorted.size}"
  IO.println s!"constant_count\t{total}"
  IO.println "columns\tname\tkind\tmodule\tarity\tlevel_params\tentries"
  for (_, row) in sorted do
    IO.println row
  IO.println "columns_summary\troot\tkind\tcount"
  for (key, count) in summary do
    IO.println s!"summary\t{key}\t{count}"
