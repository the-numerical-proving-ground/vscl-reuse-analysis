import Lean

open Lean

namespace VSCLDirectUsage

private def bodyConstants : ConstantInfo → NameSet
  | .defnInfo d => d.value.getUsedConstantsAsSet
  | .thmInfo d => d.value.getUsedConstantsAsSet
  | .opaqueInfo d => d.value.getUsedConstantsAsSet
  | .recInfo d => d.rules.foldl (init := {}) fun names rule =>
      names ++ rule.rhs.getUsedConstantsAsSet
  | _ => {}

private def ownerModule? (env : Environment) (name : Name) : Option Name := do
  let index ← env.getModuleIdxFor? name
  return env.header.moduleNames[index]!

private def isLibraryModule (libraryRoot moduleName : Name) : Bool :=
  moduleName == libraryRoot || moduleName.toString.startsWith (libraryRoot.toString ++ ".")

/-- Follow submitted helper bodies only. Library and Mathlib bodies are opaque
    boundaries for this metric. Declaration types are not additional roots. -/
private def collect (env : Environment) (moduleName target libraryPrefix : Name) :
    IO (Array Name × Array Name) := do
  unless (env.find? target).isSome do
    throw <| IO.userError s!"unknown target declaration: {target}"
  unless ownerModule? env target == some moduleName do
    throw <| IO.userError "the target must belong to the submitted module"
  let mut queue := #[target]
  let mut cursor := 0
  let mut visited : NameSet := {}
  let mut library : NameSet := {}
  while cursor < queue.size do
    let name := queue[cursor]!
    cursor := cursor + 1
    unless visited.contains name do
      visited := visited.insert name
      let some info := env.find? name | continue
      for dependency in (bodyConstants info).toArray do
        if let some owner := ownerModule? env dependency then
          if isLibraryModule libraryPrefix owner then
            library := library.insert dependency
          else if owner == moduleName then
            queue := queue.push dependency
  let sortNames := fun (names : NameSet) =>
    names.toArray.qsort fun a b => a.toString < b.toString
  return (sortNames library, sortNames visited)

unsafe def run (args : List String) : IO UInt32 := do
  let (moduleText, targetText, prefixText) ← match args with
    | [m, t] => pure (m, t, "NumStability")
    | [m, t, p] => pure (m, t, p)
    | _ =>
        IO.eprintln "usage: lean --run direct_usage.lean MODULE TARGET [LIBRARY_MODULE_PREFIX]"
        return 2
  initSearchPath (← findSysroot)
  let moduleName := moduleText.toName
  withImportModules #[{ module := moduleName }] {} fun env => do
    let (used, reachable) ← collect env moduleName targetText.toName prefixText.toName
    IO.println <| (Json.mkObj [
      ("metric", Json.str "direct-proof-declarations-v1"),
      ("module", Json.str moduleText),
      ("target", Json.str targetText),
      ("library_module_prefix", Json.str prefixText),
      ("count", toJson used.size),
      ("declarations", toJson <| used.map Name.toString),
      ("reachable_submitted_declarations", toJson <| reachable.map Name.toString)
    ]).compress
    return 0

end VSCLDirectUsage

unsafe def main (args : List String) : IO UInt32 := VSCLDirectUsage.run args
