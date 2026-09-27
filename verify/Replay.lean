import Lean
open Lean

def closureOf (env : Environment) (roots : Array Name) : IO NameSet := do
  let mut seen : NameSet := {}
  let mut stack := roots
  while stack.size > 0 do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | none => throw <| IO.userError s!"missing constant {n}"
    | some ci =>
      for m in ci.getUsedConstantsAsSet do
        unless seen.contains m do stack := stack.push m
      match ci with
      | .inductInfo v =>
        for c in v.ctors do stack := stack.push c
        for a in v.all do stack := stack.push a
      | .ctorInfo v => stack := stack.push v.induct
      | .recInfo v => for a in v.all do stack := stack.push a
      | _ => pure ()
  return seen

unsafe def main (args : List String) : IO UInt32 := do
  let tamper := args.contains "tamper"
  initSearchPath (← findSysroot)
  let roots : Array Name := #[`Collatz.nd_collatz_uniform_explicit, `Collatz.nd_collatz_uniform,
    `Collatz.tstarExponent_eq, `Collatz.tstarExponent_pos,
    `FirstPassageLinearTransport.FixedBarrier.fixedBarrier_failure_count]
  let t0 ← IO.monoMsNow
  let full ← importModules #[{module := `CollatzND.Core.Explicit}] {} (trustLevel := 0) (loadExts := false)
  let cl ← closureOf full roots
  IO.println s!"closure size: {cl.size}"
  let base ← importModules #[{module := `Mathlib}] {} (trustLevel := 0) (loadExts := false)
  let mut newMap : Std.HashMap Name ConstantInfo := {}
  let mut axioms : Array Name := #[]
  let mut skipped : Array Name := #[]
  let mut mods : Std.HashMap Name Nat := {}
  for n in cl do
    let ci := (full.find? n).get!
    if let .axiomInfo _ := ci then axioms := axioms.push n
    if ci.isUnsafe || ci.isPartial then skipped := skipped.push n
    match base.find? n with
    | some ci' =>
      -- identical in base?
      unless ci'.type == ci.type do IO.println s!"TYPE MISMATCH base/full: {n}"
    | none =>
      newMap := newMap.insert n ci
      let modName := match full.getModuleIdxFor? n with
        | some idx => full.header.moduleNames[idx.toNat]!
        | none => `unknown
      let top := modName.getRoot
      mods := mods.insert top ((mods.getD top 0) + 1)
  IO.println s!"axioms in closure: {axioms}"
  IO.println s!"unsafe/partial in closure: {skipped}"
  IO.println s!"constants to replay (not in Mathlib): {newMap.size}"
  for (m, k) in mods.toList do IO.println s!"  from {m}: {k}"
  let t1 ← IO.monoMsNow
  IO.println s!"import+closure took {(t1 - t0)/1000}s; replaying..."
  if tamper then
    let r := `FirstPassageLinearTransport.FixedBarrier.fixedBarrier_failure_count_timed_rate
    match newMap[r]? with
    | some (.thmInfo v) =>
      newMap := newMap.insert r (.thmInfo { v with value := mkConst ``True.intro })
      IO.println "TAMPERED fixedBarrier_failure_count_timed_rate := True.intro"
    | _ => IO.println "tamper target not found"
  let env' ← base.replay newMap
  let t2 ← IO.monoMsNow
  IO.println s!"replay OK in {(t2 - t1)/1000}s"
  for r in roots do
    match env'.toKernelEnv.find? r, full.find? r with
    | some a, some b =>
      IO.println s!"{r}: in replayed env, type equal = {a.type == b.type}, isThm = {a matches .thmInfo _}"
    | _, _ => IO.println s!"{r}: MISSING after replay"
  let mut inK := 0
  for (n, _) in newMap.toList do
    if (env'.toKernelEnv.find? n).isSome then inK := inK + 1
  IO.println s!"replayed constants present in kernel env: {inK}/{newMap.size}"
  return 0
