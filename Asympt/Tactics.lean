import Lean.Elab.Tactic

open Lean Elab.Tactic Meta

/--
`struct_exact s` tries to find a field of the structure `s`
that closes the goal when applied, and fails otherwise
-/
elab "struct_exact" id:ident : tactic => do
  let goal ← getMainGoal
  let expr ← elabTerm id none
  let type ← inferType expr
  let sname := type.getAppFn.constName!
  let env ← getEnv
  let idfields := getStructureFields env sname
  for field in idfields do
    let fval ← mkProjection expr field
    try
      let newgoals ← goal.apply fval
      if newgoals.length == 0 then return
    catch _ => continue
  failure
