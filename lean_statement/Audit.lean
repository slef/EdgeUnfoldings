import SixVertexUnfolding
import Lean.Util.CollectAxioms

/-! Reject unfinished proofs or extra axioms anywhere in this library's theorem dependencies. -/

open Lean in
run_cmd do
  let environment ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  -- Share the dependency traversal between declarations; imported proofs overlap heavily.
  let mut auditState : CollectAxioms.State := {}
  for (name, info) in environment.constants.toList do
    if (privateToUserName name).toString.startsWith "SixVertexUnfolding." then
      let (_, nextState) := ((CollectAxioms.collect name).run environment).run auditState
      auditState := nextState
      for dependency in auditState.axioms do
        unless allowed.contains dependency do
          throwError "{name} depends on an unapproved axiom: {dependency}"
      if let .thmInfo _ := info then
        count := count + 1
  if count == 0 then
    throwError "No project theorems were audited."
  logInfo m!"Audited {count} project theorem declarations: only propext, Classical.choice, and Quot.sound."
