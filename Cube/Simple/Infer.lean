import Cube.Simple.Basic

namespace Cube.Simple.Expr

partial def infer (expr : Expr) : SimpleM Ty := do
  match expr with
  | .bvar idx => throw s!"Unbound variable index: {idx}"
  | .app fn arg => 
      if let .fun t1 t2 ← infer fn then
        let t3 ← infer arg
        if t1 = t3 then
          return t2
        else
          throw s!"Arg type mismatch in {repr expr}, argument should have type {repr t1} but has type {repr t3}"
      else
        throw s!"Function type mismatch in {repr expr}, function should have function type"
  | .lam t1 body =>
    let newFVar := FVar.fresh (← getCtx)
    let newBody := body.instantiate (.fvar newFVar)
    let ctx ← getCtx
    modify (fun ctx => ctx.insert newFVar t1)
    try
      let t2 ← infer newBody
      return .fun t1 t2
    finally
      set ctx
  | .fvar fvarId =>
    if let some typ := (← getCtx).find? fvarId then
      return typ
    else
      throw s!"FVarId: {repr fvarId} not found in context"
  | .const name => 
    if let some typ := (← getEnv).find? name then
      return typ
    else
      throw s!"Constant: {name} not found in environment"

#eval infer [stlc| (λ f : ℕ → ℕ. f 12) (λ x : ℕ. x)] |>.run' (Env.empty.insert "12" .nat) {}
#eval infer [stlc| (λ f : ℕ → ℕ. g (f 12)) (λ x : ℕ. x)] |>.run' (Env.empty.insert "12" .nat) (Context.empty.insert ⟨"g", 0⟩ [stlcTy| ℕ → ℕ])

end Cube.Simple.Expr
