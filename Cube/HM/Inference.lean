import Cube.HM.Basic

namespace Cube.HM

def Ty.varBind (fvarId : FVarId) (ty : Ty) : HMM Substitution := do
  if .tvar fvarId == ty then
    return .empty
  else if ty.free.find? fvarId |>.isSome then
    throw s!"occurs check failed {repr fvarId} vs {repr ty}"
  else
    return .empty |>.insert fvarId ty

partial def Ty.mgu (t1 t2 : Ty) : HMM Substitution := do
  match t1, t2 with
  | .fun l1 r1, .fun l2 r2 =>
    let s1 ← mgu l1 l2
    let s2 ← mgu (r1.apply s1) (r2.apply s1)
    return s1.compose s2
  | .tvar u, t | t, .tvar u => varBind u t
  | .const n1, .const n2 =>
    if n1 == n2 then
      return .empty
    else
      throw s!"{n1} is not the same type as s2"
  | _, _ => throw s!"Could not unify types {repr t1} and {repr t2}"

/-
Algorithm W after https://github.com/wh5a/Algorithm-W-Step-By-Step/blob/master/AlgorithmW.pdf
-/
partial def algoW (expr : Expr) : HMM Ty := do
  let (subst, ty) ← go expr
  return Types.apply subst ty
where
  go (expr : Expr) : HMM (Ty.Substitution × Ty) := do
    match expr with
    | .bvar idx => throw s!"Unbound variable index: {idx}"
    | .fvar fvarId =>
      if let some typ := (← getCtx).find? fvarId then
        return (.empty, ← typ.instantiate)
      else
        throw s!"FVarId: {repr fvarId} not found in context"
    | .const name => 
      if let some typ := (← getEnv).find? name then
        return (.empty, ← typ.instantiate)
      else
        throw s!"Constant: {name} not found in environment"
    | .lam body =>
      let newFVar := FVar.fresh (← getCtx)
      let newBody := body.instantiate (.fvar newFVar)
      let t1 := .tvar (← FVar.freshM Kind.unit)
      let ctx ← getCtx
      modifyThe Context (fun ctx => ctx.insert newFVar ⟨[], t1⟩)
      let (subst, t2) ← go newBody
      set ctx
      return (subst, .fun (Types.apply subst t1) t2)
    | .app fn arg =>
      let (fnSubst, fnTy) ← go fn
      let ctx ← getCtx
      modifyThe Context (fun ctx => Types.apply fnSubst ctx)
      let (argSubst, argTy) ← go arg
      set ctx
      let t' := .tvar (← FVar.freshM Kind.unit)
      let unifier ← Ty.mgu (Types.apply argSubst fnTy) (.fun argTy t')
      return (fnSubst.compose argSubst |>.compose unifier, Types.apply unifier t')
    | .let val body =>
      let (valSubst, valTy) ← go val
      let ctx ← getCtx
      let newFVar := FVar.fresh ctx
      modifyThe Context (fun ctx => ctx.insert newFVar (valTy.generalize (Types.apply valSubst ctx)))
      let newBody := body.instantiate (.fvar newFVar)
      let (bodySubst, bodyTy) ← go newBody
      set ctx
      return (valSubst.compose bodySubst, bodyTy)

#eval algoW [hm| (λ x . x) 0] |>.run' .empty (.empty |>.insert "0" ⟨[], .const "Nat"⟩) .empty
#eval algoW [hm| (λ x . x)] |>.run' .empty .empty .empty
#eval algoW [hm| let id := (λ x . x) in id] |>.run' .empty .empty .empty
#eval algoW [hm| let const1 := (λ x . λ y . x) in const1] |>.run' .empty .empty .empty
#eval algoW [hm| let const2 := (λ x . λ y . y) in const2] |>.run' .empty .empty .empty
#eval algoW [hm| let const1 := (λ x . λ y . x) in const1 0] |>.run' .empty (.empty |>.insert "0" ⟨[], .const "Nat"⟩) .empty

end Cube.HM
