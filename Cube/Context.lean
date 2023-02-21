import Std.Data.RBMap

namespace Cube

structure FVarId where
  name : String
  id : Nat
deriving Repr, DecidableEq

def FVarId.toName (fvarId : FVarId) : Lean.Name :=
    .str (.num .anonymous fvarId.id) fvarId.name

instance : Ord FVarId where
  compare lhs rhs := lhs.toName.cmp rhs.toName

abbrev Env (Expr : Type u) := Std.RBMap String Expr (inferInstance : Ord String).compare
abbrev Context (Expr : Type u)  := Std.RBMap FVarId Expr (inferInstance : Ord FVarId).compare

def Env.get (env : Env Expr) (name : String) : Option Expr := env.find? name

def Context.empty : Context Expr := Std.RBMap.empty

def Context.update (ctx : Context Expr) (var : FVarId) (ty : Expr) : Context Expr :=
  ctx.insert var ty

def Context.get (ctx : Context Expr) (var : FVarId) : Option Expr := ctx.find? var

-- TODO: These should appear in std4 eventually
theorem Context.get_empty (var : FVarId): Context.empty.get var = (none : Option Expr) := by
  simp [Context.get, Std.RBMap.find?, empty, Std.RBMap.empty, Std.mkRBMap, Std.mkRBSet, Std.RBMap.findEntry?, Std.RBSet.findP?, Std.RBNode.find?, Option.map]

theorem Context.get_update (ctx : Context Expr) (var : FVarId) (ty : Expr) : (ctx.update var ty).get var = some ty := by sorry

theorem Context.get_update_irrelevant (ctx : Context Expr) (var1 var2 : FVarId) (ty : Expr) (h : var1 ≠ var2) : (ctx.update var1 ty).get var2 = ctx.get var2 := by sorry

def FVar.fresh (ctx : Context Expr) : FVarId :=
  match ctx.max with
  | none => ⟨"_uniq", 0⟩
  | some (⟨_, idx⟩, _) => ⟨"_uniq", idx + 1⟩

def FVar.freshM (ty : Expr) : StateM (Context Expr) FVarId := do
  let ctx ← get
  let new := FVar.fresh ctx
  set (ctx.update new ty)
  return new

theorem FVar.fresh_is_fresh (ctx : Context Expr) : ctx.get (FVar.fresh ctx) = none := sorry
theorem FVar.freshM_is_fresh (ctx : Context Expr) : ctx.get ((FVar.freshM ty).run' ctx) = none := by
  simp [FVar.freshM, fresh_is_fresh]

end Cube
