import Std.Data.RBMap

namespace Cube

structure FVarId where
  name : String
  id : Nat
deriving Repr, DecidableEq, Hashable

def FVarId.toName (fvarId : FVarId) : Lean.Name :=
    .str (.num .anonymous fvarId.id) fvarId.name

instance : Ord FVarId where
  compare lhs rhs := lhs.toName.cmp rhs.toName

abbrev Env (Expr : Type u) := Std.RBMap String Expr (inferInstance : Ord String).compare
abbrev Context (Expr : Type u)  := Std.RBMap FVarId Expr (inferInstance : Ord FVarId).compare
abbrev Substitution (Expr : Type u)  := Std.RBMap FVarId Expr (inferInstance : Ord FVarId).compare

def Env.empty : Env Expr := {}
def Context.empty : Context Expr := {}
def Substitution.empty : Substitution Expr := {}
def Substitution.compose (subst1 subst2 : Substitution Expr) : Substitution Expr :=
  subst1.foldl (init := subst2) Std.RBMap.insert

def FVar.fresh (ctx : Context Expr) : FVarId :=
  match ctx.max with
  | none => ⟨"_uniq", 0⟩
  | some (⟨_, idx⟩, _) => ⟨"_uniq", idx + 1⟩

def FVar.freshM {m : Type → Type} [MonadStateOf (Context Expr) m] [Monad m] (ty : Expr) : m FVarId := do
  let ctx ← get
  let new := FVar.fresh ctx
  set (ctx.insert new ty)
  return new

end Cube
