import Cube.Util
import Cube.Context

import Std.Lean.HashSet

import Lean

open Lean

namespace Cube.HM

inductive Kind where
| unit

inductive Ty where
| tvar (fvarId : FVarId)
| fun (t1 t2 : Ty)
| const (name : String)
deriving Repr, Hashable, BEq, Inhabited

structure Scheme where
  binder : List FVarId
  body : Ty

inductive Ast where
| var (name : String)
| const (name : String)
| lam (var : String) (body : Ast)
| app (func : Ast) (arg : Ast)
| let (name : String) (val : Ast) (body : Ast)

inductive Expr where
| bvar (idx : Nat)
| fvar (name : FVarId)
| lam (body : Expr)
| const (name : String)
| app (func : Expr) (arg : Expr)
| let (val : Expr) (body : Expr)
deriving Repr

abbrev TranslationEnv := List String

def Ast.toExpr : Ast → TranslationEnv → Expr
| .var name, vs =>
  match vs.findIdx? (name = ·) with
  | some idx => .bvar idx
  | none => .fvar ⟨name, 0⟩
| .const name, _ => .const name
| .app func arg, vs => .app (toExpr func vs) (toExpr arg vs)
| .lam x body, vs => .lam (toExpr body <| x :: vs)
| .let x val body, vs => .let (toExpr val vs) (toExpr body <| x :: vs)

declare_syntax_cat hm

syntax ident : hm
syntax num : hm
syntax hm:10 hm:11 : hm
syntax "λ " ident " . " hm : hm
syntax "let " ident ":=" hm " in " hm : hm
syntax "(" hm ")" : hm

syntax "[hmA|" hm "]" : term
syntax "[hm|" hm "]" : term

macro_rules
  | `([hmA| $x:ident]) =>
    let strId := x.getId.toString
    let first := strId.get ⟨0⟩
    if first.isUpper then
      `(Ast.const $(quote <| strId))
    else
      `(Ast.var $(quote strId))
  | `([hmA| $n:num]) => `(Ast.const $(quote n.getNat.repr))
  | `([hmA| λ $x . $b]) => `(Ast.lam $(quote x.getId.toString) [hmA| $b])
  | `([hmA| let $x := $val in $b]) => `(Ast.let $(quote x.getId.toString) [hmA| $val] [hmA| $b])
  | `([hmA| $f $x]) => `(Ast.app [hmA| $f] [hmA| $x])
  | `([hmA| ($x)]) => `([hmA| $x])
  | `([hm| $t ]) => `(Ast.toExpr [hmA| $t] [])

#eval [hm| λ x . let y := (Add x) x in A y]

abbrev Context := Cube.Context Scheme
abbrev TyContext := Cube.Context Kind
abbrev Env := Cube.Env Scheme
abbrev HMT (m : Type → Type) := StateT TyContext (ReaderT Env (StateT Context (ExceptT String m)))
abbrev HMM := HMT Id

def getCtx : HMM Context := do return (← getThe Context)
def getTyCtx : HMM TyContext := do return (← getThe TyContext)
def getEnv : HMM Env := do return (← readThe Env)

def HMM.run' (x : HMM α) (tyCtx : TyContext) (env : Env) (ctx : Context) : Except String α :=
  StateT.run' x tyCtx |>.run env |>.run' ctx


abbrev Ty.Substitution := Cube.Substitution Ty

class Types (α : Type u) where
  free : α → HashSet FVarId
  apply : Ty.Substitution → α → α

instance [Types α] : Types (List α) where
  free l := List.foldl (init := .empty) HashSet.merge (l.map Types.free)
  apply s xs := xs.map (Types.apply s)

namespace Ty

def free (ty : Ty) : HashSet FVarId :=
  go ty .empty
where
  go (ty : Ty) (set : HashSet FVarId) : HashSet FVarId :=
    match ty with
    | .tvar fvarId => set.insert fvarId
    | .fun t1 t2 => go t2 (go t1 set)
    | .const _ => set

def apply (subst : Substitution) (ty : Ty) : Ty :=
  match ty with
  | .tvar fvarId => (subst.find? fvarId |>.getD (.tvar fvarId))
  | .fun t1 t2 => .fun (apply subst t1) (apply subst t2)
  | .const name => .const name

instance : Types Ty where
  free := free
  apply := apply

end Ty

namespace Scheme

def free (scheme : Scheme) : HashSet FVarId :=
  let bodyFree := scheme.body.free
  scheme.binder.foldl (init := bodyFree) HashSet.erase

def apply (subst : Ty.Substitution) (scheme : Scheme) : Scheme :=
  let subst := scheme.binder.foldl (init := subst) .erase
  { scheme with body := scheme.body.apply subst }

instance : Types Scheme where
  free := free
  apply := apply

end Scheme

namespace Context

def free (ctx : Context) : HashSet FVarId :=
  Types.free ctx.valuesList

def apply (subst : Ty.Substitution) (ctx : Context) : Context :=
  ctx.mapVal (fun _ value => Types.apply subst value)

instance : Types Context where
  free := free
  apply := apply

end Context

def Ty.generalize (ctx : Context) (ty : Ty) : Scheme :=
  let binder := Types.free ctx |>.fold (init := Types.free ty) .erase
  { binder := binder.toList , body := ty}

def Scheme.instantiate (scheme : Scheme) : HMM Ty := do
  let freshFVars ← scheme.binder.mapM (fun _ => .tvar <$> FVar.freshM Kind.unit)
  let subst := Std.RBMap.ofList (scheme.binder.zip freshFVars) _
  return Types.apply subst scheme.body

namespace Expr
abbrev Substitution := Cube.Substitution Expr

-- From I'm not a number I'm a free variable
def abstract (expr : Expr) (target : FVarId) (idx : Nat := 0): Expr :=
  match expr with
  | .fvar name =>
    if target = name then
      .bvar idx
    else
      .fvar name
  | .app fn arg => .app (abstract fn target idx) (abstract arg target idx )
  | .lam body => .lam (abstract body target (idx + 1))
  | .let val body => .let (abstract val target idx) (abstract body target (idx + 1))
  | .const name => .const name
  | .bvar idx => .bvar idx

def instantiate (expr : Expr) (image : Expr) (targetIdx : Nat := 0) : Expr :=
  match expr with
  | .bvar idx =>
    if idx = targetIdx then
      image
    else
      .bvar idx
  | .app fn arg => .app (instantiate fn image targetIdx ) (instantiate arg image targetIdx )
  | .lam body => .lam (instantiate body image (targetIdx + 1))
  | .let val body => .let (instantiate val image targetIdx) (instantiate body image (targetIdx + 1))
  | .fvar name => .fvar name
  | .const name => .const name

def substitute (expr : Expr) (fvarId : FVarId) (image : Expr) : Expr :=
  expr.abstract fvarId |>.instantiate image

def applySubst (subst : Substitution) (expr : Expr) : Expr :=
  subst.toList.foldl (init := expr) (fun expr (fvarId, image) => expr.substitute fvarId image)

end Expr


end Cube.HM
