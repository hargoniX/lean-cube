import Cube.Simple.Basic
import Lean
open Lean

namespace Cube.Simple.Bidirectional

inductive Ast where
| annot (ast : Ast) (ty : Ty)
| var (name : String)
| const (name : String)
| lam (var : String) (body : Ast)
| app (func : Ast) (arg : Ast)
deriving Repr

inductive Expr where
| annot (expr : Expr) (ty : Ty)
| bvar (idx : Nat)
| fvar (name : FVarId)
| lam (body : Expr)
| const (name : String)
| app (func : Expr) (arg : Expr)
deriving Repr, DecidableEq, Inhabited, Hashable

abbrev TranslationEnv := List String

def Ast.toExpr : Ast → TranslationEnv → Expr
| annot ast ty, vs => .annot (toExpr ast vs) ty
| var name, vs =>
  match vs.findIdx? (name = ·) with
  | some idx => .bvar idx
  | none => .fvar ⟨name, 0⟩
| const name, _ => .const name
| app func arg, vs => .app (toExpr func vs) (toExpr arg vs)
| lam x body, vs => .lam (toExpr body <| x :: vs)

declare_syntax_cat stlcBd

syntax ident : stlcBd
syntax num : stlcBd
syntax stlcBd:10 stlcBd:11 : stlcBd
syntax "λ " ident " . " stlcBd : stlcBd
syntax "(" stlcBd ")" : stlcBd
syntax "(" stlcBd ":" stlcTy ")" : stlcBd

syntax "[stlcBdA|" stlcBd "]" : term
syntax "[stlcBd|" stlcBd "]" : term

macro_rules
  | `([stlcBdA| $x:ident]) =>
    let strId := x.getId.toString
    let first := strId.get ⟨0⟩
    if first.isUpper then
      `(Ast.const $(quote <| strId))
    else
      `(Ast.var $(quote strId))
  | `([stlcBdA| $n:num]) => `(Ast.const $(quote n.getNat.repr))
  | `([stlcBdA| λ $x . $b]) => `(Ast.lam $(quote x.getId.toString) [stlcBdA| $b])
  | `([stlcBdA| $f $x]) => `(Ast.app [stlcBdA| $f] [stlcBdA| $x])
  | `([stlcBdA| ($x)]) => `([stlcBdA| $x])
  | `([stlcBdA| ($x : $ty)]) => `(Ast.annot [stlcBdA| $x] [stlcTy| $ty])
  | `([stlcBd| $t ]) => `(Ast.toExpr [stlcBdA| $t] [])

#eval [stlcBd| λ f . (λ x . (f (x : ℕ)) free)]

namespace Expr

def abstract (expr : Expr) (target : FVarId) (idx : Nat := 0) : Expr :=
  match expr with
  | .fvar name =>
    if target = name then
      .bvar idx
    else
      .fvar name
  | .app fn arg => .app (abstract fn target idx) (abstract arg target idx)
  | .lam body => .lam (abstract body target (idx + 1))
  | .const name => .const name
  | .bvar idx => .bvar idx
  | .annot x ty => .annot (abstract x target idx) ty

def instantiate (expr : Expr) (image : Expr) (targetIdx : Nat := 0) : Expr :=
  match expr with
  | .bvar idx =>
    if idx = targetIdx then
      image
    else
      .bvar idx
  | .app fn arg => .app (instantiate fn image targetIdx ) (instantiate arg image targetIdx )
  | .lam body => .lam (instantiate body image (targetIdx + 1))
  | .fvar name => .fvar name
  | .const name => .const name
  | .annot x ty => .annot (instantiate x image targetIdx) ty

mutual

def check (expr : Expr) (ty : Ty) : SimpleM Bool := do
  match expr with
  | .lam body =>
    match ty with
    | .fun t1 t2 =>
      let newFVar := FVar.fresh (← getCtx)
      let newBody := body.instantiate (.fvar newFVar)
      let ctx ← getCtx
      modify (fun ctx => ctx.insert newFVar t1)
      try
        check newBody t2
      finally
        set ctx
    | _ => throw s!"Lambda expression {repr expr} cannot have non function type: {repr ty}"
  | _ =>
    let synthedTy ← synthesize expr
    return synthedTy == ty

def synthesize (expr : Expr) : SimpleM Ty := do
  match expr with
  | .bvar idx => throw s!"Unbound variable index: {idx}"
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
  | .app fn arg =>
      if let .fun t1 t2 ← synthesize fn then
        if ← check arg t1 then
          return t2
        else
          throw s!"Arg type mismatch in {repr expr}, argument should have type {repr t1}"
      else
        throw s!"Function type mismatch in {repr expr}, function should have function type"
  | .annot x ty =>
    if ← check x ty then
      return ty
    else
      throw s!"Expression {repr x} should have type {repr ty} but that is invalid"
  | .lam _ => throw s!"Cannot blindly infer types of lambda expression {repr expr}"

end
-- TODO: Use another size measure where fvar and bvar size is equivalent, then it works
termination_by _ => expr
decreasing_by sorry

#eval synthesize [stlcBd| ((λ f . (λ x . f x) : (ℕ → ℕ) → ℕ → ℕ) Add) 0] |>.run' (Env.empty.insert "Add" (.fun .nat .nat) |>.insert "0" .nat) Context.empty

end Expr

end Cube.Simple.Bidirectional
