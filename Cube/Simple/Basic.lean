import Cube.Util
import Cube.Context

import Lean

open Lean

namespace Cube.Simple

inductive Ty where
| nat
| fun (pre : Ty) (image : Ty)
deriving Repr, DecidableEq, Inhabited, Hashable

def Ty.telescope (ty : Ty) : Array Ty :=
  go ty #[]
where
  go (ty : Ty) (acc : Array Ty) :=
    match ty with
    | .nat => acc.push .nat
    | .fun t1 t2 => go t2 (acc.push t1)

def Ty.ofTelescope (telescope : Array Ty) : Ty :=
  telescope[:telescope.size - 1].foldr (init := telescope[telescope.size - 1]!) (fun arg acc => .fun arg acc)

inductive Ast where
| var (name : String)
| const (name : String)
| lam (var : String) (ty : Ty) (body : Ast)
| app (func : Ast) (arg : Ast)
deriving Repr

inductive Expr where
| bvar (idx : Nat)
| fvar (name : FVarId)
| lam (ty : Ty) (body : Expr)
| const (name : String)
| app (func : Expr) (arg : Expr)
deriving Repr, DecidableEq, Inhabited, Hashable

abbrev TranslationEnv := List String

def Ast.toExpr : Ast → TranslationEnv → Expr
| var name, vs =>
  match vs.findIdx? (name = ·) with
  | some idx => .bvar idx
  | none => .fvar ⟨name, 0⟩
| const name, _ => .const name
| app func arg, vs => .app (toExpr func vs) (toExpr arg vs)
| lam x ty body, vs => .lam ty (toExpr body <| x :: vs)

declare_syntax_cat stlc
declare_syntax_cat stlcTy
syntax "ℕ" : stlcTy
syntax stlcTy "→" stlcTy : stlcTy
syntax "(" stlcTy ")" : stlcTy

syntax ident : stlc
syntax num : stlc
syntax stlc:10 stlc:11 : stlc
syntax "λ " ident ":" stlcTy " . " stlc : stlc
syntax "(" stlc ")" : stlc

syntax "[stlcTy|" stlcTy "]" : term
syntax "[stlcA|" stlc "]" : term
syntax "[stlc|" stlc "]" : term

macro_rules
  | `([stlcTy| ℕ]) => `(Ty.nat)
  | `([stlcTy| $a → $b]) => `(Ty.fun [stlcTy| $a] [stlcTy| $b])
  | `([stlcTy| ($x)]) => `([stlcTy| $x])

  | `([stlcA| $x:ident]) =>
    let strId := x.getId.toString
    let first := strId.get ⟨0⟩
    if first.isUpper then
      `(Ast.const $(quote <| strId))
    else
      `(Ast.var $(quote strId))
  | `([stlcA| $n:num]) => `(Ast.const $(quote n.getNat.repr))
  | `([stlcA| λ $x : $ty . $b]) => `(Ast.lam $(quote x.getId.toString) [stlcTy| $ty]  [stlcA| $b])
  | `([stlcA| $f $x]) => `(Ast.app [stlcA| $f] [stlcA| $x])
  | `([stlcA| ($x)]) => `([stlcA| $x])
  | `([stlc| $t ]) => `(Ast.toExpr [stlcA| $t] [])

#eval [stlcTy| (ℕ → ℕ → ℕ) → ℕ → ℕ] == (Ty.ofTelescope [stlcTy| (ℕ → ℕ → ℕ) → ℕ → ℕ].telescope)
#eval [stlc| λ x : ℕ . (λ y : ℕ → ℕ . (free y) x)]

abbrev Context := Cube.Context Ty
abbrev Env := Cube.Env Ty
abbrev Substitution := Cube.Substitution Expr
abbrev SimpleT (m : Type → Type) := ReaderT Env (StateT Context (ExceptT String m))
abbrev SimpleM := SimpleT Id

def getCtx : SimpleM Context := do return (← get)
def getEnv : SimpleM Env := do return (← read)
def SimpleM.run' (x : SimpleM α) (env : Env) (ctx : Context) : Except String α :=
  x.run env |>.run' ctx

namespace Expr

-- From I'm not a number I'm a free variable
def abstract (expr : Expr) (target : FVarId) (idx : Nat := 0): Expr :=
  match expr with
  | .fvar name =>
    if target = name then
      .bvar idx
    else
      .fvar name
  | .app fn arg => .app (abstract fn target idx) (abstract arg target idx )
  | .lam ty body => .lam ty (abstract body target (idx + 1))
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
  | .lam ty body => .lam ty (instantiate body image (targetIdx + 1))
  | .fvar name => .fvar name
  | .const name => .const name

def substitute (expr : Expr) (fvarId : FVarId) (image : Expr) : Expr :=
  expr.abstract fvarId |>.instantiate image

def applySubst (subst : Substitution) (expr : Expr) : Expr :=
  subst.toList.foldl (init := expr) (fun expr (fvarId, image) => expr.substitute fvarId image)

def lambdaLength (expr : Expr) (n : Nat := 0) : Nat :=
  match expr with
  | .lam _ body => lambdaLength body (n + 1)
  | _ => n

def typeLength (ty : Ty) : Nat :=
  match ty with
  | .nat => 0
  | .fun _ t2 => 1 + typeLength t2

def getNthType! (ty : Ty) (idx : Nat) : Ty :=
  match ty, idx with
  | .nat, 0 => .nat
  | .fun t1 _, 0 => t1
  | .nat, _ + 1 => panic! "Invalid index"
  | .fun _ t2, n + 1 => getNthType! t2 n

-- TODO: I think this is a locally nameless anti pattern?
def raiseIndices (expr : Expr) (n : Nat) : Expr :=
  match expr with
  | .app fn arg => .app (raiseIndices fn n) (raiseIndices arg n)
  | .lam t body => .lam t (raiseIndices body n)
  | .bvar idx => .bvar (idx + n)
  | .fvar fvarId => .fvar fvarId
  | .const name => .const name

-- TODO: These produce unbounded bvars...
def lambdaTelescope (expr : Expr) : Array Ty × Expr :=
  go expr #[]
where
  go (expr : Expr) (binders : Array Ty) : Array Ty × Expr :=
    match expr with
    | .lam t1 body => go body (binders.push t1)
    | _ => (binders, expr)

def abstractArgs (body : Expr) (args : Array Ty) : Expr :=
  args.foldr (init := body) (fun ty body => .lam ty body)

def appTelescope (expr : Expr) : Array Expr × Expr :=
  let (revArgs, remainder) := go expr #[]
  (revArgs.reverse, remainder)
where
  go (expr : Expr) (args : Array Expr) : Array Expr × Expr :=
    match expr with
    | .app fn arg => go fn (args.push arg)
    | _ => (args, expr)

def mkApp (fn : Expr) (args : Array Expr) : Expr :=
  args.foldl (init := fn) (fun fn arg => .app fn arg)

#eval mkApp (.const "A") #[.const "B", .const "C"] == [stlc| (A B) C]

-- TODO: Maybe it is worth it to have a seperate data type for βη normalized exprs
end Expr

end Cube.Simple

