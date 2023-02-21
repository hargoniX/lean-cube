import Cube.Util
import Cube.Context

import Mathlib.Tactic.Linarith

import Lean

open Lean

namespace Cube.Simple

inductive Ty where
| nat
| fun (pre : Ty) (image : Ty)
deriving Repr, DecidableEq

inductive Ast where
| var (name : String)
| const (name : String)
| lam (var : String) (ty : Ty) (body : Ast)
| app (func : Ast) (arg : Ast)

inductive Expr where
| bvar (idx : Nat)
| fvar (name : FVarId)
| lam (ty : Ty) (body : Expr) (orig : String)
| const (name : String)
| app (func : Expr) (arg : Expr)
deriving Repr, DecidableEq
abbrev TranslationEnv := List String

def Ast.toExpr : Ast → TranslationEnv → Expr
| var name, vs =>
  match vs.findIdx? (name = ·) with
  | some idx => .bvar idx
  | none => .fvar ⟨name, 0⟩
| const name, _ => .const name
| app func arg, vs => .app (toExpr func vs) (toExpr arg vs)
| lam x ty body, vs => .lam ty (toExpr body <| x :: vs) x

def Expr.toAst : Expr → TranslationEnv → Option Ast
| bvar idx, vs => do
  let x ← vs[idx]?
  return .var x
| fvar fvarId, _ => some <| .var fvarId.name
| lam ty body name, vs => do
    let body ← toAst body <| name :: vs
    return .lam name ty body
| const name, _ => some <| .const name
| .app func arg, vs => do
    let funcAst ← toAst func vs
    let argAst ← toAst arg vs
    return .app funcAst argAst

declare_syntax_cat stlc
declare_syntax_cat stlcTy
syntax "ℕ" : stlcTy
syntax stlcTy "→" stlcTy : stlcTy
syntax "(" stlcTy ")" : stlcTy

syntax ident : stlc
syntax stlc:11 stlc:10 : stlc
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
    if strId.startsWith "@" then
      `(Ast.const $(quote <| strId.drop 1))
    else
      `(Ast.var $(quote strId))
  | `([stlcA| λ $x : $ty . $b]) => `(Ast.lam $(quote x.getId.toString) [stlcTy| $ty]  [stlcA| $b])
  | `([stlcA| $f $x]) => `(Ast.app [stlcA| $f] [stlcA| $x])
  | `([stlcA| ($x)]) => `([stlcA| $x])
  | `([stlc| $t ]) => `(Ast.toExpr [stlcA| $t] [])

theorem Ast.toExpr_inv_toAst (a : Ast) (xs : List String) : Expr.toAst (Ast.toExpr a xs) xs = some a := by
  induction a generalizing xs with
  | var name =>
    simp only [Ast.toExpr]
    split
    case var.h_1 idx h =>
      simp only [Expr.toAst,Bind.bind, Option.bind, Pure.pure]
      have h2 := List.findIdx?_bounds h
      simp only [getElem?, h2, congrArg, List.getElem_eq_get, Option.some.injEq, var.injEq]
      have h3 := List.findIdx?_prop h
      simp [of_decide_eq_true h3]
    case var.h_2 => simp [Expr.toAst]
  | const name => simp[Expr.toAst, Ast.toExpr]
  | lam var ty body ih =>
    simp[Expr.toAst, Ast.toExpr, Bind.bind, Option.bind, Pure.pure, ih]
  | app func arg fih xih =>
    simp[Expr.toAst, Ast.toExpr, Bind.bind, Option.bind, fih, xih, Pure.pure]

theorem Ast.macro_correct (a : Ast) : Expr.toAst (Ast.toExpr a []) [] = some a := toExpr_inv_toAst a []

example := [stlc| λ x : ℕ . (λ y : ℕ → ℕ . free y x)]

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
  | .lam ty body orig => .lam ty (abstract body target (idx + 1)) orig
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
  | .lam ty body orig => .lam ty (instantiate body image (targetIdx + 1)) orig
  | .fvar name => .fvar name
  | .const name => .const name

inductive FVarIn (fvarId : FVarId) : Expr → Prop where
| fvarEq : FVarIn fvarId (.fvar fvarId)
| appLeft (func arg : Expr) (h : FVarIn fvarId func) : FVarIn fvarId (.app func arg)
| appRight (func arg : Expr) (h : FVarIn fvarId arg) : FVarIn fvarId (.app func arg)
| lam (ty : Ty) (body : Expr) (h : FVarIn fvarId body) : FVarIn fvarId (.lam ty body orig)

def FreshIn (fvar : FVarId) (expr : Expr) := ¬ FVarIn fvar expr
def Closed (expr : Expr) := ∀ fvar, FreshIn fvar expr

inductive LocallyClosed : Expr → Prop where
| const (name : String) : LocallyClosed (.const name)
| fvar (fvarId : FVarId) : LocallyClosed (.fvar fvarId)
| app (func arg : Expr) (closedFunc : LocallyClosed func) (closedArg : LocallyClosed arg) : LocallyClosed (.app func arg)
| lam (ty : Ty) (body : Expr) (freeBody : FreshIn x body) (closedBody : LocallyClosed (abstract body x)) : LocallyClosed (.lam ty body orig)

inductive ClosedTo : Nat → Expr → Prop where
| const (n : Nat) (name : String) : ClosedTo n (.const name)
| bvar (idx m : Nat) (closed : idx < m): ClosedTo m (.bvar idx)
| fvar (n : Nat) (fvarId : FVarId) : ClosedTo n (.fvar fvarId)
| app (func arg : Expr) (closedFunc : ClosedTo n func) (closedArg : ClosedTo n arg) : ClosedTo n (.app func arg)
| lam (closedBody : ClosedTo (n + 1) body) : ClosedTo n (.lam ty body orig)

abbrev LocallyClosed' (expr : Expr) := ClosedTo 0 expr

abbrev _root_.Cube.WfExpr := { expr : Expr // LocallyClosed expr }

theorem instantiate_abstract_self_eq (expr : Expr) (h : FreshIn target expr) : (expr.instantiate (.fvar target) i).abstract target i = expr := by
  induction expr generalizing i with
  | bvar =>
    simp only [instantiate]
    split <;> simp_all[abstract]
  | fvar =>
    simp only [instantiate, abstract]
    split
    next h2 =>
      apply h
      rw [h2]
      apply FVarIn.fvarEq
    next => rfl
  | const => simp [abstract, instantiate]
  | lam ty body orig bih =>
    simp only [instantiate, abstract, lam.injEq, and_true, true_and]
    apply bih
    intro h2
    apply h
    apply FVarIn.lam
    assumption
  | app func arg fih aih =>
    simp only [instantiate, abstract, app.injEq]
    constructor
    case left =>
      apply fih
      intro h2
      apply h
      apply FVarIn.appLeft
      assumption
    case right =>
      apply aih
      intro h2
      apply h
      apply FVarIn.appRight
      assumption

theorem abstract_instantiate_self_eq' (expr : Expr) (h : ClosedTo i expr) : (expr.abstract target i).instantiate (.fvar target) i = expr := by
  induction expr generalizing i with
  | bvar =>
    simp only [instantiate, ite_eq_right_iff]
    intro h2
    cases h
    linarith
  | const => simp [abstract, instantiate]
  | fvar =>
    simp only [abstract]
    split <;> simp_all [instantiate]
  | app func arg fih aih =>
    simp only [abstract, instantiate, app.injEq]
    cases h
    constructor
    case left => apply fih; assumption
    case right => apply aih; assumption
  | lam ty body orig ihb =>
    simp only [abstract, instantiate, lam.injEq, true_and, and_true] at *
    cases h
    apply ihb
    assumption

  
theorem LocallyClosed'.succ_closed_of_abstract_closed (h : ClosedTo i (abstract expr x i)) : ClosedTo (i + 1) expr := by
  induction expr generalizing i with
  | bvar =>
    simp only [abstract] at h
    cases h
    apply ClosedTo.bvar
    linarith
  | fvar => apply ClosedTo.fvar
  | const => apply ClosedTo.const
  | app func arg fih aih =>
    cases h
    apply ClosedTo.app
    case closedFunc => apply fih; assumption
    case closedArg => apply aih; assumption
  | lam ty body tih bih =>
    cases h
    apply ClosedTo.lam
    case closedBody => apply bih; assumption 

theorem LocallyClosed.iff_LocallyClosed' (h : LocallyClosed expr) : LocallyClosed' expr := by
  induction h with
  | const => apply ClosedTo.const
  | fvar => apply ClosedTo.fvar
  | app =>
    apply ClosedTo.app
    repeat assumption
  | lam =>
    apply ClosedTo.lam
    case closedBody =>
      apply LocallyClosed'.succ_closed_of_abstract_closed
      repeat assumption

theorem abstract_instantiate_self_eq (expr : Expr) (h : LocallyClosed expr) : (expr.abstract target).instantiate (.fvar target) = expr := by
  apply abstract_instantiate_self_eq'
  apply LocallyClosed.iff_LocallyClosed'
  assumption

end Expr

end Cube.Simple

