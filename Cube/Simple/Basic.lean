import Cube.Util

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
| fvar (name : String)
| lam (ty : Ty) (body : Expr) (orig : String)
| const (name : String)
| app (func : Expr) (arg : Expr)
deriving Repr, DecidableEq

abbrev TranslationEnv := List String

def Ast.toExpr : Ast → TranslationEnv → Expr
| var name, vs =>
  match vs.findIdx? (name = ·) with
  | some idx => .bvar idx
  | none => .fvar name
| const name, _ => .const name
| app func arg, vs => .app (toExpr func vs) (toExpr arg vs)
| lam x ty body, vs => .lam ty (toExpr body <| x :: vs) x

def Expr.toAst : Expr → TranslationEnv → Option Ast
| bvar idx, vs => do
  let x ← vs[idx]?
  return .var x
| fvar name, _ => some <| .var name
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

end Cube.Simple

