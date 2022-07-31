import Lean
open Lean

namespace List

def findIdx? (p : α → Bool) : List α → Option Nat
  | []    => none
  | a::as => match p a with
    | true  => some 0
    | false => Nat.succ <*> findIdx? p as

theorem findIdx?_bounds (h : findIdx? p xs = some idx) : idx < xs.length := by
  induction xs generalizing idx with
  | nil => contradiction
  | cons x xs ih =>
    simp only [findIdx?] at h
    split at h
    case cons.h_1 =>
      injection (Eq.symm h)
      simp_all_arith
    case cons.h_2 =>
      simp only [Seq.seq, Option.bind, (· <$> ·), Option.map] at h
      split at h
      case h_1 h2 =>
        injection (Eq.symm h)
        simp_all_arith
      case h_2 => contradiction

theorem findIdx?_prop (h : findIdx? p xs = some idx) : p (getElem xs idx (findIdx?_bounds h)) := by
  induction xs generalizing idx with
  | nil => contradiction
  | cons x xs ih =>
    simp only [findIdx?] at h
    -- For some reason split doesnt work here: TODO Report bug
    cases h2 : (p x) with
    | true =>
      simp[h2] at h
      have h3 := Eq.symm h
      simp[GetElem.getElem, h3, List.get, h2]
    | false =>
      simp only [Seq.seq, Option.bind, (· <$> ·), Option.map, h2] at h
      split at h
      case cons.false.h_1 h3 =>
        injection (Eq.symm h)
        simp_all_arith[GetElem.getElem, List.get]
      case cons.false.h_2 => contradiction

end List

namespace Cube.Simple

inductive Ty where
| nat
| fun (x : Ty) (res : Ty)
deriving Repr

inductive Ast where
| var (x : String)
| const (x : String)
| lam (x : String) (ty : Ty) (b : Ast)
| app (f : Ast) (x : Ast)

inductive Expr where
| bvar (idx : Nat)
| fvar (name : String)
| lam (ty : Ty) (body : Expr) (orig : String)
| const (name : String)
| app (f : Expr) (x : Expr)
deriving Repr

abbrev TranslationEnv := List String

namespace TranslationEnv

inductive Wf : TranslationEnv → Prop

end TranslationEnv

def Ast.toExpr : Ast → TranslationEnv → Expr
| var x, vs =>
  match vs.findIdx? (x = ·) with
  | some idx => .bvar idx
  | none => .fvar x
| const x, _ => .const x
| app f x, vs => .app (toExpr f vs) (toExpr x vs)
| lam x ty b, vs => .lam ty (toExpr b <| x :: vs) x

def Expr.toAst : Expr → TranslationEnv → Option Ast
| bvar idx, vs => do
  let x ← vs[idx]?
  pure <| .var x
| fvar x, _ => some <| .var x
| lam ty b x, vs => do
    let body ← toAst b <| x :: vs
    pure <| .lam x ty body
| const name, _ => some <| .const name
| .app f x, vs => do
    let fAst ← toAst f vs
    let xAst ← toAst x vs
    pure <| .app fAst xAst


declare_syntax_cat stlc
declare_syntax_cat stlcTy
syntax "ℕ" : stlcTy
syntax stlcTy "->" stlcTy : stlcTy
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
  | `([stlcTy| $a -> $b]) => `(Ty.fun [stlcTy| $a] [stlcTy| $b])
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
    -- bvar case
    case var.h_1 idx h =>
      -- unfold do notation
      simp only [Expr.toAst,Bind.bind, Option.bind, Pure.pure] 
      have h2 := List.findIdx?_bounds h
      simp only [getElem?, h2, congrArg] -- TODO: possibly nicer
      repeat (apply congrArg) -- TODO: replace with simp
      have h3 := List.findIdx?_prop h
      simp [of_decide_eq_true h3]
    -- fvar case
    case var.h_2 => simp [Expr.toAst]
  | const x => simp[Expr.toAst, Ast.toExpr]
  | lam x ty b ih =>
    simp[Expr.toAst, Ast.toExpr, Bind.bind, Option.bind, Pure.pure, ih] 
  | app f x fih xih =>
    simp[Expr.toAst, Ast.toExpr, Bind.bind, Option.bind, fih, xih, Pure.pure] 
  

theorem Ast.macro_correct (a : Ast) : Expr.toAst (Ast.toExpr a []) [] = some a := toExpr_inv_toAst a []

#eval [stlc| λ x : ℕ . (λ y : ℕ -> ℕ . freee y x)]

end Cube.Simple
