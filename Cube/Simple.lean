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
deriving Repr, DecidableEq

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
deriving Repr, DecidableEq

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
  return .var x
| fvar x, _ => some <| .var x
| lam ty b x, vs => do
    let body ← toAst b <| x :: vs
    return .lam x ty body
| const name, _ => some <| .const name
| .app f x, vs => do
    let fAst ← toAst f vs
    let xAst ← toAst x vs
    return .app fAst xAst


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

namespace Expr

inductive ClosedTo : Nat → Expr → Prop where
| bvar (h : n < m): ClosedTo m (.bvar n)
| lam (h : ClosedTo (n + 1) body) : ClosedTo n (.lam ty body orig)
| const : ClosedTo n (.const name)
| app (h1 : ClosedTo n f) (h2 : ClosedTo n x) : ClosedTo n (.app f x)

abbrev Closed (e : Expr) := ClosedTo 0 e

def ClosedExpr := { e : Expr // Closed e }

abbrev Context := List Ty
abbrev Env := String → Option Ty

inductive Typing : Env → Context → Expr → Ty → Prop where
| const (h : env name = some typ) : Typing env ctx (.const name) typ
| app (h1 : Typing env ctx f (.fun t1 t2)) (h2 : Typing env ctx x t1) : Typing env ctx (.app f x) t2
| lam (h : Typing env (t1 :: ctx) body t2) : Typing env ctx (.lam t1 body orig) (.fun t1 t2)
| bvar (h : idx < ctx.length) : Typing env ctx (.bvar idx) (ctx.get ⟨idx, h⟩)

notation Δ " :: " Γ " ⊢ " e " : " t => Typing Δ Γ e t

def ClosedExpr.infer (expr : ClosedExpr) (env : Env) : Option Ty :=
  go expr.val expr.property [] rfl
where
  go {n : Nat} (expr : Expr) (h1 : ClosedTo n expr) (ctx : Context) (h2 : ctx.length = n) : Option Ty := 
    match expr with
    | .bvar idx =>
      if hVar:idx < n then
        some <| ctx.get ⟨idx, h2 ▸ hVar⟩
      else
        none
    | .app fn arg => Id.run do
      have closedFn : ClosedTo n fn := by
        cases h1; assumption
      have closedArg : ClosedTo n arg := by
        cases h1; assumption
      if let some (.fun t1 t2) := go fn closedFn ctx h2 then
        if let some t3 := go arg closedArg ctx h2 then
          if t1 = t3 then
            return some t2
      return none
    | .lam t1 body _ =>
      have bodyClosed : ClosedTo (ctx.length + 1) body := by
        cases h1
        rw [h2]
        assumption
      if let some t2 := go body bodyClosed (t1 :: ctx) rfl then
        some (.fun t1 t2)
      else
        none
    | .fvar .. => nomatch h1
    | .const name =>
      match env name with
      | some ty => some ty
      | none => none

theorem ClosedExpr.infer.go_sound (expr : Expr) (env : Env) (ctx : Context) (h1 : ClosedTo ctx.length expr) (h2 : ClosedExpr.infer.go env expr h1 ctx rfl = some t) : env :: ctx ⊢ expr : t := by
  induction expr generalizing t ctx with
  | fvar => contradiction
  | const name =>
    unfold infer.go at h2
    split at h2
    next =>
      apply Typing.const
      simp [*]
    next => contradiction
  | app f x fih xih =>
    simp [infer.go, Id.run] at h2
    repeat split at h2
    next =>
      injections
      simp_all
      apply Typing.app
      case h1 =>
        apply fih _ (by cases h1; assumption)
        assumption
      case h2 =>
        apply xih _ (by cases h1; assumption)
        assumption
    repeat contradiction
  | lam ty body _ ih =>
    simp [infer.go] at h2
    split at h2
    next _ _ t3 h3 =>
      simp at h2
      rw[←h2]
      apply Typing.lam
      apply ih
      exact h3
    next => contradiction
  | bvar idx =>
    have idx_get : t = ctx.get ⟨idx, (by cases h1; assumption)⟩ := by
      unfold go at h2
      split at h2
      next =>
        injections
        simp [*]
      next => contradiction
    rw[idx_get]
    apply Typing.bvar

theorem ClosedExpr.infer_sound (expr : ClosedExpr) (env : Env) (h : expr.infer env = some t) : env :: [] ⊢ expr.val : t := by
  unfold infer at h
  apply ClosedExpr.infer.go_sound
  assumption

theorem ClosedExpr.infer.go_complete (expr : Expr) (env : Env) (ctx : Context) (h1 : ClosedTo ctx.length expr) (h2 : env :: ctx ⊢ expr : t) : ClosedExpr.infer.go env expr h1 ctx rfl = some t := by
  induction h2 with
  | const =>
    unfold go
    split
    next => simp_all
    next => simp_all
  | app hf hx ih1 ih2 =>
    have ih1 := ih1 (by cases h1; assumption)
    have ih2 := ih2 (by cases h1; assumption)
    simp[go, Id.run]
    repeat split
    next => simp_all
    next => simp_all
    next _ _ _ t _ _ _ _ _ _ _ _ _ h =>
      apply False.elim
      apply h t
      assumption
    next _ _ _ t1 t2 _ _ _ _ h =>
      apply False.elim
      apply h t1 t2
      assumption
  | lam _ ih =>
    have ih := ih (by cases h1; assumption)
    simp[go]
    split
    next => simp_all
    next _ _ _ _ _ _ _ h =>
      apply False.elim
      apply h _ ih
  | bvar h_idx => simp_all[go]

theorem ClosedExpr.infer_complete (expr : ClosedExpr) (env : Env) (h : env :: [] ⊢ expr.val : t) :  expr.infer env = some t := by
  unfold infer
  apply ClosedExpr.infer.go_complete _ _ []
  assumption

def ClosedExpr.typecheck (env : Env) (expr : ClosedExpr) (typ : Ty) : Bool := Id.run do
  if let some inferredTyp := expr.infer env then
    if inferredTyp = typ then
      return true
  return false

theorem ClosedExpr.typecheck_sound (expr : ClosedExpr) (t : Ty) (env : Env) (h : expr.typecheck env t = true) : env :: [] ⊢ expr.val : t := by
  simp [typecheck, Id.run] at h
  repeat split at h
  next =>
    apply infer_sound
    simp [*]
  repeat contradiction

theorem ClosedExpr.typecheck_complete (expr : ClosedExpr) (t : Ty) (env : Env) (h : env :: [] ⊢ expr.val : t) : expr.typecheck env t = true := by
  simp [typecheck, Id.run]
  split
  next _ t2 h2 =>
    have : some t2 = some t := by
      rw[←h2]
      apply infer_complete
      assumption
    simp_all
  next _ h2 =>
    apply False.elim
    apply h2
    apply infer_complete
    assumption

def abstract (target : String) (expr : Expr) : Expr :=
  go 0 expr
where
  go (idx : Nat) (expr : Expr) :=
    match expr with
    | .fvar name =>
      if target = name then
        .bvar idx
      else
        .fvar name
    | .app fn arg => .app (go idx fn) (go idx arg)
    | .lam ty body orig => .lam ty (go (idx + 1) body) orig
    | .const name => .const name
    | .bvar idx => .bvar idx

def instantiate (image : Expr) (expr : Expr) : Expr :=
  go 0 expr
where
  go (targetIdx : Nat) (expr : Expr) :=
    match expr with
    | .bvar idx =>
      if idx = targetIdx then
        image
      else
        .bvar idx
    | .app fn arg => .app (go targetIdx fn) (go targetIdx arg)
    | .lam ty body orig => .lam ty (go (targetIdx + 1) body) orig
    | .fvar name => .fvar name
    | .const name => .const name

def substitute (image : Expr) (name : String) (expr : Expr) : Expr :=
  expr.abstract name |>.instantiate image
end Expr

end Cube.Simple
