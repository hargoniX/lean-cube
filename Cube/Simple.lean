import Lean
import Std.Data.List.Lemmas
import Mathlib.Init.Algebra.Order
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Tactic.Linarith

open Lean

namespace List

theorem findIdx?_lower_bound (h : findIdx? p xs s = some idx) : s ≤ idx := by
  induction xs generalizing s with
  | nil => contradiction
  | cons x xs ih =>
    unfold findIdx? at h
    split at h
    next => injections; simp_all_arith
    next =>
      apply Nat.le_trans
      next => exact Nat.le_succ s
      next => simp_all [ih]

theorem findIdx?_bounds' (h : findIdx? p xs s = some idx) : idx < xs.length + s := by
  induction xs generalizing s with
  | nil => contradiction
  | cons x xs ih =>
    unfold findIdx? at h
    split at h
    next h => injection h.symm; simp_all_arith[Zero.zero]
    next =>
      rw [length_cons, Nat.succ_add]
      have final := ih h
      rw [Nat.add_succ] at final
      assumption

theorem findIdx?_bounds (h : findIdx? p xs = some idx) : idx < xs.length := findIdx?_bounds' h

theorem findIdx?_prop_idx (h : findIdx? p xs s = some idx) : idx - s < length xs := by
  have h1 := findIdx?_bounds' h
  have h2 := findIdx?_lower_bound h
  rw [←Nat.add_sub_cancel (length xs) s]
  exact tsub_lt_tsub_right_of_le h2 h1

theorem findIdx?_prop (h : findIdx? p xs s = some idx) : p (getElem xs (idx - s) (findIdx?_prop_idx h)) := by
  induction xs generalizing idx s with
  | nil => contradiction
  | cons x xs ih =>
    unfold findIdx? at h
    split at h
    next h => injection h.symm; simp_all[get]
    next =>
      have : idx ≠ 0 := by
        intro falso
        have : s + 1 ≤ idx := findIdx?_lower_bound h
        cases this <;> contradiction
      cases idx with
      | zero => contradiction
      | succ idx =>
        have t := ih h
        have : idx + 1 - s = (idx - s) + 1 := by
          rw [Nat.add_comm]
          rw [Nat.add_sub_assoc]
          rw [Nat.add_comm]
          apply Nat.le_of_succ_le_succ
          exact findIdx?_lower_bound h
        simp at t
        simp [get, this, t]

end List

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

#eval [stlc| λ x : ℕ . (λ y : ℕ → ℕ . freee y x)]

namespace Expr

inductive ClosedTo : Nat → Expr → Prop where
| bvar (idx m : Nat) (closed : idx < m): ClosedTo m (.bvar idx)
| lam (closed : ClosedTo (n + 1) body) : ClosedTo n (.lam ty body orig)
| const (n : Nat) (name : String) : ClosedTo n (.const name)
| app (func arg : Expr) (closedFunc : ClosedTo n func) (closedArg : ClosedTo n arg) : ClosedTo n (.app func arg)

abbrev Closed (expr : Expr) := ClosedTo 0 expr

def ClosedExpr := { expr : Expr // Closed expr }

abbrev Context := List Ty
abbrev Env := String → Option Ty

def Context.set (ctx : Context) (n : Nat) (ty : Ty) : Context :=
  match ctx, n with
  | [], 0 => [ty]
  | [], _ + 1 => []
  | _ :: xs, 0 => ty :: xs
  | x :: xs, n + 1 => x :: set xs n ty

@[simp]
theorem Context.set_nil_zero : Context.set [] 0 ty = [ty] := rfl

@[simp]
theorem Context.set_nil_succ : Context.set [] (i + 1) ty = [] := rfl

@[simp]
theorem Context.set_cons_zero : Context.set (x :: xs) 0 ty = ty :: xs := rfl

@[simp]
theorem Context.set_cons_succ : Context.set (x :: xs) (i + 1) ty = x :: (Context.set xs i ty) := rfl

theorem Context.get_set (ctx : Context) (i : Nat) (h : i < (Context.set ctx i ty).length) : List.get (Context.set ctx i ty) ⟨i, h⟩ = ty :=
  match ctx, i with
  | [], 0 => rfl
  | [], _ + 1 => by simp_arith [set, List.length] at h
  | _ :: xs, 0 => rfl
  | x :: xs, n + 1 => by
    simp only [set]
    apply get_set

theorem Context.length_le_set_length : ctx.length ≤ (Context.set ctx i ty).length :=
  match ctx, i with
  | [], 0 => by simp_arith
  | [], _ + 1 => by simp_arith
  | _ :: xs, 0 => by simp_arith[set_cons_zero]
  | x :: xs, n + 1 => by
    simp only [Context.set_cons_succ, List.length_cons]
    apply Nat.succ_le_succ
    apply length_le_set_length

theorem Context.set_bounds_eq_length (h : i < ctx.length) : (Context.set ctx i ty).length = ctx.length :=
  match ctx, i with
  | [], 0 => by contradiction
  | [], _ + 1 => by contradiction
  | _ :: xs, 0 => by simp
  | x :: xs, n + 1 => by
    simp only [set_cons_succ, List.length_cons, Nat.succ.injEq]
    apply set_bounds_eq_length
    apply Nat.lt_of_succ_lt_succ
    assumption

theorem Context.set_out_of_bounds_eq_length (h : ctx.length < i) : (Context.set ctx i ty).length = ctx.length :=
  match ctx, i with
  | [], 0 => by contradiction
  | [], _ + 1 => by simp
  | _ :: xs, 0 => by simp
  | x :: xs, n + 1 => by
    simp only [set_cons_succ, List.length_cons, Nat.succ.injEq]
    apply set_out_of_bounds_eq_length
    apply Nat.lt_of_succ_lt_succ
    assumption

theorem Context.set_succ_bound_eq_append (h : i = ctx.length) : (Context.set ctx i ty) = ctx ++ [ty] :=
  match ctx, i with
  | [], 0 => by simp
  | [], _ + 1 => by contradiction
  | _ :: xs, 0 => by contradiction
  | x :: xs, n + 1 => by
    simp [set_cons_succ, List.length_cons, Nat.succ.injEq, true_and]
    apply set_succ_bound_eq_append
    injection h

theorem Context.set_succ_bound_length_eq_succ_length (h : i = ctx.length) : (Context.set ctx i ty).length = ctx.length + 1 := by
  simp_all[Context.set_succ_bound_eq_append]

theorem Context.get_set_neq (h1 : i = ctx.length) (h2 : idx ≠ i) (h3 : idx < List.length ctx) : List.get (Context.set ctx i ty) ⟨idx, by rw[Context.set_succ_bound_length_eq_succ_length]; apply Nat.lt_succ_of_lt h3; exact h1⟩ = List.get ctx ⟨idx, h3⟩ :=
  match ctx, i with
  | [], 0 => by contradiction
  | [], _ + 1 => by contradiction
  | _ :: xs, 0 => by contradiction
  | x :: xs, n + 1 => by
    simp only [set_cons_succ, List.length_cons]
    cases idx with
    | zero => simp
    | succ idx =>
      simp only [List.get_cons_succ]
      apply get_set_neq
      injection h1
      next =>
        intro h
        apply h2
        simp [h]

theorem Context.get_set_irrelevant (ctx : Context) (i1 i2 : Nat) (h1 : i2 < ctx.length) (h2 : i1 ≠ i2) : List.get (Context.set ctx i1 ty) ⟨i2, Nat.lt_of_lt_of_le h1 length_le_set_length⟩ = List.get ctx ⟨i2, h1⟩ :=
  match ctx, i1 with
  | [], 0 => by
    simp only [set, List.length] at h1
    cases h1
    repeat contradiction
  | [], _ + 1 => by simp [Context.set_nil_succ]
  | _ :: xs, 0 => by
    simp only [Context.set_cons_zero]
    cases i2 with
    | zero => contradiction
    | succ i2 => simp only [List.get_cons_succ]
  | x :: xs, n + 1 => by
    simp only [Context.set_cons_succ]
    cases i2 with
    | zero => simp
    | succ i2 =>
      simp only [List.get_cons_succ]
      apply get_set_irrelevant
      simp_all

inductive Typing : Env → Context → Expr → Ty → Prop where
| const (in_env : env name = some typ) : Typing env ctx (.const name) typ
| app (func_type : Typing env ctx func (.fun t1 t2)) (arg_type : Typing env ctx arg t1) : Typing env ctx (.app func arg) t2
| lam (body_type : Typing env (t1 :: ctx) body t2) : Typing env ctx (.lam t1 body orig) (.fun t1 t2)
| bvar (idx : Nat) (bound : idx < ctx.length) : Typing env ctx (.bvar idx) (ctx.get ⟨idx, bound⟩)

notation:40 "("Δ ", " Γ ")" " ⊢ " e " : " t => Typing Δ Γ e t

theorem ClosedTo.of_typed (h : (env, ctx) ⊢ expr : ty) : ClosedTo ctx.length expr := by
  induction h with
  | const => apply ClosedTo.const
  | app _ _ func_ih arg_ih => simp [ClosedTo.app, *]
  | bvar => simp [ClosedTo.bvar, *]
  | lam =>
    apply ClosedTo.lam
    assumption

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

theorem ClosedExpr.infer.go_sound (expr : Expr) (env : Env) (ctx : Context) (h1 : ClosedTo ctx.length expr) (h2 : ClosedExpr.infer.go env expr h1 ctx rfl = some t) : (env, ctx) ⊢ expr : t := by
  induction expr generalizing t ctx with
  | fvar => contradiction
  | const name =>
    unfold infer.go at h2
    split at h2 <;> simp [Typing.const, *]
  | app f x fih xih =>
    simp only [infer.go, Id.run] at h2
    repeat split at h2
    next =>
      injections
      simp_all
      apply Typing.app
      case func_type =>
        apply fih _ (by cases h1; assumption)
        assumption
      case arg_type =>
        apply xih _ (by cases h1; assumption)
        assumption
    repeat contradiction
  | lam ty body _ ih =>
    simp only [infer.go] at h2
    split at h2
    next _ _ t3 h3 =>
      injections h2
      rw[←h2]
      apply Typing.lam
      apply ih
      exact h3
    next => contradiction
  | bvar idx =>
    have idx_get : t = ctx.get ⟨idx, (by cases h1; assumption)⟩ := by
      unfold go at h2
      split at h2 <;> simp_all
    rw[idx_get]
    apply Typing.bvar

theorem ClosedExpr.infer_sound (expr : ClosedExpr) (env : Env) (h : expr.infer env = some t) : (env, []) ⊢ expr.val : t := by
  unfold infer at h
  apply ClosedExpr.infer.go_sound
  assumption

theorem ClosedExpr.infer.go_complete (expr : Expr) (env : Env) (ctx : Context) (h1 : ClosedTo ctx.length expr) (h2 : (env, ctx) ⊢ expr : t) : ClosedExpr.infer.go env expr h1 ctx rfl = some t := by
  induction h2 with
  | const =>
    unfold go
    split <;> simp_all
  | app _ _ ih1 ih2 =>
    have ih1 := ih1 (by cases h1; assumption)
    have ih2 := ih2 (by cases h1; assumption)
    simp[go, Id.run]
    repeat split <;> simp_all
  | lam _ ih =>
    have ih := ih (by cases h1; assumption)
    simp[go]
    split <;> simp_all
  | bvar h_idx => simp_all[go]

theorem ClosedExpr.infer_complete (expr : ClosedExpr) (env : Env) (h : (env, []) ⊢ expr.val : t) :  expr.infer env = some t := by
  unfold infer
  apply ClosedExpr.infer.go_complete _ _ []
  assumption

def ClosedExpr.typecheck (env : Env) (expr : ClosedExpr) (typ : Ty) : Bool := Id.run do
  if let some inferredTyp := expr.infer env then
    if inferredTyp = typ then
      return true
  return false

theorem ClosedExpr.typecheck_sound (expr : ClosedExpr) (t : Ty) (env : Env) (h : expr.typecheck env t = true) : (env, []) ⊢ expr.val : t := by
  simp [typecheck, Id.run] at h
  repeat split at h
  next =>
    apply infer_sound
    simp [*]
  repeat contradiction

theorem ClosedExpr.typecheck_complete (expr : ClosedExpr) (t : Ty) (env : Env) (h : (env, []) ⊢ expr.val : t) : expr.typecheck env t = true := by
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

theorem Typing.unique (h1 : (env, ctx) ⊢ expr : ty1) (h2 : (env, ctx) ⊢ expr : ty2) : ty1 = ty2 := by
  match term:h1 with
  | .const .. => cases h2; simp_all
  | .bvar .. => cases h2; simp_all
  | .app h3 h4 .. =>
    cases h2 with
    | app h5 h6 =>
      have := unique h3 h5
      injections
  | .lam h3 =>
    cases h2 with
    | lam h4 =>
      have := unique h3 h4
      simp_all

theorem Typing.weakening (h1 : ctx' = ctx ++ additional) (h2 : (env, ctx) ⊢ expr : typ) : (env, ctx') ⊢ expr : typ := by
  induction h2 generalizing ctx' with
  | const =>
    apply Typing.const
    assumption
  | app _ _ ihf ihx =>
    apply Typing.app
    case func_type =>
      apply ihf
      assumption
    case arg_type =>
      apply ihx
      assumption
  | lam _ ih =>
    apply Typing.lam
    apply ih
    simp[h1]
  | bvar idx =>
    rw[h1, ←List.get_append idx]
    apply Typing.bvar

theorem Typing.weakening_empty (ctx : Context) (h : (env, []) ⊢ expr : typ) : (env, ctx) ⊢ expr : typ :=
  Typing.weakening (List.nil_append ctx).symm h

-- From I'm not a number I'm a free variable
def abstract (target : String) (expr : Expr) (idx : Nat := 0): Expr :=
  match expr with
  | .fvar name =>
    if target = name then
      .bvar idx
    else
      .fvar name
  | .app fn arg => .app (abstract target fn idx) (abstract target arg idx )
  | .lam ty body orig => .lam ty (abstract target body (idx + 1)) orig
  | .const name => .const name
  | .bvar idx => .bvar idx

def instantiate (image : Expr) (expr : Expr) (targetIdx : Nat := 0): Expr :=
  match expr with
  | .bvar idx =>
    if idx = targetIdx then
      image
    else
      .bvar idx
  | .app fn arg => .app (instantiate image fn targetIdx ) (instantiate image arg targetIdx )
  | .lam ty body orig => .lam ty (instantiate image body (targetIdx + 1)) orig
  | .fvar name => .fvar name
  | .const name => .const name

def substitute (image : Expr) (name : String) (expr : Expr) : Expr :=
  expr.abstract name |>.instantiate image

theorem Typing.instantiate_preserves (h1 : (env, []) ⊢ v : ty) (h2 : (env, (Context.set ctx i ty)) ⊢ expr : ty') : (env, ctx) ⊢ (instantiate v expr i) : ty' := by
  induction expr generalizing ctx ty' i with
  | const =>
    simp only [instantiate]
    cases h2
    apply Typing.const
    assumption
  | bvar idx =>
    simp only [instantiate]
    split
    case inl h =>
      have : ty' = ty := by
        rw[h] at h2
        cases h2
        apply Context.get_set
      apply weakening_empty
      rw[this]
      assumption
    case inr neq =>
      cases h2 with
      | bvar _ bound  =>
        cases Nat.lt_trichotomy i ctx.length with
        | inl h =>
          have neq_symm : i ≠ idx := by intro h; apply neq h.symm
          have lt : idx < ctx.length := by
            simp only [Context.set_bounds_eq_length, h] at bound
            assumption
          simp [Context.get_set_irrelevant, lt, neq_symm, Typing.bvar]
        | inr h =>
          cases h with
          | inl =>
            rw [Context.set_succ_bound_length_eq_succ_length] at bound

            have helper {n m : Nat} (h1 : n < m + 1) (h2 : n ≠ m) : n < m := by
              cases lt_or_gt_of_ne h2 <;> linarith
            have : idx < List.length ctx := helper (by assumption) (by simp_all)
            next =>
              rw [Context.get_set_neq]
              apply Typing.bvar
              assumption
              next => intro h; apply neq h
              assumption
            next => assumption
          | inr =>
            rw [Context.get_set_irrelevant]
            next => apply Typing.bvar
            next =>
              rw [Context.set_out_of_bounds_eq_length] at bound
              repeat assumption
            next => intro h; apply neq h.symm
  | fvar => cases h2
  | lam _ _ _ ih =>
    simp only [instantiate]
    cases h2
    apply Typing.lam
    apply ih
    assumption
  | app _ _ fih xih =>
    simp only [instantiate]
    cases h2
    apply Typing.app
    case func_type =>
      apply fih
      repeat assumption
    case arg_type =>
      apply xih
      repeat assumption

@[simp]
def isLam : Expr → Bool
| .lam .. => true
| _ => false

inductive Value : Expr → Prop where
| lam : Value (.lam ty body orig)
| const : Value (.const name)
| constApp (h : Value v) : Value (.app (.const name) v)
| app (h1 : Value f) (h2 : ¬f.isLam) (h3 : Value v) : Value (.app f v)

inductive BetaStep : Expr → Expr → Prop where
| lamApp : BetaStep (.app (.lam ty body orig) arg) (instantiate arg body)
| leftApp (h : BetaStep t1 t1') : BetaStep (.app t1 t2) (.app t1' t2)
| rightApp (h1 : Value t1) (h2 : BetaStep t2 t2') : BetaStep (.app t1 t2) (.app t1 t2')

inductive Multi (R : α → α → Prop) : α → α → Prop where
| rfl : Multi R x x
| step (x y z : α) (h1 : R x y) (h2 : Multi R y z) : Multi R x z

def normal_form (R : α → α → Prop) (t : α) : Prop := ¬ ∃ t', R t t'
def step_normal_form (expr : Expr) : Prop := normal_form BetaStep expr
abbrev BetaReduction := Multi BetaStep

notation t1 " →β " t2 => BetaStep t1 t2
notation t1 " →β* " t2 => BetaReduction t1 t2

example : [stlc| (λ x : ℕ → ℕ . x) (λ x : ℕ . x)] →β [stlc| (λ x : ℕ . x)] := by
  simp [Ast.toExpr, List.findIdx?]
  apply BetaStep.lamApp

theorem Expr.subject_reduction (expr : Expr) (typed_expr : (env, []) ⊢ expr : ty) (reduces : expr →β expr') : (env, []) ⊢ expr' : ty := by
  cases typed_expr with
  | const => cases reduces
  | app =>
    cases reduces
    case lamApp lam_typed =>
      cases lam_typed with
      | lam body_typed =>
        rw [←Context.set_nil_zero] at body_typed
        apply Typing.instantiate_preserves
        repeat assumption
    case leftApp =>
      apply Typing.app
      apply subject_reduction
      repeat assumption
    case rightApp =>
      apply Typing.app
      assumption
      apply subject_reduction
      repeat assumption
  | lam => cases reduces
  | bvar => cases reduces

theorem Value.normal (expr : Expr) (h : Value expr) : step_normal_form expr := by
  induction h with
  | lam =>
    intro h
    cases h with
    | intro t' ht' =>
      cases ht'
  | const =>
    intro h
    cases h with
    | intro t' ht' =>
      cases ht'
  | constApp _ ih =>
    intro h
    cases h with
    | intro t' ht' =>
      cases ht' with
      | leftApp h => cases h
      | rightApp h =>
        apply False.elim
        apply ih
        constructor
        assumption
  | app h1 h2 _ h4 h5 =>
    intro h
    cases h with
    | intro t' ht' =>
      cases ht' with
      | lamApp => simp[isLam] at h2
      | leftApp =>
        apply h4
        constructor
        assumption
      | rightApp =>
        apply h5
        constructor
        assumption

theorem Value.terminated (expr expr' : Expr) (h1 : Value expr) (h2 : expr →β* expr') : expr = expr' := by
  cases h2 with
  | rfl => rfl
  | step =>
    apply False.elim
    apply Value.normal
    assumption
    constructor
    assumption

def halts (expr : Expr) : Prop := ∃ expr', (expr →β expr') ∧ Value expr'

def R (t : Ty) (expr : Expr) : Prop :=
  (∀ env, (env , []) ⊢ expr : t) ∧ halts expr ∧ match t with
  | .nat => True
  | .fun t1 t2 => ∀ s, R t1 s → R t2 (.app expr s)

theorem R.halts (h : R typ expr) : halts expr := by
  cases typ <;> (
    unfold R at h
    cases h with
    | intro left right =>
      cases right;
      assumption
  )

theorem R.typable (h : R typ expr) (env : Env) : (env, []) ⊢ expr : typ := by
  cases typ <;> (
    unfold R at h;
    cases h with
    | intro left right => exact left env)


theorem R.beta_reduction_preserves (h1 : expr →β expr') (h2 : R typ expr) : R typ expr' := by
  sorry

theorem Expr.strong_normalization (expr : Expr) (typed : (env, ctx) ⊢ expr : ty) : ∃ target, (expr →β target) ∧ Value target := by
  sorry

end Expr

end Cube.Simple
