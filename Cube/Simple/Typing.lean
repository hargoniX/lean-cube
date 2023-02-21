import Cube.Context
import Cube.Simple.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic

namespace Cube.Simple

namespace Expr

abbrev Context := Cube.Context Ty
abbrev Env := Cube.Env Ty

inductive Typing : Env → Context → Expr → Ty → Prop where
| const (name : String) (typ : Ty) (in_env : env.get name = some typ) : Typing env ctx (.const name) typ
| fvar (fvarId : FVarId) (inContext : ctx.get fvarId = some ty) : Typing env ctx (.fvar fvarId) ty
| app (func arg : Expr) (t1 t2 : Ty) (func_type : Typing env ctx func (.fun t1 t2)) (arg_type : Typing env ctx arg t1) : Typing env ctx (.app func arg) t2
| lam ( body : Expr) (t1 t2 : Ty) (L : Finset FVarId) (body_type : ∀ fvarId , fvarId ∉ L → Typing env (ctx.update fvarId t1) (body.instantiate (.fvar fvarId)) t2) : Typing env ctx (.lam t1 body orig) (.fun t1 t2)

notation:40 "("Δ ", " Γ ")" " ⊢ " e " : " t => Typing Δ Γ e t

/-
TODO: Induction principle for empty context, this should allow easier arguing over closed terms
TODO: Build machinery to fix the lam case
TODO: Investigate cofinite quantification: https://www.chargueraud.org/research/2009/ln/main.pdf
-/
theorem LocallyClosed.of_typed (h : (env, Context.empty) ⊢ expr : ty) : LocallyClosed expr := by
  cases h with
  | const => apply LocallyClosed.const
  | fvar fvarId ih => apply LocallyClosed.fvar
  | app func arg t1 _ hfunc harg =>
    have fih := of_typed hfunc
    have aih := of_typed harg
    apply LocallyClosed.app
    repeat assumption
  | lam body t1 t2 L hbody =>
    apply LocallyClosed.lam
    sorry
    sorry
    sorry

def WfExpr.infer (expr : WfExpr) (env : Env) : Option Ty :=
  go expr.val expr.property Context.empty
where
  go (expr : Expr) (h1 : LocallyClosed expr) (ctx : Context) : Option Ty :=
    match expr with
    | .bvar .. => none
    | .app fn arg => Id.run do
      have closedFn : LocallyClosed fn := by
        cases h1; assumption
      have closedArg : LocallyClosed arg := by
        cases h1; assumption
      if let some (.fun t1 t2) := go fn closedFn ctx then
        if let some t3 := go arg closedArg ctx then
          if t1 = t3 then
            return some t2
      return none
    | .lam t1 body orig =>
      let newFVar := FVar.fresh ctx
      let newCtx := ctx.update newFVar t1
      let newBody := body.instantiate (.fvar newFVar)
      have bodyClosed : LocallyClosed newBody := by
        cases h1
        sorry
      -- TODO: Instantiate .fvar preserves size
      -- Note: sizeOf for Expr looks at the content of data, I don't want that, .fvar and .bvar should always have size 1
      -- -> I'll need a custom size measure to make this pretty
      have wf : sizeOf (instantiate body (fvar (FVar.fresh ctx))) < 1 + sizeOf t1 + sizeOf body + sizeOf orig := sorry
      if let some t2 := go newBody bodyClosed newCtx then
        some (.fun t1 t2)
      else
        none
    | .fvar fvarId => ctx.get fvarId
    | .const name => env.get name 
termination_by go expr h1 ctx => expr

theorem WfExpr.infer.go_sound (expr : Expr) (env : Env) (ctx : Context) (h1 : LocallyClosed expr) (h2 : WfExpr.infer.go env expr h1 ctx = some t) : (env, ctx) ⊢ expr : t := by
  induction expr generalizing t ctx with
  | bvar => contradiction
  | fvar => sorry
  | const name =>
    unfold infer.go at h2
    apply Typing.const
    assumption
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
      case L => sorry
      case body_type =>
        intro fvarId hf
        sorry
    next => contradiction

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



end Expr

end Cube.Simple
