import Cube.Simple.Typing

inductive Multi (R : α → α → Prop) : α → α → Prop where
| rfl : Multi R x x
| step (x y z : α) (h1 : R x y) (h2 : Multi R y z) : Multi R x z

theorem Multi.confluent_of_determ (hdeterm : ∀ x y1 y2, R x y1 → R x y2 → y1 = y2) : ∀ x y1 y2, (Multi R) x y1 → (Multi R) x y2 → ∃ y3, (Multi R) y1 y3 ∧ (Multi R) y2 y3 := by
  intro x y1 y2 h1 h2
  induction h1 generalizing y2 with
  | rfl =>
    cases h2 with
    | rfl =>
      repeat constructor
      repeat apply Multi.rfl
    | step _ _ _ h1 h2 =>
      apply Exists.intro y2
      constructor
      case left => apply Multi.step <;> assumption
      case right => apply Multi.rfl
  | step _ _ _ h3 h4 ih =>
    cases h2 with
    | rfl =>
      apply Exists.intro _
      constructor
      case left => apply Multi.rfl
      case right => apply Multi.step <;> assumption
    | step _ _ _ h5 h6 =>
      apply ih
      have := hdeterm _ _ _ h3 h5
      rw [this]
      assumption

namespace Cube.Simple

@[simp]
def Expr.isLam : Expr → Bool
| .lam .. => true
| _ => false

inductive Value : Expr → Prop where
| lam : Value (.lam ty body orig)
| const : Value (.const name)
| constApp (h : Value v) : Value (.app (.const name) v)
| app (h1 : Value f) (h2 : ¬f.isLam) (h3 : Value v) : Value (.app f v)

inductive BetaStep : Expr → Expr → Prop where
| lamApp (h : Value arg) : BetaStep (.app (.lam ty body orig) arg) (Expr.instantiate arg body)
| leftApp (h : BetaStep t1 t1') : BetaStep (.app t1 t2) (.app t1' t2)
| rightApp (h1 : Value t1) (h2 : BetaStep t2 t2') : BetaStep (.app t1 t2) (.app t1 t2')

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
    case lamApp lam_typed _ =>
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
      | lamApp => simp[Expr.isLam] at h2
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

theorem Expr.step_deterministic (expr expr1' expr2' : Expr) (h1 : expr →β expr1') (h2 : expr →β expr2') : expr1' = expr2' := by
  induction h1 generalizing expr2' with
  | lamApp hval =>
    cases h2 with
    | lamApp => rfl
    | leftApp h => cases h
    | rightApp h1 hsteps =>
      exfalso
      apply Value.normal _ hval
      constructor
      assumption
  | leftApp h3 ih =>
    cases h2 with
    | lamApp => cases h3
    | leftApp h4 =>
      simp only [app.injEq, and_true]
      apply ih
      assumption
    | rightApp hval hsteps =>
      exfalso
      apply Value.normal _ hval
      constructor
      assumption
  | rightApp _ _ ih =>
    cases h2 with
    | lamApp =>
      exfalso
      apply Value.normal _ _
      constructor
      repeat assumption
    | leftApp =>
      exfalso
      apply Value.normal _ _
      constructor
      repeat assumption
    | rightApp =>
      simp only [app.injEq, true_and]
      apply ih
      assumption

theorem Expr.church_rosser (expr expr1' expr2' : Expr) (h1 : expr →β* expr1') (h2 : expr →β* expr2') : ∃ expr3', (expr1' →β* expr3') ∧ (expr2' →β* expr3') := by
  apply Multi.confluent_of_determ step_deterministic
  repeat assumption

def Expr.halts (expr : Expr) : Prop := ∃ expr', (expr →β* expr') ∧ Value expr'

theorem Value.halts (expr : Expr) (h : Value expr) : expr.halts := by
  constructor
  constructor
  exact Multi.rfl
  assumption

def R (env : Expr.Env) (t : Ty) (expr : Expr) : Prop :=
  ((env , []) ⊢ expr : t) ∧ expr.halts ∧ match t with
  | .nat => True
  | .fun t1 t2 => ∀ s, R env t1 s → R env t2 (.app expr s)

theorem R.halts (h : R env typ expr) : expr.halts := by
  cases typ <;> (
    unfold R at h
    cases h with
    | intro left right =>
      cases right;
      assumption
  )

theorem R.typable_empty (h : R env typ expr) : (env, []) ⊢ expr : typ := by
  cases typ <;> (
    unfold R at h;
    cases h with
    | intro left right => exact left)

theorem Expr.step_preserves_halt (expr expr' : Expr) (steps : expr →β expr') : expr.halts ↔ expr'.halts := by
  constructor
  case mp =>
    intro h
    match h with
    | ⟨w, ⟨hw, hv⟩⟩ =>
      cases hw with
      | rfl =>
        exfalso
        apply Value.normal
        repeat (first | assumption | constructor)
      | step _ _ _ steps2 multistep =>
        rewrite [Expr.step_deterministic _ _ _ steps steps2]
        apply Exists.intro
        constructor
        repeat assumption
  case mpr =>
    intro h
    match h with
    | ⟨w, ⟨hw, hv⟩⟩ =>
      constructor
      constructor
      case left => apply Multi.step; repeat assumption
      case right => assumption

theorem R.step_preserves (expr expr' : Expr) (steps : expr →β expr') : R env t expr → R env t expr' := by
  intro h
  induction t generalizing expr expr' with
  | nat =>
    simp_all only [R, and_true]
    constructor
    case left =>
      apply Expr.subject_reduction
      exact h.left
      assumption
    case right =>
      rw[←Expr.step_preserves_halt]
      exact h.right
      assumption
  | «fun» preimage image preih imih =>
    simp_all only [R]
    refine And.intro ?_ (And.intro ?_ ?_)
    next =>
      apply Expr.subject_reduction
      exact h.left
      assumption
    next =>
      rw[←Expr.step_preserves_halt]
      exact h.right.left
      assumption
    next =>
      intro s hs
      apply imih
      case steps =>
        apply BetaStep.leftApp
        assumption
      case h =>
        apply h.right.right
        assumption

theorem R.multi_step_preserves (expr expr' : Expr) (steps : expr →β* expr') : R env t expr → R env t expr' := by
  intro h
  induction steps with
  | rfl => assumption
  | step _ _ _ _ _ ih2 =>
    apply ih2
    apply R.step_preserves
    repeat assumption

theorem R.step_preserves' (typed : (env, []) ⊢ expr : t) (steps : expr →β expr') (h : R env t expr') : R env t expr := by
  induction t generalizing expr expr' with
  | nat =>
    simp_all only [R, and_true, true_and]
    rw[Expr.step_preserves_halt]
    exact h.right
    assumption
  | «fun» preimage image preih imih =>
    simp_all only [R, true_and]
    constructor
    case left =>
      rw[Expr.step_preserves_halt]
      exact h.right.left
      assumption
    case right =>
      intro s hs
      apply imih
      case typed =>
        unfold R at hs
        apply Expr.Typing.app
        assumption
        exact hs.left
      case steps =>
        apply BetaStep.leftApp
        assumption
      case h =>
        apply h.right.right
        assumption

theorem R.multi_step_preserves' (typed : (env, []) ⊢ expr : t) (steps : expr →β* expr') (h : R env t expr') : R env t expr := by
  induction steps with
  | rfl => assumption
  | step _ _ _ _ _ ih2 =>
    apply R.step_preserves'
    assumption
    assumption
    apply ih2
    case typed =>
      apply Expr.subject_reduction
      repeat assumption
    case h => assumption

theorem Expr.strong_normalization (expr : Expr) (typed : (env, ctx) ⊢ expr : ty) : ∃ target, (expr →β target) ∧ Value target := by
  sorry

end Cube.Simple
