import Std.Data.Nat.Lemmas
import Std.Data.List.Lemmas


namespace Cube

abbrev Context := List

def Context.set (ctx : Context α) (n : Nat) (ty : α) : Context α :=
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

theorem Context.get_set (ctx : Context α) (i : Nat) (h : i < (Context.set ctx i ty).length) : List.get (Context.set ctx i ty) ⟨i, h⟩ = ty :=
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

theorem Context.get_set_neq {ctx : Context α} (h1 : i = ctx.length) (h2 : idx ≠ i) (h3 : idx < List.length ctx) : List.get (Context.set ctx i ty) ⟨idx, by rw[Context.set_succ_bound_length_eq_succ_length]; apply Nat.lt_succ_of_lt h3; assumption⟩ = List.get ctx ⟨idx, h3⟩ :=
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

theorem Context.get_set_irrelevant (ctx : Context α) (i1 i2 : Nat) (h1 : i2 < ctx.length) (h2 : i1 ≠ i2) : List.get (Context.set ctx i1 ty) ⟨i2, Nat.lt_of_lt_of_le h1 length_le_set_length⟩ = List.get ctx ⟨i2, h1⟩ :=
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

end Cube
