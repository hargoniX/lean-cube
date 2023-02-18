import Std.Data.List.Lemmas
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Order.Basic

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
