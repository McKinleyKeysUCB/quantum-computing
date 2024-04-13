
import Init.Data.Nat.Basic
import Mathlib.Tactic.Lemma
import Mathlib.Order.Basic
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Data.Nat.Defs
import Quantum.Definitions

lemma Nat.pos_iff_one_le {n : ℕ} :
  0 < n ↔ 1 ≤ n
  := calc
    0 < n ↔ n ≠ 0       := Nat.pos_iff_ne_zero
    _     ↔ 1 ≤ n       := by symm; apply one_le_iff_ne_zero

lemma Fin.eq_zero_of_Fin_1 {i : Fin 1} :
  i = 0
  := by
    apply eq_of_val_eq
    apply Nat.lt_one_iff.mp i.isLt

lemma Fin.eq_three_of_ne_all {i : Fin 4} (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
  i = 3
  := by
    apply Fin.ext
    apply Fin.val_ne_iff.mpr at hi0
    apply Fin.val_ne_iff.mpr at hi1
    apply Fin.val_ne_iff.mpr at hi2
    apply Nat.le_antisymm
    · exact Fin.succ_le_succ_iff.mp i.isLt
    apply Nat.pos_iff_ne_zero.mpr at hi0
    apply Nat.pos_iff_one_le.mp at hi0
    apply (Nat.lt_of_le_of_ne · hi1.symm) at hi0
    exact Nat.lt_of_le_of_ne hi0 hi2.symm

lemma Fin.bash2 {P : Fin 2 → Fin 1 → Prop} (hP0 : P 0 0) (hP1 : P 1 0) :
  ∀ (i : Fin 2) (j : Fin 1), P i j
  := by
    intro i j
    rw [Fin.eq_zero_of_Fin_1 (i := j)]
    by_cases hi0 : i = 0
    · rw [hi0]
      exact hP0
    have hi1 : i = 1 := eq_one_of_neq_zero i hi0
    rw [hi1]
    exact hP1

lemma Fin.bash4 {P : Fin 4 → Fin 1 → Prop} (hP0 : P 0 0) (hP1 : P 1 0) (hP2 : P 2 0) (hP3 : P 3 0) :
  ∀ (i : Fin 4) (j : Fin 1), P i j
  := by
    intro i j
    rw [Fin.eq_zero_of_Fin_1 (i := j)]
    by_cases hi0 : i = 0
    · rw [hi0]
      exact hP0
    by_cases hi1 : i = 1
    · rw [hi1]
      exact hP1
    by_cases hi2 : i = 2
    · rw [hi2]
      exact hP2
    have hi3 : i = 3 := Fin.eq_three_of_ne_all hi0 hi1 hi2
    rw [hi3]
    exact hP3
