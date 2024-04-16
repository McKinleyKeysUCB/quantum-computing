
import Init.Data.Nat.Basic
import Mathlib.Tactic.Lemma
import Mathlib.Order.Basic
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

notation "√" a => Complex.ofReal (Real.sqrt a)

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

lemma if_true_false {p : Bool} :
  (if p then true else false) = p
  := by
    by_cases h : p <;> simp [h]

lemma false_of_mem_Fin_zero (a : Fin 0) :
  False
  := by
    have : a.val < 0 := a.isLt
    rw [@Nat.lt_iff_le_and_ne] at this
    rcases this with ⟨h₁, h₂⟩
    apply Nat.eq_zero_of_le_zero at h₁
    exact h₂ h₁

lemma one_div_sqrt_two_sq :
  (1/√2) * (1/√2) = 1/2
  := by
    rw [
      div_mul_div_comm,
      one_mul,
      ← sq _,
      Complex.ofReal_eq_coe,
      ← Complex.ofReal_pow,
    ]
    simp only [Nat.ofNat_nonneg, Real.sq_sqrt, Complex.ofReal_ofNat, one_div]

lemma if_then_self_else_not_self {P : Prop} [Decidable P] :
  if P then P else ¬P
  := by
    simp only [ite_prop_iff_or, and_self, em]

lemma not_forall₂ {α β : Type} {P : α → β → Prop} :
  (¬∀ (x : α) (y : β), P x y) ↔ ∃ (x : α), ∃ (y : β), ¬P x y
  := by
    rw [not_forall]
    constructor
    · intro h
      rcases h with ⟨x, h⟩
      rw [not_forall] at h
      rcases h with ⟨y, h⟩
      use x
      use y
    · intro h
      rcases h with ⟨x, ⟨y, h⟩⟩
      use x
      rw [not_forall]
      use y
