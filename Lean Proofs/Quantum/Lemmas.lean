
import Init.Data.Nat.Basic
import Mathlib.Tactic.Lemma
import Mathlib.Order.Basic
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic

notation "√" a => Complex.ofReal (Real.sqrt a)


/-
 - Nat
 -/

lemma Nat.pos_iff_one_le {n : ℕ} :
  0 < n ↔ 1 ≤ n
  := calc
    0 < n ↔ n ≠ 0       := Nat.pos_iff_ne_zero
    _     ↔ 1 ≤ n       := by symm; apply one_le_iff_ne_zero


/-
 - Fin
 -/

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

lemma Fin.false_of_mem_Fin_zero (a : Fin 0) :
  False
  := by
    have : a.val < 0 := a.isLt
    rw [@Nat.lt_iff_le_and_ne] at this
    rcases this with ⟨h₁, h₂⟩
    apply Nat.eq_zero_of_le_zero at h₁
    exact h₂ h₁

def Fin.div_mod_inv {a b : ℕ} (q : Fin a) (r : Fin b) : Fin (a * b) :=
  ⟨b * q + r, by
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    dsimp only
    have : q + 1 ≤ a := by
      exact hq
    calc
      _ < b * q + b       := by simp only [add_lt_add_iff_left, hr]
      _ = b * (q + 1)     := by ring
      _ ≤ b * a           := Nat.mul_le_mul_left b hq
      _ = a * b           := mul_comm _ _
  ⟩

lemma Fin.divNat_div_mod_inv {a b : ℕ} {q : Fin a} {r : Fin b} :
  (div_mod_inv q r).divNat = q
  := by
    by_cases hb : b = 0
    · rw [hb] at r
      exfalso
      exact Fin.false_of_mem_Fin_zero r
    · apply Nat.zero_lt_of_ne_zero at hb
      rw [div_mod_inv, Fin.divNat]
      apply Fin.ext
      dsimp only
      rw [
        Nat.div_eq_sub_mod_div,
        Nat.mul_add_mod,
        Nat.mod_eq_of_lt r.isLt,
        add_tsub_cancel_right,
        Nat.mul_div_cancel_left _ hb,
      ]

lemma Fin.modNat_div_mod_inv {a b : ℕ} {q : Fin a} {r : Fin b} :
  (div_mod_inv q r).modNat = r
  := by
    rw [div_mod_inv, Fin.modNat]
    apply Fin.ext
    dsimp only
    rw [
      Nat.add_mod,
      Nat.mul_mod_right,
      zero_add,
      Nat.mod_mod,
      Nat.mod_eq_of_lt r.isLt,
    ]

lemma Fin.eq_of_div_eq_div_and_mod_eq_mod {a b : ℕ} {x y : Fin (a * b)} (hdiv : x.divNat = y.divNat) (hmod : x.modNat = y.modNat) :
  x = y
  := by
    simp only [divNat, mk.injEq] at hdiv
    simp only [modNat, mk.injEq] at hmod
    apply Fin.ext
    rw [← Nat.div_add_mod ↑x b, ← Nat.div_add_mod ↑y b, hdiv, hmod]

lemma Fin.div_div_eq_div_cast {a b c : ℕ} {i : Fin (a * b * c)} {h : (a * b * c) = (a * (b * c))} :
  Fin.divNat (Fin.divNat i) = Fin.divNat (Fin.cast h i)
  := by
    unfold divNat
    simp only [coe_cast, mk.injEq]
    rw [Nat.div_div_eq_div_mul, mul_comm c b]

lemma Fin.mod_div_eq_div_mod_cast {a b c : ℕ} {i : Fin (a * b * c)} {h : (a * b * c) = (a * (b * c))} :
  Fin.modNat (Fin.divNat i) = Fin.divNat (Fin.modNat (Fin.cast h i))
  := by
    unfold divNat modNat
    simp only [coe_cast, mk.injEq]
    rw [Nat.mod_mul_left_div_self]

lemma Fin.mod_eq_mod_mod_cast {a b c : ℕ} {i : Fin (a * b * c)} {h : (a * b * c) = (a * (b * c))} :
  Fin.modNat i = Fin.modNat (Fin.modNat (Fin.cast h i))
  := by
    unfold modNat
    simp only [coe_cast, Nat.mod_mul_left_mod]


/-
 - Casting
 -/

lemma cast_apply_eq_apply {α α' β β' γ : Type} {f : α → β → γ} {a : α} {b : β} {a' : α'} {b' : β'} (ha : HEq a' a) (hb : HEq b' b) {h : (α → β → γ) = (α' → β' → γ)} :
  cast h f a' b' = f a b
  := by
    cases ha
    cases hb
    rfl


/-
 - Logic
 -/

lemma if_true_false {p : Bool} :
  (if p then true else false) = p
  := by
    by_cases h : p <;> simp only [h, ↓reduceIte]

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


/-
 - Matrix
 -/

lemma Matrix.ne_zero_of_element_ne_zero {m n α : Type} [Zero α] {M : Matrix m n α} (i : m) (j : n) (hij : M i j ≠ 0) :
  M ≠ 0
  := by
    exact fun a => hij (congrFun (congrFun a i) j)


/-
 - Square Roots
 -/

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

lemma one_div_sqrt_half_mul_half :
  ↑(1 / Real.sqrt (1 / 2)) * (1 / 2) = 1 / Complex.ofReal (Real.sqrt 2)
  := by
    rw [Complex.ofReal_eq_coe, Complex.div_ofReal, Complex.ofReal_mul']
    simp only [
      one_div,
      Real.sqrt_inv,
      div_inv_eq_mul,
      one_mul,
      Complex.inv_re,
      Complex.re_ofNat,
      Complex.normSq_ofNat,
      div_self_mul_self',
      Complex.inv_im,
      Complex.im_ofNat,
      neg_zero,
      zero_div,
      mul_zero,
      Complex.one_re,
      Complex.one_im,
      Complex.mk.injEq,
      and_true,
    ]
    rw [← division_def, Real.sqrt_div_self]

lemma one_div_sqrt_half_mul_one_div_sqrt_two :
  ↑(1 / Real.sqrt (1 / 2)) * (1 / Complex.ofReal (Real.sqrt 2)) = 1
  := by
    simp only [one_div, Real.sqrt_inv, div_inv_eq_mul, one_mul, Complex.ofReal_eq_coe, ne_eq,
      Complex.ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_inv_cancel]

lemma sqrt_two_div_two_sq :
  Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2
  := by
    simp only [Real.sqrt_div_self', one_div, ← mul_inv, Nat.ofNat_nonneg, Real.mul_self_sqrt]
