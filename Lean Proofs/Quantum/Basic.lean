
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Quantum.Definitions
import Quantum.Lemmas

lemma norm_ket0_eq_1 :
  | |0⟩ | = 1
  := by
    simp [norm, ket0', Qubit.α, Qubit.β]
lemma norm_ket1_eq_1 :
  | |1⟩ | = 1
  := by
    simp [norm, ket1', Qubit.α, Qubit.β]

lemma norm_ket_plus_eq_1 :
  | |+⟩ | = 1
  := by
    simp [norm, ket_plus', Qubit.α, Qubit.β]
    sorry

lemma qubit_tens_qubit (a b : Qubit) :
  a ⊗ b = Matrix.of (fun i _ =>
    if i = 0 then
      (a 0 0) * (b 0 0)
    else if i = 1 then
      (a 0 0) * (b 1 0)
    else if i = 2 then
      (a 1 0) * (b 0 0)
    else
      (a 1 0) * (b 1 0)
  )
  := by
    dsimp only [Tens]
    simp
    apply funext₂
    intro i j
    have hj : j = 0 := by
      apply Fin.eq_zero
    by_cases i0 : i = 0
    · simp [i0, hj]
      congr
    by_cases i1 : i = 1
    · simp [i1, hj]
      congr
    by_cases i2 : i = 2
    · simp [i2, hj]
      congr
    have i3 : i = 3 := by
      have : i.val < 4 := i.isLt
      apply Fin.ext
      apply Fin.val_ne_iff.mpr at i0
      apply Fin.val_ne_iff.mpr at i1
      apply Fin.val_ne_iff.mpr at i2
      apply Nat.pos_iff_ne_zero.mpr at i0
      apply Nat.pos_iff_one_le.mp at i0
      apply (Nat.lt_of_le_of_ne · i1.symm) at i0
      have two_lt : (2 : ℕ) < ↑i := by
        exact Nat.lt_of_le_of_ne i0 i2.symm
      have : ↑i ≤ 3 := by
        exact Fin.succ_le_succ_iff.mp this
      exact Nat.le_antisymm this two_lt
    simp [i3, hj]
    congr

lemma temp (i : Fin 4) (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
  i = 3
  := by
    rw [Fin.ext_iff]
    rw [Ne, Fin.ext_iff] at *
    
    sorry

lemma bash4 {P : Fin 4 → Fin 1 → Prop} (hP0 : P 0 0) (hP1 : P 1 0) (hP2 : P 2 0) (hP3 : P 3 0) :
  ∀ (i : Fin 4) (j : Fin 1), P i j
  := by
    sorry

lemma ket0_tens_ket0_eq_ket00 :
  |0⟩ ⊗ |0⟩ = |00⟩
  := by
    rw [qubit_tens_qubit, ← Matrix.ext_iff]
    intro i j
    unfold ket0' ket00'
    simp
lemma ket1_tens_ket1_eq_ket11 :
  |1⟩ ⊗ |1⟩ = |11⟩
  := by
    rw [qubit_tens_qubit, ← Matrix.ext_iff]
    intro i j
    unfold ket1' ket11'
    simp
    by_cases hi0 : i = 0
    · simp [*]
    by_cases hi1 : i = 1
    · simp [*]
    by_cases hi2 : i = 2
    · simp [*]
    have hi3 : i = 3 := temp i hi0 hi1 hi2
    simp [*]

lemma tens_add {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  C ⊗ (A + B) = C ⊗ A + C ⊗ B
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, Tens, Tens, Tens]
    simp
    rw [mul_add]
lemma add_tens {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  (A + B) ⊗ C = A ⊗ C + B ⊗ C
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, Tens, Tens, Tens]
    simp
    rw [add_mul]

lemma mul_tens {m₁ n₁ m₂ n₂ : ℕ} {s : ℂ} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} :
  (s • A) ⊗ B = s • (A ⊗ B)
  := by
    simp [Tens, Pi.smul_def]
    apply funext₂
    intro i j
    ring
lemma tens_mul {m₁ n₁ m₂ n₂ : ℕ} {s : ℂ} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} :
  A ⊗ (s • B) = s • (A ⊗ B)
  := by
    simp [Tens, Pi.smul_def]
    apply funext₂
    intro i j
    ring

lemma decompose_qubit_into_Z_basis (φ : Qubit) :
  φ = φ.α • |0⟩ + φ.β • |1⟩
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply]
    rw [Matrix.smul_apply, Matrix.smul_apply]
    have hj : j = 0 := by
      apply Fin.eq_zero
    rw [hj, ket0', ket1']
    by_cases hi : i = 0
    · rw [
        hi,
        if_pos rfl,
        if_neg zero_ne_one,
      ]
      simp
      congr
    · apply Fin.eq_one_of_neq_zero i at hi
      rw [
        hi,
        if_neg one_ne_zero,
        if_pos rfl,
      ]
      simp
      congr

lemma tens_self (φ : Qubit) :
  let α := φ 0 0
  let β := φ 1 0
  φ ⊗ φ = Matrix.of (fun i _ =>
    if i = 0 then
      α^2
    else if i = 1 then
      α * β
    else if i = 2 then
      β * α
    else
      β^2
  )
  := by
    intro α β
    rw [qubit_tens_qubit, pow_two, pow_two]
