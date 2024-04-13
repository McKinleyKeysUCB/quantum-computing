
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Quantum.Definitions
import Quantum.Lemmas

lemma norm_ket0_eq_1 :
  | |0⟩ | = 1
  := by
    simp [norm, ket0, Qubit.α, Qubit.β]

lemma norm_ket1_eq_1 :
  | |1⟩ | = 1
  := by
    simp [norm, ket1, Qubit.α, Qubit.β]

lemma norm_ket_plus_eq_1 :
  | |+⟩ | = 1
  := by
    simp [norm, ket_plus, Qubit.α, Qubit.β]
    rw [inv_eq_one_div, add_halves]

lemma qubit_unitary {φ : Qubit} (h : Complex.normSq φ.α + Complex.normSq φ.β = 1) :
  φ.unitary
  := by
    sorry

lemma ket0_unitary :
  |0⟩.unitary
  := by
    apply qubit_unitary
    unfold Qubit.α Qubit.β ket0
    simp
lemma ket1_unitary :
  |1⟩.unitary
  := by
    apply qubit_unitary
    unfold Qubit.α Qubit.β ket1
    simp
lemma bra1_mul_ket0 :
  ⟨1| * |0⟩ = 0
  := by
    unfold bra1 ket0 ket1 QMatrix.adjoint
    apply Matrix.ext
    intro i j
    simp [Matrix.mul_apply]
lemma bra0_mul_ket1 :
  ⟨0| * |1⟩ = 0
  := by
    unfold bra0 ket0 ket1 QMatrix.adjoint
    apply Matrix.ext
    intro i j
    simp [Matrix.mul_apply]

lemma ket_plus_eq_ket0_plus_ket1 :
  |+⟩ = (1/√2) • (|0⟩ + |1⟩)
  := by
    unfold ket_plus ket0 ket1
    apply Matrix.ext
    apply Fin.bash2 <;> simp

lemma ket_minus_eq_ket0_minus_ket1 :
  |-⟩ = (1/√2) • (|0⟩ - |1⟩)
  := by
    unfold ket_minus ket0 ket1
    apply Matrix.ext
    apply Fin.bash2 <;> simp

lemma qubit_tens_qubit (a b : Qubit) :
  a ⨂ b = fun i _ =>
    if i = 0 then
      (a 0 0) * (b 0 0)
    else if i = 1 then
      (a 0 0) * (b 1 0)
    else if i = 2 then
      (a 1 0) * (b 0 0)
    else
      (a 1 0) * (b 1 0)
  := by
    dsimp only [tens]
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

lemma ket0_tens_ket0_eq_ket00 :
  |0⟩ ⨂ |0⟩ = |00⟩
  := by
    rw [qubit_tens_qubit, ← Matrix.ext_iff]
    intro i j
    unfold ket0 ket00
    simp
lemma ket1_tens_ket1_eq_ket11 :
  |1⟩ ⨂ |1⟩ = |11⟩
  := by
    rw [qubit_tens_qubit, ← Matrix.ext_iff]
    unfold ket1 ket11
    simp only [Fin.isValue, zero_ne_one, ↓reduceIte, mul_zero, mul_one, Matrix.of_apply]
    apply Fin.bash4 <;> simp [*]

lemma tens_add {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  C ⨂ (A + B) = C ⨂ A + C ⨂ B
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, tens, tens, tens]
    simp
    rw [mul_add]
lemma add_tens {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  (A + B) ⨂ C = A ⨂ C + B ⨂ C
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, tens, tens, tens]
    simp
    rw [add_mul]

lemma smul_tens {m₁ n₁ m₂ n₂ : ℕ} {s : ℂ} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} :
  (s • A) ⨂ B = s • (A ⨂ B)
  := by
    simp [tens, Pi.smul_def]
    apply funext₂
    intro i j
    ring
lemma tens_smul {m₁ n₁ m₂ n₂ : ℕ} {s : ℂ} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} :
  A ⨂ (s • B) = s • (A ⨂ B)
  := by
    simp [tens, Pi.smul_def]
    apply funext₂
    intro i j
    ring

def div_mod_inv {a b : ℕ} (q : Fin a) (r : Fin b) : Fin (a * b) :=
  ⟨b * q + r, by
    rcases q with ⟨q, hq⟩
    rcases r with ⟨r, hr⟩
    dsimp only
    have : q + 1 ≤ a := by
      exact hq
    calc
      _ < b * q + b       := by simp [hr]
      _ = b * (q + 1)     := by ring
      _ ≤ b * a           := Nat.mul_le_mul_left b hq
      _ = a * b           := mul_comm _ _
  ⟩

-- theorem tens_ext {M : QMatrix (m*p) (n*q)} (h : ∀ (r : Fin m) (s : Fin n) (v : Fin p) (w : Fin q), A r s * B v w = M (div_mod_inv r v) (div_mod_inv s w)) :
--   -- A ⨂ B = M
--   M = A ⨂ B
--   := by
--     sorry

lemma tens_mul_tens {a₁ b₁ c₁ a₂ b₂ c₂ : ℕ} {A : QMatrix a₁ b₁} {B : QMatrix a₂ b₂} {C : QMatrix b₁ c₁} {D : QMatrix b₂ c₂} :
  (A ⨂ B) * (C ⨂ D) = (A * C) ⨂ (B * D)
  := by
    -- apply tens_ext
    -- intro r s v w
    -- unfold tens
    -- rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
    -- dsimp
    simp
    apply Matrix.ext
    intro i j
    simp [Matrix.mul_apply]
    rw [Finset.sum_mul_sum]
    
    sorry

lemma zero_tens {m₁ n₁ m₂ n₂ : ℕ} {M : QMatrix m₂ n₂} :
  (0 : QMatrix m₁ n₁) ⨂ M = 0
  := by
    simp
    rfl
lemma tens_zero {m₁ n₁ m₂ n₂ : ℕ} {M : QMatrix m₁ n₁} :
  M ⨂ (0 : QMatrix m₂ n₂) = 0
  := by
    simp
    rfl

lemma CNOT_mul_ket0_tens {φ : Qubit} :
  CNOT * (|0⟩ ⨂ φ) = |0⟩ ⨂ φ
  := by
    unfold CNOT
    rw [
      Matrix.add_mul,
      tens_mul_tens,
      tens_mul_tens,
      Matrix.mul_assoc,
      ket0_unitary,
      Matrix.mul_assoc,
      bra1_mul_ket0,
      Matrix.mul_one,
      Matrix.mul_zero,
      zero_tens,
      I₂,
      Matrix.one_mul,
    ]
    simp
lemma CNOT_mul_ket1_tens {φ : Qubit} :
  CNOT * (|1⟩ ⨂ φ) = |1⟩ ⨂ (X * φ)
  := by
    unfold CNOT
    rw [
      Matrix.add_mul,
      tens_mul_tens,
      tens_mul_tens,
      Matrix.mul_assoc,
      Matrix.mul_assoc,
      ket1_unitary,
      bra0_mul_ket1,
      Matrix.mul_one,
      Matrix.mul_zero,
      zero_tens,
    ]
    simp

lemma X_mul_ket0 :
  X * |0⟩ = |1⟩
  := by
    unfold X ket0 ket1
    apply Matrix.ext
    apply Fin.bash2 <;> {
      rw [Matrix.mul_apply]
      simp
    }
lemma X_mul_ket1 :
  X * |1⟩ = |0⟩
  := by
    unfold X ket0 ket1
    apply Matrix.ext
    apply Fin.bash2 <;> {
      rw [Matrix.mul_apply]
      simp
    }

lemma decompose_qubit_into_Z_basis (φ : Qubit) :
  φ = φ.α • |0⟩ + φ.β • |1⟩
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply]
    rw [Matrix.smul_apply, Matrix.smul_apply]
    have hj : j = 0 := by
      apply Fin.eq_zero
    rw [hj, ket0, ket1]
    by_cases hi : i = 0
    · rw [hi]
      simp
    · apply Fin.eq_one_of_neq_zero i at hi
      rw [hi]
      simp

lemma tens_self (φ : Qubit) :
  let α := φ 0 0
  let β := φ 1 0
  φ ⨂ φ = fun i _ =>
    if i = 0 then
      α^2
    else if i = 1 then
      α * β
    else if i = 2 then
      β * α
    else
      β^2
  := by
    intro α β
    rw [qubit_tens_qubit, pow_two, pow_two]



@[simp]
lemma H_ket0 :
  H * |0⟩ = |+⟩
  := by
    unfold H ket0 ket_plus
    rw [Matrix.smul_mul]
    congr
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply]
    simp

@[simp]
lemma H_ket1 :
  H * |1⟩ = |-⟩
  := by
    unfold H ket1 ket_minus
    rw [Matrix.smul_mul]
    congr
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply]
    simp


/-
 - Adjoints
 -/

@[simp]
lemma double_adjoint {m n : ℕ} (M : QMatrix m n) :
  M†† = M
  := by
    apply Matrix.ext
    intro i j
    simp

@[simp]
lemma adjoint_mul {a b c : ℕ} (A : QMatrix a b) (B : QMatrix b c) :
  (A * B)† = B† * A†
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply']
    unfold QMatrix.adjoint
    rw [Matrix.mul_apply', ← Matrix.star_dotProduct_star]
    rfl

@[simp]
lemma proj_hermitian {m n : ℕ} (M : QMatrix m n) :
  QSquare.hermitian (M * M†)
  := by
    simp
