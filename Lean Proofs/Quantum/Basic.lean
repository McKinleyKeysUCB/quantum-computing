
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Quantum.Definitions
import Quantum.Congruence
import Quantum.Adjoint
import Quantum.TensorProduct


/-
 - Basic Lemmas
 -/

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

lemma ket0_unitary :
  |0⟩.unitary
  := by
    unfold QMatrix.unitary ket0 QMatrix.adjoint
    apply Matrix.ext
    intro i j
    simp [Fin.eq_zero i, Fin.eq_zero j, Matrix.mul_apply]

lemma ket1_unitary :
  |1⟩.unitary
  := by
    unfold QMatrix.unitary ket1 QMatrix.adjoint
    apply Matrix.ext
    intro i j
    simp [Fin.eq_zero i, Fin.eq_zero j, Matrix.mul_apply]

lemma bra0_mul_ket0 :
  ⟨0| * |0⟩ = 1
  := ket0_unitary

lemma bra1_mul_ket1 :
  ⟨1| * |1⟩ = 1
  := ket1_unitary

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

lemma qubit_unitary {φ : Qubit} :
  φ.unitary ↔ Complex.normSq φ.α + Complex.normSq φ.β = 1
  := by
    unfold QMatrix.unitary
    rw [decompose_qubit_into_Z_basis φ]
    simp only [adjoint_add, Matrix.add_mul, Matrix.mul_add, adjoint_smul, Matrix.mul_smul, Matrix.smul_mul, smul_add, smul_smul]
    rw [ket0_unitary, ket1_unitary, bra0_mul_ket1, bra1_mul_ket0]
    simp only [Complex.star_def, smul_zero, add_zero, zero_add, Matrix.smul_of, Fin.isValue,
      Matrix.of_add_of, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, ↓reduceIte, zero_ne_one,
      smul_eq_mul, mul_one, mul_zero, one_ne_zero]
    rw [← add_smul, ← Matrix.ext_iff]
    simp [Matrix.smul_apply, Matrix.one_apply, Fin.eq_zero, Complex.mul_conj]
    rw [← Complex.ofReal_add, Complex.ofReal_eq_one]

lemma qubit_unitary' {φ : Qubit} :
  φ.unitary ↔ star φ.α * φ.α + star φ.β * φ.β = 1
  := by
    rw [qubit_unitary, Complex.star_def]
    simp only [← Complex.normSq_eq_conj_mul_self]
    rw [← Complex.ofReal_add, Complex.ofReal_eq_one]


/-
 - Projection
 -/

lemma proj_mul_self {φ : Qubit} (h : φ.unitary) :
  φ * φ† * φ = φ
  := by
    rw [Matrix.mul_assoc, h, Matrix.mul_one]

@[simp]
lemma proj0_mul_ket0 :
  |0⟩ * ⟨0| * |0⟩ = |0⟩
  :=
    proj_mul_self ket0_unitary

@[simp]
lemma proj0_mul_ket1 :
  |0⟩ * ⟨0| * |1⟩ = 0
  := by
    rw [Matrix.mul_assoc, bra0_mul_ket1, Matrix.mul_zero]

@[simp]
lemma proj1_mul_ket0 :
  |1⟩ * ⟨1| * |0⟩ = 0
  := by
    rw [Matrix.mul_assoc, bra1_mul_ket0, Matrix.mul_zero]

@[simp]
lemma proj1_mul_ket1 :
  |1⟩ * ⟨1| * |1⟩ = |1⟩
  :=
    proj_mul_self ket1_unitary

lemma zero_proj_phi {φ : Qubit} :
  |0⟩⟨0| * φ = φ.α • |0⟩
  := by
    nth_rw 1 [decompose_qubit_into_Z_basis φ]
    simp only [Matrix.mul_add, Matrix.mul_smul, proj0_mul_ket0, proj0_mul_ket1, smul_zero, add_zero, Qubit.α]

lemma one_proj_phi {φ : Qubit} :
  |1⟩⟨1| * φ = φ.β • |1⟩
  := by
    nth_rw 1 [decompose_qubit_into_Z_basis φ]
    simp only [Matrix.mul_add, Matrix.mul_smul, proj1_mul_ket0, proj1_mul_ket1, smul_zero, zero_add, Qubit.β]

@[simp]
lemma zero_proj_phi' {φ : Qubit} :
  QMatrix.toReal ((|0⟩⟨0| * φ)† * (|0⟩⟨0| * φ)) = ‖φ.α‖
  := by
    rw [
      zero_proj_phi,
      adjoint_smul,
      Matrix.smul_mul,
      Matrix.mul_smul,
      smul_smul,
      ket0_unitary,
      QMatrix.toReal,
      Matrix.smul_apply,
      Matrix.one_apply,
      if_pos rfl,
      smul_eq_mul,
      mul_one,
      Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re,
    ]

@[simp]
lemma one_proj_phi' {φ : Qubit} :
  QMatrix.toReal ((|1⟩⟨1| * φ)† * (|1⟩⟨1| * φ)) = ‖φ.β‖
  := by
    rw [
      one_proj_phi,
      adjoint_smul,
      Matrix.smul_mul,
      Matrix.mul_smul,
      smul_smul,
      ket1_unitary,
      QMatrix.toReal,
      Matrix.smul_apply,
      Matrix.one_apply,
      if_pos rfl,
      smul_eq_mul,
      mul_one,
      Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self,
      Complex.ofReal_re,
    ]


/-
 - Two-Qubit Lemmas
 -/

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
lemma ket0_tens_ket0 :
  |0⟩ ⨂ |0⟩ = |00⟩
  := by
    rw [qubit_tens_qubit, ← Matrix.ext_iff]
    intro i j
    unfold ket0 ket00
    simp

@[simp]
lemma ket0_tens_ket1 :
  |0⟩ ⨂ |1⟩ = |01⟩
  := by
    rw [qubit_tens_qubit, ← Matrix.ext_iff]
    intro i j
    unfold ket0 ket1 ket01
    simp
    intro i'
    rw [if_neg]
    norm_num [i']

@[simp]
lemma ket1_tens_ket0 :
  |1⟩ ⨂ |0⟩ = |10⟩
  := by
    rw [qubit_tens_qubit, ← Matrix.ext_iff]
    intro i j
    unfold ket0 ket1 ket10
    simp
    by_cases hi : i = 2 <;> simp [hi]

@[simp]
lemma ket1_tens_ket1 :
  |1⟩ ⨂ |1⟩ = |11⟩
  := by
    rw [qubit_tens_qubit, ← Matrix.ext_iff]
    unfold ket1 ket11
    simp only [Fin.isValue, zero_ne_one, ↓reduceIte, mul_zero, mul_one, Matrix.of_apply]
    apply Fin.bash4 <;> simp [*]


/-
 - CNOT
 -/

@[simp]
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

@[simp]
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

-- TODO: The proofs of these lemmas are basically copies of the above ones. Figure out a better way of proving them.

@[simp]
lemma CNOT'_mul_tens_ket0 {φ : Qubit} :
  CNOT' * (φ ⨂ |0⟩) = φ ⨂ |0⟩
  := by
    unfold CNOT'
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
      tens_zero,
      I₂,
      Matrix.one_mul,
    ]
    simp

@[simp]
lemma CNOT'_mul_tens_ket1 {φ : Qubit} :
  CNOT' * (φ ⨂ |1⟩) = (X * φ) ⨂ |1⟩
  := by
    unfold CNOT'
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
      tens_zero,
    ]
    simp


/-
 - X Gate
 -/

@[simp]
lemma X_mul_ket0 :
  X * |0⟩ = |1⟩
  := by
    unfold X ket0 ket1
    apply Matrix.ext
    apply Fin.bash2 <;> {
      rw [Matrix.mul_apply]
      simp
    }

@[simp]
lemma X_mul_ket1 :
  X * |1⟩ = |0⟩
  := by
    unfold X ket0 ket1
    apply Matrix.ext
    apply Fin.bash2 <;> {
      rw [Matrix.mul_apply]
      simp
    }

lemma X_mul_qubit' {α β : ℂ} :
  X * (α•|0⟩ + β•|1⟩) = β•|0⟩ + α•|1⟩
  := by
    simp only [Matrix.mul_add, Matrix.mul_smul, X_mul_ket0, X_mul_ket1, add_comm]

lemma X_mul_qubit {φ : Qubit} :
  X * φ = φ.β•|0⟩ + φ.α•|1⟩
  := by
    nth_rw 1 [decompose_qubit_into_Z_basis φ]
    rw [X_mul_qubit']


/-
 - Z Gate
 -/

@[simp]
lemma Z_mul_ket0 :
  Z * |0⟩ = |0⟩
  := by
    unfold Z ket0
    apply Matrix.ext
    apply Fin.bash2 <;> {
      rw [Matrix.mul_apply]
      simp
    }

@[simp]
lemma Z_mul_ket1 :
  Z * |1⟩ = -|1⟩
  := by
    unfold Z ket1
    apply Matrix.ext
    apply Fin.bash2 <;> {
      rw [Matrix.mul_apply]
      simp
    }

lemma Z_mul_qubit' {α β : ℂ} :
  Z * (α•|0⟩ + β•|1⟩) = α•|0⟩ - β•|1⟩
  := by
    simp only [Matrix.mul_add, Matrix.mul_smul, Z_mul_ket0, Z_mul_ket1, smul_neg, sub_eq_add_neg]

lemma Z_mul_qubit {φ : Qubit} :
  Z * φ = φ.α•|0⟩ - φ.β•|1⟩
  := by
    nth_rw 1 [decompose_qubit_into_Z_basis φ]
    rw [Z_mul_qubit']


/-
 - H Gate
 -/

@[simp]
lemma H_mul_ket0 :
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
lemma H_mul_ket1 :
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
 - Unitaries
 -/

@[simp]
lemma unitary_tens_unitary {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} (hA : A.unitary) (hB : B.unitary) :
  (A ⨂ B).unitary
  := by
    unfold QMatrix.unitary
    rw [adjoint_tens, tens_mul_tens, hA, hB]
    unfold tens
    apply Matrix.ext
    intro i j
    simp [Matrix.one_apply, Fin.modNat, Fin.divNat]
    by_cases h : i = j
    · rw [if_pos]
      simp [h]
      exact congrFun (congrArg HMod.hMod (congrArg Fin.val h)) n₂
    · simp [*]
      intro h'
      contrapose h
      rw [not_not] at h ⊢
      rw [Fin.ext_iff, ← Nat.div_add_mod ↑i n₂, ← Nat.div_add_mod ↑j n₂]
      simp [*]

lemma ket00_unitary :
  |00⟩.unitary
  := by
    rw [← ket0_tens_ket0]
    exact unitary_tens_unitary ket0_unitary ket0_unitary

lemma ket01_unitary :
  |01⟩.unitary
  := by
    rw [← ket0_tens_ket1]
    exact unitary_tens_unitary ket0_unitary ket1_unitary

lemma ket10_unitary :
  |10⟩.unitary
  := by
    rw [← ket1_tens_ket0]
    exact unitary_tens_unitary ket1_unitary ket0_unitary

lemma ket11_unitary :
  |11⟩.unitary
  := by
    rw [← ket1_tens_ket1]
    exact unitary_tens_unitary ket1_unitary ket1_unitary


/-
 - Hermitian
 -/

lemma hermitian_of_symm_of_real {n : ℕ} {M : QSquare n} (hs : M.symmetric) (hr : M.real) :
  M.hermitian
  := by
    unfold QSquare.hermitian QMatrix.adjoint
    unfold QSquare.symmetric Matrix.transpose at hs
    unfold QMatrix.real at hr
    apply Matrix.ext_iff.mpr at hs
    apply Matrix.ext
    intro i j
    specialize hs i j
    specialize hr j i
    rw [Matrix.of_apply] at hs
    rw [hr, hs]

lemma X_symm :
  X.symmetric
  := by
    apply Matrix.ext
    simp only [Matrix.transpose_apply, X, Eq.comm, forall_const]

lemma X_real :
  X.real
  := by
    simp only [QMatrix.real, X, Complex.star_def, RingHom.map_ite_zero_one, forall_const]

lemma X_hermitian :
  X.hermitian
  := hermitian_of_symm_of_real X_symm X_real

lemma Z_symm :
  Z.symmetric
  := by
    apply Matrix.ext
    simp only [Matrix.transpose_apply, Z, Eq.comm, Fin.isValue]
    intro i j
    rw [apply_ite₂ (· = ·)]
    by_cases h : i = j
    · simp only [h, ↓reduceIte, Fin.isValue]
    · rw [if_neg h]

lemma Z_real :
  Z.real
  := by
    simp [QMatrix.real, Z, Complex.star_def, RingHom.map_ite_zero_one, forall_const]
    intro i j
    by_cases h : i = j
    · simp only [h, ↓reduceIte, Fin.isValue, apply_ite, map_one, map_neg, ite_eq_left_iff, neg_eq_self_iff, one_ne_zero, imp_false, not_not, ite_eq_right_iff, eq_neg_self_iff, if_then_self_else_not_self]
    · simp only [h, ↓reduceIte, map_zero]

lemma Z_hermitian :
  Z.hermitian
  := hermitian_of_symm_of_real Z_symm Z_real

@[simp]
lemma proj_hermitian {m n : ℕ} {M : QMatrix m n} :
  QSquare.hermitian (M * M†)
  := by
    simp


/-
 - Entanglement
 -/

lemma entangle_ket00 :
  CNOT * (H ⨂ I₂) * |00⟩ = |Φ+⟩
  := by
    rw [
      Matrix.mul_assoc,
      ← ket0_tens_ket0,
      tens_mul_tens,
      H_mul_ket0,
      I₂,
      Matrix.one_mul,
      ket_plus_eq_ket0_plus_ket1,
      smul_tens,
      add_tens,
      Matrix.mul_smul,
      Matrix.mul_add,
      CNOT_mul_ket0_tens,
      CNOT_mul_ket1_tens,
      X_mul_ket0,
      ket0_tens_ket0,
      ket1_tens_ket1,
    ]

lemma entangle_ket00' :
  CNOT' * (I₂ ⨂ H) * |00⟩ = |Φ+⟩
  := by
    rw [
      Matrix.mul_assoc,
      ← ket0_tens_ket0,
      tens_mul_tens,
      H_mul_ket0,
      I₂,
      Matrix.one_mul,
      ket_plus_eq_ket0_plus_ket1,
      tens_smul,
      tens_add,
      Matrix.mul_smul,
      Matrix.mul_add,
      CNOT'_mul_tens_ket0,
      CNOT'_mul_tens_ket1,
      X_mul_ket0,
      ket0_tens_ket0,
      ket1_tens_ket1,
    ]
