
import Quantum.Basic

/-
 - The proofs in this file are so long that my Lean client times out when verifying them. We have to increase the max heartbeats so that Lean won't time out.
 -/
set_option maxHeartbeats 500000

def CNOT₂₁ := I₂ ⨂ CNOT'
def CNOT₀₁ := CNOT ⨂ I₂

noncomputable
def Qmeasure₀ := Qmeasure₃₀
noncomputable
def Qmeasure₁ := Qmeasure₃₁
noncomputable
def Qmeasure₀_rng := Qmeasure₃₀_rng
noncomputable
def Qmeasure₁_rng := Qmeasure₃₁_rng

def extract₂ (state : Qubits 3) : Qubit :=
  ((⟨00| + ⟨01| + ⟨10| + ⟨11|) ⨂ I₂) * state

def entangle_ket00 :
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
def entangle_ket00' :
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

noncomputable
def teleport_random (φ : Qubit) : Random Qubit := do
  let state₀ := φ ⨂ |00⟩
  let state₁ := CNOT₂₁ * (I₂ ⨂ I₂ ⨂ H) * state₀
  let state₂ := (H ⨂ I₂ ⨂ I₂) * CNOT₀₁ * state₁
  let ⟨a, state₃⟩ ← Qmeasure₀ state₂
  let ⟨b, state₄⟩ ← Qmeasure₁ state₃
  let mut result := extract₂ state₄
  if a then
    result := X * result
  if b then
    result := Z * result
  pure result

structure TeleportRNGResult (φ : Qubit) where
  ψ : Qubit
  hφ : ψ = φ
  rng : RNG

noncomputable
def teleport_rng (φ : Qubit) (hφ : φ.unitary) (rng : RNG) :
  TeleportRNGResult φ :=
  let α := φ.α
  let β := φ.β
  let state₀ := φ ⨂ |00⟩
  let state₁ := CNOT₂₁ * (I₂ ⨂ I₂ ⨂ H) * state₀
  have : state₁ = φ ⨂ |Φ+⟩ := by
    unfold_let state₁ state₀
    unfold CNOT₂₁
    rw [tens_assoc]
    -- Get rid of the cast
    change I₂ ⨂ CNOT' * (I₂ ⨂ (I₂ ⨂ H)) * (φ ⨂ |00⟩) = φ ⨂ |Φ+⟩
    rw [
      tens_mul_tens,
      I₂,
      Matrix.mul_one,
      tens_mul_tens,
      Matrix.one_mul,
      ← I₂,
      entangle_ket00',
    ]
  let state₂ := (H ⨂ I₂ ⨂ I₂) * CNOT₀₁ * state₁
  have : state₂ = (1/2 : ℂ) • (
    |00⟩ ⨂ (α•|0⟩ + β•|1⟩) +
    |01⟩ ⨂ (β•|0⟩ + α•|1⟩) +
    |10⟩ ⨂ (α•|0⟩ - β•|1⟩) +
    |11⟩ ⨂ (-β•|0⟩ + α•|1⟩)
  ) := by
    unfold_let state₂
    rw [
      this,
      ket_Phi_plus,
      tens_smul,
      Matrix.mul_smul,
      decompose_qubit_into_Z_basis (φ := φ),
      tens_add,
    ]
    nth_rw 1 [
      ← ket0_tens_ket0,
      ← ket1_tens_ket1,
    ]
    conv =>
      lhs
      arg 2
      arg 2
      change (cast_matrix (α •|0⟩ + β • |1⟩) ⨂ (|0⟩ ⨂ |0⟩)) + (cast_matrix (α • |0⟩ + β • |1⟩) ⨂ (|1⟩ ⨂ |1⟩))
    rw [
      ← tens_assoc,
      ← tens_assoc,
      add_tens,
    ]
    nth_rw 2 [add_tens]
    unfold CNOT₀₁
    rw [
      tens_mul_tens,
      Matrix.mul_add,
      tens_mul_tens,
      tens_mul_tens,
      Matrix.mul_add,
      -- First term
      smul_tens,
      Matrix.mul_smul,
      Matrix.mul_assoc,
      CNOT_mul_ket0_tens,
      tens_mul_tens,
      H_mul_ket0,
      -- Second term
      smul_tens,
      Matrix.mul_smul,
      Matrix.mul_assoc,
      CNOT_mul_ket1_tens,
      X_mul_ket0,
      tens_mul_tens,
      H_mul_ket1,
    ]
    conv =>
      lhs
      arg 2
      arg 2
      rw [
        -- Third term
        Matrix.mul_add,
        smul_tens,
        Matrix.mul_smul,
        Matrix.mul_assoc,
        CNOT_mul_ket0_tens,
        tens_mul_tens,
        H_mul_ket0,
        -- Fourth term
        smul_tens,
        Matrix.mul_smul,
        Matrix.mul_assoc,
        CNOT_mul_ket1_tens,
        X_mul_ket1,
        tens_mul_tens,
        H_mul_ket1,
      ]
    rw [
      I₂,
      Matrix.one_mul,
      Matrix.one_mul,
      Matrix.one_mul,
      Matrix.one_mul,
      Matrix.one_mul,
      ket_plus_eq_ket0_plus_ket1,
      ket_minus_eq_ket0_minus_ket1,
    ]
    conv =>
      lhs
      rw [smul_add]
      args
      {
        arg 2
        rw [
          smul_tens,
          smul_comm (m := α),
          smul_tens,
          smul_comm (m := β),
          ← smul_add,
        ]
      }
      {
        arg 2
        rw [
          smul_tens,
          smul_comm (m := α),
          smul_tens,
          smul_comm (m := β),
          ← smul_add,
        ]
      }
    rw [
      ← smul_tens,
      smul_smul,
    ]
    nth_rw 3 [← smul_tens]
    rw [
      smul_smul,
      smul_tens,
      smul_tens,
      ← smul_add,
      one_div_sqrt_two_sq,
      add_tens,
      smul_tens,
      ← tens_smul,
      smul_tens,
      ← tens_smul,
    ]
    nth_rw 2 [add_tens]
    rw [
      smul_tens,
      ← tens_smul,
      smul_tens,
      ← tens_smul,
      add_tens,
      add_tens,
      sub_tens,
      sub_tens,
      add_tens,
      add_tens,
      sub_tens,
      sub_tens,
      ket0_tens_ket0,
      ket0_tens_ket1,
      ket1_tens_ket0,
      ket1_tens_ket1,
    ]
    congr 1
    conv =>
      rhs
      rw [
        tens_add,
        tens_add,
        tens_sub,
        tens_add,
        ← neg_one_mul,
        ← smul_smul,
      ]
      arg 2
      rw [tens_smul, neg_one_smul]
    conv =>
      rhs
      rw [← add_assoc, ← sub_eq_add_neg]
    simp only [add_assoc, add_sub_assoc]
    congr 1
    conv =>
      lhs
      rw [add_left_comm, ← add_sub_right_comm, add_sub_assoc]
    conv =>
      rhs
      rw [add_left_comm]
    congr 1
    conv =>
      lhs
      rw [
        ← add_sub_assoc,
        add_comm (|11⟩ ⨂ α • |1⟩),
        ← add_sub_assoc,
        add_left_comm,
        ← add_sub_assoc,
        add_left_comm,
        add_sub_assoc,
        add_sub_assoc,
        add_left_comm,
        add_sub_assoc,
        add_sub_assoc,
        add_sub_assoc,
        add_sub_assoc,
      ]
    congr 2
    conv =>
      rhs
      rw [
        ← add_sub_right_comm,
        ← add_sub_right_comm,
        add_sub_assoc,
        add_sub_assoc,
      ]
  
  
  /-
   - First Measurement
   -/
  
  /-
   - Unfortunately we can't use destructuring syntax like
   -   let ⟨⟨a, state₃⟩, rng⟩ := Qmeasure₀_rng state₂ rng
   - because then Lean won't remember the definitions of `a` and `state₃`.
   - So we have to manually unpack the tuple.
   -/
  let first_measurement := Qmeasure₀_rng state₂ rng
  let a := first_measurement.1.1
  let state₃ := first_measurement.1.2
  let rng₁ := first_measurement.2
  
  let proj0 := (|0⟩⟨0| ⨂ I₂ ⨂ I₂) * state₂
  let proj1 := (|1⟩⟨1| ⨂ I₂ ⨂ I₂) * state₂
  have hproj0 :
    proj0 = (1/2 : ℂ) • (|00⟩ ⨂ (α•|0⟩ + β•|1⟩) + |01⟩ ⨂ (β•|0⟩ + α•|1⟩))
    := by
      unfold_let proj0
      rw [this, Matrix.mul_smul]
      congr 1
      simp only [Matrix.mul_add, tens_mul_tens, I₂, Matrix.one_mul, ← ket0_tens_ket0, ← ket0_tens_ket1, ← ket1_tens_ket0, ← ket1_tens_ket1]
      rw [tens_mul_tens, tens_mul_tens, tens_mul_tens, tens_mul_tens]
      simp only [proj0_mul_ket0, proj0_mul_ket1, Matrix.one_mul, zero_tens, add_zero]
  have hproj1 :
    proj1 = (1/2 : ℂ) • (|10⟩ ⨂ (α•|0⟩ - β•|1⟩) + |11⟩ ⨂ (-β•|0⟩ + α•|1⟩))
    := by
      unfold_let proj1
      rw [this, Matrix.mul_smul]
      congr 1
      simp only [Matrix.mul_add, tens_mul_tens, I₂, Matrix.one_mul, ← ket0_tens_ket0, ← ket0_tens_ket1, ← ket1_tens_ket0, ← ket1_tens_ket1]
      rw [tens_mul_tens, tens_mul_tens, tens_mul_tens, tens_mul_tens]
      simp only [proj1_mul_ket1, proj1_mul_ket0, Matrix.one_mul, zero_tens, zero_add]
  have proj0_half_unitary :
    QMatrix.toReal (proj0† * proj0) = (1/2 : ℝ)
    := by
      rw [hproj0]
      simp only [adjoint_add, adjoint_smul, adjoint_tens, Matrix.mul_smul, Matrix.mul_add, Matrix.smul_mul, ← smul_add, smul_smul, Matrix.add_mul, tens_mul_tens]
      rw [ket00_unitary, ket01_unitary]
      simp only [← ket0_tens_ket1, ← ket0_tens_ket0, adjoint_tens]
      rw [tens_mul_tens, bra1_mul_ket0, tens_mul_tens, bra0_mul_ket1, ket0_unitary, ket1_unitary]
      simp only [tens_zero, zero_tens, smul_zero, zero_add, add_zero]
      simp only [one_tens, QMatrix.toReal, Matrix.smul_apply, Matrix.add_apply]
      simp only [QMatrix.cast_apply, Fin.cast_zero, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one]
      rw [qubit_unitary', mul_comm, mul_comm (star φ.β)] at hφ
      change α * star α + β * star β = 1 at hφ
      rw [hφ, add_comm (β * star β), hφ]
      norm_num
  have proj1_half_unitary :
    QMatrix.toReal (proj1† * proj1) = (1/2 : ℝ)
    := by
      rw [hproj1]
      simp only [adjoint_add, adjoint_sub, adjoint_smul, adjoint_tens, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub, Matrix.smul_mul, ← smul_add, smul_smul, Matrix.add_mul, Matrix.sub_mul, tens_mul_tens]
      rw [ket10_unitary, ket11_unitary]
      simp only [← ket1_tens_ket1, ← ket1_tens_ket0, adjoint_tens]
      rw [tens_mul_tens, bra1_mul_ket0, tens_mul_tens, bra0_mul_ket1, ket0_unitary, ket1_unitary]
      simp only [tens_zero, zero_tens, smul_zero, zero_add, add_zero, sub_zero, zero_sub]
      simp only [one_tens, QMatrix.toReal, Matrix.smul_apply, Matrix.add_apply]
      simp only [QMatrix.cast_apply, Fin.cast_zero, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one, mul_neg, sub_neg_eq_add, star_neg, neg_mul, neg_neg]
      rw [qubit_unitary', mul_comm, mul_comm (star φ.β)] at hφ
      change α * star α + β * star β = 1 at hφ
      rw [hφ, add_comm (β * star β), hφ]
      norm_num
  have ha : a = (rng.flip (1/2)).1 := by
    unfold_let a first_measurement
    unfold Qmeasure₀_rng Qmeasure₃₀_rng Qmeasure_single_qubit_rng
    simp only [proj0, proj0_half_unitary, proj1, proj1_half_unitary]
    simp only [apply_ite Prod.fst, apply_ite Prod.snd]
    rw [if_true_false]
  have hstate₃ : state₃ =
    if a then
      (1/√2) • (|10⟩ ⨂ (α•|0⟩ - β•|1⟩) + |11⟩ ⨂ (-β•|0⟩ + α•|1⟩))
    else
      (1/√2) • (|00⟩ ⨂ (α•|0⟩ + β•|1⟩) + |01⟩ ⨂ (β•|0⟩ + α•|1⟩))
  := by
    unfold_let state₃
    unfold_let first_measurement at a ⊢
    unfold Qmeasure₀_rng Qmeasure₃₀_rng Qmeasure_single_qubit_rng
    simp only [proj0, proj0_half_unitary, proj1, proj1_half_unitary]
    simp only [apply_ite Prod.fst, apply_ite Prod.snd]
    rw [← ha]
    congr 1
    · unfold_let proj1 at hproj1
      rw [hproj1, smul_smul]
      congr 1
      exact one_div_sqrt_half_mul_half
    · unfold_let proj0 at hproj0
      rw [hproj0, smul_smul]
      congr 1
      exact one_div_sqrt_half_mul_half
  
  
  /-
   - Second Measurement
   -/
  
  let second_measurement := Qmeasure₁_rng state₃ rng₁
  let b := second_measurement.1.1
  let state₄ := second_measurement.1.2
  let rng₂ := second_measurement.2
  
  let proj0 := (I₂ ⨂ |0⟩⟨0| ⨂ I₂) * state₃
  let proj1 := (I₂ ⨂ |1⟩⟨1| ⨂ I₂) * state₃
  have hproj0 :
    proj0 =
      if a then
        (1/√2) • (|10⟩ ⨂ (α•|0⟩ - β•|1⟩))
      else
        (1/√2) • (|00⟩ ⨂ (α•|0⟩ + β•|1⟩))
    := by
      simp only [proj0, hstate₃, apply_ite]
      by_cases ha : a <;> {
        simp only [if_pos, if_neg, ha, if_false, Matrix.mul_smul]
        congr 1
        simp only [tens_mul_tens, Matrix.mul_add, ← ket0_tens_ket0, ← ket0_tens_ket1, ← ket1_tens_ket0, ← ket1_tens_ket1, I₂, Matrix.one_mul]
        rw [tens_mul_tens, tens_mul_tens, proj0_mul_ket0, proj0_mul_ket1]
        simp only [tens_zero, zero_tens, one_tens, add_zero, Matrix.one_mul]
      }
  have hproj1 :
    proj1 =
      if a then
        (1/√2) • (|11⟩ ⨂ (-β•|0⟩ + α•|1⟩))
      else
        (1/√2) • (|01⟩ ⨂ (β•|0⟩ + α•|1⟩))
    := by
      simp only [proj1, hstate₃, apply_ite]
      by_cases ha : a <;> {
        simp only [if_pos, if_neg, ha, if_false, Matrix.mul_smul]
        congr 1
        simp only [tens_mul_tens, Matrix.mul_add, ← ket0_tens_ket0, ← ket0_tens_ket1, ← ket1_tens_ket0, ← ket1_tens_ket1, I₂, Matrix.one_mul]
        rw [tens_mul_tens, tens_mul_tens, proj1_mul_ket0, proj1_mul_ket1]
        simp only [tens_zero, zero_tens, one_tens, zero_add, Matrix.one_mul]
      }
  have proj0_half_unitary :
    QMatrix.toReal (proj0† * proj0) = (1/2 : ℝ)
    := by
      rw [hproj0]
      rw [qubit_unitary', mul_comm, mul_comm (star φ.β)] at hφ
      change α * star α + β * star β = 1 at hφ
      by_cases ha : a <;> {
        simp only [if_pos, if_neg, ha, if_false]
        simp only [adjoint_add, adjoint_smul, adjoint_tens, Matrix.mul_smul, Matrix.mul_add, Matrix.smul_mul, ← smul_add, smul_smul, Matrix.add_mul, tens_mul_tens]
        try rw [ket10_unitary, adjoint_sub]
        try rw [ket00_unitary]
        simp only [Matrix.sub_mul, Matrix.mul_sub, bra1_mul_ket0, bra0_mul_ket1, adjoint_smul, Matrix.mul_smul, Matrix.smul_mul, smul_zero]
        rw [ket0_unitary, ket1_unitary]
        simp only [sub_zero, zero_sub, add_zero, zero_add]
        simp only [one_tens, QMatrix.toReal, Matrix.smul_apply, Matrix.add_apply, smul_neg, sub_eq_add_neg, neg_neg]
        simp only [QMatrix.cast_apply, Fin.cast_zero, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one, hφ]
        norm_num
        exact sqrt_two_div_two_sq
      }
  have proj1_half_unitary :
    QMatrix.toReal (proj1† * proj1) = (1/2 : ℝ)
    := by
      rw [hproj1]
      rw [qubit_unitary', mul_comm, mul_comm (star φ.β)] at hφ
      change α * star α + β * star β = 1 at hφ
      by_cases ha : a <;> {
        simp only [if_pos, if_neg, ha, if_false]
        simp only [adjoint_add, adjoint_smul, adjoint_tens, Matrix.mul_smul, Matrix.mul_add, Matrix.smul_mul, ← smul_add, smul_smul, Matrix.add_mul, tens_mul_tens]
        try rw [ket01_unitary]
        try rw [ket11_unitary]
        simp only [Matrix.sub_mul, Matrix.mul_sub, bra1_mul_ket0, bra0_mul_ket1, adjoint_smul, Matrix.mul_smul, Matrix.smul_mul, smul_zero]
        rw [ket0_unitary, ket1_unitary]
        simp only [sub_zero, zero_sub, add_zero, zero_add]
        simp only [one_tens, QMatrix.toReal, Matrix.smul_apply, Matrix.add_apply, smul_neg, sub_eq_add_neg, neg_neg]
        simp only [QMatrix.cast_apply, Fin.cast_zero, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, if_true, smul_eq_mul, mul_one, neg_mul, mul_neg, star_neg, neg_neg]
        rw [add_comm, hφ]
        norm_num
        exact sqrt_two_div_two_sq
      }
  have hb : b = (rng₁.flip (1/2)).1 := by
    unfold_let b second_measurement
    unfold Qmeasure₁_rng Qmeasure₃₁_rng Qmeasure_single_qubit_rng
    simp only [proj0, proj0_half_unitary, proj1, proj1_half_unitary]
    simp only [apply_ite Prod.fst, apply_ite Prod.snd]
    rw [if_true_false]
  have hstate₄ : state₄ =
    if a then
      if b then
        |11⟩ ⨂ (-β•|0⟩ + α•|1⟩)
      else
        |10⟩ ⨂ (α•|0⟩ - β•|1⟩)
    else
      if b then
        |01⟩ ⨂ (β•|0⟩ + α•|1⟩)
      else
        |00⟩ ⨂ (α•|0⟩ + β•|1⟩)
  := by
    unfold_let state₄
    unfold_let second_measurement at b ⊢
    unfold Qmeasure₁_rng Qmeasure₃₁_rng Qmeasure_single_qubit_rng
    simp only [proj0, proj0_half_unitary, proj1, proj1_half_unitary]
    simp only [apply_ite Prod.fst, apply_ite Prod.snd]
    rw [← hb]
    unfold_let proj0 at hproj0
    unfold_let proj1 at hproj1
    by_cases ha : a <;> {
      simp only [if_pos, if_neg, ha, if_false]
      congr 1 <;> simp only [hproj0, hproj1, if_pos, if_neg, ha, if_false, smul_smul, one_div_sqrt_half_mul_one_div_sqrt_two, one_smul]
    }
  
  
  /-
   - Extraction
   -/
  
  let result₀ := extract₂ state₄
  
  have hresult₀ : result₀ =
    if a then
      if b then
        -β•|0⟩ + α•|1⟩
      else
        α•|0⟩ - β•|1⟩
    else
      if b then
        β•|0⟩ + α•|1⟩
      else
        α•|0⟩ + β•|1⟩
  := by
    unfold_let result₀
    rw [hstate₄, extract₂, bra00, bra01, bra10, bra11, ← ket0_tens_ket0, ← ket0_tens_ket1, ← ket1_tens_ket0, ← ket1_tens_ket1]
    simp only [adjoint_tens]
    by_cases ha : a <;> by_cases hb : b <;> {
      simp only [if_pos, if_neg, ha, hb, if_false ]
      rw [tens_mul_tens]
      simp only [Matrix.add_mul]
      rw [tens_mul_tens, tens_mul_tens, tens_mul_tens, tens_mul_tens]
      try rw [ket0_unitary]
      try rw [ket1_unitary]
      simp only [bra0_mul_ket1, bra1_mul_ket0, tens_zero, zero_tens, add_zero, zero_add, I₂, Matrix.one_mul]
      rw [tens_assoc, one_tens, one_tens]
      rfl
    }
  
  
  /-
   - X Gate
   -/
  
  let result₁ := if b then X * result₀ else result₀
  
  have hresult₁ : result₁ =
    if a then
      α•|0⟩ + (-β)•|1⟩
    else
      α•|0⟩ + β•|1⟩
  := by
    unfold_let result₁
    rw [hresult₀]
    by_cases hb : b <;> {
      simp only [if_pos, if_neg, hb, if_false]
      try rw [apply_ite (fun q : Qubit => X * q)]
      congr 1 <;> {
        try rw [X_mul_qubit']
        -- All but one of the goals should be closed by now
        try rw [neg_smul, ← sub_eq_add_neg]
      }
    }
  
  
  /-
   - Z Gate
   -/
  
  let result₂ := if a then Z * result₁ else result₁
  
  have hresult₂ : result₂ = α•|0⟩ + β•|1⟩
  := by
    unfold_let result₂
    rw [hresult₁]
    by_cases ha : a
    · simp only [if_pos ha]
      rw [Z_mul_qubit', sub_eq_add_neg, ← neg_smul, neg_neg]
    · simp only [if_neg ha]
      
  
  let ψ := result₂
  have hψ : ψ = φ := by
    unfold_let ψ
    rw [hresult₂]
    unfold_let α β
    rw [← decompose_qubit_into_Z_basis φ]
  
  ⟨ψ, hψ, rng₂⟩
