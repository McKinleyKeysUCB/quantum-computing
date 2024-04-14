
import Quantum.Basic

def CNOT₂₁ := I₂ ⨂ CNOT'
def CNOT₀₁ := CNOT ⨂ I₂

noncomputable
def Qmeasure₀ := Qmeasure₃₀
noncomputable
def Qmeasure₁ := Qmeasure₃₁

def extract₂ (state : Qubits 3) : Random Qubit := do
  sorry

def entangle :
  CNOT' * (I₂ ⨂ H) * |00⟩ = |Φ+⟩
  := by
    sorry
def entangle' :
  CNOT * (H ⨂ I₂) * |00⟩ = |Φ+⟩
  := by
    rw [
      Matrix.mul_assoc,
      ← ket0_tens_ket0_eq_ket00,
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
      ket0_tens_ket0_eq_ket00,
      ket1_tens_ket1_eq_ket11,
    ]

noncomputable
def teleport (φ : Qubit) : Random Qubit := do
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
      entangle,
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
      ← ket0_tens_ket0_eq_ket00,
      ← ket1_tens_ket1_eq_ket11,
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
      ket0_tens_ket0_eq_ket00,
      ket0_tens_ket1_eq_ket01,
      ket1_tens_ket0_eq_ket10,
      ket1_tens_ket1_eq_ket11,
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
  let ⟨a, state₃⟩ ← Qmeasure₀ state₂
  let ⟨b, state₄⟩ ← Qmeasure₁ state₃
  let mut final ← extract₂ state₄
  if a then
    final := X * final
  if b then
    final := Z * final
  pure final

def mymul (a b : ℕ) := a * b
def myadd (a b : ℕ) := a + b

def blah (n : ℕ) :=
  let a := mymul n 2
  let b := myadd a 1
  myadd a b

-- example {n : ℕ} :
--   blah n = myadd (mymul 4 n) 1
--   := by
--     unfold blah
--     rw?
    
    -- sorry
    -- conv =>
    --   lhs
    --   intro a b
    
    -- show 1 + 1 = 2
    -- sorry

theorem quantum_teleportation {φ : Qubit} :
  ℙ[teleport φ = φ] = 1
  := by
    unfold teleport probability_equals does_equal
    -- simp [Qmeasure₀, I₂, X, Z, CNOT₀₁, CNOT₂₁]
    
    conv =>
      lhs
      arg 0
      -- intro state₀
    
      -- arg 0
      -- intro state₀
      -- intro state₁
      -- intro state₂
    sorry
