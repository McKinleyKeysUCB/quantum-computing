
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
      H_ket0,
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
  let state₀ := φ ⨂ |00⟩
  let state₁ := CNOT₂₁ * (I₂ ⨂ I₂ ⨂ H) * state₀
  have : state₁ = φ ⨂ (1/√2)•(|00⟩ + |11⟩) := by
    unfold_let state₁
    
    sorry
  let state₂ := (H ⨂ I₂ ⨂ I₂) * CNOT₀₁ * state₁
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

def binary_search (arr : List ℕ) (key : ℕ) : Bool :=
  let mid := (arr.length / 2)
  if arr.length = 0 then false
  else if arr.get mid = key then true
  else if key < arr.get mid then binary_search arr.take mid key
  else binary_search arr.drop (mid + 1) key

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
      intro state₀
    
      -- arg 0
      -- intro state₀
      -- intro state₁
      -- intro state₂
    sorry
