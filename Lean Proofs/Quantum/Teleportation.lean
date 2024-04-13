
import Quantum.Basic

def CNOT₂₁ := I₂ ⨂ I₂ ⨂ |0⟩⟨0| + I₂ ⨂ X ⨂ |1⟩⟨1|
def CNOT₀₁ := |0⟩⟨0| ⨂ I₂ ⨂ I₂ + |1⟩⟨1| ⨂ X ⨂ I₂

noncomputable
def teleport (state : Qubits 3) : Random (Qubits 3) := do
  let first_stage := CNOT₂₁ * (I₂ ⨂ I₂ ⨂ H)
  let second_stage := (H ⨂ I₂ ⨂ I₂) * CNOT₀₁
  let state₁ : Qubits 3 := first_stage * state
  let state₂ : Qubits 3 := second_stage * state
  let ⟨a, state₃⟩ ← Qmeasure₃₀ state₂
  let ⟨b, state₄⟩ ← Qmeasure₃₁ state₃
  
  sorry
  

theorem quantum_teleportation {φ : Qubit} :
  (teleport (φ ⨂ |00⟩)).extract 2 = φ
  := by
    sorry
