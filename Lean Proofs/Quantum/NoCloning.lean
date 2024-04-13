
import Quantum.Basic

theorem no_cloning :
  ¬∃ (U : QMatrix 4 4), ∀ (φ : Qubit), |φ| = 1 → U * (φ ⨂ |0⟩) = φ ⨂ φ
  := by
    apply by_contradiction
    rw [not_not]
    intro h
    rcases h with ⟨U, h⟩
    let first_expansion (φ : Qubit) : Qubits 2 :=
      fun i j =>
        if i = 0 then
          φ.α^2
        else if i = 1 then
          φ.α * φ.β
        else if i = 2 then
          φ.β * φ.α
        else
          φ.β^2
    let second_expansion (φ : Qubit) : Qubits 2 :=
      fun i _ =>
        if i = 0 then
          φ.α
        else if i = 1 then
          0
        else if i = 2 then
          0
        else
          φ.β
    have eq_first_expansion (φ : Qubit) (hφ : |φ| = 1) :
      U * (φ ⨂ |0⟩) = first_expansion φ
      := by
        rw [h φ hφ, tens_self]
        rfl
    have eq_second_expansion (φ : Qubit) :
      U * (φ ⨂ |0⟩) = second_expansion φ
      := by
        nth_rw 1 [decompose_qubit_into_Z_basis φ]
        rw [
          add_tens,
          Matrix.mul_add,
          mul_tens,
          Matrix.mul_smul,
          h _ norm_ket0_eq_1,
          mul_tens,
          Matrix.mul_smul,
          h _ norm_ket1_eq_1,
          ket0_tens_ket0_eq_ket00,
          ket1_tens_ket1_eq_ket11,
        ]
        apply Matrix.ext
        apply Fin.bash4 <;> simp [ket00, ket11, second_expansion]
    have first_eq_second (φ : Qubit) (hφ : |φ| = 1) :
      first_expansion φ = second_expansion φ
      := calc
        _ = U * (φ ⨂ |0⟩)         := (eq_first_expansion φ hφ).symm
        _ = second_expansion φ    := eq_second_expansion φ
    specialize first_eq_second |+⟩ norm_ket_plus_eq_1
    unfold_let first_expansion second_expansion at first_eq_second
    apply Matrix.ext_iff.mpr at first_eq_second
    specialize first_eq_second 1 0
    simp [ket_plus, Qubit.α, Qubit.β] at first_eq_second
