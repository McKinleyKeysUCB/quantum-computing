
import Quantum.Basic

lemma prob_Zmeasure_eq_ket0 {φ : Qubit} :
  ℙ[Zmeasure φ ≡ |0⟩] = ‖φ.α‖
  := by
    unfold Zmeasure Qmeasure_qubit
    simp only [probability_congruent, instMonadRandom, Random, zero_proj_phi', one_div,
      Complex.ofReal_inv, one_proj_phi', Random.bind, Random.pure, is_congruent, mul_ite, mul_one,
      mul_zero]
    rw [zero_proj_phi, one_proj_phi]
    simp only [probability_congruent, Random.bind, Random.pure, is_congruent, Matrix.smul_of, Fin.isValue, mul_ite, mul_one, mul_zero]
    nth_rw 2 [if_neg]
    rw [add_zero]
    by_cases hα : φ.α = 0
    · rw [if_neg]
      · simp only [hα, map_zero]
      rw [hα, Complex.normSq_zero, Real.sqrt_zero]
      simp only [Complex.ofReal_zero, inv_zero, Fin.isValue, zero_smul, smul_zero, Matrix.of_zero]
      apply ncong_zero_of_ne_zero
      apply Matrix.ne_zero_of_element_ne_zero 0 0
      rw [ket0]
      simp only [Fin.isValue, Matrix.of_apply, ↓reduceIte, ne_eq, one_ne_zero, not_false_eq_true]
    · rw [if_pos]
      rw [smul_smul]
      apply cong_smul_self
      rw [
        Complex.normSq_mul,
        Complex.normSq_inv,
        Complex.normSq_ofReal,
        Real.mul_self_sqrt (Complex.normSq_nonneg _),
        inv_mul_eq_div,
        ← Complex.normSq_div,
        div_self hα,
      ]
      apply map_one
    rw [smul_smul]
    by_cases hβ : φ.β = 0
    · rw [
        hβ,
        Complex.normSq_zero,
        Real.sqrt_zero,
        Complex.ofReal_zero,
        Complex.inv_zero,
        zero_mul,
        zero_smul,
        Matrix.of_zero,
      ]
      apply ncong_zero_of_ne_zero
      rw [Ne, ← Matrix.ext_iff, not_forall₂]
      use 0
      use 0
      simp only [Fin.isValue, Matrix.of_apply, ↓reduceIte, Matrix.zero_apply, one_ne_zero, not_false_eq_true]
    · apply ncong_smul_of_ncong
      · simp only [map_mul, map_inv₀, Complex.normSq_ofReal, mul_inv_rev, ← sq]
        rw [
          Real.sq_sqrt (Complex.normSq_nonneg _),
          (inv_mul_eq_one₀ _).mpr rfl,
        ]
        rw [Ne, Complex.normSq_eq_zero]
        exact hβ
      · exact ket0_ncong_ket1
