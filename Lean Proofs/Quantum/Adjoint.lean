
import Quantum.Definitions

@[simp]
lemma double_adjoint {m n : ℕ} {M : QMatrix m n} :
  M†† = M
  := by
    apply Matrix.ext
    intro i j
    simp

@[simp]
lemma adjoint_mul {a b c : ℕ} {A : QMatrix a b} {B : QMatrix b c} :
  (A * B)† = B† * A†
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply']
    unfold QMatrix.adjoint
    rw [Matrix.mul_apply', ← Matrix.star_dotProduct_star]
    rfl

@[simp]
lemma adjoint_smul {m n : ℕ} {c : ℂ} {M : QMatrix m n} :
  (c • M)† = star c • M†
  := by
    apply Matrix.ext
    simp only [QMatrix.adjoint, Matrix.smul_apply, smul_eq_mul, star_mul', Complex.star_def,
      implies_true]

@[simp]
lemma adjoint_add {m n : ℕ} {A B : QMatrix m n} :
  (A + B)† = A† + B†
  := by
    apply Matrix.ext
    simp only [QMatrix.adjoint, Matrix.add_apply, star_add, Complex.star_def, implies_true]

@[simp]
lemma adjoint_sub {m n : ℕ} {A B : QMatrix m n} :
  (A - B)† = A† - B†
  := by
    apply Matrix.ext
    simp only [QMatrix.adjoint, Matrix.sub_apply, star_sub, Complex.star_def, implies_true]

@[simp]
lemma adjoint_tens {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} :
  (A ⨂ B)† = A† ⨂ B†
  := by
    apply Matrix.ext
    simp only [QMatrix.adjoint, tens, Matrix.of_apply, star_mul', Complex.star_def, implies_true]
