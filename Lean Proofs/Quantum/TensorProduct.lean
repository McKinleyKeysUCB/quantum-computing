
import Quantum.Definitions

open BigOperators

@[simp]
lemma tens_add {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  C ⨂ (A + B) = C ⨂ A + C ⨂ B
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, tens, tens, tens]
    simp only [Matrix.add_apply, Matrix.of_apply]
    rw [mul_add]

@[simp]
lemma add_tens {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  (A + B) ⨂ C = A ⨂ C + B ⨂ C
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, tens, tens, tens]
    simp only [Matrix.add_apply, Matrix.of_apply]
    rw [add_mul]

@[simp]
lemma tens_sub {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  C ⨂ (A - B) = C ⨂ A - C ⨂ B
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.sub_apply, tens, tens, tens]
    simp only [Matrix.sub_apply, Matrix.of_apply]
    rw [mul_sub]

@[simp]
lemma sub_tens {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  (A - B) ⨂ C = A ⨂ C - B ⨂ C
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.sub_apply, tens, tens, tens]
    simp only [Matrix.sub_apply, Matrix.of_apply]
    rw [sub_mul]

@[simp]
lemma smul_tens {m₁ n₁ m₂ n₂ : ℕ} {s : ℂ} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} :
  (s • A) ⨂ B = s • (A ⨂ B)
  := by
    simp only [tens, Matrix.smul_apply, smul_eq_mul, Matrix.smul_of, Pi.smul_def, EmbeddingLike.apply_eq_iff_eq]
    apply funext₂
    intro i j
    ring

@[simp]
lemma tens_smul {m₁ n₁ m₂ n₂ : ℕ} {s : ℂ} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} :
  A ⨂ (s • B) = s • (A ⨂ B)
  := by
    simp only [tens, Matrix.smul_apply, smul_eq_mul, Matrix.smul_of, Pi.smul_def, EmbeddingLike.apply_eq_iff_eq]
    apply funext₂
    intro i j
    ring

-- Helper lemma for `tens_mul_tens`.
lemma Finset.sum_Fin_mul {α : Type} [AddCommMonoid α] {a b : ℕ} (f : Fin a → Fin b → α) :
  (∑ x : Fin (a * b), f (Fin.divNat x) (Fin.modNat x)) = (∑ x : Fin a, ∑ y : Fin b, f x y)
  := by
    rw [← Fintype.sum_prod_type']
    let g (x : Fin (a * b)) : Fin a × Fin b := ⟨Fin.divNat x, Fin.modNat x⟩
    let AB : Finset (Fin (a * b)) := univ
    have : univ (α := Fin a × Fin b) = image g AB := by
      unfold_let g AB
      rw [ext_iff]
      intro x
      constructor
      · intro
        rw [mem_image]
        use Fin.div_mod_inv x.1 x.2
        constructor
        · simp only [mem_univ]
        rw [Fin.divNat_div_mod_inv, Fin.modNat_div_mod_inv]
      · intro hx
        rw [mem_image] at hx
        rcases hx with ⟨y, ⟨_, hxy⟩⟩
        rw [← hxy]
        simp only [mem_univ]
    simp only [this]
    rw [sum_image]
    intro x _ y _ h
    simp only [Prod.mk.injEq, g] at h
    rcases h with ⟨left, right⟩
    exact Fin.eq_of_div_eq_div_and_mod_eq_mod left right

-- TODO: Implement
-- theorem tens_ext {M : QMatrix (m*p) (n*q)} (h : ∀ (r : Fin m) (s : Fin n) (v : Fin p) (w : Fin q), A r s * B v w = M (div_mod_inv r v) (div_mod_inv s w)) :
--   A ⨂ B = M
--   := by
--     sorry

lemma tens_mul_tens {a₁ b₁ c₁ a₂ b₂ c₂ : ℕ} {A : QMatrix a₁ b₁} {B : QMatrix a₂ b₂} {C : QMatrix b₁ c₁} {D : QMatrix b₂ c₂} :
  (A ⨂ B) * (C ⨂ D) = (A * C) ⨂ (B * D)
  := by
    unfold tens
    apply Matrix.ext
    intro i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul_sum, ← mul_assoc]
    let f (x : Fin b₁) (y : Fin b₂) := (A i.divNat x) * (B i.modNat y) * (C x j.divNat) * (D y j.modNat)
    change ∑ x : Fin (b₁ * b₂), f x.divNat x.modNat = ∑ x : Fin b₁, ∑ y : Fin b₂, (A i.divNat x) * (C x j.divNat) * (B i.modNat y) * (D y j.modNat)
    rw [Finset.sum_Fin_mul]
    unfold_let f
    simp only [mul_left_comm, mul_right_comm, mul_assoc]

/-
 - Use this notation to help Lean understand that two matrix types are the same. For example, Lean doesn't automatically understand that `QMatrix (2^3) (2^3)` and `QMatrix 8 8` are the same type. This example produces an error:
 - example (A : QMatrix 8 8) (B : QMatrix (2^3) (2^3)) :
     A = B
     := by
       sorry
 - To fix this error, we can write `A = cast_matrix B` instead.
 -/
notation "cast_matrix" M => cast (by ring_nf) M

lemma QMatrix.cast_apply {m₁ n₁ m₂ n₂ : ℕ} {i : Fin m₂} {j : Fin n₂} {h : QMatrix m₁ n₁ = QMatrix m₂ n₂} {M : QMatrix m₁ n₁} (hm : m₁ = m₂) (hn : n₁ = n₂) :
  (cast h M) i j = M (Fin.cast hm.symm i) (Fin.cast hn.symm j)
  := by
    rw [cast_apply_eq_apply] <;> {
      rw [Fin.heq_ext_iff]
      rfl
      symm
      assumption
    }

@[simp]
lemma tens_assoc {a b c d e f : ℕ} {A : QMatrix a b} {B : QMatrix c d} {C : QMatrix e f} :
  (A ⨂ B) ⨂ C = cast_matrix (A ⨂ (B ⨂ C))
  := by
    apply Matrix.ext
    intro i j
    simp only [tens, Matrix.of_apply]
    rw [QMatrix.cast_apply (by ring) (by ring), Matrix.of_apply, mul_assoc]
    congr 1
    · congr 1 <;> exact Fin.div_div_eq_div_cast
    congr 1
    · congr 1 <;> exact Fin.mod_div_eq_div_mod_cast
    congr 1 <;> exact Fin.mod_eq_mod_mod_cast

@[simp]
lemma tens_zero {m₁ n₁ m₂ n₂ : ℕ} {M : QMatrix m₁ n₁} :
  M ⨂ (0 : QMatrix m₂ n₂) = 0
  := by
    simp only [tens, Matrix.zero_apply, mul_zero]
    rfl

@[simp]
lemma zero_tens {m₁ n₁ m₂ n₂ : ℕ} {M : QMatrix m₂ n₂} :
  (0 : QMatrix m₁ n₁) ⨂ M = 0
  := by
    simp only [tens, Matrix.zero_apply, zero_mul]
    rfl

@[simp]
lemma tens_one {m n : ℕ} {M : QMatrix m n} :
  M ⨂ (1 : QSquare 1) = cast_matrix M
  := by
    apply Matrix.ext
    intro i j
    simp only [tens, Matrix.of_apply]
    have hi : Fin.modNat i = 0 := by
      apply Fin.ext
      simp only [Fin.coe_fin_one, Fin.isValue]
    have hj : Fin.modNat j = 0 := by
      apply Fin.ext
      simp only [Fin.coe_fin_one, Fin.isValue]
    rw [
      hi,
      hj,
      Matrix.one_apply,
      if_pos rfl,
      mul_one,
      QMatrix.cast_apply (mul_one _).symm (mul_one _).symm,
      Fin.divNat,
      Fin.divNat,
    ]
    simp only [Nat.div_one]
    congr

@[simp]
lemma one_tens {m n : ℕ} {M : QMatrix m n} :
  (1 : QSquare 1) ⨂ M = cast_matrix M
  := by
    apply Matrix.ext
    intro i j
    simp only [tens, Matrix.of_apply]
    have hi : Fin.divNat i = 0 := by
      apply Fin.ext
      simp only [Fin.coe_fin_one, Fin.isValue]
    have hj : Fin.divNat j = 0 := by
      apply Fin.ext
      simp only [Fin.coe_fin_one, Fin.isValue]
    rw [
      hi,
      hj,
      Matrix.one_apply,
      if_pos rfl,
      one_mul,
      QMatrix.cast_apply (one_mul _).symm (one_mul _).symm,
    ]
    unfold Fin.modNat
    rcases i with ⟨i, hi'⟩
    rw [one_mul m] at hi'
    rcases j with ⟨j, hj'⟩
    rw [one_mul n] at hj'
    congr <;> {
      apply Nat.mod_eq_of_lt
      dsimp only
      assumption
    }

lemma transpose_tens {m₁ n₁ m₂ n₂} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} :
  (A ⨂ B)ᵀ = Aᵀ ⨂ Bᵀ
  := by
    apply Matrix.ext
    intros
    simp only [tens, Matrix.transpose_apply, Matrix.of_apply]
