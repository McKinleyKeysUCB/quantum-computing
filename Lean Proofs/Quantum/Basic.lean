
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Quantum.Definitions
import Quantum.Lemmas

open BigOperators

lemma one_div_sqrt_two_sq :
  (1/√2) * (1/√2) = 1/2
  := by
    sorry

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

lemma qubit_unitary {φ : Qubit} :
  φ.unitary ↔ Complex.normSq φ.α + Complex.normSq φ.β = 1
  := by
    sorry

lemma qubit_unitary' {φ : Qubit} :
  φ.unitary ↔ star φ.α * φ.α + star φ.β * φ.β = 1
  := by
    sorry

lemma ket0_unitary :
  |0⟩.unitary
  := by
    rw [qubit_unitary, Qubit.α, Qubit.β, ket0]
    simp
lemma ket1_unitary :
  |1⟩.unitary
  := by
    rw [qubit_unitary, Qubit.α, Qubit.β, ket1]
    simp
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

@[simp]
lemma tens_add {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  C ⨂ (A + B) = C ⨂ A + C ⨂ B
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, tens, tens, tens]
    simp
    rw [mul_add]
@[simp]
lemma add_tens {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  (A + B) ⨂ C = A ⨂ C + B ⨂ C
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.add_apply, tens, tens, tens]
    simp
    rw [add_mul]
@[simp]
lemma tens_sub {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  C ⨂ (A - B) = C ⨂ A - C ⨂ B
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.sub_apply, tens, tens, tens]
    simp
    rw [mul_sub]
@[simp]
lemma sub_tens {m₁ n₁ m₂ n₂ : ℕ} {A : QMatrix m₁ n₁} {B : QMatrix m₁ n₁} {C : QMatrix m₂ n₂} :
  (A - B) ⨂ C = A ⨂ C - B ⨂ C
  := by
    apply Matrix.ext
    intro i j
    rw [Matrix.sub_apply, tens, tens, tens]
    simp
    rw [sub_mul]

@[simp]
lemma smul_tens {m₁ n₁ m₂ n₂ : ℕ} {s : ℂ} {A : QMatrix m₁ n₁} {B : QMatrix m₂ n₂} :
  (s • A) ⨂ B = s • (A ⨂ B)
  := by
    simp [tens, Pi.smul_def]
    apply funext₂
    intro i j
    ring
@[simp]
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

lemma divNat_div_mod_inv {a b : ℕ} {q : Fin a} {r : Fin b} :
  (div_mod_inv q r).divNat = q
  := by
    by_cases hb : b = 0
    · rw [hb] at r
      exfalso
      exact false_of_mem_Fin_zero r
    · apply Nat.zero_lt_of_ne_zero at hb
      rw [div_mod_inv, Fin.divNat]
      apply Fin.ext
      dsimp
      rw [
        Nat.div_eq_sub_mod_div,
        Nat.mul_add_mod,
        Nat.mod_eq_of_lt r.isLt,
        add_tsub_cancel_right,
        Nat.mul_div_cancel_left _ hb,
      ]

lemma modNat_div_mod_inv {a b : ℕ} {q : Fin a} {r : Fin b} :
  (div_mod_inv q r).modNat = r
  := by
    rw [div_mod_inv, Fin.modNat]
    apply Fin.ext
    dsimp
    rw [
      Nat.add_mod,
      Nat.mul_mod_right,
      zero_add,
      Nat.mod_mod,
      Nat.mod_eq_of_lt r.isLt,
    ]

lemma eq_of_div_eq_div_and_mod_eq_mod {a b : ℕ} {x y : Fin (a * b)} (hdiv : x.divNat = y.divNat) (hmod : x.modNat = y.modNat) :
  x = y
  := by
    simp [Fin.divNat] at hdiv
    simp [Fin.modNat] at hmod
    apply Fin.ext
    rw [← Nat.div_add_mod ↑x b, ← Nat.div_add_mod ↑y b, hdiv, hmod]

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
        use div_mod_inv x.1 x.2
        constructor
        · simp only [mem_univ]
        rw [divNat_div_mod_inv, modNat_div_mod_inv]
      · intro hx
        rw [mem_image] at hx
        rcases hx with ⟨y, ⟨_, hxy⟩⟩
        rw [← hxy]
        simp only [mem_univ]
    simp only [this]
    rw [sum_image]
    intro x _ y _ h
    simp [g] at h
    rcases h with ⟨left, right⟩
    exact eq_of_div_eq_div_and_mod_eq_mod left right

-- theorem tens_ext {M : QMatrix (m*p) (n*q)} (h : ∀ (r : Fin m) (s : Fin n) (v : Fin p) (w : Fin q), A r s * B v w = M (div_mod_inv r v) (div_mod_inv s w)) :
--   -- A ⨂ B = M
--   M = A ⨂ B
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

lemma cast_apply_eq_apply {α α' β β' γ : Type} {f : α → β → γ} {a : α} {b : β} {a' : α'} {b' : β'} (ha : HEq a' a) (hb : HEq b' b) {h : (α → β → γ) = (α' → β' → γ)} :
  cast h f a' b' = f a b
  := by
    cases ha
    cases hb
    rfl

lemma QMatrix.cast_apply {m₁ n₁ m₂ n₂ : ℕ} {i : Fin m₂} {j : Fin n₂} {h : QMatrix m₁ n₁ = QMatrix m₂ n₂} {M : QMatrix m₁ n₁} (hm : m₁ = m₂) (hn : n₁ = n₂) :
  (cast h M) i j = M (Fin.cast hm.symm i) (Fin.cast hn.symm j)
  := by
    rw [cast_apply_eq_apply]
    · exact (Fin.heq_ext_iff (id hm.symm)).mpr rfl
    · exact (Fin.heq_ext_iff (id hn.symm)).mpr rfl

lemma Fin.div_div_eq_div_cast {a b c : ℕ} {i : Fin (a * b * c)} {h : (a * b * c) = (a * (b * c))} :
  Fin.divNat (Fin.divNat i) = Fin.divNat (Fin.cast h i)
  := by
    unfold divNat
    simp
    rw [Nat.div_div_eq_div_mul, mul_comm c b]

lemma Fin.mod_div_eq_div_mod_cast {a b c : ℕ} {i : Fin (a * b * c)} {h : (a * b * c) = (a * (b * c))} :
  Fin.modNat (Fin.divNat i) = Fin.divNat (Fin.modNat (Fin.cast h i))
  := by
    unfold divNat modNat
    simp
    rw [Nat.mod_mul_left_div_self]

lemma Fin.mod_eq_mod_mod_cast {a b c : ℕ} {i : Fin (a * b * c)} {h : (a * b * c) = (a * (b * c))} :
  Fin.modNat i = Fin.modNat (Fin.modNat (Fin.cast h i))
  := by
    unfold modNat
    simp

@[simp]
lemma tens_assoc {a b c d e f : ℕ} {A : QMatrix a b} {B : QMatrix c d} {C : QMatrix e f} :
  (A ⨂ B) ⨂ C = cast_matrix (A ⨂ (B ⨂ C))
  := by
    apply Matrix.ext
    intro i j
    simp
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
    simp
    rfl
@[simp]
lemma zero_tens {m₁ n₁ m₂ n₂ : ℕ} {M : QMatrix m₂ n₂} :
  (0 : QMatrix m₁ n₁) ⨂ M = 0
  := by
    simp
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
      simp
    have hj : Fin.modNat j = 0 := by
      apply Fin.ext
      simp
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
    simp
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
      simp
    have hj : Fin.divNat j = 0 := by
      apply Fin.ext
      simp
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
 - Adjoints
 -/

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

@[simp]
lemma proj_hermitian {m n : ℕ} {M : QMatrix m n} :
  QSquare.hermitian (M * M†)
  := by
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
 - Square Roots
 -/

lemma one_div_sqrt_half_mul_half :
  ↑(1 / Real.sqrt (1 / 2)) * (1 / 2) = 1 / Complex.ofReal (Real.sqrt 2)
  := by
    rw [Complex.ofReal_eq_coe, Complex.div_ofReal, Complex.ofReal_mul']
    simp
    rw [← division_def, Real.sqrt_div_self]

lemma one_div_sqrt_half_mul_one_div_sqrt_two :
  ↑(1 / Real.sqrt (1 / 2)) * (1 / Complex.ofReal (Real.sqrt 2)) = 1
  := by
    simp only [one_div, Real.sqrt_inv, div_inv_eq_mul, one_mul, Complex.ofReal_eq_coe, ne_eq,
      Complex.ofReal_eq_zero, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_inv_cancel]

lemma sqrt_two_div_two_sq :
  Real.sqrt 2 / 2 * (Real.sqrt 2 / 2) = 1 / 2
  := by
    simp only [Real.sqrt_div_self', one_div, ← mul_inv, Nat.ofNat_nonneg, Real.mul_self_sqrt]
