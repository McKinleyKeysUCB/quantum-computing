
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Quantum.Probability

open ComplexConjugate BigOperators Nat

notation "√" a => Complex.ofReal (Real.sqrt a)

@[reducible]
def QMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) ℂ
@[reducible]
def QSquare (n : ℕ) := QMatrix n n
@[reducible]
def QVector (n : ℕ) := QMatrix n 1

@[reducible]
def Qubit := QVector 2
@[reducible]
def Qubits (n : ℕ) := QVector (2 ^ n)

@[reducible]
def Qubit.α (φ : Qubit) := φ 0 0
@[reducible]
def Qubit.β (φ : Qubit) := φ 1 0

@[simp]
def QMatrix.adjoint {m n : ℕ} (M : QMatrix m n) : QMatrix n m :=
  fun i j =>
    star (M j i)

notation M "†" => QMatrix.adjoint M

notation M "ᵀ" => Matrix.transpose M

noncomputable
def norm (φ : Qubit) :=
  (Complex.normSq φ.α + Complex.normSq φ.β).sqrt

notation:70 "|" φ "|" => norm φ
notation:70 "‖" φ "‖" => Complex.normSq φ

@[reducible]
def ket0 : Qubit :=
  Matrix.of (fun i _ => if i = 0 then 1 else 0)

@[reducible]
def bra0 := ket0†

@[reducible]
def ket1 : Qubit :=
  Matrix.of (fun i _ => if i = 1 then 1 else 0)

@[reducible]
def bra1 := ket1†

noncomputable
def ket_plus : Qubit :=
  (1/√2) • Matrix.of (fun _ _ => 1)

noncomputable
def ket_minus : Qubit :=
  (1/√2) • Matrix.of (fun i _ => if i = 0 then 1 else -1)

def ket00 : Qubits 2 :=
  fun i _ => if i = 0 then 1 else 0
def ket01 : Qubits 2 :=
  fun i _ => if i = 1 then 1 else 0
def ket10 : Qubits 2 :=
  fun i _ => if i = 2 then 1 else 0
def ket11 : Qubits 2 :=
  fun i _ => if i = 3 then 1 else 0

@[reducible]
def bra00 := ket00†
@[reducible]
def bra01 := ket01†
@[reducible]
def bra10 := ket10†
@[reducible]
def bra11 := ket11†

notation "|0⟩" => ket0
notation "|1⟩" => ket1
notation "|00⟩" => ket00
notation "|01⟩" => ket01
notation "|10⟩" => ket10
notation "|11⟩" => ket11
notation "|+⟩" => ket_plus
notation "|-⟩" => ket_minus
notation "⟨0|" => bra0
notation "⟨1|" => bra1
notation "⟨00|" => bra00
notation "⟨01|" => bra01
notation "⟨10|" => bra10
notation "⟨11|" => bra11


/-
 - Bell States
 -/

@[reducible]
noncomputable
def ket_Phi_plus : Qubits 2 :=
  (1/√2) • (|00⟩ + |11⟩)
@[reducible]
noncomputable
def ket_Phi_minus : Qubits 2 :=
  (1/√2) • (|00⟩ - |11⟩)
@[reducible]
noncomputable
def ket_Psi_plus : Qubits 2 :=
  (1/√2) • (|01⟩ + |10⟩)
@[reducible]
noncomputable
def ket_Psi_minus : Qubits 2 :=
  (1/√2) • (|01⟩ - |10⟩)

notation "|Φ+⟩" => ket_Phi_plus
notation "|Φ-⟩" => ket_Phi_minus
notation "|Ψ+⟩" => ket_Psi_plus
notation "|Ψ-⟩" => ket_Psi_minus


def I {n : ℕ} : QSquare n := 1
def I₂ : QSquare 2 := 1

def X : QSquare 2 :=
  fun i j =>
    if i = j then
      0
    else
      1

def Z : QSquare 2 :=
  fun i j =>
    if i = j then
      if i = 0 then
        1
      else
        -1
    else
      0

@[simp]
noncomputable
def H : QSquare 2 :=
  (1/√2) • Matrix.of (fun i j =>
    if i = 0 ∨ j = 0 then
      1
    else
      -1
  )

notation "|0⟩⟨0|" => |0⟩ * ⟨0|
notation "|1⟩⟨1|" => |1⟩ * ⟨1|

@[simp]
def tens {m₁ n₁ m₂ n₂ : ℕ} (A : QMatrix m₁ n₁) (B : QMatrix m₂ n₂) :
  QMatrix (m₁ * m₂) (n₁ * n₂)
  :=
    Matrix.of (fun (i j) =>
      A (Fin.divNat i) (Fin.divNat j) *
      B (Fin.modNat i) (Fin.modNat j))

infixl:70 " ⨂ " => tens

-- def partial_trace {n m : ℕ} (M : QSquare (n * m)) : QSquare n :=
--   fun i j =>
--     ∑ k, sorry

@[reducible]
def CNOT : QSquare 4 :=
  |0⟩⟨0| ⨂ I₂ + |1⟩⟨1| ⨂ X

@[reducible]
def CNOT' : QSquare 4 :=
  I₂ ⨂ |0⟩⟨0| + X ⨂ |1⟩⟨1|

def CNOTₙ (n : ℕ) (control target : Fin n) : QSquare (2^n) :=
  fun i j =>
    sorry

@[simp]
def zero_proj : QMatrix 2 2 := |0⟩ * ⟨0|
@[simp]
def one_proj : QMatrix 2 2 := |1⟩ * ⟨1|

def QMatrix.toReal (M : QMatrix 1 1) : ℝ :=
  (M 0 0).re

instance : Coe (QMatrix 1 1) ℝ where
  coe M := M.toReal

-- instance {m n : ℕ} : HSMul (QMatrix m n) ℂ (QMatrix m n) where
--   hSMul M c := Matrix.smul.smul c M
-- instance {m n : ℕ} : HSMul (QMatrix m n) ℝ (QMatrix m n) where
--   hSMul M c := Matrix.smul.smul c M

def QVector.congruent {n : ℕ} (a b : QVector n) :=
  ∃ (c : ℂ), Complex.normSq c = 1 ∧ c • a = b

notation:80 a " ≡ " b => QVector.congruent a b
notation:80 a " ≢ " b => ¬QVector.congruent a b

-- #eval (1 : ℂ) / (1 : ℂ)

lemma not_forall₂ {α β : Type} {P : α → β → Prop} :
  (¬∀ (x : α) (y : β), P x y) ↔ ∃ (x : α), ∃ (y : β), ¬P x y
  := by
    rw [not_forall]
    constructor
    · intro h
      rcases h with ⟨x, h⟩
      rw [not_forall] at h
      rcases h with ⟨y, h⟩
      use x
      use y
    · intro h
      rcases h with ⟨x, ⟨y, h⟩⟩
      use x
      rw [not_forall]
      use y

noncomputable
instance {a b : QVector n} : Decidable (a ≡ b) := by
  let P (i : Fin n) := a i 0 ≠ 0
  cases hP : Fin.find P with
  | none =>
    rw [Fin.find_eq_none_iff] at hP
    have ha : a = 0 := by
      apply Matrix.ext
      intro i j
      rw [Matrix.zero_apply, Fin.eq_zero j]
      specialize hP i
      simp only [Fin.isValue, ne_eq, not_not, P] at hP
      exact hP
    by_cases hb : b = 0
    · apply Decidable.isTrue
      use 1
      simp [ha, hb]
    · apply Decidable.isFalse
      unfold QVector.congruent
      rw [not_exists]
      intro c
      rw [not_and]
      intro
      rw [ha]
      simp [*, Eq.comm]
  | some i =>
    have hi : a i 0 ≠ 0 := by
      change P i
      apply Fin.find_spec
      rw [Option.mem_def, hP]
    let c := b i 0 / a i 0
    have {c' : ℂ} (hcc' : c ≠ c') : c' • a ≠ b := by
      rw [Ne, ← Matrix.ext_iff, not_forall₂]
      use i
      use 0
      rw [Matrix.smul_apply]
      unfold_let c at hcc'
      simp only [Fin.isValue, smul_eq_mul]
      rw [← propext (eq_div_iff hi), Eq.comm]
      exact hcc'
    by_cases hc : Complex.normSq c = 1
    · by_cases h : c • a = b
      · apply Decidable.isTrue
        use c
      · apply Decidable.isFalse
        unfold QVector.congruent
        rw [not_exists]
        intro c'
        rw [not_and]
        intro
        by_cases hcc' : c = c'
        · rw [← hcc']
          exact h
        · exact this hcc'
    · apply Decidable.isFalse
      unfold QVector.congruent
      rw [not_exists]
      intro c'
      rw [not_and]
      intro hc'
      apply this
      rw [Ne]
      have hnorm : ¬Complex.normSq c = Complex.normSq c' := by
        rw [hc']
        exact hc
      exact fun a ↦ hnorm (congrArg (⇑Complex.normSq) a)

@[simp]
noncomputable
def is_congruent {n : ℕ} (a b : QVector n) : [0,1] :=
  if a ≡ b then 1 else 0

@[simp]
noncomputable
def probability_congruent {n : ℕ} (a : Random (QVector n)) (b : QVector n) : [0,1] :=
  a (is_congruent b)

notation "ℙ[" a:100 " ≡ " b:100 "]" => probability_congruent a b

@[simp]
noncomputable
def Qmeasure_general {n m : ℕ} (φ : QVector n) (M : Fin m → QSquare n) : Random (QVector n) :=
  fun f =>
    ∑ i : Fin m,
      let Mᵢ := M i
      let p : [0,1] := (Mᵢ * φ)† * (Mᵢ * φ)
      let φᵢ := Complex.ofReal' (1 / p.sqrt) • (Mᵢ * φ)
      p * f φᵢ

@[simp]
noncomputable
def Qmeasure_single_qubit {n : ℕ} (φ : QVector n) (M₀ M₁ : QSquare n) : Random (Bool × QVector n) :=
  let p₀ : [0,1] := (M₀ * φ)† * (M₀ * φ)
  let φ₀ := Complex.ofReal' (1 / p₀.sqrt) • (M₀ * φ)
  let p₁ : [0,1] := (M₁ * φ)† * (M₁ * φ)
  let φ₁ := Complex.ofReal' (1 / p₁.sqrt) • (M₁ * φ)
  fun f => p₀ * f ⟨false, φ₀⟩ + p₁ * f ⟨true, φ₁⟩

noncomputable
def Qmeasure_single_qubit_rng {n : ℕ} (φ : QVector n) (M₀ M₁ : QSquare n) (rng : RNG) : (Bool × QVector n) × RNG :=
  let p₀ : [0,1] := (M₀ * φ)† * (M₀ * φ)
  let φ₀ := Complex.ofReal' (1 / p₀.sqrt) • (M₀ * φ)
  let p₁ : [0,1] := (M₁ * φ)† * (M₁ * φ)
  let φ₁ := Complex.ofReal' (1 / p₁.sqrt) • (M₁ * φ)
  let ⟨result, rng⟩ := rng.flip p₁
  if result then
    ⟨⟨true, φ₁⟩, rng⟩
  else
    ⟨⟨false, φ₀⟩, rng⟩

@[simp]
noncomputable
def Qmeasure₃₀ (φ : QVector 8) : Random (Bool × QVector 8) :=
  Qmeasure_single_qubit φ (|0⟩⟨0| ⨂ I₂ ⨂ I₂) (|1⟩⟨1| ⨂ I₂ ⨂ I₂)

@[simp]
noncomputable
def Qmeasure₃₁ (φ : QVector 8) : Random (Bool × QVector 8) :=
  Qmeasure_single_qubit φ (I₂ ⨂ |0⟩⟨0| ⨂ I₂) (I₂ ⨂ |1⟩⟨1| ⨂ I₂)

noncomputable
def Qmeasure₃₀_rng (φ : QVector 8) (rng : RNG) : (Bool × QVector 8) × RNG :=
  Qmeasure_single_qubit_rng φ (|0⟩⟨0| ⨂ I₂ ⨂ I₂) (|1⟩⟨1| ⨂ I₂ ⨂ I₂) rng

noncomputable
def Qmeasure₃₁_rng (φ : QVector 8) (rng : RNG) : (Bool × QVector 8) × RNG :=
  Qmeasure_single_qubit_rng φ (I₂ ⨂ |0⟩⟨0| ⨂ I₂) (I₂ ⨂ |1⟩⟨1| ⨂ I₂) rng

@[simp]
noncomputable
def Zmeasure (φ : Qubit) : Random (Qubit) := do
  let result ← Qmeasure_single_qubit φ |0⟩⟨0| |1⟩⟨1|
  pure result.2

def Qmeasure' (φ : Qubit) : Random Qubit :=
  fun f => ‖φ.α‖ * f |0⟩ + ‖φ.β‖ * f |1⟩


lemma cong_symm {n : ℕ} {a b : QVector n} :
  (a ≡ b) → (b ≡ a)
  := by
    intro ⟨c, ⟨hc, h⟩⟩
    use conj c
    constructor
    · simp [hc]
    · rw [
        ← h,
        smul_smul,
        ← Complex.normSq_eq_conj_mul_self,
        hc,
      ]
      simp

lemma cong_comm {n : ℕ} {a b : QVector n} :
  (a ≡ b) ↔ (b ≡ a)
  :=
    ⟨cong_symm, cong_symm⟩

lemma ncong_of_eq_zero_of_ne_zero {n : ℕ} {a b : QVector n} (i : Fin n) (ha : a i 0 = 0) (hb : b i 0 ≠ 0) :
  a ≢ b
  := by
    apply by_contradiction
    intro h
    rw [not_not] at h
    rcases h with ⟨c, ⟨_, h⟩⟩
    apply Matrix.ext_iff.mpr at h
    specialize h i 0
    rw [Matrix.smul_apply, ha, smul_zero] at h
    exact hb h.symm

lemma ncong_zero_of_ne_zero {n : ℕ} {φ : QVector n} (h : φ ≠ 0) :
  ¬φ ≡ 0
  := by
    rw [
      Ne,
      ← Matrix.ext_iff,
      not_forall,
    ] at h
    rcases h with ⟨i, h⟩
    rw [not_forall] at h
    rcases h with ⟨j, h⟩
    rw [Matrix.zero_apply] at h
    rw [cong_comm]
    apply ncong_of_eq_zero_of_ne_zero i
    · rw [Matrix.zero_apply]
    · rw [← Fin.eq_zero j]
      exact h

lemma ncong_smul_of_ncong {n : ℕ} {a b : QVector n} {c : ℂ} (h : a ≢ b) :
  a ≢ c • b
  := by
    apply by_contradiction
    intro h'
    rw [not_not] at h'
    rcases h' with ⟨c', ⟨hc', h'⟩⟩
    
    sorry
lemma ket0_ncong_ket1 :
  |0⟩ ≢ |1⟩
  := by
    apply ncong_of_eq_zero_of_ne_zero 1
    · simp [ket0]
    · simp [ket1]

lemma zero_smul_zero :
  (0 : ℝ) • (0 : QMatrix 2 1) = (0 : QMatrix 2 1)
  := by
    rw [← @Matrix.ext_iff]
    intros
    simp

lemma QMatrix.ne_zero_of_element_ne_zero {m n : ℕ} {A : QMatrix m n} (i : Fin m) (j : Fin n) (hij : A i j ≠ 0) :
  A ≠ 0
  := by
    exact fun a => hij (congrFun (congrFun a i) j)

lemma real_smul {r : ℝ} {m n : ℕ} {A : QMatrix m n} :
  r • A = (Complex.ofReal' r) • A
  := by
    apply Matrix.ext
    intro i j
    simp [Matrix.smul_apply]

lemma cong_smul_self {n : ℕ} {φ : QVector n} {c : ℂ} (hc : Complex.normSq c = 1):
  φ ≡ c • φ
  := by
    use c


/-
 - Square Matrix Properties
 -/

section SquareMatrixProperties

variable {n : ℕ} (M : QSquare n)

@[simp]
def QSquare.symmetric := Mᵀ = M

@[simp]
def QSquare.hermitian := M = M†

@[simp]
def QSquare.normal := M† * M = M * M†

end SquareMatrixProperties



/-
 - Matrix Properties
 -/

section MatrixProperties

variable {m n : ℕ} (M : QMatrix m n)

@[simp, reducible]
def QMatrix.unitary := M† * M = 1

@[simp]
def QMatrix.real := ∀ (i : Fin m) (j : Fin n), star (M i j) = M i j

end MatrixProperties
