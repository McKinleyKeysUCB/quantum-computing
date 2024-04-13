
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Quantum.Probability

open ComplexConjugate BigOperators Nat

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

def Qubit.α (φ : Qubit) := φ 0 0
def Qubit.β (φ : Qubit) := φ 1 0

@[simp]
def QMatrix.adjoint {m n : ℕ} (M : QMatrix m n) : QMatrix n m :=
  fun i j =>
    star (M j i)

notation M "†" => QMatrix.adjoint M

noncomputable
def norm (φ : Qubit) :=
  (Complex.normSq φ.α + Complex.normSq φ.β).sqrt

notation:70 "|" φ "|" => norm φ
notation:70 "‖" φ "‖" => Complex.normSq φ

def ket0 : Qubit :=
  fun i _ => if i = 0 then 1 else 0

def bra0 := ket0†
  
def ket1 : Qubit :=
  fun i _ => if i = 1 then 1 else 0

def bra1 := ket1†

noncomputable
def ket_plus : Qubit :=
  fun _ _ => 1 / Real.sqrt 2

noncomputable
def ket_minus : Qubit :=
  fun i _ => if i = 0 then 1 / Real.sqrt 2 else -1 / Real.sqrt 2

def ket00 : Qubits 2 :=
  fun i _ => if i = 0 then 1 else 0
def ket01 : Qubits 2 :=
  fun i _ => if i = 1 then 1 else 0
def ket10 : Qubits 2 :=
  fun i _ => if i = 2 then 1 else 0
def ket11 : Qubits 2 :=
  fun i _ => if i = 3 then 1 else 0

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

noncomputable
def H : QSquare 2 :=
  fun i j =>
    if i = 0 then
      1 / Real.sqrt 2
    else
      if j = 0 then 1 / Real.sqrt 2 else -1 / Real.sqrt 2

def CNOT : QSquare 4 :=
  fun i j =>
    if i = 0 ∨ i = 1 then
      if i = j then 1 else 0
    else
      if (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) then
        1
      else
        0

def CNOT' (n : ℕ) (control target : Fin n) : QSquare (2^n) :=
  fun i j =>
    
    sorry

def CX (n : ℕ) (control target : Fin n) : QSquare (2^n) :=
  fun i j =>
    
    sorry
def CZ (n : ℕ) (control target : Fin n) : QSquare (2^n) :=
  fun i j =>
    sorry

@[simp]
def tens {m₁ n₁ m₂ n₂ : ℕ} (A : QMatrix m₁ n₁) (B : QMatrix m₂ n₂) :
  QMatrix (m₁ * m₂) (n₁ * n₂)
  :=
    Matrix.of (fun (i j) =>
      A (Fin.divNat i) (Fin.divNat j) *
      B (Fin.modNat i) (Fin.modNat j))

infixl:70 " ⨂ " => tens

def Qubits.extract {n : ℕ} (state : Qubits n) (i : Fin n) : Qubit :=
  sorry

notation:90 state "[" i "]" => Qubits.extract state i


@[simp]
def zero_proj : QMatrix 2 2 := |0⟩ * ⟨0|
@[simp]
def one_proj : QMatrix 2 2 := |1⟩ * ⟨1|

notation "|0⟩⟨0|" => |0⟩ * ⟨0|
notation "|1⟩⟨1|" => |1⟩ * ⟨1|

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

instance {a b : QVector n} : Decidable (a ≡ b) := by
  sorry

@[simp]
noncomputable
def is_congruent {n : ℕ} (a b : QVector n) : [0,1] :=
  if a ≡ b then 1 else 0

@[simp]
noncomputable
def probability_congruent {n : ℕ} (a : RandM (QVector n)) (b : QVector n) : [0,1] :=
  a (is_congruent b)

notation "ℙ[" a:100 " ≡ " b:100 "]" => probability_congruent a b

@[simp]
noncomputable
def Qmeasure_general {n m : ℕ} (φ : QVector n) (M : Fin m → QSquare n) : RandM (QVector n) :=
  fun f =>
    ∑ i : Fin m,
      let Mᵢ := M i
      let p : [0,1] := (Mᵢ * φ)† * (Mᵢ * φ)
      let φᵢ := Complex.ofReal' (1 / p.sqrt) • (Mᵢ * φ)
      p * f φᵢ

@[simp]
noncomputable
def Qmeasure_single_qubit {n : ℕ} (φ : QVector n) (M₀ M₁ : QSquare n) : RandM (Bool × QVector n) :=
  let p₀ : [0,1] := (M₀ * φ)† * (M₀ * φ)
  let φ₀ := Complex.ofReal' (1 / p₀.sqrt) • (M₀ * φ)
  let p₁ : [0,1] := (M₁ * φ)† * (M₁ * φ)
  let φ₁ := Complex.ofReal' (1 / p₁.sqrt) • (M₁ * φ)
  fun f => p₀ * f ⟨false, φ₀⟩ + p₁ * f ⟨true, φ₁⟩

@[simp]
noncomputable
def Qmeasure₃₀ (φ : QVector 8) : RandM (Bool × QVector 8) :=
  Qmeasure_single_qubit φ (|0⟩⟨0| ⨂ I₂ ⨂ I₂) (|1⟩⟨1| ⨂ I₂ ⨂ I₂)

@[simp]
noncomputable
def Qmeasure₃₁ (φ : QVector 8) : RandM (Bool × QVector 8) :=
  Qmeasure_single_qubit φ (I₂ ⨂ |0⟩⟨0| ⨂ I₂) (I₂ ⨂ |1⟩⟨1| ⨂ I₂)

@[simp]
noncomputable
def Zmeasure (φ : Qubit) : RandM (Qubit) := do
  let result ← Qmeasure_single_qubit φ |0⟩⟨0| |1⟩⟨1|
  pure result.2

def Qmeasure' (φ : Qubit) : RandM Qubit :=
  fun f => ‖φ.α‖ * f |0⟩ + ‖φ.β‖ * f |1⟩

lemma zero_proj_phi {φ : Qubit} :
  |0⟩⟨0| * φ = φ.α • |0⟩
  := by
    sorry
-- @[simp]
lemma one_proj_phi {φ : Qubit} :
  |1⟩⟨1| * φ = φ.β • |1⟩
  := by
    sorry
@[simp]
lemma zero_proj_phi' {φ : Qubit} :
  QMatrix.toReal ((|0⟩⟨0| * φ)† * (|0⟩⟨0| * φ)) = ‖φ.α‖
  := by
    sorry
@[simp]
lemma one_proj_phi' {φ : Qubit} :
  QMatrix.toReal ((|1⟩⟨1| * φ)† * (|1⟩⟨1| * φ)) = ‖φ.β‖
  := by
    sorry


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

lemma Qmeasure0 {φ : Qubit} :
  ℙ[Zmeasure φ ≡ |0⟩] = ‖φ.α‖
  := by
    conv =>
      lhs
      args
      unfold Zmeasure Qmeasure_single_qubit
      simp [zero_proj_phi', one_proj_phi']
      rw [zero_proj_phi, one_proj_phi]
    simp
    nth_rw 2 [if_neg]
    rw [add_zero]
    by_cases hα : φ.α = 0
    · rw [if_neg]
      · simp [hα]
      rw [hα, Complex.normSq_zero, Real.sqrt_zero]
      simp
      apply ncong_zero_of_ne_zero
      apply QMatrix.ne_zero_of_element_ne_zero 0 0
      rw [ket0]
      simp
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
    apply ncong_smul_of_ncong
    exact ket0_ncong_ket1


/-
 - Square Matrix Properties
 -/

section SquareMatrixProperties

variable {n : ℕ} (M : QSquare n)

@[simp]
def QSquare.hermitian := M = M†

@[simp]
def QSquare.normal := M† * M = M * M†

-- def QMatrix.symmetric := M = M^T

end SquareMatrixProperties



/-
 - Matrix Properties
 -/

section MatrixProperties

variable {m n : ℕ} (M : QMatrix m n)

@[simp]
def QMatrix.unitary := M * M† = 1

end MatrixProperties
