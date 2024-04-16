
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic
import Quantum.Probability
import Quantum.Lemmas

open BigOperators Nat

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

@[reducible]
def CNOT : QSquare 4 :=
  |0⟩⟨0| ⨂ I₂ + |1⟩⟨1| ⨂ X

@[reducible]
def CNOT' : QSquare 4 :=
  I₂ ⨂ |0⟩⟨0| + X ⨂ |1⟩⟨1|

@[simp]
def zero_proj : QMatrix 2 2 := |0⟩ * ⟨0|
@[simp]
def one_proj : QMatrix 2 2 := |1⟩ * ⟨1|

def QMatrix.toReal (M : QMatrix 1 1) : ℝ :=
  (M 0 0).re

instance : Coe (QMatrix 1 1) ℝ where
  coe M := M.toReal


/-
 - Congruence
 -/

def QVector.congruent {n : ℕ} (a b : QVector n) :=
  ∃ (c : ℂ), Complex.normSq c = 1 ∧ c • a = b

notation:80 a " ≡ " b => QVector.congruent a b
notation:80 a " ≢ " b => ¬QVector.congruent a b


/-
 - Measurement
 -/

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
