
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

@[reducible]
def QMatrix (m n : ℕ) :=
  Matrix (Fin m) (Fin n) ℂ

@[reducible]
def Qubit := QMatrix 2 1
def Qubits (n : ℕ) := QMatrix (2 ^ n) 1

def Qubit.α (φ : Qubit) := φ 0 0
def Qubit.β (φ : Qubit) := φ 1 0

noncomputable
def norm (φ : Qubit)
  := (Complex.normSq φ.α + Complex.normSq φ.β).sqrt

notation:70 "|" φ "|" => norm φ

noncomputable
def ket0 : Qubit := ![
  ![1],
  ![0]
]
noncomputable
def ket0' : Qubit := fun i _ => if i = 0 then 1 else 0

noncomputable
def ket1 : Qubit := ![
  ![0],
  ![1]
]
noncomputable
def ket1' : Qubit := fun i _ => if i = 1 then 1 else 0

notation "|0⟩" => ket0'
notation "|1⟩" => ket1'

lemma norm_ket0_eq_1 :
  | |0⟩ | = 1
  := by
    simp [norm, ket0', Qubit.α, Qubit.β]
lemma norm_ket1_eq_1 :
  | |1⟩ | = 1
  := by
    simp [norm, ket1', Qubit.α, Qubit.β]

noncomputable
def ket00 : Qubits 2 := ![
  ![1],
  ![0],
  ![0],
  ![0]
]
noncomputable
def ket00' : Qubits 2 := fun i _ => if i = 0 then 1 else 0
noncomputable
def ket01' : Qubits 2 := fun i _ => if i = 1 then 1 else 0
noncomputable
def ket10' : Qubits 2 := fun i _ => if i = 2 then 1 else 0
noncomputable
def ket11' : Qubits 2 := fun i _ => if i = 3 then 1 else 0

notation "|00⟩" => ket00'
notation "|01⟩" => ket01'
notation "|10⟩" => ket10'
notation "|11⟩" => ket11'

noncomputable
def ket_plus := ![
  ![1 / Real.sqrt 2],
  ![1 / Real.sqrt 2]
]
noncomputable
def ket_minus := ![
  ![1 / Real.sqrt 2],
  ![-1 / Real.sqrt 2]
]

noncomputable
def ket_plus' : Qubit := fun _ _ => 1 / Real.sqrt 2
noncomputable
def ket_minus' : Qubit := fun i _ => if i = 0 then 1 / Real.sqrt 2 else -1 / Real.sqrt 2

notation "|+⟩" => ket_plus'
notation "|-⟩" => ket_minus'

def X := ![
  ![0, 1],
  ![1, 0]
]
def Z := ![
  ![1, 0],
  ![0, -1]
]
noncomputable
def H := ![
  ![1 / Real.sqrt 2, 1 / Real.sqrt 2],
  ![1 / Real.sqrt 2, -1 / Real.sqrt 2]
]

def Tens {m₁ n₁ m₂ n₂ : ℕ} (A : QMatrix m₁ n₁) (B : QMatrix m₂ n₂) :
  QMatrix (m₁ * m₂) (n₁ * n₂)
  :=
    Matrix.of (fun (i j) =>
      A (Fin.divNat i) (Fin.divNat j) *
      B (Fin.modNat i) (Fin.modNat j)
    )

infixl:70 " ⊗ " => Tens
