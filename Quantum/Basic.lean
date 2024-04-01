
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

lemma Nat.pos_iff_one_le {n : ℕ} :
  0 < n ↔ 1 ≤ n
  := calc
    0 < n ↔ n ≠ 0       := pos_iff_ne_zero
    _     ↔ 1 ≤ n       := by symm; apply one_le_iff_ne_zero

def hello := "world"