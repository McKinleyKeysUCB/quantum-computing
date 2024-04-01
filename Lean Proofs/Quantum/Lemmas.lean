
import Init.Data.Nat.Basic
import Mathlib.Tactic.Lemma
import Mathlib.Order.Basic
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Data.Nat.Defs

lemma Nat.pos_iff_one_le {n : ℕ} :
  0 < n ↔ 1 ≤ n
  := calc
    0 < n ↔ n ≠ 0       := Nat.pos_iff_ne_zero
    _     ↔ 1 ≤ n       := by symm; apply one_le_iff_ne_zero
