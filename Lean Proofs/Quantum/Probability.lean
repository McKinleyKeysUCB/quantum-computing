
import Mathlib.Data.Real.Basic

-- def Prob : Set ℝ := {x : ℝ | 0 ≤ x ∧ x ≤ 1}
notation "[0,1]" => ℝ

@[reducible, simp]
def M (α : Type) := (α → [0,1]) → [0,1]

@[reducible, simp]
noncomputable
def coin_flip : M Bool :=
  fun f =>
    1/2 * f false + 1/2 * f true

@[reducible, simp]
def my_unit {τ : Type} (t : τ) : M τ :=
  fun f => f t

@[reducible, simp]
def my_bind {τ σ : Type} (μ : M τ) (m : τ → M σ) : M σ :=
  fun f =>
    μ (fun x : τ => m x f)

@[simp]
instance : Monad M where
  pure := my_unit
  bind := my_bind

@[reducible, simp]
noncomputable
def nat_coin_flip : M ℕ :=
  my_bind coin_flip (fun heads => if heads then 1 else 0)

noncomputable
def test (n : ℕ) : M Bool :=
  if n = 0 then
    my_unit true
  else
    my_bind (coin_flip) fun heads =>
      if heads && n = 5 then
        my_unit true
      else
        my_unit false
noncomputable
def test' (n : ℕ) : M Bool := do
  if n = 0 then
    pure true
  else
    let heads ← coin_flip
    if heads && n = 5 then
      pure true
    else
      pure false

-- def two_flips : M ℕ :=
--   my_bind nat_coin_flip fun a =>
--     my_bind nat_coin_flip fun b =>
--       my_unit (a + b)

noncomputable
def two_flips : M ℕ := do
  let a ← nat_coin_flip
  let b ← nat_coin_flip
  pure (a + b)

@[reducible, simp]
def does_equal {α : Type} [DecidableEq α] (t : α) (x : α) : [0,1] :=
  if t = x then 1 else 0

@[reducible, simp]
def probability_equals {α : Type} [DecidableEq α] (a : M α) (b : α) : [0,1] :=
  a (does_equal b)

notation:100 "ℙ[" a:100 " = " b:100 "]" => probability_equals a b

lemma test_0_eq_true :
  ℙ[test 0 = true] = 1
  := by
    unfold test
    simp

lemma test'_0_eq_true :
  ℙ[test' 0 = true] = 1
  := by
    unfold test'
    simp

lemma test_5_is_50_50 :
  ℙ[test 5 = true] = 1/2
  := by
    unfold test
    simp
lemma test'_5_is_50_50 :
  ℙ[test' 5 = true] = 1/2
  := by
    unfold test'
    simp

lemma Pr_two_flips_eq_1 :
  ℙ[two_flips = 1] = 1/2
  := by
    unfold two_flips
    simp
