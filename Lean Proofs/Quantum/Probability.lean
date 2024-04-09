
import Mathlib.Data.Real.Basic

-- def Prob : Set ℝ := {x : ℝ | 0 ≤ x ∧ x ≤ 1}
@[reducible]
def Prob := ℝ
notation "[0,1]" => Prob

@[reducible, simp]
def RandM (α : Type) := (α → [0,1]) → [0,1]

@[simp]
def RandM.pure (x : α) : RandM α :=
  fun f => f x

@[simp]
def RandM.bind (left : RandM α) (right : α → RandM β) : RandM β :=
  fun (f : β → [0,1]) =>
    left (fun (x : α) => right x f)

@[simp]
instance : Monad RandM where
  pure := RandM.pure
  bind := RandM.bind



@[simp]
def does_equal [DecidableEq α] (t : α) (x : α) : [0,1] :=
  if t = x then (1 : ℝ) else (0 : ℝ)

@[simp]
def probability_equals [DecidableEq α] (a : RandM α) (b : α) : [0,1] :=
  a (does_equal b)

notation:100 "ℙ[" a:100 " = " b:100 "]" => probability_equals a b



@[simp]
noncomputable
def coin_flip : RandM Bool :=
  fun f =>
    1/2 * f false + 1/2 * f true

@[simp]
noncomputable
def nat_coin_flip : RandM ℕ := do
  if ← coin_flip then
    pure 1
  else
    pure 0

noncomputable
def test (n : ℕ) : RandM Bool :=
  if n = 0 then
    pure true
  else
    bind (coin_flip) fun heads =>
      if heads && n = 5 then
        pure true
      else
        pure false
noncomputable
def test' (n : ℕ) : RandM Bool := do
  if n = 0 then
    pure true
  else
    let heads ← coin_flip
    if heads && n = 5 then
      pure true
    else
      pure false

-- noncomputable
-- def two_flips : RandM ℕ :=
--   bind nat_coin_flip fun a =>
--     bind nat_coin_flip fun b =>
--       pure (a + b)
noncomputable
def two_flips : RandM ℕ := do
  let a ← nat_coin_flip
  let b ← nat_coin_flip
  pure (a + b)

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

lemma Pr_two_flips_eq_0 :
  ℙ[two_flips = 0] = 1/4
  := by
    unfold two_flips
    simp
    norm_num
lemma Pr_two_flips_eq_1 :
  ℙ[two_flips = 1] = 1/2
  := by
    unfold two_flips
    simp
    norm_num
lemma Pr_two_flips_eq_2 :
  ℙ[two_flips = 2] = 1/4
  := by
    unfold two_flips
    simp
    norm_num
