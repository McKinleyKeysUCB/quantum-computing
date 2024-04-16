
import Mathlib.Data.Real.Basic


/-
 - We define the range `[0,1]` to be `ℝ` for simplicity, but it would be good to replace this with a correct definition in the future, such as
 -   `def Prob : Set ℝ := {x : ℝ | 0 ≤ x ∧ x ≤ 1}`
 -/

@[reducible]
def Prob := ℝ

notation "[0,1]" => Prob


/-
 - Random Number Generator
 -/

structure RNG where
  f : ℕ → [0,1]
  n : ℕ

def RNG.next (rng : RNG) : [0,1] × RNG :=
  let result := rng.f rng.n
  let new_rng := {f := rng.f, n := rng.n.succ}
  ⟨result, new_rng⟩

-- Returns `true` with probability `p` and `false` with probability `1 - p`.
noncomputable
def RNG.flip (rng : RNG) (p : [0,1]) : Bool × RNG :=
  let ⟨result, rng⟩ := rng.next
  ⟨result < p, rng⟩


/-
 - Random Monad
 -/

@[reducible, simp]
def Random (α : Type) := (α → [0,1]) → [0,1]

@[simp]
def Random.pure (x : α) : Random α :=
  fun f => f x

@[simp]
def Random.bind (left : Random α) (right : α → Random β) : Random β :=
  fun (f : β → [0,1]) =>
    left (fun (x : α) => right x f)

@[simp]
instance : Monad Random where
  pure := Random.pure
  bind := Random.bind

@[simp]
def does_equal [DecidableEq α] (t : α) (x : α) : [0,1] :=
  if t = x then 1 else 0

@[simp]
def probability_equals [DecidableEq α] (a : Random α) (b : α) : [0,1] :=
  a (does_equal b)

notation "ℙ[" a:100 " = " b:100 "]" => probability_equals a b


/-
 - Examples
 -/

@[simp]
noncomputable
def coin_flip : Random Bool :=
  fun f =>
    1/2 * f false + 1/2 * f true

@[simp]
noncomputable
def nat_coin_flip : Random ℕ := do
  if ← coin_flip then
    pure 1
  else
    pure 0

noncomputable
def test (n : ℕ) : Random Bool :=
  if n = 0 then
    pure true
  else
    bind (coin_flip) fun heads =>
      if heads && n = 5 then
        pure true
      else
        pure false

-- The same as `test` but using Lean's monadic programming syntax.
noncomputable
def test' (n : ℕ) : Random Bool := do
  if n = 0 then
    pure true
  else
    let heads ← coin_flip
    if heads && n = 5 then
      pure true
    else
      pure false

noncomputable
def two_flips : Random ℕ :=
  bind nat_coin_flip fun a =>
    bind nat_coin_flip fun b =>
      pure (a + b)

-- The same as `two_flips` but using Lean's monadic programming syntax.
noncomputable
def two_flips' : Random ℕ := do
  let a ← nat_coin_flip
  let b ← nat_coin_flip
  pure (a + b)


/-
 - Example Lemmas
 -/

lemma test_0_eq_true :
  ℙ[test 0 = true] = 1
  := by
    unfold test
    simp only [probability_equals, ↓reduceIte, instMonadRandom, Random, Random.pure, does_equal]

lemma test'_0_eq_true :
  ℙ[test' 0 = true] = 1
  := by
    unfold test'
    simp only [probability_equals, ↓reduceIte, instMonadRandom, Random, Random.pure, does_equal]

lemma test_5_is_50_50 :
  ℙ[test 5 = true] = 1/2
  := by
    unfold test
    simp only [probability_equals, OfNat.ofNat_ne_zero, ↓reduceIte, instMonadRandom, Random, decide_True, Bool.and_true, Random.bind, coin_flip, one_div, Random.pure, does_equal, mul_zero, mul_one, zero_add]

lemma test'_5_is_50_50 :
  ℙ[test' 5 = true] = 1/2
  := by
    unfold test'
    simp only [probability_equals, OfNat.ofNat_ne_zero, ↓reduceIte, instMonadRandom, Random, decide_True, Bool.and_true, Random.bind, coin_flip, one_div, Random.pure, does_equal, mul_zero, mul_one, zero_add]

lemma Pr_two_flips_eq_0 :
  ℙ[two_flips' = 0] = 1/4
  := by
    unfold two_flips'
    simp only [probability_equals, instMonadRandom, Random, nat_coin_flip, Random.bind, coin_flip, one_div, ↓reduceIte, Random.pure, does_equal, add_zero, mul_one, zero_add, zero_ne_one, mul_zero, Nat.reduceAdd, OfNat.zero_ne_ofNat]
    norm_num

lemma Pr_two_flips_eq_1 :
  ℙ[two_flips' = 1] = 1/2
  := by
    unfold two_flips'
    simp only [probability_equals, instMonadRandom, Random, nat_coin_flip, Random.bind, coin_flip, one_div, ↓reduceIte, Random.pure, does_equal, add_zero, one_ne_zero, mul_zero, zero_add, mul_one, Nat.reduceAdd, OfNat.one_ne_ofNat]
    norm_num

lemma Pr_two_flips_eq_2 :
  ℙ[two_flips' = 2] = 1/4
  := by
    unfold two_flips'
    simp only [probability_equals, instMonadRandom, Random, nat_coin_flip, Random.bind, coin_flip, one_div, ↓reduceIte, Random.pure, does_equal, add_zero, OfNat.ofNat_ne_zero, mul_zero, zero_add, OfNat.ofNat_ne_one, Nat.reduceAdd, mul_one]
    norm_num
