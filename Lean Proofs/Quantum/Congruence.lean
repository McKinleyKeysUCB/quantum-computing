
import Quantum.Definitions

/-
 - Proof that `≡` is decidable.
 - The `noncomputable` is there because the proof relies on `Complex.instField`, which is noncomputable. There might be a way around this.
 -/
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


/-
 - Lemmas
 -/

lemma cong_symm {n : ℕ} {a b : QVector n} :
  (a ≡ b) → (b ≡ a)
  := by
    intro ⟨c, ⟨hc, h⟩⟩
    use star c
    constructor
    · simp [hc]
    · rw [
        ← h,
        smul_smul,
        Complex.star_def,
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

lemma ncong_smul_of_ncong {n : ℕ} {a b : QVector n} {c : ℂ} (hc : Complex.normSq c = 1) (h : a ≢ b) :
  a ≢ c • b
  := by
    apply by_contradiction
    intro h'
    rw [not_not] at h'
    rcases h' with ⟨c', ⟨hc', h'⟩⟩
    apply h
    use c' / c
    constructor
    · simp [hc', hc]
    · rw [division_def, mul_comm, mul_smul, h', ← mul_smul]
      have hc : c ≠ 0 := by
        contrapose hc
        rw [not_not] at hc
        rw [hc]
        simp only [map_zero, zero_ne_one, not_false_eq_true]
      rw [(inv_mul_eq_one₀ hc).mpr rfl, one_smul]

lemma ket0_ncong_ket1 :
  |0⟩ ≢ |1⟩
  := by
    apply ncong_of_eq_zero_of_ne_zero 1
    · simp [ket0]
    · simp [ket1]

lemma cong_smul_self {n : ℕ} {φ : QVector n} {c : ℂ} (hc : Complex.normSq c = 1):
  φ ≡ c • φ
  := by
    use c
