import Hironaka.Resolution.HironakaActualFormalInitialDiagram

/-!
# Actual finite-degree deglex weights

The weights are explicit positive integers produced from the true finite
vertex set. Their strict comparison covers EVERY larger exponent, including
the infinitely many higher-degree exponents, rather than a supplied tail set.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualFiniteDegLexWeights

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram

def positionalDigitWeight (B : ℕ) : (n : ℕ) → Fin n → ℕ
  | 0 => Fin.elim0
  | n+1 => Fin.cons (B ^ n) (positionalDigitWeight B n)

def positionalCode {n : ℕ} (B : ℕ) (f : Fin n → ℕ) : ℕ :=
  ∑ i, positionalDigitWeight B n i * f i

private theorem positionalCode_succ {n : ℕ} (B : ℕ) (f : Fin (n+1) → ℕ) :
    positionalCode B f = B ^ n * f 0 + positionalCode B (fun i : Fin n => f i.succ) := by
  simp only [positionalCode,Fin.sum_univ_succ,positionalDigitWeight,Fin.cons_zero,Fin.cons_succ]

theorem positionalCode_lt_pow (B : ℕ) (_hB : 0 < B) {n : ℕ}
    (f : Fin n → ℕ) (hf : ∀ i, f i < B) : positionalCode B f < B ^ n := by
  induction n with
  | zero => simp [positionalCode]
  | succ n ih =>
    rw [positionalCode_succ]
    calc
      _ < B ^ n * f 0 + B ^ n :=
        Nat.add_lt_add_left (ih (fun i => f i.succ) (fun i => hf i.succ)) _
      _ = B ^ n * (f 0 + 1) := by ring
      _ ≤ B ^ n * B := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (hf 0))
      _ = B ^ (n+1) := (pow_succ B n).symm

theorem positionalCode_lt_of_lex (B : ℕ) (hB : 0 < B) {n : ℕ}
    (f g : Fin n → ℕ) (hf : ∀ i, f i < B) (hg : ∀ i, g i < B)
    (hlex : ∃ i, (∀ j, j < i → f j = g j) ∧ f i < g i) :
    positionalCode B f < positionalCode B g := by
  induction n with
  | zero => obtain ⟨i,_⟩ := hlex; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨i,he,hi⟩ := hlex
    cases i using Fin.cases with
    | zero =>
      rw [positionalCode_succ,positionalCode_succ]
      calc
        _ < B ^ n * f 0 + B ^ n := Nat.add_lt_add_left
          (positionalCode_lt_pow B hB (fun j : Fin n => f j.succ) (fun j => hf j.succ)) _
        _ = B ^ n * (f 0 + 1) := by ring
        _ ≤ B ^ n * g 0 := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hi)
        _ ≤ B ^ n * g 0 + positionalCode B (fun j : Fin n => g j.succ) := Nat.le_add_right _ _
    | succ i =>
      rw [positionalCode_succ,positionalCode_succ,he 0 (Fin.succ_pos i)]
      apply Nat.add_lt_add_left
      exact ih (fun j => f j.succ) (fun j => g j.succ)
        (fun j => hf j.succ) (fun j => hg j.succ)
        ⟨i,fun j hj => he j.succ (Fin.succ_lt_succ_iff.mpr hj),hi⟩

def weightedDegree {n : ℕ} (W : Fin n → ℕ) (a : Fin n →₀ ℕ) : ℕ :=
  ∑ i, W i * a i

def degLexWeight (n M : ℕ) (i : Fin n) : ℕ :=
  (M+1) ^ n + positionalDigitWeight (M+1) n i

theorem degLexWeight_positive (n M : ℕ) (i : Fin n) : 0 < degLexWeight n M i :=
  lt_of_lt_of_le (pow_pos (Nat.succ_pos M) n) (Nat.le_add_right _ _)

private theorem digit_lt_radix_of_degree_le {n M : ℕ} (a : Fin n →₀ ℕ)
    (ha : normalExponentDegree a ≤ M) (i : Fin n) : a i < M+1 := by
  have hi : a i ≤ normalExponentDegree a :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

private theorem weightedDegree_degLexWeight {n : ℕ} (M : ℕ) (a : Fin n →₀ ℕ) :
    weightedDegree (degLexWeight n M) a =
      (M+1) ^ n * normalExponentDegree a + positionalCode (M+1) a := by
  simp only [weightedDegree,degLexWeight,add_mul,Finset.sum_add_distrib,
    normalExponentDegree,Finset.mul_sum,positionalCode]

/-- The actual degree-first lex order, against ALL larger exponents, is realized internally. -/
theorem weightedDegree_strict_of_degLex {n : ℕ} (M : ℕ) (a b : Fin n →₀ ℕ)
    (ha : normalExponentDegree a ≤ M)
    (hab : MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn b) :
    weightedDegree (degLexWeight n M) a < weightedDegree (degLexWeight n M) b := by
  have horder := Finsupp.DegLex.lt_iff.mp (MonomialOrder.degLex_lt_iff.mp hab)
  rw [weightedDegree_degLexWeight,weightedDegree_degLexWeight]
  rcases horder with hd | ⟨hd,hlex⟩
  · have hdeg : normalExponentDegree a < normalExponentDegree b := by
      simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using hd
    have hc := positionalCode_lt_pow (M+1) (Nat.succ_pos M) a
      (digit_lt_radix_of_degree_le a ha)
    calc
      _ < (M+1) ^ n * normalExponentDegree a + (M+1) ^ n := Nat.add_lt_add_left hc _
      _ = (M+1) ^ n * (normalExponentDegree a + 1) := by ring
      _ ≤ (M+1) ^ n * normalExponentDegree b :=
        Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hdeg)
      _ ≤ _ := Nat.le_add_right _ _
  · have hdeg : normalExponentDegree a = normalExponentDegree b := by
      simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using hd
    have hb : normalExponentDegree b ≤ M := hdeg ▸ ha
    have hc := positionalCode_lt_of_lex (M+1) (Nat.succ_pos M) a b
      (digit_lt_radix_of_degree_le a ha) (digit_lt_radix_of_degree_le b hb)
      (Finsupp.Lex.lt_iff.mp hlex)
    rw [hdeg]
    exact Nat.add_lt_add_left hc _

/-- The true finite initial vertices produce one positive weight vector for all their true tails. -/
theorem exists_actualDiagram_positive_weights (n : ℕ)
    (J : Ideal (MvPowerSeries (Fin n) ℂ)) :
    ∃ W : Fin n → ℕ, (∀ i, 0 < W i) ∧
      ∀ a : actualInitialVertices MonomialOrder.degLex J, ∀ b : Fin n →₀ ℕ,
        MonomialOrder.degLex.toSyn a.val < MonomialOrder.degLex.toSyn b →
        weightedDegree W a.val < weightedDegree W b := by
  let M := ∑ a : actualInitialVertices MonomialOrder.degLex J, normalExponentDegree a.val
  refine ⟨degLexWeight n M,degLexWeight_positive n M,?_⟩
  intro a b hab
  have ha : normalExponentDegree a.val ≤ M := by
    change normalExponentDegree a.val ≤
      ∑ b : actualInitialVertices MonomialOrder.degLex J, normalExponentDegree b.val
    exact Finset.single_le_sum
      (f := fun b : actualInitialVertices MonomialOrder.degLex J => normalExponentDegree b.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  exact weightedDegree_strict_of_degLex M a.val b ha hab

end

end Hironaka.HironakaActualFiniteDegLexWeights
