/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalFormalHSTransfer
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.Data.Finsupp.PWO
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! Actual coefficient minima, genuine formal convolution, and internally constructed vertex series. -/
set_option autoImplicit false
open Set Classical
open scoped MonomialOrder
namespace Hironaka.HironakaActualFormalInitialDiagram
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer

variable {n : ℕ}

/-- A genuine nonzero series has an actual least nonzero coefficient for every genuine monomial order. -/
theorem exists_actualInitialExponent (m : MonomialOrder (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) :
    ∃ a : Fin n →₀ ℕ, MvPowerSeries.coeff a F ≠ 0 ∧
      ∀ b, MvPowerSeries.coeff b F ≠ 0 → m.toSyn a ≤ m.toSyn b := by
  let S : Set m.syn := m.toSyn '' F.support
  have hn : S.Nonempty := (Function.support_nonempty_iff.mpr hF).image _
  have hw : S.IsWF := Set.IsWF.of_wellFoundedLT S
  obtain ⟨a, ha, he⟩ := hw.min_mem hn
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [he]
  exact hw.min_le hn ⟨b, hb, rfl⟩

/-- The internally chosen lowest ACTUAL coefficient exponent, with no supplied diagram. -/
def actualInitialExponent (m : MonomialOrder (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) : Fin n →₀ ℕ :=
  Classical.choose (exists_actualInitialExponent m F hF)

/-- Both actual coefficient properties of the internally selected minimum. -/
theorem actualInitialExponent_spec (m : MonomialOrder (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) :
    MvPowerSeries.coeff (actualInitialExponent m F hF) F ≠ 0 ∧
      ∀ b, MvPowerSeries.coeff b F ≠ 0 → m.toSyn (actualInitialExponent m F hF) ≤ m.toSyn b :=
  Classical.choose_spec (exists_actualInitialExponent m F hF)

/-- Every genuinely lower coefficient vanishes. -/
theorem coeff_eq_zero_of_lt_actualInitialExponent (m : MonomialOrder (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) (b : Fin n →₀ ℕ)
    (hb : m.toSyn b < m.toSyn (actualInitialExponent m F hF)) :
    MvPowerSeries.coeff b F = 0 := by
  by_contra hc
  exact (not_le_of_gt hb) ((actualInitialExponent_spec m F hF).2 b hc)

/-- The actual nonzero coefficient and lower vanishing uniquely characterize the minimum. -/
theorem actualInitialExponent_eq_of_coefficients (m : MonomialOrder (Fin n))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) (a : Fin n →₀ ℕ)
    (ha : MvPowerSeries.coeff a F ≠ 0)
    (hlow : ∀ b, m.toSyn b < m.toSyn a → MvPowerSeries.coeff b F = 0) :
    actualInitialExponent m F hF = a := by
  apply m.toSyn.injective
  apply le_antisymm ((actualInitialExponent_spec m F hF).2 a ha)
  by_contra h
  exact (actualInitialExponent_spec m F hF).1 (hlow _ (lt_of_not_ge h))

/-- Genuine finite-antidiagonal multiplication retains precisely the two actual leading coefficients. -/
theorem coeff_mul_actualInitialExponent (m : MonomialOrder (Fin n))
    (F G : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) (hG : G ≠ 0) :
    MvPowerSeries.coeff (actualInitialExponent m F hF + actualInitialExponent m G hG) (F*G)=
      MvPowerSeries.coeff (actualInitialExponent m F hF) F *
        MvPowerSeries.coeff (actualInitialExponent m G hG) G := by
  classical
  let a := actualInitialExponent m F hF
  let b := actualInitialExponent m G hG
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_single_of_mem (a,b) (by simp [a,b])
  rintro ⟨u,v⟩ huv hne
  have he : m.toSyn u + m.toSyn v = m.toSyn a + m.toSyn b := by
    rw [← map_add, ← map_add]
    exact congrArg m.toSyn (Finset.mem_antidiagonal.mp huv)
  rcases trichotomy_of_add_eq_add he with hh | hh | hh
  · exact False.elim (hne (by
      congr 1
      · exact m.toSyn.injective hh.1
      · exact m.toSyn.injective hh.2))
  · rw [coeff_eq_zero_of_lt_actualInitialExponent m F hF u hh, zero_mul]
  · rw [coeff_eq_zero_of_lt_actualInitialExponent m G hG v hh, mul_zero]

/-- The minimum of a genuine formal product is the sum of its internally proved minima. -/
theorem actualInitialExponent_mul (m : MonomialOrder (Fin n))
    (F G : MvPowerSeries (Fin n) ℂ) (hF : F ≠ 0) (hG : G ≠ 0) :
    actualInitialExponent m (F*G) (mul_ne_zero hF hG)=
      actualInitialExponent m F hF + actualInitialExponent m G hG := by
  apply actualInitialExponent_eq_of_coefficients
  · rw [coeff_mul_actualInitialExponent]
    exact mul_ne_zero (actualInitialExponent_spec m F hF).1 (actualInitialExponent_spec m G hG).1
  · intro c hc
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨u,v⟩ huv
    have hlt : m.toSyn u < m.toSyn (actualInitialExponent m F hF) ∨
        m.toSyn v < m.toSyn (actualInitialExponent m G hG) := by
      by_contra h
      push Not at h
      have hs := add_le_add h.1 h.2
      rw [← map_add,← map_add,Finset.mem_antidiagonal.mp huv] at hs
      exact (not_le_of_gt hc) hs
    rcases hlt with hu | hv
    · rw [coeff_eq_zero_of_lt_actualInitialExponent m F hF u hu,zero_mul]
    · rw [coeff_eq_zero_of_lt_actualInitialExponent m G hG v hv,mul_zero]

/-- Every true formal monomial has its literal nonzero coefficient. -/
theorem actualMonomial_ne_zero (a : Fin n →₀ ℕ) :
    MvPowerSeries.monomial a (1 : ℂ) ≠ 0 := by
  intro h
  have he := congrArg (MvPowerSeries.coeff a) h
  simp at he

/-- Its actual minimum is its original exponent. -/
theorem actualInitialExponent_monomial (m : MonomialOrder (Fin n)) (a : Fin n →₀ ℕ) :
    actualInitialExponent m (MvPowerSeries.monomial a (1 : ℂ)) (actualMonomial_ne_zero a)=a := by
  apply actualInitialExponent_eq_of_coefficients
  · simp
  · intro b hb
    have hne : b ≠ a := by intro h; subst b; exact lt_irrefl _ hb
    simp [MvPowerSeries.coeff_monomial,hne]

/-- The whole ACTUAL ideal defines its diagram by its own genuine nonzero series. -/
def actualInitialDiagram (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Set (Fin n →₀ ℕ) :=
  {a | ∃ F ∈ I, ∃ hF : F ≠ 0, actualInitialExponent m F hF=a}

/-- Actual multiplication by a true monomial proves closure under every original exponent shift. -/
theorem actualInitialDiagram_add (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a b : Fin n →₀ ℕ) (ha : a ∈ actualInitialDiagram m I) :
    b+a ∈ actualInitialDiagram m I := by
  obtain ⟨F,hI,hF,he⟩ := ha
  refine ⟨MvPowerSeries.monomial b 1*F,I.mul_mem_left _ hI,
    mul_ne_zero (actualMonomial_ne_zero b) hF,?_⟩
  rw [actualInitialExponent_mul m _ _ (actualMonomial_ne_zero b) hF,
    actualInitialExponent_monomial,he]

/-- The real diagram is upper for the SAME pointwise exponent order. -/
theorem actualInitialDiagram_upper (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a c : Fin n →₀ ℕ) (ha : a ∈ actualInitialDiagram m I) (hac : a ≤ c) :
    c ∈ actualInitialDiagram m I := by
  have h := actualInitialDiagram_add m I a (c-a) ha
  simpa only [tsub_add_cancel_of_le hac] using h

/-- The actual zero ideal has no nonzero coefficient witness. -/
theorem actualInitialDiagram_bot (m : MonomialOrder (Fin n)) :
    actualInitialDiagram m (⊥ : Ideal (MvPowerSeries (Fin n) ℂ))=∅ := by
  ext a
  constructor
  · rintro ⟨F,hF,hne,_⟩
    exact False.elim (hne (by simpa using hF))
  · simp

/-- Dickson's lemma applies to the genuine minimal exponents of the true whole diagram. -/
theorem actualInitialDiagram_vertices_finite (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    {a | Minimal (· ∈ actualInitialDiagram m I) a}.Finite :=
  WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)

/-- The finite vertex set is constructed from the ACTUAL whole ideal. -/
def actualInitialVertices (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Finset (Fin n →₀ ℕ) :=
  (actualInitialDiagram_vertices_finite m I).toFinset

/-- Every actual diagram exponent lies above one of its internally constructed actual vertices. -/
theorem mem_actualInitialDiagram_iff_vertex_le (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (c : Fin n →₀ ℕ) :
    c ∈ actualInitialDiagram m I ↔ ∃ a ∈ actualInitialVertices m I, a ≤ c := by
  constructor
  · intro hc
    obtain ⟨a,ha,hmin⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ actualInitialDiagram m I) c hc
    exact ⟨a,by simpa [actualInitialVertices] using hmin,ha⟩
  · rintro ⟨a,ha,hac⟩
    have hm : Minimal (· ∈ actualInitialDiagram m I) a := by
      simpa [actualInitialVertices] using ha
    exact actualInitialDiagram_upper m I a c hm.prop hac

/-- Each true vertex internally supplies a monic GENUINE member of the SAME whole ideal. -/
theorem exists_actual_monic_vertex_series (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : Fin n →₀ ℕ) (ha : a ∈ actualInitialVertices m I) :
    ∃ F ∈ I, ∃ hF : F ≠ 0, actualInitialExponent m F hF=a ∧ MvPowerSeries.coeff a F=1 := by
  have hm : Minimal (· ∈ actualInitialDiagram m I) a := by
    simpa [actualInitialVertices] using ha
  obtain ⟨G,hG,hne,he⟩ := hm.prop
  have hc : MvPowerSeries.coeff a G ≠ 0 := he ▸ (actualInitialExponent_spec m G hne).1
  let F := MvPowerSeries.C (MvPowerSeries.coeff a G)⁻¹*G
  have hcoeff : MvPowerSeries.coeff a F=1 := by
    dsimp only [F]
    rw [MvPowerSeries.coeff_C_mul,inv_mul_cancel₀ hc]
  have hF : F ≠ 0 := by
    intro hz
    have hzero : MvPowerSeries.coeff a F=0 := by rw [hz,map_zero]
    exact one_ne_zero (hcoeff.symm.trans hzero)
  refine ⟨F,I.mul_mem_left _ hG,hF,?_,hcoeff⟩
  apply actualInitialExponent_eq_of_coefficients
  · rw [hcoeff]; exact one_ne_zero
  · intro b hb
    dsimp only [F]
    rw [MvPowerSeries.coeff_C_mul,coeff_eq_zero_of_lt_actualInitialExponent m G hne b (he.symm ▸ hb),mul_zero]

/-- The genuine degree-first minimum detects exactly the true formal variable powers. -/
theorem mem_formal_variables_pow_iff_degree_initialExponent (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ≠ 0) (q : ℕ) :
    F ∈ genuineFormalVariables n ^ q ↔
      q ≤ normalExponentDegree (actualInitialExponent MonomialOrder.degLex F hF) := by
  rw [mem_genuineFormalVariables_pow_iff_coefficients_zero]
  constructor
  · intro h
    by_contra hlt
    exact (actualInitialExponent_spec MonomialOrder.degLex F hF).1
      (h _ (lt_of_not_ge hlt))
  · intro h a ha
    apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex F hF a
    apply (MonomialOrder.degLex_lt_iff).mpr
    apply (Finsupp.DegLex.lt_iff).mpr
    left
    simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using lt_of_lt_of_le ha h

end
end Hironaka.HironakaActualFormalInitialDiagram
