/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalVertexDivision

/-! Canonical normal representatives and genuinely reduced formal vertex series. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualReducedFormalStandardBasis
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
variable {n : ℕ}

/-- The actual division remainder represents the same class modulo the whole ideal. -/
theorem sub_actualFormalRemainder_mem (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ) :
    F - actualFormalRemainder m I F ∈ I := by
  have he := actual_formal_vertex_division m I F
  have hs : F - actualFormalRemainder m I F =
      ∑ a : actualInitialVertices m I, actualFormalQuotient m I F a * actualVertexSeries m I a := by
    exact sub_eq_iff_eq_add.mpr he
  rw [hs]
  apply Ideal.sum_mem
  intro a _
  exact I.mul_mem_left _ (actualVertexSeries_spec m I a).1

/-- A member of the actual whole ideal supported outside its diagram is zero. -/
theorem eq_zero_of_mem_of_diagram_coefficients_zero (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ I)
    (hz : ∀ c ∈ actualInitialDiagram m I, MvPowerSeries.coeff c F = 0) : F = 0 := by
  by_contra hne
  exact (actualInitialExponent_spec m F hne).1 (hz _ ⟨F,hF,hne,rfl⟩)

/-- The actual remainder is the unique normal representative of its ideal class. -/
theorem actualFormalRemainder_unique (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F H : MvPowerSeries (Fin n) ℂ)
    (hclass : F - H ∈ I)
    (hnormal : ∀ c ∈ actualInitialDiagram m I, MvPowerSeries.coeff c H = 0) :
    H = actualFormalRemainder m I F := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mem_of_diagram_coefficients_zero m I
  · have he : H - actualFormalRemainder m I F =
        (F - actualFormalRemainder m I F) - (F - H) := by abel
    rw [he]
    exact I.sub_mem (sub_actualFormalRemainder_mem m I F) hclass
  · intro c hc
    rw [map_sub,hnormal c hc,actualFormalRemainder_coefficient_diagram m I F c hc,sub_self]

/-- Actual ideal membership is equivalent to vanishing of the canonical normal representative. -/
theorem actualFormalRemainder_eq_zero_iff (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalRemainder m I F = 0 ↔ F ∈ I := by
  constructor
  · intro h
    simpa only [h,sub_zero] using sub_actualFormalRemainder_mem m I F
  · exact actualFormalRemainder_eq_zero_of_mem m I F

/-- Uniqueness makes the actual normal representative additive. -/
theorem actualFormalRemainder_add (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F G : MvPowerSeries (Fin n) ℂ) :
    actualFormalRemainder m I (F + G) =
      actualFormalRemainder m I F + actualFormalRemainder m I G := by
  symm
  apply actualFormalRemainder_unique
  · have he : F + G - (actualFormalRemainder m I F + actualFormalRemainder m I G) =
        (F - actualFormalRemainder m I F) + (G - actualFormalRemainder m I G) := by abel
    rw [he]
    exact I.add_mem (sub_actualFormalRemainder_mem m I F) (sub_actualFormalRemainder_mem m I G)
  · intro c hc
    simp only [map_add,actualFormalRemainder_coefficient_diagram m I F c hc,
      actualFormalRemainder_coefficient_diagram m I G c hc,add_zero]

/-- The actual normal representative respects the genuine complex scalar action. -/
theorem actualFormalRemainder_smul (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (z : ℂ) (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalRemainder m I (z • F) = z • actualFormalRemainder m I F := by
  symm
  apply actualFormalRemainder_unique
  · rw [← smul_sub]
    simpa only [Algebra.smul_def] using
      I.mul_mem_left (algebraMap ℂ (MvPowerSeries (Fin n) ℂ) z) (sub_actualFormalRemainder_mem m I F)
  · intro c hc
    rw [map_smul,actualFormalRemainder_coefficient_diagram m I F c hc,smul_zero]

/-- Every series supported outside the actual diagram is its own normal representative. -/
theorem actualFormalRemainder_eq_self (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ)
    (hF : ∀ c ∈ actualInitialDiagram m I, MvPowerSeries.coeff c F = 0) :
    actualFormalRemainder m I F = F := by
  symm
  exact actualFormalRemainder_unique m I F F (by simp only [sub_self,I.zero_mem]) hF

/-- The canonical normal representative is idempotent. -/
theorem actualFormalRemainder_idempotent (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ) :
    actualFormalRemainder m I (actualFormalRemainder m I F) = actualFormalRemainder m I F :=
  actualFormalRemainder_eq_self m I _ (actualFormalRemainder_coefficient_diagram m I F)

/-- The genuine canonical normal-form projection, with the standard scalar action. -/
def actualFormalNormalProjection (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun := actualFormalRemainder m I
  map_add' := actualFormalRemainder_add m I
  map_smul' := actualFormalRemainder_smul m I

/-- The actual image consists exactly of series supported outside the whole ideal diagram. -/
theorem mem_range_actualFormalNormalProjection_iff (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (H : MvPowerSeries (Fin n) ℂ) :
    H ∈ Set.range (actualFormalNormalProjection m I) ↔
      ∀ c ∈ actualInitialDiagram m I, MvPowerSeries.coeff c H = 0 := by
  constructor
  · rintro ⟨F,rfl⟩
    exact actualFormalRemainder_coefficient_diagram m I F
  · intro hH
    exact ⟨H,actualFormalRemainder_eq_self m I H hH⟩

/-- The coefficient recursion preserves every genuine initial segment of its monomial order. -/
theorem actualDivisionCoefficient_eq_zero_of_lt (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ)
    (a : Fin n →₀ ℕ)
    (hF : ∀ c, m.toSyn c < m.toSyn a → MvPowerSeries.coeff c F = 0) :
    ∀ c, m.toSyn c < m.toSyn a → actualDivisionCoefficient m I F c = 0 := by
  intro c
  have hwf := InvImage.wf m.toSyn (wellFounded_lt : WellFounded ((· < ·) : m.syn → m.syn → Prop))
  induction c using hwf.induction with
  | h c ih =>
      intro hc
      rw [actualDivisionCoefficient_eq,hF c hc]
      have ht : actualDivisionTail m I F c = 0 := by
        unfold actualDivisionTail
        apply Finset.sum_eq_zero
        intro b _
        apply Finset.sum_eq_zero
        intro p _
        by_cases hs : m.toSyn (p.1 + (b : Fin n →₀ ℕ)) < m.toSyn c
        · rw [if_pos hs]
          split_ifs
          · rw [ih _ hs (lt_trans hs hc),zero_mul]
          · rfl
        · rw [if_neg hs]
      rw [ht,sub_self]

/-- Canonical normal representatives preserve the actual initial segment, without extra weight hypotheses. -/
theorem actualFormalRemainder_coefficient_lower (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ)
    (a : Fin n →₀ ℕ)
    (hF : ∀ c, m.toSyn c < m.toSyn a → MvPowerSeries.coeff c F = 0)
    (c : Fin n →₀ ℕ) (hc : m.toSyn c < m.toSyn a) :
    MvPowerSeries.coeff c (actualFormalRemainder m I F) = 0 := by
  have hz := actualDivisionCoefficient_eq_zero_of_lt m I F a hF c hc
  change (if c ∈ actualInitialDiagram m I then 0 else actualDivisionCoefficient m I F c) = 0
  split_ifs <;> simp only [hz]

/-- The reduced vertex member is the monomial minus its genuine canonical normal representative. -/
def actualReducedVertexSeries (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I) :
    MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.monomial (a : Fin n →₀ ℕ) 1 -
    actualFormalRemainder m I (MvPowerSeries.monomial (a : Fin n →₀ ℕ) 1)

/-- The reduced vertex member belongs to the original whole ideal. -/
theorem actualReducedVertexSeries_mem (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I) :
    actualReducedVertexSeries m I a ∈ I :=
  sub_actualFormalRemainder_mem m I _

/-- On the entire diagram the reduced member has exactly its single monic vertex coefficient. -/
theorem actualReducedVertexSeries_coefficient_diagram (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I)
    (c : Fin n →₀ ℕ) (hc : c ∈ actualInitialDiagram m I) :
    MvPowerSeries.coeff c (actualReducedVertexSeries m I a) =
      if c = (a : Fin n →₀ ℕ) then 1 else 0 := by
  simp only [actualReducedVertexSeries,map_sub,
    actualFormalRemainder_coefficient_diagram m I _ c hc,sub_zero,
    MvPowerSeries.coeff_monomial]

/-- The reduced member has the original monic vertex coefficient. -/
theorem actualReducedVertexSeries_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I) :
    MvPowerSeries.coeff (a : Fin n →₀ ℕ) (actualReducedVertexSeries m I a) = 1 := by
  have ha : (a : Fin n →₀ ℕ) ∈ actualInitialDiagram m I :=
    (mem_actualInitialDiagram_iff_vertex_le m I _).mpr ⟨a,a.property,le_rfl⟩
  simpa only [ite_true] using actualReducedVertexSeries_coefficient_diagram m I a a ha

/-- Every coefficient below the genuine vertex still vanishes after reduction. -/
theorem actualReducedVertexSeries_coefficient_lower (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I)
    (c : Fin n →₀ ℕ) (hc : m.toSyn c < m.toSyn (a : Fin n →₀ ℕ)) :
    MvPowerSeries.coeff c (actualReducedVertexSeries m I a) = 0 := by
  have hm : ∀ b, m.toSyn b < m.toSyn (a : Fin n →₀ ℕ) →
      MvPowerSeries.coeff b (MvPowerSeries.monomial (a : Fin n →₀ ℕ) (1 : ℂ)) = 0 := by
    intro b hb
    have hne : b ≠ (a : Fin n →₀ ℕ) := by
      intro he
      exact (ne_of_lt hb) (congrArg m.toSyn he)
    simp only [MvPowerSeries.coeff_monomial,if_neg hne]
  rw [actualReducedVertexSeries,map_sub,hm c hc,
    actualFormalRemainder_coefficient_lower m I _ a hm c hc,sub_self]

/-- The internally reduced vertex member is genuinely nonzero. -/
theorem actualReducedVertexSeries_ne_zero (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I) :
    actualReducedVertexSeries m I a ≠ 0 := by
  intro he
  have hc := actualReducedVertexSeries_coefficient m I a
  rw [he,map_zero] at hc
  exact zero_ne_one hc

/-- Reduction preserves the actual initial exponent, rather than just a chosen label. -/
theorem actualReducedVertexSeries_initialExponent (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I) :
    actualInitialExponent m (actualReducedVertexSeries m I a)
      (actualReducedVertexSeries_ne_zero m I a) = (a : Fin n →₀ ℕ) := by
  apply actualInitialExponent_eq_of_coefficients
  · rw [actualReducedVertexSeries_coefficient]
    exact one_ne_zero
  · exact actualReducedVertexSeries_coefficient_lower m I a

/-- These conditions uniquely determine the reduced member inside the same whole ideal. -/
theorem actualReducedVertexSeries_unique (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I)
    (G : MvPowerSeries (Fin n) ℂ) (hG : G ∈ I)
    (hcoeff : ∀ c ∈ actualInitialDiagram m I, MvPowerSeries.coeff c G =
      if c = (a : Fin n →₀ ℕ) then 1 else 0) : G = actualReducedVertexSeries m I a := by
  apply sub_eq_zero.mp
  apply eq_zero_of_mem_of_diagram_coefficients_zero m I
  · exact I.sub_mem hG (actualReducedVertexSeries_mem m I a)
  · intro c hc
    rw [map_sub,hcoeff c hc,actualReducedVertexSeries_coefficient_diagram m I a c hc,sub_self]

/-- An actual subideal with the entire same diagram is already the whole ideal. -/
theorem ideal_eq_of_le_of_diagram_le (m : MonomialOrder (Fin n))
    (I J : Ideal (MvPowerSeries (Fin n) ℂ)) (hJI : J ≤ I)
    (hdiag : actualInitialDiagram m I ⊆ actualInitialDiagram m J) : I = J := by
  apply le_antisymm _ hJI
  intro F hF
  apply (actualFormalRemainder_eq_zero_iff m J F).mp
  have hR : actualFormalRemainder m J F ∈ I := by
    have he : actualFormalRemainder m J F = F - (F - actualFormalRemainder m J F) := by abel
    rw [he]
    exact I.sub_mem hF (hJI (sub_actualFormalRemainder_mem m J F))
  apply eq_zero_of_mem_of_diagram_coefficients_zero m I _ hR
  intro c hc
  exact actualFormalRemainder_coefficient_diagram m J F c (hdiag hc)

/-- The canonical reduced vertex members generate the original whole formal ideal. -/
theorem actual_formal_ideal_eq_span_reduced_vertex_series (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    I = Ideal.span (range (actualReducedVertexSeries m I)) := by
  let J := Ideal.span (range (actualReducedVertexSeries m I))
  have hJI : J ≤ I := by
    apply Ideal.span_le.mpr
    rintro G ⟨a,rfl⟩
    exact actualReducedVertexSeries_mem m I a
  apply ideal_eq_of_le_of_diagram_le m I J hJI
  intro c hc
  obtain ⟨a,ha,hac⟩ := (mem_actualInitialDiagram_iff_vertex_le m I c).mp hc
  let v : actualInitialVertices m I := ⟨a,ha⟩
  have hav : a ∈ actualInitialDiagram m J :=
    ⟨actualReducedVertexSeries m I v,Ideal.subset_span ⟨v,rfl⟩,
      actualReducedVertexSeries_ne_zero m I v,actualReducedVertexSeries_initialExponent m I v⟩
  exact actualInitialDiagram_upper m J a c hav hac

end
end Hironaka.HironakaActualReducedFormalStandardBasis
