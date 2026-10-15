/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalInitialDiagram

/-! Genuine coefficient-recursive formal division by internally constructed actual vertex series. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFormalVertexDivision
noncomputable section
open HironakaActualFormalInitialDiagram
variable {n : ℕ}

/-- Every actual diagram exponent internally supplies an actual dominating vertex. -/
theorem exists_actualDivisionOwner (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (c : Fin n →₀ ℕ) (hc : c ∈ actualInitialDiagram m I) :
    ∃ a : actualInitialVertices m I, (a : Fin n →₀ ℕ) ≤ c := by
  obtain ⟨a,ha,hac⟩ := (mem_actualInitialDiagram_iff_vertex_le m I c).mp hc
  exact ⟨⟨a,ha⟩,hac⟩

/-- The internally fixed owner partitions the ACTUAL diagram, with none outside it. -/
def actualDivisionOwner (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (c : Fin n →₀ ℕ) : Option (actualInitialVertices m I) :=
  if hc : c ∈ actualInitialDiagram m I then
    some (Classical.choose (exists_actualDivisionOwner m I c hc)) else none

/-- A genuine owner's actual vertex lies pointwise below its exponent. -/
theorem actualDivisionOwner_le (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (c : Fin n →₀ ℕ) (a : actualInitialVertices m I) (ha : actualDivisionOwner m I c=some a) :
    (a : Fin n →₀ ℕ) ≤ c := by
  unfold actualDivisionOwner at ha
  split_ifs at ha with hc
  · have he := Option.some.inj ha
    rw [← he]
    exact Classical.choose_spec (exists_actualDivisionOwner m I c hc)

/-- No owner occurs exactly outside the GENUINE whole ideal diagram. -/
theorem actualDivisionOwner_eq_none_iff (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (c : Fin n →₀ ℕ) :
    actualDivisionOwner m I c=none ↔ c ∉ actualInitialDiagram m I := by
  by_cases hc : c ∈ actualInitialDiagram m I <;> simp [actualDivisionOwner,hc]

/-- Each actual vertex supplies an internally chosen genuine monic series of the SAME whole ideal. -/
def actualVertexSeries (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ :=
  Classical.choose (exists_actual_monic_vertex_series m I a a.property)

/-- Actual ideal membership, nonvanishing, original vertex, and genuine monic coefficient. -/
theorem actualVertexSeries_spec (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices m I) :
    actualVertexSeries m I a ∈ I ∧ ∃ hF : actualVertexSeries m I a ≠ 0,
      actualInitialExponent m (actualVertexSeries m I a) hF=(a : Fin n →₀ ℕ) ∧
        MvPowerSeries.coeff (a : Fin n →₀ ℕ) (actualVertexSeries m I a)=1 :=
  Classical.choose_spec (exists_actual_monic_vertex_series m I a a.property)

/-- The actual lowest vertex coefficient is genuinely one. -/
theorem actualVertexSeries_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I) :
    MvPowerSeries.coeff (a : Fin n →₀ ℕ) (actualVertexSeries m I a)=1 :=
  (actualVertexSeries_spec m I a).2.choose_spec.2

/-- Every coefficient below its true vertex is zero. -/
theorem actualVertexSeries_coefficient_lower (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (a : actualInitialVertices m I) (b : Fin n →₀ ℕ)
    (hb : m.toSyn b < m.toSyn (a : Fin n →₀ ℕ)) :
    MvPowerSeries.coeff b (actualVertexSeries m I a)=0 := by
  obtain ⟨hF,he,_⟩ := (actualVertexSeries_spec m I a).2
  exact coeff_eq_zero_of_lt_actualInitialExponent m _ hF b (he.symm ▸ hb)

/-- Actual well-founded coefficient recursion; every recursive call is strictly lower. -/
def actualDivisionCoefficient (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) : ℂ :=
  (InvImage.wf m.toSyn (wellFounded_lt : WellFounded ((· < ·) : m.syn → m.syn → Prop))).fix
    (C := fun _ => ℂ) (fun d rec =>
      MvPowerSeries.coeff d F -
        ∑ a : actualInitialVertices m I, ∑ p ∈ Finset.antidiagonal d,
          if h : m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn d then
            if actualDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
              rec (p.1+(a : Fin n →₀ ℕ)) h *
                MvPowerSeries.coeff p.2 (actualVertexSeries m I a)
            else 0
          else 0) c

/-- The actual recursive correction at an exponent, expressed with the completed coefficient function. -/
def actualDivisionTail (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) : ℂ :=
  ∑ a : actualInitialVertices m I, ∑ p ∈ Finset.antidiagonal c,
    if m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c then
      if actualDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
        actualDivisionCoefficient m I F (p.1+(a : Fin n →₀ ℕ)) *
          MvPowerSeries.coeff p.2 (actualVertexSeries m I a)
      else 0
    else 0

/-- The defining genuine recursion equation, without any caller coefficient solution. -/
theorem actualDivisionCoefficient_eq (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) :
    actualDivisionCoefficient m I F c=MvPowerSeries.coeff c F-actualDivisionTail m I F c := by
  rw [actualDivisionCoefficient,WellFounded.fix_eq]
  simp only [actualDivisionTail,actualDivisionCoefficient,dite_eq_ite]

/-- Genuine formal quotient series have the ACTUAL disjoint owner coefficients. -/
def actualFormalQuotient (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (F : MvPowerSeries (Fin n) ℂ) (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ :=
  fun b => if actualDivisionOwner m I (b+(a : Fin n →₀ ℕ))=some a then
    actualDivisionCoefficient m I F (b+(a : Fin n →₀ ℕ)) else 0

/-- The genuine remainder has zero coefficients at EVERY true diagram exponent. -/
def actualFormalRemainder (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (F : MvPowerSeries (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ :=
  fun c => if c ∈ actualInitialDiagram m I then 0 else actualDivisionCoefficient m I F c

/-- A nonzero actual quotient coefficient forces the SAME genuine owner part. -/
theorem actualFormalQuotient_support (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (b : Fin n →₀ ℕ)
    (hb : MvPowerSeries.coeff b (actualFormalQuotient m I F a) ≠ 0) :
    actualDivisionOwner m I (b+(a : Fin n →₀ ℕ))=some a := by
  by_contra h
  exact hb (by simp [MvPowerSeries.coeff_apply,actualFormalQuotient,h])

/-- The actual remainder has no nonzero coefficient in the ACTUAL whole ideal diagram. -/
theorem actualFormalRemainder_coefficient_diagram (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ)
    (c : Fin n →₀ ℕ) (hc : c ∈ actualInitialDiagram m I) :
    MvPowerSeries.coeff c (actualFormalRemainder m I F)=0 := by
  simp [MvPowerSeries.coeff_apply,actualFormalRemainder,hc]

private theorem actual_quotient_monomial_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) :
    MvPowerSeries.coeff c (actualFormalQuotient m I F a * MvPowerSeries.monomial a 1)=
      if actualDivisionOwner m I c=some a then actualDivisionCoefficient m I F c else 0 := by
  rw [MvPowerSeries.coeff_mul_monomial]
  by_cases hac : (a : Fin n →₀ ℕ) ≤ c
  · simp [hac,MvPowerSeries.coeff_apply,actualFormalQuotient,tsub_add_cancel_of_le hac]
  · have ho : actualDivisionOwner m I c ≠ some a := fun h => hac (actualDivisionOwner_le m I c a h)
    simp [hac,ho]

private theorem actual_quotient_tail_summand (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) (p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ))
    (hp : p ∈ Finset.antidiagonal c) :
    MvPowerSeries.coeff p.1 (actualFormalQuotient m I F a) *
        MvPowerSeries.coeff p.2 (actualVertexSeries m I a-MvPowerSeries.monomial a 1)=
      if m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c then
        if actualDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
          actualDivisionCoefficient m I F (p.1+(a : Fin n →₀ ℕ)) *
            MvPowerSeries.coeff p.2 (actualVertexSeries m I a)
        else 0
      else 0 := by
  have he : p.1+p.2=c := Finset.mem_antidiagonal.mp hp
  by_cases hpa : p.2=(a : Fin n →₀ ℕ)
  · have hs : p.1+(a : Fin n →₀ ℕ)=c := hpa ▸ he
    simp [map_sub,hpa,actualVertexSeries_coefficient,hs]
  · have hm : MvPowerSeries.coeff p.2 (MvPowerSeries.monomial (a : Fin n →₀ ℕ) (1 : ℂ))=0 := by
      simp [MvPowerSeries.coeff_monomial,hpa]
    rw [map_sub,hm,sub_zero]
    by_cases hs : m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c
    · rw [if_pos hs]
      simp only [MvPowerSeries.coeff_apply,actualFormalQuotient,ite_mul,zero_mul]
    · have hz : MvPowerSeries.coeff p.2 (actualVertexSeries m I a)=0 := by
        by_contra hne
        have hle : m.toSyn (a : Fin n →₀ ℕ) ≤ m.toSyn p.2 := by
          by_contra h
          exact hne (actualVertexSeries_coefficient_lower m I a p.2 (lt_of_not_ge h))
        have hlt : m.toSyn (a : Fin n →₀ ℕ) < m.toSyn p.2 :=
          lt_of_le_of_ne hle (fun h => hpa (m.toSyn.injective h.symm))
        apply hs
        rw [← he,map_add,map_add]
        exact add_lt_add_of_le_of_lt (le_refl _) hlt
      rw [if_neg hs,hz,mul_zero]

private theorem actual_quotient_product_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) :
    MvPowerSeries.coeff c (actualFormalQuotient m I F a * actualVertexSeries m I a)=
      (if actualDivisionOwner m I c=some a then actualDivisionCoefficient m I F c else 0)+
      ∑ p ∈ Finset.antidiagonal c,
        if m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c then
          if actualDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
            actualDivisionCoefficient m I F (p.1+(a : Fin n →₀ ℕ)) *
              MvPowerSeries.coeff p.2 (actualVertexSeries m I a)
          else 0
        else 0 := by
  have he : actualVertexSeries m I a=MvPowerSeries.monomial a 1+
      (actualVertexSeries m I a-MvPowerSeries.monomial a 1) := by abel
  conv_lhs => rw [he,mul_add,map_add]
  rw [actual_quotient_monomial_coefficient]
  congr 1
  rw [MvPowerSeries.coeff_mul]
  exact Finset.sum_congr rfl (fun p hp => actual_quotient_tail_summand m I F a c p hp)

/-- EVERY actual series has a WHOLE genuine finite-antidiagonal division identity. -/
theorem actual_formal_vertex_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ) :
    F=(∑ a : actualInitialVertices m I, actualFormalQuotient m I F a*actualVertexSeries m I a)+
      actualFormalRemainder m I F := by
  apply MvPowerSeries.ext
  intro c
  rw [map_add,map_sum]
  simp_rw [actual_quotient_product_coefficient]
  rw [Finset.sum_add_distrib]
  change MvPowerSeries.coeff c F=
    (∑ a : actualInitialVertices m I,
      if actualDivisionOwner m I c=some a then actualDivisionCoefficient m I F c else 0)+
    actualDivisionTail m I F c+MvPowerSeries.coeff c (actualFormalRemainder m I F)
  cases ho : actualDivisionOwner m I c with
  | none =>
      have hc := (actualDivisionOwner_eq_none_iff m I c).mp ho
      simp only [reduceCtorEq,ite_false,Finset.sum_const_zero,zero_add]
      have hr : MvPowerSeries.coeff c (actualFormalRemainder m I F)=actualDivisionCoefficient m I F c := by
        change (if c ∈ actualInitialDiagram m I then 0 else actualDivisionCoefficient m I F c)=_
        exact if_neg hc
      rw [hr,actualDivisionCoefficient_eq]
      ring
  | some a =>
      have hc : c ∈ actualInitialDiagram m I := by
        by_contra hc
        have hn := (actualDivisionOwner_eq_none_iff m I c).mpr hc
        rw [ho] at hn
        cases hn
      simp only [Option.some.injEq,Finset.sum_ite_eq,Finset.mem_univ,if_true]
      rw [actualFormalRemainder_coefficient_diagram m I F c hc,add_zero,actualDivisionCoefficient_eq]
      exact (sub_add_cancel _ _).symm

/-- For a true whole ideal member the actual internally constructed remainder vanishes. -/
theorem actualFormalRemainder_eq_zero_of_mem (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ I) :
    actualFormalRemainder m I F=0 := by
  have hs : (∑ a : actualInitialVertices m I, actualFormalQuotient m I F a*actualVertexSeries m I a) ∈ I :=
    I.sum_mem (fun a _ => I.mul_mem_left _ (actualVertexSeries_spec m I a).1)
  have he : actualFormalRemainder m I F=F-
      ∑ a : actualInitialVertices m I, actualFormalQuotient m I F a*actualVertexSeries m I a := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (actual_formal_vertex_division m I F).symm
  have hr : actualFormalRemainder m I F ∈ I := by rw [he]; exact I.sub_mem hF hs
  by_contra hne
  let c := actualInitialExponent m (actualFormalRemainder m I F) hne
  have hc : c ∈ actualInitialDiagram m I := ⟨actualFormalRemainder m I F,hr,hne,rfl⟩
  exact (actualInitialExponent_spec m (actualFormalRemainder m I F) hne).1
    (actualFormalRemainder_coefficient_diagram m I F c hc)

/-- Actual whole ideal membership is expressed by the internally constructed genuine quotient coefficients. -/
theorem actual_formal_ideal_member_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ I) :
    F=∑ a : actualInitialVertices m I, actualFormalQuotient m I F a*actualVertexSeries m I a := by
  have h := actual_formal_vertex_division m I F
  rw [actualFormalRemainder_eq_zero_of_mem m I F hF,add_zero] at h
  exact h

/-- Internally constructed actual monic vertex series generate BOTH sides of the original WHOLE formal ideal. -/
theorem actual_formal_ideal_eq_span_vertex_series (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    I=Ideal.span (range (actualVertexSeries m I)) := by
  apply le_antisymm
  · intro F hF
    rw [actual_formal_ideal_member_division m I F hF]
    apply Ideal.sum_mem
    intro a _
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨a,rfl⟩
  · apply Ideal.span_le.mpr
    rintro G ⟨a,rfl⟩
    exact (actualVertexSeries_spec m I a).1

end
end Hironaka.HironakaActualFormalVertexDivision
