/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualReducedFormalStandardBasis
import Hironaka.Resolution.HironakaActualFormalCoordinatePowerDivision

/-! Genuine whole recursion for specified monic vertex members, including the actual reduced basis. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualReducedBasisDivision
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision
variable {n : ℕ}

/-- Actual original ideal members and their genuine monic vertex coefficients; no division input. -/
structure ActualMonicVertexFamily (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) where
  series : actualInitialVertices m I → MvPowerSeries (Fin n) ℂ
  mem : ∀ a, series a ∈ I
  monic : ∀ a : actualInitialVertices m I, MvPowerSeries.coeff (a : Fin n →₀ ℕ) (series a) = 1
  lower : ∀ (a : actualInitialVertices m I) (b : Fin n →₀ ℕ), m.toSyn b < m.toSyn (a : Fin n →₀ ℕ) → MvPowerSeries.coeff b (series a) = 0

/-- The specified family's SAME actual series. -/
def familyVertexSeries (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily m I) (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ := B.series a

theorem familyVertexSeries_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (a : actualInitialVertices m I) :
    MvPowerSeries.coeff (a : Fin n →₀ ℕ) (familyVertexSeries m I B a) = 1 := B.monic a

theorem familyVertexSeries_coefficient_lower (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (a : actualInitialVertices m I) (b : Fin n →₀ ℕ)
    (hb : m.toSyn b < m.toSyn (a : Fin n →₀ ℕ)) :
    MvPowerSeries.coeff b (familyVertexSeries m I B a) = 0 := B.lower a b hb

/-- Actual well-founded coefficient recursion; every recursive call is strictly lower. -/
def familyDivisionCoefficient (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) : ℂ :=
  (InvImage.wf m.toSyn (wellFounded_lt : WellFounded ((· < ·) : m.syn → m.syn → Prop))).fix
    (C := fun _ => ℂ) (fun d rec =>
      MvPowerSeries.coeff d F -
        ∑ a : actualInitialVertices m I, ∑ p ∈ Finset.antidiagonal d,
          if h : m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn d then
            if HironakaActualFormalVertexDivision.actualDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
              rec (p.1+(a : Fin n →₀ ℕ)) h *
                MvPowerSeries.coeff p.2 (familyVertexSeries m I B a)
            else 0
          else 0) c

/-- The actual recursive correction at an exponent, expressed with the completed coefficient function. -/
def familyDivisionTail (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) : ℂ :=
  ∑ a : actualInitialVertices m I, ∑ p ∈ Finset.antidiagonal c,
    if m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c then
      if HironakaActualFormalVertexDivision.actualDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
        familyDivisionCoefficient m I B F (p.1+(a : Fin n →₀ ℕ)) *
          MvPowerSeries.coeff p.2 (familyVertexSeries m I B a)
      else 0
    else 0

/-- The defining genuine recursion equation, without any caller coefficient solution. -/
theorem familyDivisionCoefficient_eq (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (F : MvPowerSeries (Fin n) ℂ) (c : Fin n →₀ ℕ) :
    familyDivisionCoefficient m I B F c=MvPowerSeries.coeff c F-familyDivisionTail m I B F c := by
  rw [familyDivisionCoefficient,WellFounded.fix_eq]
  simp only [familyDivisionTail,familyDivisionCoefficient,dite_eq_ite]

/-- Genuine formal quotient series have the ACTUAL disjoint owner coefficients. -/
def familyFormalQuotient (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) (a : actualInitialVertices m I) : MvPowerSeries (Fin n) ℂ :=
  fun b => if HironakaActualFormalVertexDivision.actualDivisionOwner m I (b+(a : Fin n →₀ ℕ))=some a then
    familyDivisionCoefficient m I B F (b+(a : Fin n →₀ ℕ)) else 0

/-- The genuine remainder has zero coefficients at EVERY true diagram exponent. -/
def familyFormalRemainder (m : MonomialOrder (Fin n)) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ :=
  fun c => if c ∈ actualInitialDiagram m I then 0 else familyDivisionCoefficient m I B F c

/-- A nonzero actual quotient coefficient forces the SAME genuine owner part. -/
theorem familyFormalQuotient_support (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (b : Fin n →₀ ℕ)
    (hb : MvPowerSeries.coeff b (familyFormalQuotient m I B F a) ≠ 0) :
    HironakaActualFormalVertexDivision.actualDivisionOwner m I (b+(a : Fin n →₀ ℕ))=some a := by
  by_contra h
  exact hb (by simp [MvPowerSeries.coeff_apply,familyFormalQuotient,h])

/-- The actual remainder has no nonzero coefficient in the ACTUAL whole ideal diagram. -/
theorem familyFormalRemainder_coefficient_diagram (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (c : Fin n →₀ ℕ) (hc : c ∈ actualInitialDiagram m I) :
    MvPowerSeries.coeff c (familyFormalRemainder m I B F)=0 := by
  simp [MvPowerSeries.coeff_apply,familyFormalRemainder,hc]

private theorem family_quotient_monomial_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) :
    MvPowerSeries.coeff c (familyFormalQuotient m I B F a * MvPowerSeries.monomial a 1)=
      if HironakaActualFormalVertexDivision.actualDivisionOwner m I c=some a then familyDivisionCoefficient m I B F c else 0 := by
  rw [MvPowerSeries.coeff_mul_monomial]
  by_cases hac : (a : Fin n →₀ ℕ) ≤ c
  · simp [hac,MvPowerSeries.coeff_apply,familyFormalQuotient,tsub_add_cancel_of_le hac]
  · have ho : HironakaActualFormalVertexDivision.actualDivisionOwner m I c ≠ some a := fun h => hac (HironakaActualFormalVertexDivision.actualDivisionOwner_le m I c a h)
    simp [hac,ho]

private theorem family_quotient_tail_summand (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) (p : (Fin n →₀ ℕ) × (Fin n →₀ ℕ))
    (hp : p ∈ Finset.antidiagonal c) :
    MvPowerSeries.coeff p.1 (familyFormalQuotient m I B F a) *
        MvPowerSeries.coeff p.2 (familyVertexSeries m I B a-MvPowerSeries.monomial a 1)=
      if m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c then
        if HironakaActualFormalVertexDivision.actualDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
          familyDivisionCoefficient m I B F (p.1+(a : Fin n →₀ ℕ)) *
            MvPowerSeries.coeff p.2 (familyVertexSeries m I B a)
        else 0
      else 0 := by
  have he : p.1+p.2=c := Finset.mem_antidiagonal.mp hp
  by_cases hpa : p.2=(a : Fin n →₀ ℕ)
  · have hs : p.1+(a : Fin n →₀ ℕ)=c := hpa ▸ he
    simp [map_sub,hpa,familyVertexSeries_coefficient,hs]
  · have hm : MvPowerSeries.coeff p.2 (MvPowerSeries.monomial (a : Fin n →₀ ℕ) (1 : ℂ))=0 := by
      simp [MvPowerSeries.coeff_monomial,hpa]
    rw [map_sub,hm,sub_zero]
    by_cases hs : m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c
    · rw [if_pos hs]
      simp only [MvPowerSeries.coeff_apply,familyFormalQuotient,ite_mul,zero_mul]
    · have hz : MvPowerSeries.coeff p.2 (familyVertexSeries m I B a)=0 := by
        by_contra hne
        have hle : m.toSyn (a : Fin n →₀ ℕ) ≤ m.toSyn p.2 := by
          by_contra h
          exact hne (familyVertexSeries_coefficient_lower m I B a p.2 (lt_of_not_ge h))
        have hlt : m.toSyn (a : Fin n →₀ ℕ) < m.toSyn p.2 :=
          lt_of_le_of_ne hle (fun h => hpa (m.toSyn.injective h.symm))
        apply hs
        rw [← he,map_add,map_add]
        exact add_lt_add_of_le_of_lt (le_refl _) hlt
      rw [if_neg hs,hz,mul_zero]

private theorem family_quotient_product_coefficient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (F : MvPowerSeries (Fin n) ℂ)
    (a : actualInitialVertices m I) (c : Fin n →₀ ℕ) :
    MvPowerSeries.coeff c (familyFormalQuotient m I B F a * familyVertexSeries m I B a)=
      (if HironakaActualFormalVertexDivision.actualDivisionOwner m I c=some a then familyDivisionCoefficient m I B F c else 0)+
      ∑ p ∈ Finset.antidiagonal c,
        if m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c then
          if HironakaActualFormalVertexDivision.actualDivisionOwner m I (p.1+(a : Fin n →₀ ℕ))=some a then
            familyDivisionCoefficient m I B F (p.1+(a : Fin n →₀ ℕ)) *
              MvPowerSeries.coeff p.2 (familyVertexSeries m I B a)
          else 0
        else 0 := by
  have he : familyVertexSeries m I B a=MvPowerSeries.monomial a 1+
      (familyVertexSeries m I B a-MvPowerSeries.monomial a 1) := by abel
  conv_lhs => rw [he,mul_add,map_add]
  rw [family_quotient_monomial_coefficient]
  congr 1
  rw [MvPowerSeries.coeff_mul]
  exact Finset.sum_congr rfl (fun p hp => family_quotient_tail_summand m I B F a c p hp)

/-- EVERY actual series has a WHOLE genuine finite-antidiagonal division identity. -/
theorem family_formal_vertex_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (F : MvPowerSeries (Fin n) ℂ) :
    F=(∑ a : actualInitialVertices m I, familyFormalQuotient m I B F a*familyVertexSeries m I B a)+
      familyFormalRemainder m I B F := by
  apply MvPowerSeries.ext
  intro c
  rw [map_add,map_sum]
  simp_rw [family_quotient_product_coefficient]
  rw [Finset.sum_add_distrib]
  change MvPowerSeries.coeff c F=
    (∑ a : actualInitialVertices m I,
      if HironakaActualFormalVertexDivision.actualDivisionOwner m I c=some a then familyDivisionCoefficient m I B F c else 0)+
    familyDivisionTail m I B F c+MvPowerSeries.coeff c (familyFormalRemainder m I B F)
  cases ho : HironakaActualFormalVertexDivision.actualDivisionOwner m I c with
  | none =>
      have hc := (HironakaActualFormalVertexDivision.actualDivisionOwner_eq_none_iff m I c).mp ho
      simp only [reduceCtorEq,ite_false,Finset.sum_const_zero,zero_add]
      have hr : MvPowerSeries.coeff c (familyFormalRemainder m I B F)=familyDivisionCoefficient m I B F c := by
        change (if c ∈ actualInitialDiagram m I then 0 else familyDivisionCoefficient m I B F c)=_
        exact if_neg hc
      rw [hr,familyDivisionCoefficient_eq]
      ring
  | some a =>
      have hc : c ∈ actualInitialDiagram m I := by
        by_contra hc
        have hn := (HironakaActualFormalVertexDivision.actualDivisionOwner_eq_none_iff m I c).mpr hc
        rw [ho] at hn
        cases hn
      simp only [Option.some.injEq,Finset.sum_ite_eq,Finset.mem_univ,if_true]
      rw [familyFormalRemainder_coefficient_diagram m I B F c hc,add_zero,familyDivisionCoefficient_eq]
      exact (sub_add_cancel _ _).symm

/-- For a true whole ideal member the actual internally constructed remainder vanishes. -/
theorem familyFormalRemainder_eq_zero_of_mem (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ I) :
    familyFormalRemainder m I B F=0 := by
  have hs : (∑ a : actualInitialVertices m I, familyFormalQuotient m I B F a*familyVertexSeries m I B a) ∈ I :=
    I.sum_mem (fun a _ => I.mul_mem_left _ (B.mem a))
  have he : familyFormalRemainder m I B F=F-
      ∑ a : actualInitialVertices m I, familyFormalQuotient m I B F a*familyVertexSeries m I B a := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (family_formal_vertex_division m I B F).symm
  have hr : familyFormalRemainder m I B F ∈ I := by rw [he]; exact I.sub_mem hF hs
  by_contra hne
  let c := actualInitialExponent m (familyFormalRemainder m I B F) hne
  have hc : c ∈ actualInitialDiagram m I := ⟨familyFormalRemainder m I B F,hr,hne,rfl⟩
  exact (actualInitialExponent_spec m (familyFormalRemainder m I B F) hne).1
    (familyFormalRemainder_coefficient_diagram m I B F c hc)

/-- Actual whole ideal membership is expressed by the internally constructed genuine quotient coefficients. -/
theorem family_formal_ideal_member_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ I) :
    F=∑ a : actualInitialVertices m I, familyFormalQuotient m I B F a*familyVertexSeries m I B a := by
  have h := family_formal_vertex_division m I B F
  rw [familyFormalRemainder_eq_zero_of_mem m I B F hF,add_zero] at h
  exact h

/-- Internally constructed actual monic vertex series generate BOTH sides of the original WHOLE formal ideal. -/
theorem family_formal_ideal_eq_span_vertex_series (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) :
    I=Ideal.span (range (familyVertexSeries m I B)) := by
  apply le_antisymm
  · intro F hF
    rw [family_formal_ideal_member_division m I B F hF]
    apply Ideal.sum_mem
    intro a _
    apply Ideal.mul_mem_left
    exact Ideal.subset_span ⟨a,rfl⟩
  · apply Ideal.span_le.mpr
    rintro G ⟨a,rfl⟩
    exact B.mem a

/-- The genuine recursion preserves every actual weight compatible with its true vertex coefficients. -/
theorem familyDivisionCoefficient_eq_zero_of_weight_lt (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (w : Fin n → ℕ) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      Finsupp.weight w b < Finsupp.weight w (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (familyVertexSeries m I B a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → MvPowerSeries.coeff c F=0) :
    ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → familyDivisionCoefficient m I B F c=0 := by
  intro c
  have hwf := InvImage.wf m.toSyn (wellFounded_lt : WellFounded ((· < ·) : m.syn → m.syn → Prop))
  induction c using hwf.induction with
  | h c ih =>
      intro hc
      rw [familyDivisionCoefficient_eq,hF c hc]
      have ht : familyDivisionTail m I B F c=0 := by
        unfold familyDivisionTail
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro p hp
        by_cases hs : m.toSyn (p.1+(a : Fin n →₀ ℕ)) < m.toSyn c
        · rw [if_pos hs]
          split_ifs
          · by_cases hz : MvPowerSeries.coeff p.2 (familyVertexSeries m I B a)=0
            · rw [hz,mul_zero]
            · have hle : Finsupp.weight w (a : Fin n →₀ ℕ) ≤ Finsupp.weight w p.2 := by
                by_contra h
                exact hz (hvertex a p.2 (lt_of_not_ge h))
              have he : Finsupp.weight w p.1+Finsupp.weight w p.2=Finsupp.weight w c := by
                rw [← map_add,Finset.mem_antidiagonal.mp hp]
              have hsmall : Finsupp.weight w (p.1+(a : Fin n →₀ ℕ)) < d := by
                rw [map_add]
                exact lt_of_le_of_lt ((Nat.add_le_add_left hle _).trans (le_of_eq he)) hc
              rw [ih _ hs hsmall,zero_mul]
          · rfl
        · rw [if_neg hs]
      rw [ht,sub_self]

/-- The SAME genuine quotient series have the actual shifted weight bounds. -/
theorem familyFormalQuotient_coefficient_weight_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (w : Fin n → ℕ) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      Finsupp.weight w b < Finsupp.weight w (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (familyVertexSeries m I B a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → MvPowerSeries.coeff c F=0)
    (a : actualInitialVertices m I) (b : Fin n →₀ ℕ)
    (hb : Finsupp.weight w b+Finsupp.weight w (a : Fin n →₀ ℕ) < d) :
    MvPowerSeries.coeff b (familyFormalQuotient m I B F a)=0 := by
  have hz := familyDivisionCoefficient_eq_zero_of_weight_lt m I B w d F hvertex hF
    (b+(a : Fin n →₀ ℕ)) (by rwa [map_add])
  change (if HironakaActualFormalVertexDivision.actualDivisionOwner m I (b+(a : Fin n →₀ ℕ))=some a then
    familyDivisionCoefficient m I B F (b+(a : Fin n →₀ ℕ)) else 0)=0
  split_ifs <;> simp only [hz]

/-- The ACTUAL remainder retains the numerator's compatible weight filtration. -/
theorem familyFormalRemainder_coefficient_weight_bound (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (w : Fin n → ℕ) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      Finsupp.weight w b < Finsupp.weight w (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (familyVertexSeries m I B a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → MvPowerSeries.coeff c F=0)
    (c : Fin n →₀ ℕ) (hc : Finsupp.weight w c < d) :
    MvPowerSeries.coeff c (familyFormalRemainder m I B F)=0 := by
  have hz := familyDivisionCoefficient_eq_zero_of_weight_lt m I B w d F hvertex hF c hc
  change (if c ∈ actualInitialDiagram m I then 0 else familyDivisionCoefficient m I B F c)=0
  split_ifs <;> simp only [hz]

/-- Actual ideal members retain the genuine WHOLE division identity and the SAME centre-weight coefficient bounds. -/
theorem family_formal_ideal_member_weighted_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I) (w : Fin n → ℕ) (d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hmem : F ∈ I)
    (hvertex : ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
      Finsupp.weight w b < Finsupp.weight w (a : Fin n →₀ ℕ) →
        MvPowerSeries.coeff b (familyVertexSeries m I B a)=0)
    (hF : ∀ c : Fin n →₀ ℕ, Finsupp.weight w c < d → MvPowerSeries.coeff c F=0) :
    F=∑ a : actualInitialVertices m I, familyFormalQuotient m I B F a*familyVertexSeries m I B a ∧
      ∀ a : actualInitialVertices m I, ∀ b : Fin n →₀ ℕ,
        MvPowerSeries.coeff b (familyFormalQuotient m I B F a) ≠ 0 →
          d-Finsupp.weight w (a : Fin n →₀ ℕ) ≤ Finsupp.weight w b := by
  refine ⟨family_formal_ideal_member_division m I B F hmem,?_⟩
  intro a b hb
  have hle : d ≤ Finsupp.weight w b+Finsupp.weight w (a : Fin n →₀ ℕ) := by
    by_contra h
    exact hb (familyFormalQuotient_coefficient_weight_bound m I B w d F hvertex hF a b (lt_of_not_ge h))
  omega


/-- Every specified actual family gives the SAME genuine canonical normal representative. -/
theorem familyFormalRemainder_eq_canonical (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) :
    familyFormalRemainder m I B F =
      HironakaActualFormalVertexDivision.actualFormalRemainder m I F := by
  apply actualFormalRemainder_unique
  · have he : F - familyFormalRemainder m I B F =
        ∑ a : actualInitialVertices m I, familyFormalQuotient m I B F a * familyVertexSeries m I B a :=
      sub_eq_iff_eq_add.mpr (family_formal_vertex_division m I B F)
    rw [he]
    exact I.sum_mem (fun a _ => I.mul_mem_left _ (B.mem a))
  · exact familyFormalRemainder_coefficient_diagram m I B F

/-- Actual whole selected-coordinate powers, for the VERY SAME recursively constructed quotients. -/
theorem familyFormalQuotient_mem_coordinate_power (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (A : Set (Fin n)) (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hB : ∀ a : actualInitialVertices m I, familyVertexSeries m I B a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ))
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ q) (a : actualInitialVertices m I) :
    familyFormalQuotient m I B F a ∈ actualFormalCoordinateIdeal n A ^
      (q-Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)) := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff A _ _).mpr
  intro b hb
  apply familyFormalQuotient_coefficient_weight_bound m I B (actualCoordinateWeight A) q F
    (fun a => (mem_actualFormalCoordinateIdeal_pow_iff A _ _).mp (hB a))
    ((mem_actualFormalCoordinateIdeal_pow_iff A q F).mp hF) a b
  omega

/-- The canonical reduced members INTERNALLY supply every input to the true family recursion. -/
def actualReducedVertexFamily (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) : ActualMonicVertexFamily m I where
  series := actualReducedVertexSeries m I
  mem := actualReducedVertexSeries_mem m I
  monic := actualReducedVertexSeries_coefficient m I
  lower := actualReducedVertexSeries_coefficient_lower m I

/-- Genuine WHOLE division by the ACTUAL reduced basis, rather than arbitrary chosen monic members. -/
theorem actual_reduced_basis_entire_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (F : MvPowerSeries (Fin n) ℂ) :
    F = (∑ a : actualInitialVertices m I,
      familyFormalQuotient m I (actualReducedVertexFamily m I) F a * actualReducedVertexSeries m I a) +
        HironakaActualFormalVertexDivision.actualFormalRemainder m I F := by
  simpa only [familyFormalRemainder_eq_canonical, familyVertexSeries, actualReducedVertexFamily] using
    family_formal_vertex_division m I (actualReducedVertexFamily m I) F

/-- The SAME actual reduced-basis quotients retain genuine whole selected-centre powers. -/
theorem actual_reduced_basis_entire_filtered_division (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n)) (q : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hI : F ∈ I)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ q)
    (hB : ∀ a : actualInitialVertices m I, actualReducedVertexSeries m I a ∈
      actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)) :
    F = (∑ a : actualInitialVertices m I,
      familyFormalQuotient m I (actualReducedVertexFamily m I) F a * actualReducedVertexSeries m I a) ∧
      ∀ a : actualInitialVertices m I,
        familyFormalQuotient m I (actualReducedVertexFamily m I) F a ∈
          actualFormalCoordinateIdeal n A ^
            (q-Finsupp.weight (actualCoordinateWeight A) (a : Fin n →₀ ℕ)) := by
  exact ⟨family_formal_ideal_member_division m I (actualReducedVertexFamily m I) F hI,
    familyFormalQuotient_mem_coordinate_power m I (actualReducedVertexFamily m I) A q F hB hF⟩

end
end Hironaka.HironakaActualReducedBasisDivision
