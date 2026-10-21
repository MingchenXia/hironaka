/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualOriginalReducedVertexBasis
/-!
# Exact canonical analytic owner quotients and genuine initial syzygy lifts

A least actual shifted initial exponent proves whole owner-supported quotient
relations are zero. Thus the convergent original canonical division quotients
have EXACTLY the genuine recursive formal Taylor series and retain the same
shifted whole maximal powers. Actual approximate analytic relations can then
be corrected to genuine SAME-family analytic syzygies. A literal homogeneous
relation on the actual canonical initial forms internally supplies the next
order of error, yielding analytic syzygies with the prescribed initial parts.
No quotient/convergence/filtration/syzygy/tracking certificate is supplied.

Blueprint: `hironaka-actual-owner-analytic-division-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators Topology
namespace Hironaka.HironakaActualOwnerAnalyticDivision
noncomputable section
open HironakaActualFormalInitialDiagram HironakaActualReducedBasisDivision
  HironakaActualFormalVertexDivision HironakaActualReducedFormalStandardBasis
variable {n : ℕ}

/-- A genuine WHOLE relation with disjoint actual owner supports has no nonzero quotient component. -/
theorem owner_supported_relation_eq_zero (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (H : actualInitialVertices m I → MvPowerSeries (Fin n) ℂ)
    (hOwner : ∀ a β,actualDivisionOwner m I (β+a.val)≠some a→MvPowerSeries.coeff β (H a)=0)
    (hRel : (∑ a,B.series a*H a)=0) : ∀ a,H a=0 := by
  have hB (a : actualInitialVertices m I) : B.series a≠0 := by
    intro h
    have hc := B.monic a
    rw [h,map_zero] at hc
    exact zero_ne_one hc
  have hLead (a : actualInitialVertices m I) : actualInitialExponent m (B.series a) (hB a)=a.val :=
    actualInitialExponent_eq_of_coefficients m (B.series a) (hB a) a.val (by rw [B.monic];exact one_ne_zero) (B.lower a)
  let β := fun a : actualInitialVertices m I => if h : H a≠0 then actualInitialExponent m (H a) h else 0
  have hβ (a : actualInitialVertices m I) (ha : H a≠0) : β a=actualInitialExponent m (H a) ha := by simp only [β,dif_pos ha]
  have hOwn (a : actualInitialVertices m I) (ha : H a≠0) : actualDivisionOwner m I (a.val+β a)=some a := by
    by_contra h
    have hz := hOwner a (β a) (by simpa only [add_comm] using h)
    exact (actualInitialExponent_spec m (H a) ha).1 (by simpa only [hβ a ha] using hz)
  have hProd (a : actualInitialVertices m I) (ha : H a≠0) :
      actualInitialExponent m (B.series a*H a) (mul_ne_zero (hB a) ha)=a.val+β a := by
    rw [actualInitialExponent_mul m (B.series a) (H a) (hB a) ha,hLead,←hβ a ha]
  have hCoeff (a : actualInitialVertices m I) (ha : H a≠0) :
      MvPowerSeries.coeff (a.val+β a) (B.series a*H a)≠0 := by
    have h := coeff_mul_actualInitialExponent m (B.series a) (H a) (hB a) ha
    rw [hLead,←hβ a ha,B.monic,one_mul] at h
    rw [h]
    simpa only [hβ a ha] using (actualInitialExponent_spec m (H a) ha).1
  intro a₀
  by_contra ha₀
  let S := Finset.univ.filter (fun a : actualInitialVertices m I => H a≠0)
  have hS : S.Nonempty := ⟨a₀,by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and];exact ha₀⟩
  obtain ⟨a,ha,hmin⟩ := Finset.exists_min_image S (fun a => m.toSyn (a.val+β a)) hS
  have haH : H a≠0 := (Finset.mem_filter.mp ha).2
  have hOther (b : actualInitialVertices m I) (hba : b≠a) :
      MvPowerSeries.coeff (a.val+β a) (B.series b*H b)=0 := by
    by_cases hbH : H b=0
    · simp only [hbH,mul_zero,map_zero]
    · have hbS : b∈S := by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and];exact hbH
      have hle := hmin b hbS
      have hne : m.toSyn (a.val+β a)≠m.toSyn (b.val+β b) := by
        intro he
        have hc := m.toSyn.injective he
        have ho := (hOwn a haH).symm.trans (hc ▸ hOwn b hbH)
        exact hba (Option.some.inj ho).symm
      apply coeff_eq_zero_of_lt_actualInitialExponent m _ (mul_ne_zero (hB b) hbH)
      rw [hProd b hbH]
      exact lt_of_le_of_ne hle hne
  have hc := congrArg (MvPowerSeries.coeff (a.val+β a)) hRel
  rw [map_sum,map_zero] at hc
  have hs : (∑ b : actualInitialVertices m I,MvPowerSeries.coeff (a.val+β a) (B.series b*H b))=
      MvPowerSeries.coeff (a.val+β a) (B.series a*H a) :=
    Finset.sum_eq_single a (fun b _ hb => hOther b hb) (by simp)
  rw [hs] at hc
  exact hCoeff a haH hc

/-- Every genuine owner-supported whole division with the canonical remainder has exactly the SAME recursive formal quotients. -/
theorem owner_division_quotients_eq_familyFormalQuotient (m : MonomialOrder (Fin n))
    (I : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily m I)
    (F : MvPowerSeries (Fin n) ℂ) (H : actualInitialVertices m I → MvPowerSeries (Fin n) ℂ)
    (hOwner : ∀ a β,actualDivisionOwner m I (β+a.val)≠some a→MvPowerSeries.coeff β (H a)=0)
    (hDiv : F=(∑ a,B.series a*H a)+actualFormalRemainder m I F) :
    ∀ a,H a=familyFormalQuotient m I B F a := by
  have hrec := family_formal_vertex_division m I B F
  rw [familyFormalRemainder_eq_canonical] at hrec
  have hrec' : F=(∑ a,B.series a*familyFormalQuotient m I B F a)+actualFormalRemainder m I F := by
    simpa only [familyVertexSeries,mul_comm] using hrec
  have hsum := add_right_cancel (hDiv.symm.trans hrec')
  have hrel : (∑ a,B.series a*(H a-familyFormalQuotient m I B F a))=0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,hsum,sub_self]
  have hz := owner_supported_relation_eq_zero m I B (fun a => H a-familyFormalQuotient m I B F a)
    (by
      intro a β hne
      have hf : MvPowerSeries.coeff β (familyFormalQuotient m I B F a)=0 := by
        by_contra h
        exact hne (familyFormalQuotient_support m I B F a β h)
      rw [map_sub,hOwner a β hne,hf,sub_self]) hrel
  exact fun a => sub_eq_zero.mp (hz a)

open HolGerm HironakaActualOriginalFormalTaylor HironakaActualOriginalReducedVertexBasis
  HironakaRelativeNormalMonomialBasis

/-- Original analytic division produces the literal recursive Taylor quotients and their WHOLE shifted maximal powers. -/
theorem exists_original_filtered_reduced_vertex_division
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (g : HolGerm (ComplexModel (0+n)))
    (q : ℕ) (hg : g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^q) :
    ∃ (H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)))
      (s : HolGerm (ComplexModel (0+n))),
      g=(∑ a,originalReducedVertexBasis J a*H a)+s ∧
      originalTaylorAlgHom n s=actualFormalRemainder MonomialOrder.degLex
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) (originalTaylorAlgHom n g) ∧
      (∀ a,originalTaylorAlgHom n (H a)=familyFormalQuotient MonomialOrder.degLex
        (Ideal.map (originalTaylorAlgHom n).toRingHom J)
        (actualReducedVertexFamily MonomialOrder.degLex (Ideal.map (originalTaylorAlgHom n).toRingHom J))
        (originalTaylorAlgHom n g) a) ∧
      ∀ a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(q-normalExponentDegree a.val) := by
  obtain ⟨H,s,hdiv,hs,hOwner⟩ := exists_original_reduced_vertex_division J g
  let I := Ideal.map (originalTaylorAlgHom n).toRingHom J
  let B := actualReducedVertexFamily MonomialOrder.degLex I
  have hTaylor : ∀ a,originalTaylorAlgHom n (H a)=familyFormalQuotient MonomialOrder.degLex I B (originalTaylorAlgHom n g) a := by
    apply owner_division_quotients_eq_familyFormalQuotient MonomialOrder.degLex I B (originalTaylorAlgHom n g)
      (fun a => originalTaylorAlgHom n (H a)) hOwner
    have h := congrArg (originalTaylorAlgHom n) hdiv
    rw [map_add,map_sum,hs] at h
    simpa only [map_mul,originalReducedVertexBasis_taylor,B,I,actualReducedVertexFamily] using h
  have hw (α : Fin n →₀ ℕ) : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) α=normalExponentDegree α := by
    rw [← Finsupp.degree_eq_weight_one]
    simp only [Finsupp.degree_eq_sum,normalExponentDegree]
  have hvertex (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) I) (β : Fin n →₀ ℕ)
      (hβ : Finsupp.weight (fun _ : Fin n => (1 : ℕ)) β<Finsupp.weight (fun _ : Fin n => (1 : ℕ)) a.val) :
      MvPowerSeries.coeff β (familyVertexSeries MonomialOrder.degLex I B a)=0 := by
    apply actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex I a β
    apply MonomialOrder.degLex_lt_iff.mpr
    apply Finsupp.DegLex.lt_iff.mpr
    left
    simpa only [Finsupp.degree_eq_weight_one,ofDegLex_toDegLex] using hβ
  refine ⟨H,s,hdiv,hs,hTaylor,?_⟩
  intro a
  apply (mem_original_maximal_pow_iff_formal_coefficients_zero n _ (H a)).mpr
  intro β hβ
  rw [hTaylor]
  apply familyFormalQuotient_coefficient_weight_bound MonomialOrder.degLex I B (fun _ => 1) q
    (originalTaylorAlgHom n g) hvertex
    (by
      intro α hα
      exact (mem_original_maximal_pow_iff_formal_coefficients_zero n q g).mp hg α (by rwa [hw] at hα)) a β
  rw [hw,hw]
  omega

/-- An actual finite-order relation error is corrected to a genuine SAME-family analytic syzygy with exact shifted orders. -/
theorem exists_original_canonical_syzygy_of_relation_error
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (P : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)))
    (q : ℕ) (hP : (∑ a,originalReducedVertexBasis J a*P a)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^q) :
    ∃ C : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
      (∑ a,originalReducedVertexBasis J a*C a)=0 ∧
      ∀ a,P a-C a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(q-normalExponentDegree a.val) := by
  let E := ∑ a,originalReducedVertexBasis J a*P a
  have hE : E∈J := Ideal.sum_mem _ fun a _ => Ideal.mul_mem_right _ _ (originalReducedVertexBasis_mem J a)
  obtain ⟨Q,s,hdiv,hs,_hTaylor,hQ⟩ := exists_original_filtered_reduced_vertex_division J E q hP
  have hs0 : s=0 := by
    apply originalTaylorAlgHom_injective n
    rw [map_zero,hs,actualFormalRemainder_eq_zero_of_mem]
    exact Ideal.mem_map_of_mem _ hE
  rw [hs0,add_zero] at hdiv
  refine ⟨fun a => P a-Q a,?_,?_⟩
  · simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←hdiv,sub_self]
  · intro a
    simpa only [sub_sub_cancel] using hQ a

private theorem coefficient_product_eq_initial_of_homogeneous_left
    (H F : MvPowerSeries (Fin n) ℂ) (D d : ℕ) (hd : d≤D) (hH : H.IsHomogeneous (D-d))
    (hF : ∀ α : Fin n →₀ ℕ,α.degree<d→MvPowerSeries.coeff α F=0)
    (α : Fin n →₀ ℕ) (hα : α.degree≤D) :
    MvPowerSeries.coeff α (H*F)=MvPowerSeries.coeff α (H*MvPowerSeries.homogeneousComponent d F) := by
  rw [MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨u,v⟩ huv
  by_cases hu : MvPowerSeries.coeff u H=0
  · simp only [hu,zero_mul]
  · have hud : u.degree=D-d := by
      by_contra h
      exact hu (hH.coeff_eq_zero h)
    have hs : u.degree+v.degree=α.degree := by
      rw [← map_add]
      exact congrArg (fun β : Fin n →₀ ℕ => β.degree) (Finset.mem_antidiagonal.mp huv)
    have hv : v.degree≤d := by omega
    rw [MvPowerSeries.coeff_homogeneousComponent]
    by_cases hve : v.degree=d
    · rw [if_pos hve]
    · rw [if_neg hve,hF v (by omega),mul_zero]

/-- A TRUE homogeneous relation on the SAME original initial forms internally yields an actual analytic syzygy with precisely those leading components. -/
theorem exists_original_initial_syzygy_lift
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (P : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)))
    (D : ℕ) (hD : ∀ a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J),normalExponentDegree a.val≤D)
    (hP : ∀ a,(originalTaylorAlgHom n (P a)).IsHomogeneous (D-normalExponentDegree a.val))
    (hRel : (∑ a,originalTaylorAlgHom n (P a)*MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
      (originalTaylorAlgHom n (originalReducedVertexBasis J a)))=0) :
    ∃ C : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
      (∑ a,originalReducedVertexBasis J a*C a)=0 ∧
      (∀ a,MvPowerSeries.homogeneousComponent (D-normalExponentDegree a.val)
        (originalTaylorAlgHom n (C a))=originalTaylorAlgHom n (P a)) ∧
      ∀ a,P a-C a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(D+1-normalExponentDegree a.val) := by
  have hLow (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) (β : Fin n →₀ ℕ) (hβ : β.degree<normalExponentDegree a.val) :
      MvPowerSeries.coeff β (originalTaylorAlgHom n (originalReducedVertexBasis J a))=0 := by
    rw [originalReducedVertexBasis_taylor]
    apply actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex _ a β
    apply MonomialOrder.degLex_lt_iff.mpr
    apply Finsupp.DegLex.lt_iff.mpr
    left
    simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using hβ
  have hError : (∑ a,originalReducedVertexBasis J a*P a)∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(D+1) := by
    apply (mem_original_maximal_pow_iff_formal_coefficients_zero n (D+1) _).mpr
    intro α hα
    rw [map_sum,map_sum]
    simp_rw [map_mul]
    have hαD : α.degree≤D := by simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using Nat.le_of_lt_succ hα
    have hc := congrArg (MvPowerSeries.coeff α) hRel
    rw [map_sum,map_zero] at hc
    calc
      _=(∑ a,MvPowerSeries.coeff α (originalTaylorAlgHom n (P a)*MvPowerSeries.homogeneousComponent
        (normalExponentDegree a.val) (originalTaylorAlgHom n (originalReducedVertexBasis J a)))) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [mul_comm]
          exact coefficient_product_eq_initial_of_homogeneous_left _ _ D _ (hD a) (hP a) (hLow a) α hαD
      _=0 := hc
  obtain ⟨C,hC,hCorr⟩ := exists_original_canonical_syzygy_of_relation_error J P (D+1) hError
  refine ⟨C,hC,?_,hCorr⟩
  intro a
  apply MvPowerSeries.ext
  intro β
  rw [MvPowerSeries.coeff_homogeneousComponent]
  by_cases hβ : β.degree=D-normalExponentDegree a.val
  · rw [if_pos hβ]
    have hz := (mem_original_maximal_pow_iff_formal_coefficients_zero n _ (P a-C a)).mp (hCorr a) β
      (by
        have ha := hD a
        have he : normalExponentDegree β=β.degree := by simp only [normalExponentDegree,Finsupp.degree_eq_sum]
        rw [he,hβ]
        omega)
    rw [map_sub,map_sub] at hz
    exact (sub_eq_zero.mp hz).symm
  · rw [if_neg hβ]
    exact (MvPowerSeries.IsHomogeneous.coeff_eq_zero (hP a) hβ).symm

end
end Hironaka.HironakaActualOwnerAnalyticDivision
