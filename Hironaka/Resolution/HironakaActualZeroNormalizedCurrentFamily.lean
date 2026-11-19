import Hironaka.Resolution.HironakaActualNormalZeroAnalyticSaturation
import Hironaka.Resolution.HironakaActualInheritedWholePrefixNormalization
import Hironaka.Resolution.HironakaActualInheritedSourcePermutationFamily

/-! A genuine SECOND-SOURCE analytic state for the same zero-chart normalized
members. Natural source powers and actual marked orders internally produce the
current whole diagram, current vertex labels, a monic analytic current family,
its whole ideal and every historical whole prefix. No target family or diagram
certificate is an input. This zero-direction producer does not assert arbitrary
direction analytic adaptation, canonical-centre position or original G8 closure.
Blueprint: hironaka-actual-zero-normalized-current-family-extension.tex. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualZeroNormalizedCurrentFamily
noncomputable section
open HolGerm HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
 HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
 HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
 HironakaActualFormalStrictGenerators HironakaActualRelativeStandardnessInheritedDivision
 HironakaActualOriginalFormalHSTransfer
 HironakaActualNormalZeroOwnerSupport HironakaActualNormalZeroOwnerConverse
 HironakaActualNormalZeroFormalSaturation HironakaActualNormalZeroAnalyticSaturation
 HironakaActualInheritedWholePrefixNormalization HironakaActualInheritedSourcePermutationFamily
 HironakaActualInheritedCurrentSourceRelabel
variable {n : ℕ}

private theorem cast_vertex_val {V W : Finset (Fin n →₀ ℕ)} (h : V=W) (a : V) :
    (sourceVertexSetCast h a).val=a.val := by
  cases h
  rfl

private theorem cast_family_range {V W : Finset (Fin n →₀ ℕ)} (h : V=W)
    (F : V → HolGerm (ComplexModel n)) :
    range (sourceRawFamilyCast h F)=range F := by
  ext g
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨a,rfl⟩ := (sourceVertexSetCast h).surjective a
    exact ⟨a,(sourceRawFamilyCast_apply h F a).symm⟩
  · rintro ⟨a,rfl⟩
    exact ⟨sourceVertexSetCast h a,sourceRawFamilyCast_apply h F a⟩

/-- The target CURRENT family consists of the exact actual source quotients.
Its vertex cast is obtained from the internally proved whole diagram identity;
all whole prefixes are properties of that current family and can be consumed
at a further zero-chart source. -/
theorem exists_same_zero_normalized_current_family
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hmem : ∀a,G.germs a∈I) (e : Fin n)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici e)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticZeroNormalizedVertex n I G e hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k) :
    let J:=sameAnalyticZeroNormalizedIdeal n I G e hp
    actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal n J)=
      actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal n I) ∧
    ∃hV : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)=
        actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n J),
      ∃G' : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n J),
        (∀a,G'.germs (sourceVertexSetCast hV a)=sameAnalyticZeroNormalizedVertex n I G e hp a) ∧
        Ideal.span (range G'.germs)=J ∧
        (∀a,G'.germs a∈J) ∧
        (∀k,ActualInheritedPrefixReducedAt G' k) ∧
        ∀ℓ,hilbertSamuelValue J ℓ=hilbertSamuelValue I ℓ := by
  let K:=analyticZeroTaylorIdeal n I
  let B:=analyticZeroMonicFamily n I G hmem
  let H:=sameAnalyticZeroNormalizedVertex n I G e hp
  let J:=sameAnalyticZeroNormalizedIdeal n I G e hp
  have hpF (a : actualInitialVertices MonomialOrder.degLex K) :
      B.series a∈actualFormalCoordinateIdeal n (Set.Ici e)^normalExponentDegree a.val :=
    actualTaylor_mem_coordinateCentre_pow (Set.Ici e) _ (G.germs a) (hp a)
  have hTaylor (a : actualInitialVertices MonomialOrder.degLex K) :
      actualUnshiftedTaylorAlgHom n (H a)=sameMonicZeroNormalizedVertex K B e hpF a :=
    actualTaylor_sameAnalyticZeroNormalizedVertex n I G e hp a
  have hOrdersF (a : actualInitialVertices MonomialOrder.degLex K) :
      sameMonicZeroNormalizedVertex K B e hpF a∈genuineFormalVariables n^normalExponentDegree a.val := by
    have h:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom (hOrder a)
    rw [map_actualUnshifted_maximal_pow] at h
    rwa [←hTaylor]
  obtain ⟨hPure,hDiagram,_hHS⟩ := actual_normal_zero_strict_diagram_and_hs_of_inherited_marked_orders
    K K (⟨B.series,B.monic,B.lower⟩ : InheritedMonicFamily MonomialOrder.degLex K)
    rfl B.mem e hpF hOrdersF
  have hD : actualInitialDiagram MonomialOrder.degLex (analyticZeroTaylorIdeal n J)=
      actualInitialDiagram MonomialOrder.degLex K := by
    rw [show analyticZeroTaylorIdeal n J=
      actualFormalStrictTransform K (Set.Ici e) e (Set.mem_Ici.mpr le_rfl) (fun _=>0) from
        map_sameAnalyticZeroNormalizedIdeal n I G hmem e hp]
    exact hDiagram
  have hheads (a : actualInitialVertices MonomialOrder.degLex K) :
      MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (H a))=1 ∧
      ∀β,MonomialOrder.degLex.toSyn β<MonomialOrder.degLex.toSyn a.val →
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (H a))=0 := by
    rw [hTaylor]
    have hWeight : Finsupp.weight (actualCoordinateWeight (Set.Ici e\{e})) a.val=
        normalExponentDegree a.val := by
      rw [Finsupp.weight_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i≤e
      · simp only [hPure a i hi,zero_smul]
      · have hm : i∈Set.Ici e\{e}:=⟨le_of_lt (lt_of_not_ge hi),ne_of_gt (lt_of_not_ge hi)⟩
        simp only [actualCoordinateWeight,if_pos hm,smul_eq_mul,mul_one]
    constructor
    · exact (coeff_actualNormalizedFormalMember_zero_of_pure_exponent (Set.Ici e) e
        (Set.mem_Ici.mpr le_rfl) _ (B.series a) (hpF a) a.val hWeight).trans (B.monic a)
    · obtain ⟨hne,hhead⟩:=actualNormalizedFormalMember_zero_head_of_order e a.val
        (B.series a) (hPure a) (B.monic a) (B.lower a) (hpF a) (hOrdersF a)
      intro β hβ
      apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hne β
      rwa [hhead]
  have hRawPrefix : ∀k : ℕ,∀a : actualInitialVertices MonomialOrder.degLex K,
      k<normalExponentDegree a.val →∀v : actualInitialVertices MonomialOrder.degLex K,
        normalExponentDegree v.val≤k →∀α : Fin n →₀ ℕ,v.val≤α →
          MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (H a))=0 := by
    intro k a ha v hv α hvα
    have hs : (↑v.val.support : Set (Fin n))⊆Set.Ici e\{e} := by
      intro i hi
      have hgt : e < i := lt_of_not_ge (fun hie => (Finsupp.mem_support_iff.mp hi) (hPure v i hie))
      exact ⟨le_of_lt hgt,ne_of_gt hgt⟩
    rw [hTaylor]
    exact actualNormalizedFormalMember_cone_zero (Set.Ici e) e (Set.mem_Ici.mpr le_rfl)
      (fun _=>0) v.val hs (normalExponentDegree a.val) (by omega) (B.series a)
      (hpF a) (hred k a ha v hv) α hvα
  let hV:=actualInitialVertices_eq_of_diagram_eq hD.symm
  let G' : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n J):=
    { germs:=sourceRawFamilyCast hV H
      monic:=by
        intro a
        obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV).surjective a
        rw [sourceRawFamilyCast_apply,cast_vertex_val]
        exact (hheads a).1
      lower:=by
        intro a β hβ
        obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV).surjective a
        rw [sourceRawFamilyCast_apply]
        exact (hheads a).2 β (by simpa only [cast_vertex_val] using hβ) }
  have hspan : Ideal.span (range G'.germs)=J := by
    change Ideal.span (range (sourceRawFamilyCast hV H))=Ideal.span (range H)
    rw [cast_family_range]
  refine ⟨hD,hV,G',fun a=>sourceRawFamilyCast_apply hV H a,hspan,?_,?_,?_⟩
  · intro a
    change G'.germs a∈J
    have hm : G'.germs a∈Ideal.span (range G'.germs):=Ideal.mem_span_range_self (x:=a)
    simpa only [hspan] using hm
  · intro k a ha v hv α hvα
    obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV).surjective a
    obtain ⟨v,rfl⟩:=(sourceVertexSetCast hV).surjective v
    change MvPowerSeries.coeff α
      (actualUnshiftedTaylorAlgHom n (sourceRawFamilyCast hV H (sourceVertexSetCast hV a)))=0
    rw [sourceRawFamilyCast_apply]
    exact hRawPrefix k a (by simpa only [cast_vertex_val] using ha)
      v (by simpa only [cast_vertex_val] using hv) α
      (by simpa only [cast_vertex_val] using hvα)
  · exact hilbertSamuelValue_same_zero_ideal_eq_of_marked_orders n I G hmem e hp hOrder

end
end Hironaka.HironakaActualZeroNormalizedCurrentFamily
