import Hironaka.Resolution.HironakaActualZeroNormalizedCurrentFamily
import Hironaka.Resolution.HironakaActualNormalAllDirectionGeometricConverse

/-! The same historical fixed selector becomes a selector on the internally
produced CURRENT zero-normalized analytic source, with every actual contact and
Jacobian transported. This supplies all source-side structures needed by the
next zero-chart marked-cut converse; no next centre, source powers at that
centre or repeated whole-HS presentation is postulated. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualZeroNormalizedCurrentSelector
noncomputable section
open HolGerm HironakaHolomorphicJetChartInvariance HironakaHolomorphicPointJets
 HironakaActualAnalyticBlowupTaylor
 HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualFixedInheritedSelector HironakaActualCoefficientPresentationCentrePower
 HironakaActualNormalZeroAnalyticSaturation HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualNormalAllDirectionGeometricConverse HironakaActualZeroNormalizedCurrentFamily
 HironakaActualInheritedSourcePermutationFamily HironakaActualInheritedNextBlockGraph
 HironakaActualCauchyCoefficientLimits HironakaActualFixedInheritedSelectorBlowup
 HironakaActualInheritedAnalyticBlockJacobian HironakaActualOriginalTaylorDerivatives
variable {n : ℕ}

private theorem same_zero_normalized_historical_selector_contact_and_jacobian
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hmem : ∀a,G.germs a∈I) (e : Fin n)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici e)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticZeroNormalizedVertex n I G e hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀k,actualFixedSelectorContactAt S G.germs k) :
    let H:=sameAnalyticZeroNormalizedVertex n I G e hp
    (∀k,actualFixedSelectorContactAt S H k) ∧
      ∀k,actualFixedSelectorJacobian S H k=actualFixedSelectorJacobian S G.germs k := by
  have hNormalOrders : ∀a,sameAnalyticNormalNormalizedVertex n I G e e le_rfl
      (fun _=>0) hp a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val :=
    hOrder
  obtain ⟨hpf,hAll⟩:=actual_normal_marked_orders_preserve_same_historical_selector n I G hmem
    e e le_rfl (fun _=>0) hp hNormalOrders S hred hadapt
  let H:=sameAnalyticZeroNormalizedVertex n I G e hp
  have hDerivative (k)
      (j : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) k) :
      actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S H (fixedSelectorBlockEssential k j))=
        actualNormalizedFixedSelectorDerivative G S k (Set.Ici e) e
          (Set.mem_Ici.mpr le_rfl) (fun _=>0) hpf j := by
    unfold actualFixedSelectorDerivative actualNormalizedFixedSelectorDerivative
    rw [actualTaylor_actualAnalyticMultiDerivative,actualTaylor_sameAnalyticZeroNormalizedVertex]
  constructor
  · intro k j
    apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ _).mpr
    rw [map_actualAnalyticCoordinateBlockIdeal_actualTaylor]
    have hm:=(hAll k).2.1 j
    rw [←hDerivative k j] at hm
    exact hm
  · intro k
    ext j i
    have heq:=congrArg (fun A=>A j i) ((hAll k).2.2.1)
    change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
      (actualFixedSelectorDerivative S H (fixedSelectorBlockEssential k j)))=_
    rw [←actualTaylor_coeff_zero,actualTaylor_actualAnalyticCoordinateDerivative,hDerivative k j]
    exact heq

/-- A complete CURRENT analytic zero-chart source, retaining the literal SAME
members and historical selector. The returned current family, membership,
whole prefixes and contacts are outputs rather than next-stage certificates. -/
theorem exists_same_zero_normalized_current_family_and_selector
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hmem : ∀a,G.germs a∈I) (e : Fin n)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici e)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticZeroNormalizedVertex n I G e hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀k,actualFixedSelectorContactAt S G.germs k) :
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
        (∀ℓ,hilbertSamuelValue J ℓ=hilbertSamuelValue I ℓ) ∧
        (∀k,actualFixedSelectorContactAt (sourceFixedSelectorCast hV S) G'.germs k) ∧
        ∀k,(actualFixedSelectorJacobian (sourceFixedSelectorCast hV S) G'.germs k).submatrix
          (sourceBlockCast hV k) (sourceBlockCast hV k)=actualFixedSelectorJacobian S G.germs k := by
  obtain ⟨hD,hV,G',hLiteral,hSpan,hMember,hPrefix,hHS⟩:=
    exists_same_zero_normalized_current_family I G hmem e hp hOrder hred
  let H:=sameAnalyticZeroNormalizedVertex n I G e hp
  have hFamily : G'.germs=sourceRawFamilyCast hV H := by
    funext a
    obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV).surjective a
    exact (hLiteral a).trans (sourceRawFamilyCast_apply hV H a).symm
  obtain ⟨hContact,hJac⟩:=same_zero_normalized_historical_selector_contact_and_jacobian
    I G hmem e hp hOrder S hred hadapt
  refine ⟨hD,hV,G',hLiteral,hSpan,hMember,hPrefix,hHS,?_,?_⟩
  · intro k
    rw [hFamily]
    exact (sourceFixedSelectorCast_contact hV S H k).mpr (hContact k)
  · intro k
    rw [hFamily,sourceFixedSelectorCast_jacobian]
    exact hJac k

end
end Hironaka.HironakaActualZeroNormalizedCurrentSelector
