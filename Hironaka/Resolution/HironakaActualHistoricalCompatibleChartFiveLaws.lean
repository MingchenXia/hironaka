import Hironaka.Resolution.HironakaActualHistoricalNormalizedWeakPresentation
import Hironaka.Resolution.HironakaActualHistoricalMovingCentreChart

/-! The actual compatible free centre chart retains ALL five laws of the
SAME moving source family, every old label/word/selector and the entire ideal.
No source or target monic family is reselected. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalCompatibleChartFiveLaws
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaActualHistoricalNormalizedWeakPresentation
  HironakaActualHistoricalCentreFilteredDivision HironakaActualHistoricalWholeJetFrames
  HironakaActualHistoricalPrefixJetFrames HironakaActualHistoricalFormalSupportedDivision
  HironakaRelativeNormalMonomialBasis HironakaActualCauchyMonomialDivision
  HironakaActualOriginalFormalHSTransfer HironakaActualFixedInheritedSelector
  HironakaActualHistoricalMovingPrefixSupport HironakaActualHistoricalMovingCentreChart
  HironakaActualCoefficientPresentationCentrePower HironakaHolomorphicJetMonomialSpan
  HironakaActualAnalyticBlockGraphTranslation HironakaActualAnalyticFormalNormalPowers
  HironakaActualCanonicalBlockJacobian HironakaActualInheritedAnalyticBlockJacobian
  HironakaActualInheritedNestedContactFlag
  HironakaHolomorphicJetChartInvariance

variable {n k : ℕ}

private theorem formal_power_iff_analytic (q : ℕ) (F : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n F∈genuineFormalVariables n^q ↔
      F∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^q :=
  (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).trans
    (actual_maximal_power_iff_formal_coefficients_zero n q F).symm

private theorem formal_power_map_iff
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (q : ℕ) (F : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n (E F)∈genuineFormalVariables n^q ↔
      actualUnshiftedTaylorAlgHom n F∈genuineFormalVariables n^q :=
  (formal_power_iff_analytic q (E F)).trans
    ((actual_maximal_power_map_algEquiv_iff E q F).trans (formal_power_iff_analytic q F).symm)

/-- The literal degree prefixes of the SAME family keep all their actual
whole and homogeneous frames under a genuine whole fixed-section action. -/
theorem actual_fixed_section_degree_prefix_frames
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n)) (B : Set (Fin n))
    (hSection : ∀F,actualBlockProjectionGermHom B (E F)=actualBlockProjectionGermHom B F)
    (w : Fin k → CoordinateWord n) (Γ : Fin k → HolGerm (ComplexModel n))
    (hMarked : ∀i,Γ i∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^
      normalExponentDegree (wordExponent (w i)))
    (hHeads : ∀i x,x∉B → wordExponent (w i) x=0)
    (hPrefix : ∀m,HistoricalDegreePrefixFrames w (fun i=>actualUnshiftedTaylorAlgHom n (Γ i)) m) :
    ∀m,HistoricalDegreePrefixFrames w (fun i=>actualUnshiftedTaylorAlgHom n (E (Γ i))) m := by
  intro m
  let v:=historicalDegreePrefixWords w m
  let p:=historicalDegreePrefixLabel w m
  have hWhole:=actual_historical_whole_jets_of_fixed_section E B hSection v
    (fun i=>Γ (p i)) (fun i=>hMarked (p i)) (fun i=>hHeads (p i)) (hPrefix m).1
  have hTargetMarked (i) : actualUnshiftedTaylorAlgHom n (E (Γ (p i)))∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (v i)):=
    (formal_power_iff_analytic _ _).mpr ((actual_maximal_power_map_algEquiv_iff E _ _).mpr (hMarked (p i)))
  refine ⟨hWhole,?_⟩
  intro d
  rw [historicalHomogeneousColumnMap_eq_operator]
  exact historicalHomogeneousOperator_bijective v
    (fun i=>actualUnshiftedTaylorAlgHom n (E (Γ (p i)))) hTargetMarked hWhole d

/-- Genuine fixed-section and essential-derivative geometry transports ALL
five source laws, exact original Jacobians and the ENTIRE actual member ideal. -/
theorem actual_compatible_source_action_five_laws
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (hSection : ∀F,actualBlockProjectionGermHom (fixedSelectorEssential V) (E F)=
      actualBlockProjectionGermHom (fixedSelectorEssential V) F)
    (hCoordinate : ∀i∈fixedSelectorEssential V,E (coordinateGerm i)=coordinateGerm i)
    (hDerivative : ∀β : Fin n →₀ ℕ,(∀i,i∉fixedSelectorEssential V → β i=0) →
      ∀F,actualAnalyticMultiDerivative β (E F)=E (actualAnalyticMultiDerivative β F)) :
    ActualHistoricalFivePointLaws S a w (fun v=>E (Γ v)) ∧
    (∀R,actualFixedSelectorJacobian S (fun v=>E (Γ v)) R=actualFixedSelectorJacobian S Γ R) ∧
    Ideal.span (range fun v=>E (Γ v))=Ideal.map E.toRingEquiv.toRingHom (Ideal.span (range Γ)) := by
  rcases hSource with ⟨hMarked,hWhole,hPrefix,hSupported,hContact,hCones⟩
  let B:=fixedSelectorEssential V
  have hHeads (v : V) (i : Fin n) (hi : i∉B) : v.val i=0 := by
    by_contra h
    exact hi ⟨v,h⟩
  have hHeadsFin (i : Fin k) (x : Fin n) (hx : x∉B) : wordExponent (w i) x=0 := by
    rw [hw]
    exact hHeads (a i) x hx
  have hMarkedAnal (i : Fin k) : Γ (a i)∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^
      normalExponentDegree (wordExponent (w i)):=
    (formal_power_iff_analytic _ _).mp (hMarked i).1
  have hWholeTarget:=actual_historical_whole_jets_of_fixed_section E B hSection w
    (fun i=>Γ (a i)) hMarkedAnal hHeadsFin hWhole
  have hPrefixTarget:=actual_fixed_section_degree_prefix_frames E B hSection w
    (fun i=>Γ (a i)) hMarkedAnal hHeadsFin hPrefix
  have hSupportedTarget:=actual_historical_whole_supported_division_of_fixed_section E B hSection w
    (fun i=>Γ (a i)) hMarkedAnal hHeadsFin hWhole hSupported
  have hBeta (j : fixedSelectorEssential V) (i : Fin n) (hi : i∉B) : fixedSelectorBeta S j i=0 := by
    simp only [fixedSelectorBeta,Finsupp.tsub_apply,hHeads (S.selected j) i hi,zero_tsub]
  have hSelected (j : fixedSelectorEssential V) :
      actualFixedSelectorDerivative S (fun v=>E (Γ v)) j=E (actualFixedSelectorDerivative S Γ j):=
    hDerivative (fixedSelectorBeta S j) (hBeta j) (Γ (S.selected j))
  have hBlockMap (R : ℕ) : Ideal.map E.toRingEquiv.toRingHom
      (actualAnalyticCoordinateBlockIdeal (fixedSelectorBlock V R))=
      actualAnalyticCoordinateBlockIdeal (fixedSelectorBlock V R) := by
    rw [actualAnalyticCoordinateBlockIdeal,Ideal.map_span]
    apply congrArg Ideal.span
    ext F
    constructor
    · rintro ⟨G,⟨i,hi,rfl⟩,hEq⟩
      have hiB : i∈B:=(fixedSelectorBlockEssential R ⟨i,hi⟩).property
      exact ⟨i,hi,(hCoordinate i hiB).symm.trans hEq⟩
    · rintro ⟨i,hi,rfl⟩
      have hiB : i∈B:=(fixedSelectorBlockEssential R ⟨i,hi⟩).property
      exact ⟨coordinateGerm i,⟨i,hi,rfl⟩,hCoordinate i hiB⟩
  have hContactTarget (R : ℕ) : actualFixedSelectorContactAt S (fun v=>E (Γ v)) R := by
    intro j
    rw [hSelected]
    have h:=Ideal.mem_map_of_mem E.toRingEquiv.toRingHom ((hContact R).1 j)
    rwa [hBlockMap] at h
  have hJac (R : ℕ) : actualFixedSelectorJacobian S (fun v=>E (Γ v)) R=
      actualFixedSelectorJacobian S Γ R := by
    ext j i
    change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
      (actualFixedSelectorDerivative S (fun v=>E (Γ v)) (fixedSelectorBlockEssential R j)))=
      HolGerm.eval (actualAnalyticCoordinateDerivative i.val
        (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential R j)))
    rw [actualFixedSelectorDerivative_jacobian_coefficient,actualFixedSelectorDerivative_jacobian_coefficient]
    congr 1
    apply actual_pure_coefficient_of_fixed_section E B hSection
    intro x hx
    have hxi : x≠i.val := by
      intro h
      exact hx (h.symm ▸ (fixedSelectorBlockEssential R i).property)
    simp only [Finsupp.add_apply,hBeta _ x hx,Finsupp.single_eq_of_ne hxi,zero_add]
  have hConesTarget : HistoricalWholePrefixSupport V (fun v=>actualUnshiftedTaylorAlgHom n (E (Γ v))) := by
    intro R v hv u hu α hα
    have hZero : actualAnalyticMultiDerivative u.val (Γ v)=0:=
      (actualAnalyticMultiDerivative_eq_zero_iff_cone u.val (Γ v)).mpr (hCones R v hv u hu)
    apply (actualAnalyticMultiDerivative_eq_zero_iff_cone u.val (E (Γ v))).mp ?_ α hα
    rw [hDerivative u.val (hHeads u),hZero,map_zero]
  refine ⟨?_,hJac,?_⟩
  · exact ⟨(fun i=>⟨(formal_power_map_iff E _ _).mpr (hMarked i).1,
      fun h=>(hMarked i).2 ((formal_power_map_iff E _ _).mp h)⟩),hWholeTarget,hPrefixTarget,
      hSupportedTarget,(fun R=>⟨hContactTarget R,by rw [hJac];exact (hContact R).2⟩),hConesTarget⟩
  · rw [Ideal.map_span,←range_comp]
    rfl

/-- Actual regular-centre geometry produces the compatible chart and ALL
five SAME transformed source laws; no chart or target law is supplied. -/
theorem exists_actual_historical_five_law_compatible_centre_chart
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (C : Set (ComplexModel n)) (c : ℕ) (hReg : RegularAtDim (n:=n) C 0 c)
    (hPlane : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈C → z∈coordinateSubsetPlane (fixedSelectorEssential V)) :
    ∃D : ActualCompatibleMovingCentreChart (fixedSelectorEssential V) C c,
      let E:=(localGermAlgEquiv D.chart D.chart_zero).symm
      ActualHistoricalFivePointLaws S a w (fun v=>E (Γ v)) ∧
      (∀R,actualFixedSelectorJacobian S (fun v=>E (Γ v)) R=actualFixedSelectorJacobian S Γ R) ∧
      Ideal.span (range fun v=>E (Γ v))=Ideal.map E.toRingEquiv.toRingHom (Ideal.span (range Γ)) := by
  obtain ⟨D⟩:=exists_actual_compatible_moving_centre_chart (fixedSelectorEssential V) C c hReg hPlane
  refine ⟨D,?_⟩
  dsimp only
  apply actual_compatible_source_action_five_laws S Γ a w hw hSource
    (localGermAlgEquiv D.chart D.chart_zero).symm D.fixedSection ?_ D.derivative
  intro i hi
  have hProj : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ (fun z : ComplexModel n=>z i) z:=
    Eventually.of_forall fun _=>(EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
  have hInv:=holomorphic_comp D.chart.invFun (local_invFun_holomorphic D.chart D.chart_zero)
    (local_invFun_zero D.chart D.chart_zero) hProj
  change HolGerm.mk ((fun z : ComplexModel n=>z i)∘D.chart.invFun) hInv=coordinateGerm i
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z=>(D.essentialCoordinates z i hi).2

end
end Hironaka.HironakaActualHistoricalCompatibleChartFiveLaws
