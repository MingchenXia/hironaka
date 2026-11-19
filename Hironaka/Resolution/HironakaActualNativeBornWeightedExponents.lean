import Hironaka.Resolution.HironakaActualSingularBornCriticalBoundary
import Hironaka.Resolution.HironakaActualWeightedNativeRadical
import Hironaka.Resolution.HironakaActualControlledNeighborhoodGenerators
import Hironaka.Resolution.HironakaActualOriginalGeometricCentreBennett
import Hironaka.Resolution.HironakaNormalCrossingsFiniteMarkedCompletion
import Hironaka.Resolution.FactorizationFromResolution

/-! Actual reduced-stalk reflection transfers derived strict-ideal born
exponent zero to the SAME full weighted Q at its genuine native cut point.
No native point presentation outside its actual cut is required.
Blueprint: hironaka-actual-native-born-weighted-exponents-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualNativeBornWeightedExponents
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaSmoothSubmersionGermIdealColon HironakaActualControlledNeighborhoodGenerators
  HironakaActualOriginalGeometricCentreBennett HironakaActualWeightedNativeRadical
  HironakaActualHistoricalNativeStageStep HironakaActualFixedInheritedSelector
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaActualSingularBornCriticalBoundary HironakaNormalCrossingsFiniteMarkedCompletion
  HironakaStageCenters BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  DivisorExponent DivisorExponentAlong FactorizationFromResolution IdealWeightPowers
  GermIdealOrder HironakaSmoothCentreCoherentDomain HironakaActualCauchyMonomialDivision
  BlowupDerivativeIdeal

variable {n : ℕ} {X : Type} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

private theorem adapted_le_iff_stalk (I J : GermIdeal n X)
    (hI : I.IsCoherent) (hJ : J.IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    adaptedIdeal I x Φ h0≤adaptedIdeal J x Φ h0 ↔ ∀F,I.mem x F→J.mem x F := by
  constructor
  · intro h F hF
    have hf := holomorphicAt_of_mem_coherent I hI hF
    exact (mem_adaptedIdeal_iff J hJ x Φ h0 F hf).mp
      (h ((mem_adaptedIdeal_iff I hI x Φ h0 F hf).mpr hF))
  · intro h
    apply Ideal.span_le.mpr
    rintro g ⟨F,hF,hIF,rfl⟩
    exact (mem_adaptedIdeal_iff J hJ x Φ h0 F hF).mpr (h F hIF)

/-- The actual adapted vanishing stalk is radical without irreducibility. -/
theorem adapted_vanishingIdeal_isRadical (W : Set X)
    (hW : (vanishingIdeal (n:=n) W).IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    (adaptedIdeal (vanishingIdeal (n:=n) W) x Φ h0).IsRadical := by
  apply (Ideal.isRadical_iff_pow_one_lt 2 (by decide)).mpr
  intro g hg
  obtain ⟨F,hF,rfl⟩ := exists_original_adapted_representative x Φ h0 g
  have hPow : adaptedGerm x Φ h0 (fun y=>F y^2) (holomorphicAt_pow hF 2)=
      (adaptedGerm x Φ h0 F hF)^2 := by
    exact HolGerm.mk_pow _ _ 2
  rw [← hPow] at hg
  have hFpow := (mem_adaptedIdeal_iff _ hW x Φ h0 _ (holomorphicAt_pow hF 2)).mp hg
  apply (mem_adaptedIdeal_iff _ hW x Φ h0 F hF).mpr
  refine ⟨hF,?_⟩
  filter_upwards [hFpow.2] with y hy hyW
  exact (pow_eq_zero_iff (by decide : 2≠0)).mp (hy hyW)

private theorem zero_translated_adapted_vanishing (W : Set X)
    (hW : (vanishingIdeal (n:=n) W).IsCoherent) (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0) :
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Φ) 0)=
      adaptedIdeal (vanishingIdeal (n:=n) W) x Φ h0 := by
  rw [← actual_flattened_origin_eq_adapted _ hW x Φ h0]
  unfold originalCoherentOriginIdeal
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨F,hF,hMem,rfl⟩
    exact ⟨F,hF,(actual_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 F).mpr
      ((actual_zero_translated_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 F).mp hMem),rfl⟩
  · rintro ⟨F,hF,hMem,rfl⟩
    exact ⟨F,hF,(actual_zero_translated_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 F).mpr
      ((actual_flattened_vanishing_stalk_mem_iff W x Φ hsrc h0 F).mp hMem),rfl⟩

/-- At the genuine SAME native point, all reduced original stalk tests
are reflected, and the actual weighted ideal lies in the actual W stalk. -/
theorem actual_native_point_reduced_stalk_dictionary {k : ℕ}
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k→CoordinateWord n)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (W : Set X) (hW : IsComplexAnalyticSubset (n:=n) W)
    (Q : MarkedIdeal n X) (hQI : Q.ideal.IsCoherent) (x : X)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q x) :
    ∃(Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (_hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
      (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0),
      (adaptedIdeal Q.ideal x Φ h0).radical=adaptedIdeal (vanishingIdeal (n:=n) W) x Φ h0 ∧
      (∀(H : Set X), (vanishingIdeal (n:=n) H).IsCoherent →
        ((∀F,Q.ideal.mem x F→(vanishingIdeal (n:=n) H).mem x F) ↔
         (∀F,(vanishingIdeal (n:=n) W).mem x F→(vanishingIdeal (n:=n) H).mem x F))) ∧
      ∀F,Q.ideal.mem x F→(vanishingIdeal (n:=n) W).mem x F := by
  have hIW := CartanIrreducible.cartanCoherence W hW
  obtain ⟨Φ,hsrc,h0,hRad,hTests⟩ := actual_native_point_radical_dictionary S a w hPositive W Q x hAt
  rw [zero_translated_adapted_vanishing W hIW x Φ hsrc h0] at hRad hTests
  have hReduced := adapted_vanishingIdeal_isRadical W hIW x Φ h0
  rw [hReduced.radical] at hRad
  refine ⟨Φ,hsrc,h0,hRad,?_,?_⟩
  · intro H hIH
    exact (adapted_le_iff_stalk Q.ideal _ hQI hIH x Φ h0).symm.trans
      ((hTests _ (adapted_vanishingIdeal_isRadical H hIH x Φ h0)).trans
        (adapted_le_iff_stalk _ _ hIW hIH x Φ h0))
  · apply (adapted_le_iff_stalk Q.ideal _ hQI hIW x Φ h0).mp
    rw [← hRad]
    exact Ideal.le_radical

/-- The actual original singular history derives EVERY literal born
exponent zero for the SAME weighted current Q at its genuine native point. -/
theorem actual_native_born_weighted_exponent_zero {k : ℕ} {X₀ Y : CMfd.{0} n}
    (Q₀ : MarkedIdeal n X₀) (W : Set X₀) (hW : IsComplexAnalyticSubset (n:=n) W)
    (T : BlowupTower X₀ Y)
    (hStage : StageCentres (fun P C=>C⊆HironakaEmbeddedAnalytic.singularSet (n:=n)
      (strictTransform n P.proj W)) T)
    (hQI : (geoTransformAlong Q₀ T).ideal.IsCoherent)
    (hE : NormalCrossings.IsSNCDivisor n (geoTransformAlong Q₀ T).E)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k→CoordinateWord n)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (x : Y) (hNZ : IsNonzeroAlongAt univ (geoTransformAlong Q₀ T).ideal x)
    (hAt : ActualHistoricalNativePointPresentation S a w
      (strictTransform n T.proj W) (geoTransformAlong Q₀ T) x)
    (H : Set Y) (hBorn : H∈(geoTransformAlong Q₀ T).E.drop Q₀.E.length) :
    divExpAlong n univ (geoTransformAlong Q₀ T).ideal H x=0 := by
  let I := vanishingIdeal (n:=n) (strictTransform n T.proj W)
  have hWT := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  have hI : I.IsCoherent := CartanIrreducible.cartanCoherence _ hWT
  obtain ⟨Φ,_hsrc,h0,_hRad,hTests,hLe⟩ := actual_native_point_reduced_stalk_dictionary
    S a w hPositive _ hWT (geoTransformAlong Q₀ T) hQI x hAt
  have hNZ_I : IsNonzeroAlongAt univ I x := by
    obtain ⟨g,hg,hFreq⟩ := hNZ
    exact ⟨g,hLe g hg,hFreq⟩
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hBorn)
  have hH : IsClosedSubmanifold n H := hi ▸ (snc_member_codimOne_geometry hE i).1
  have hInv : (vanishingIdeal (n:=n) H).IsInvertible := hi ▸ isInvertible_vanishingIdeal_snc_member hE i
  have hIH := DivisorMetric.isCoherent_of_isInvertible hInv
  have hZero := born_boundary_vanishing_exponent_zero Q₀ W hW T hStage H hBorn hH hInv x hNZ_I
  rw [divExpAlong_univ] at hZero ⊢
  have hQHol : ∀y F,(geoTransformAlong Q₀ T).ideal.mem y F→HolomorphicAt n F y :=
    fun _ _ hF=>holomorphicAt_of_mem_coherent (geoTransformAlong Q₀ T).ideal hQI hF
  by_cases hxH : x∈H
  · obtain ⟨r,hReg⟩ := hH.2 x hxH
    have hNot : ¬IsDivNear n (geoTransformAlong Q₀ T).ideal H 1 x := by
      intro hDiv
      have hQStalk := (isDivNear_iff hQI hReg).mp hDiv
      rw [idealPow_one_of_isCoherent hIH] at hQStalk
      have hIStalk := (hTests H hIH).mp hQStalk
      have hDivI : IsDivNear n I H 1 x := by
        apply (isDivNear_iff hI hReg).mpr
        rw [idealPow_one_of_isCoherent hIH]
        exact hIStalk
      have hIHol : ∀y F,I.mem y F→HolomorphicAt n F y := fun _ _ h=>h.1
      have hNotI := not_isDivNear_divExp_succ (𝔞:=I) (H:=H) hIHol hxH
        (isNonzeroAlongAt_univ_iff.mp hNZ_I)
      rw [hZero] at hNotI
      exact hNotI hDivI
    by_contra hne
    exact hNot ((isDivNear_divExp hQHol x).mono (Nat.one_le_iff_ne_zero.mpr hne))
  · have hnone : ¬∃e,¬IsDivNear n (geoTransformAlong Q₀ T).ideal H (e+1) x := by
      rintro ⟨e,he⟩
      exact he (isDivNear_of_notMem hH.1 hxH (e+1))
    simp only [divExp,dif_neg hnone]

end
end Hironaka.HironakaActualNativeBornWeightedExponents
