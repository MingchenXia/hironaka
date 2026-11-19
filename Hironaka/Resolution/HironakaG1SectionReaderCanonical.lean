import Hironaka.Resolution.HironakaG1SupportedStepOne
import Hironaka.Resolution.HironakaG1ProperNormalOriginalTest
import Hironaka.Resolution.HironakaActualSectionInitialValues

/-! The supported section reader on the actual cylindrical test history. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG1SectionReaderCanonical

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  RelativePrincipalizationSpan GermIdealPullbackCalculus GermIdealOrder
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HomogenizedIdealAlong
  NormalCrossings HironakaActualOpenZeroSectionDifferentials HironakaActualSectionBoundaryGeometry
  HironakaActualSectionInitialValues HironakaActualNativeSectionInitialBar
  HironakaActualNativeSectionFiniteHistory HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1SupportedStepOne
  HironakaRelativeNormalIdeal HironakaSmoothSubmersionOrderedChoiceImageTrace
  HironakaSmoothSubmersionCanonicalValueDimensionShift HironakaActualSectionBoundaryDimension

variable {n k : ℕ} {U : Opens (ComplexModel n)}

private abbrev ambient (U : Opens (ComplexModel n)) :=
  CMfd.of (n := n + 1) (productOpen U)

/-- The supported section retains maximal order at the original source mark. -/
theorem sectionMarked_maximalOrder (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d) :
    IsMaximalOrderAlong (sectionMarked Q).N (sectionMarked Q).ideal (sectionMarked Q).d := by
  let M := sectionMarked Q
  have hM : IsInvDomain k M := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hComp : projection U ∘ zeroSection U = id := by
    funext z
    apply Subtype.ext
    exact tangentProjection_tangentInclusion n 1 z
  have hTrace : GermIdeal.pullback (m := n) (zeroSection U) M.ideal = Q.ideal := by
    change GermIdeal.pullback (m := n) (zeroSection U)
      (GermIdeal.pullback (m := n + 1) (projection U) Q.ideal) = _
    rw [← coherent_pullback_comp (projection_contMDiff U) (zeroSection_contMDiff U)
      Q.ideal hQ.isWellFormed.isCoherent, hComp]
    exact BlowupControlledTransform.pullback_id hQ.isWellFormed.isCoherent
  intro x hx
  change x ∈ cosupport (n + 1) (liftedCarrier Q.N) M.ideal (Q.d + 1) at hx
  rw [source_cosupport_eq_lifted Q.N M.ideal
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg), hTrace] at hx
  exact hMax (projection U x) hx.1

set_option maxHeartbeats 650000 in
/-- The actual cylindrical and section test records have equivalent
canonicality when both use the original supported section reader.
The proof derives the necessary tests at all canonical prefixes. -/
theorem canonical_iff_of_section_reader (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (ambient U) Y) :
    let M := sectionMarked Q
    let P := properNormalMarked Q
    let f : ∀ {Z : CMfd.{0} (n + 1)}, BlowupTower (ambient U) Z → Z → ℕ ×ₗ WithTop (ValTy k) :=
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) M
    IsCanonical P f T ↔ IsCanonical M f T := by
  intro M P f
  have hM : IsInvDomain (k + 1) M := section_projected_domain (k + 1) Q.N Q.E Q.ideal Q.d hQ
  have hClass := properNormalMarked_locWPEquiv_section Q hQ
  have hMmax := sectionMarked_maximalOrder Q hQ hMax
  induction T with
  | refl => exact Iff.rfl
  | @step Y Z T C π hπ ih =>
    have hCos (hCan : IsCanonical M f T) :
        (geoTransformAlong P T).cosupp = (geoTransformAlong M T).cosupp := by
      have hTest := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
        (invFamily (Nat.succ_pos n) k) M hM hMmax (Nat.succ_pos n) T hCan).2.1
      have hTestP := (hClass.wEquiv.2 T).1.mpr hTest
      exact (hClass.wEquiv.2 T).2 hTestP
    constructor
    · rintro ⟨hPrefix, hCentre⟩
      have hCan := ih.mp hPrefix
      rw [hCos hCan] at hCentre
      exact ⟨hCan, hCentre⟩
    · rintro ⟨hCan, hCentre⟩
      rw [← hCos hCan] at hCentre
      exact ⟨ih.mpr hCan, hCentre⟩

set_option maxHeartbeats 850000 in
/-- The section reader on an actual cylindrical history has equivalent
canonicality to the original native Step One reader at its own bound.
At a canonical endpoint it compares values and both maximum loci along
the actual native inclusion. -/
theorem Lift.original_native_section_reader (hn : 0 < n)
    (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    (hMax : IsMaximalOrderAlong Q.N Q.ideal Q.d)
    {Y : CMfd.{0} (n + 1)} {T : BlowupTower (ambient U) Y}
    {hWc : IsClosed (zeroPlane U)} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀ y ∈ V, RegularAtDim (n := n + 1) V y n}
    {N : BlowupTower
      (nativeManifold (Y := ambient U) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Nat.le_succ n) V hV)}
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
      (sectionMarked Q).E T V hVc hV N) :
    let M := sectionMarked Q
    let P := properNormalMarked Q
    let B := nativePullback (Y := ambient U) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
    let f : ∀ {Z : CMfd.{0} (n + 1)}, BlowupTower (ambient U) Z → Z → ℕ ×ₗ WithTop (ValTy k) :=
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) M
    let g : ∀ {Z : CMfd.{0} n}, BlowupTower
        (nativeManifold (Y := ambient U) (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U)) Z →
        Z → ℕ ×ₗ WithTop (ValTy k) := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) B
    let i : nativeManifold (Nat.le_succ n) V hV → Y := Subtype.val
    let D := maxLocus (f T) (geoTransformAlong P T).cosupp
    let E := maxLocus (g N) (geoTransformAlong B N).cosupp
    (IsCanonical P f T ↔ IsCanonical B g N) ∧
      (IsCanonical P f T →
        (∀ z, i z ∈ (geoTransformAlong P T).cosupp →
          f T (i z) = stepDimensionMap (sameIndexMap 1 k) (g N z)) ∧
        E = i ⁻¹' D ∧ i '' E = D) := by
  intro M P B f g i D E
  have hM : IsInvDomain (k + 1) M := section_projected_domain (k + 1) Q.N Q.E Q.ideal Q.d hQ
  have hSupport : M.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hTrans : IsTransverse (n + 1) (zeroPlane U) M.E :=
    isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hMmax := sectionMarked_maximalOrder Q hQ hMax
  have hReader := canonical_iff_of_section_reader (k := k) Q hQ hMax T
  have hNative := Lift.original_same_bound_step_one_canonical_iff (X := ambient U)
    (q := k) (T := T) (Q := N)
    (Nat.succ_pos n) hn M hM hSupport hTrans hMmax hLift
  refine ⟨hReader.trans hNative.symm, fun hCan => ?_⟩
  have hCanM := hReader.mp hCan
  have hTestM := (Seq.StepOneBridge.isGeoTestTower_of_isCanonical
    (invFamily (Nat.succ_pos n) k) M hM hMmax (Nat.succ_pos n) T hCanM).2.1
  have hClass := properNormalMarked_locWPEquiv_section Q hQ
  have hCos := (hClass.wEquiv.2 T).2 ((hClass.wEquiv.2 T).1.mpr hTestM)
  have hVal := (Lift.original_same_bound_step_one_values (X := ambient U)
    (q := k) (T := T) (Q := N) (Nat.succ_pos n) hn M hM
    hSupport hTrans hMmax hLift hCanM).2
  have hMaxima := Lift.original_same_bound_step_one_max_loci (X := ambient U)
    (q := k) (T := T) (Q := N) (Nat.succ_pos n) hn M hM
    hSupport hTrans hMmax hLift hCanM
  refine ⟨fun z hz => ?_, ?_⟩
  · have hzM : i z ∈ (geoTransformAlong M T).cosupp := hCos ▸ hz
    have h := hVal z hzM
    rwa [show n + 1 - n = 1 by omega] at h
  · dsimp only [D]
    rw [hCos]
    exact hMaxima

end

end Hironaka.HironakaG1SectionReaderCanonical
