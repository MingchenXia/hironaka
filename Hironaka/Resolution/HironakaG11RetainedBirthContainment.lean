import Hironaka.Resolution.HironakaG11RetainedBirthSources
import Hironaka.Resolution.HironakaG11TangentCentreContainment
import Hironaka.Resolution.HironakaG8ActualContactBirthTangency

set_option autoImplicit false

/-! Actual residual divisibility supplies the smooth source dictionary and
centre-germ containment for every old member at the same fixed birth. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11RetainedBirthContainment
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold BlowupSpaceTangent HomogenizedGlueingTower
  MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings GermIdealOrder
  DivisorExponentAlong TangentDirectionAlong ResolutionInvariantSpec StepOneValue
  HironakaG11InvBMLower HironakaG11InvBMLowerTailSucc HironakaG11InvBMStage
  HironakaG11RetainedBirthSources HironakaG11ContactBirthGeometry HironakaG11TangentCentreContainment
  HironakaG11ResidualBirthPoint HironakaG8ActualContactBirthTangency

/-- For every old member retained at the anchor, actual exceptional-term
divisibility on the contact carrier produces its literal smooth birth source
and local containment of the birth centre in that source member. -/
theorem retained_sources_contain_birth_centre_germ
    {n : ℕ} (hn : 0 < n) {X Y₀ Y₁ Y : CMfd.{0} n} (A : MarkedIdeal n X) {k : ℕ}
    (hA : IsInvDomain k A) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong A.N A.ideal A.d U u)
    (P : BlowupTower X Y₀) (C : Set Y₀) (π : Y₁ → Y₀) (hπ : IsBlowupAlong n C π)
    (Q : BlowupTower Y₁ Y)
    (hT : IsGeoTestTower (barMarked A) ((BlowupTower.step P C π hπ).append Q))
    (a z : Y) (hzU : P.proj (π (Q.proj z)) ∈ U)
    (hzP : z ∈ strictAlong Q (contactCoeffBM A u (.step P C π hπ)).N)
    (hzD : z ∈ strictAlong Q (π ⁻¹' C))
    (hdiv : IsDivNearAlong n (strictAlong Q (contactCoeffBM A u (.step P C π hπ)).N)
      (exceptionalTermBM (n := n) (throughMembers A ((BlowupTower.step P C π hπ).append Q) a)
        (coeffEmptyBM A).d) (strictAlong Q (π ⁻¹' C)) 1 z) :
    ∀ K ∈ throughMembers A ((BlowupTower.step P C π hπ).append Q) a,
      ∃ H ∈ (geoTransformAlong A P).E, IsClosedSubmanifold n H ∧
        IsClosedSubmanifold n (geoStrictTransform π C H) ∧
        K = strictAlong Q (geoStrictTransform π C H) ∧
        ∀ᶠ x in 𝓝 (π (Q.proj z)), x ∈ C → x ∈ H := by
  let T := (BlowupTower.step P C π hπ).append Q
  let S := throughMembers A T a
  have hTA : IsGeoTestTower A T := ((StepOneBridge.barMarked_wEquiv A hA).2 T).1.mp hT
  have hStep : IsGeoTestTower A (.step P C π hπ) :=
    (isGeoTestTower_append_iff A (.step P C π hπ) Q).mp hTA |>.1
  have hPA : IsGeoTestTower A P := (isGeoTestTower_step_iff A P C π hπ).mp hStep |>.1
  have hCA := (isGeoTestTower_step_iff A P C π hπ).mp hStep |>.2
  have hStepE := isGeoTestTower_emptyBoundary A (.step P C π hπ) hStep
  have hStepC := isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d (.step P C π hπ) hStepE
  have hPC : IsGeoTestTower (coeffEmptyBM A) P :=
    (isGeoTestTower_step_iff (coeffEmptyBM A) P C π hπ).mp hStepC |>.1
  have hCC := (isGeoTestTower_step_iff (coeffEmptyBM A) P C π hπ).mp hStepC |>.2
  have hpC : π (Q.proj z) ∈ C := strictAlong_subset_preimage Q
    (hπ.1.1.preimage hπ.contMDiff.continuous) hzD
  let p : openPreimage P U := ⟨π (Q.proj z),hzU⟩
  have hgeom := contact_birth_geometry A hA.isWellFormed hA.one_le_d U hu P hPA hPC hCC p hpC
  have hCP : ∀ᶠ x in 𝓝 (π (Q.proj z)), x ∈ C →
      x ∈ strictAlong P (A.N ∩ {x | u x = 0}) := by
    filter_upwards [(openPreimage P U).isOpen.mem_nhds hzU] with x hxU hxC
    exact hgeom.2.2.2.1 (show (⟨x,hxU⟩ : openPreimage P U) ∈
      (Subtype.val : openPreimage P U → Y₀) ⁻¹' C from hxC)
  have hSm := isClosedSubmanifold_of_mem_throughMembers A hA.isWellFormed hn T hT a
  have hSclosed : ∀ K ∈ S, IsClosed K := fun K hK => (hSm K hK).1
  have hSources := retained_members_have_smooth_birth_sources hn A hA.isWellFormed P C π hπ Q hTA a
  intro K hK
  obtain ⟨H,hHE,hH,hKsm,hEq⟩ := hSources K hK
  obtain ⟨i,hi⟩ := List.get_of_mem hHE
  have hmem : strictAlong Q (geoStrictTransform π C ((geoTransformAlong A P).E.get i)) ∈ S := by
    rw [hi,← hEq]
    exact hK
  have htan := tangent_le_at_actual_contact_birth_of_div A hA U hu P C π hπ Q hT i hSm hmem
    (coeffEmptyBM A).d hzU hzP hzD hdiv
  rw [hi] at htan
  have hzK : z ∈ K := residual_endpoint_mem_throughMember hSclosed hzP hzD hdiv K hK
  have hpHstrict : Q.proj z ∈ geoStrictTransform π C H := by
    have hzK' : z ∈ strictAlong Q (geoStrictTransform π C H) := hEq ▸ hzK
    exact strictAlong_subset_preimage Q isClosed_closure hzK' 
  have hpH : π (Q.proj z) ∈ H := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hH.1 hpHstrict
  have hCH := centre_germ_contained_of_tangent hCA.2.2 hpC i (by simpa only [hi] using hpH)
    hCP (by simpa only [hi] using htan)
  refine ⟨H,hHE,hH,hKsm,hEq,?_⟩
  simpa only [hi] using hCH

end Hironaka.HironakaG11RetainedBirthContainment
