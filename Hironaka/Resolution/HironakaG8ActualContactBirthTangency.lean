import Hironaka.Resolution.HironakaG8LocalizedBirthTangency
import Hironaka.Resolution.HironakaG11ActualContactTailTest
/-! # Actual contact-coefficient birth tangency -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ActualContactBirthTangency
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold BlowupSpaceTangent
  HomogenizedGlueingTower StepOneValue MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen DivisorExponentAlong TangentDirectionAlong ResolutionInvariantSpec
  HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11ActualContactTailTest
  HironakaG11ContactBirthGeometry

/-- For a literal contact-coefficient birth and actual original test suffix,
endpoint exceptional-sum divisibility forces the old boundary member to be
tangent to the contact carrier at the projected birth point. -/
theorem tangent_le_at_actual_contact_birth_of_div
    {n : ℕ} {X Y Z W : CMfd.{0} n} (A : MarkedIdeal n X) {k : ℕ}
    (hA : IsInvDomain k A) (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong A.N A.ideal A.d U u)
    (P : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (Q : BlowupTower Z W)
    (hT : IsGeoTestTower (barMarked A) ((BlowupTower.step P C π hπ).append Q))
    (i : Fin (geoTransformAlong A P).E.length)
    {S : List (Set W)} (hS : ∀ K ∈ S, IsClosedSubmanifold n K)
    (hmem : strictAlong Q (geoStrictTransform π C ((geoTransformAlong A P).E.get i)) ∈ S)
    (e : ℕ) {z : W}
    (hzU : P.proj (π (Q.proj z)) ∈ U)
    (hzP : z ∈ strictAlong Q (contactCoeffBM A u (.step P C π hπ)).N)
    (hzD : z ∈ strictAlong Q (π ⁻¹' C))
    (hdiv : IsDivNearAlong n (strictAlong Q (contactCoeffBM A u (.step P C π hπ)).N)
      (exceptionalTermBM (n := n) S e) (strictAlong Q (π ⁻¹' C)) 1 z) :
    tangentSpace n (strictAlong P (A.N ∩ {x | u x = 0})) (π (Q.proj z)) ≤
      tangentSpace n ((geoTransformAlong A P).E.get i) (π (Q.proj z)) := by
  let T : BlowupTower X Z := .step P C π hπ
  have hTA : IsGeoTestTower A (T.append Q) := ((StepOneBridge.barMarked_wEquiv A hA).2 _).1.mp hT
  have hStepA : IsGeoTestTower A T := (isGeoTestTower_append_iff A T Q).mp hTA |>.1
  have hPA : IsGeoTestTower A P := (isGeoTestTower_step_iff A P C π hπ).mp hStepA |>.1
  have hCA := (isGeoTestTower_step_iff A P C π hπ).mp hStepA |>.2
  have hStepE := isGeoTestTower_emptyBoundary A T hStepA
  have hStepC := isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d T hStepE
  have hPC : IsGeoTestTower (coeffEmptyBM A) P := (isGeoTestTower_step_iff (coeffEmptyBM A) P C π hπ).mp hStepC |>.1
  have hCC := (isGeoTestTower_step_iff (coeffEmptyBM A) P C π hπ).mp hStepC |>.2
  have hpC : π (Q.proj z) ∈ C := by
    apply MemberInterTowerAlong.strictAlong_subset_preimage Q
      (hπ.1.1.preimage hπ.contMDiff.continuous)
    exact hzD
  have hSclosed : ∀ K ∈ S, IsClosed K := fun K hK => (hS K hK).1
  have hzH := HironakaG11ResidualBirthPoint.residual_endpoint_mem_throughMember
    hSclosed hzP hzD hdiv _ hmem
  have hpHstrict : Q.proj z ∈ geoStrictTransform π C ((geoTransformAlong A P).E.get i) := by
    apply MemberInterTowerAlong.strictAlong_subset_preimage Q isClosed_closure
    exact hzH
  have hE := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA.isWellFormed P hPA).isSNCDivisor
  have hpH : π (Q.proj z) ∈ (geoTransformAlong A P).E.get i :=
    geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      (hE.1 _ (List.get_mem _ i)) hpHstrict
  let p : openPreimage P U := ⟨π (Q.proj z), hzU⟩
  have hgeom := contact_birth_geometry A hA.isWellFormed hA.one_le_d U hu P hPA hPC hCC p hpC
  have htail := actual_contact_tail_test A hA U hu T Q hT
  have hMN : (contactCoeffBM A u T).N = geoStrictTransform π C
      (strictAlong P (A.N ∩ {x | u x = 0})) := rfl
  have hborn := birth_mem_contact_boundary A u P C π hπ
  exact HironakaG8LocalizedBirthTangency.tangent_le_of_div_on_source_open hπ (openPreimage P U)
    hgeom.2.2.1 hgeom.2.2.2.1 hE hCA.2.2 i (contactCoeffBM A u T) hMN hborn Q
    htail.1 htail.2 hS hmem e hzU hzP hzD hpC hpH hdiv

end
end Hironaka.HironakaG8ActualContactBirthTangency
