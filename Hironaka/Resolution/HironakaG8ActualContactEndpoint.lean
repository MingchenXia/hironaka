import Hironaka.Resolution.HironakaG11InvBMRebase
import Hironaka.Resolution.HironakaG11ActualContactTailTest
/-! # Actual contact endpoint on a restricted suffix -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8ActualContactEndpoint
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen DivisorExponentAlong
  HomogenizedGlueingTower TangentDirectionAlong StepOneValue ResolutionInvariantSpec
  HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11InvBMRebase
  HironakaG8DomainExponents
open HironakaStepOneZeroContactRemainderGlueing (isNonzeroAlongAt_pullback_val_iff)

/-- The carrier membership and nonzero contact germ at an actual endpoint
transport to the corresponding endpoint of the literally restricted suffix. -/
theorem actual_contact_endpoint_restrict
    {n : ℕ} {X Y Z : CMfd.{0} n} (A : MarkedIdeal n X) {k : ℕ}
    (hA : IsInvDomain k A) (U : Opens X) {f : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked A) (P.append Q))
    {z : Z} (hzU : P.proj (Q.proj z) ∈ U)
    (hzN : z ∈ (contactCoeffBM A f (P.append Q)).N)
    (hnz : IsNonzeroAlongAt (contactCoeffBM A f (P.append Q)).N
      (contactCoeffBM A f (P.append Q)).ideal z) :
    let V := openPreimage P U
    let z' : openPreimage Q V := ⟨z,hzU⟩
    let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
    z' ∈ (geoTransformAlong C (restrict V Q)).N ∧
      IsNonzeroAlongAt (geoTransformAlong C (restrict V Q)).N
        (geoTransformAlong C (restrict V Q)).ideal z' := by
  let V := openPreimage P U
  let z' : openPreimage Q V := ⟨z,hzU⟩
  let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
  have hTA : IsGeoTestTower A (P.append Q) := ((StepOneBridge.barMarked_wEquiv A hA).2 _).1.mp hT
  have hTE := isGeoTestTower_emptyBoundary A (P.append Q) hTA
  have hTC := isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d (P.append Q) hTE
  have ⟨hPC,hQC⟩ := (isGeoTestTower_append_iff (coeffEmptyBM A) P Q).mp hTC
  have hRE := restrictEquiv_tail_contactCoeffBM hA.isWellFormed hA.one_le_d U hf P hPC V (fun _ h => h) Q hQC
  have hfull : (contactCoeffBM A f (P.append Q)).ideal.IsCoherent := by
    rw [contactCoeffBM_ideal]
    exact (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isWellFormed_coeffEmptyBM hA.isWellFormed) (P.append Q) hTC).isCoherent
  have hzN' : z' ∈ (geoTransformAlong C (restrict V Q)).N := by
    rw [hRE.N_eq]
    exact hzN
  have hnz' : IsNonzeroAlongAt (geoTransformAlong C (restrict V Q)).N
      (geoTransformAlong C (restrict V Q)).ideal z' :=
    (isNonzeroAlongAt_iff_of_restrictEquiv hRE hzN').mpr
      ((isNonzeroAlongAt_pullback_val_iff hfull (openPreimage Q V) z').mpr hnz)
  exact ⟨hzN',hnz'⟩

end
end Hironaka.HironakaG8ActualContactEndpoint
