import Hironaka.Resolution.HironakaG8ActualContactEndpoint

set_option autoImplicit false

/-! The literal contact-stage suffix on the tangent open has exactly the
same endpoint exponent as the ambient actual contact coefficient record. -/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ActualContactEndpointExponent
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen DivisorExponentAlong GermIdealOrder
  HomogenizedGlueingTower TangentDirectionAlong StepOneValue ResolutionInvariantSpec
  HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11InvBMRebase
  HironakaG8DomainExponents MarkedIdealOperationsAlong.MarkedIdeal

/-- On the actual tangent-open restricted suffix, the divisor exponent at
the lifted endpoint is exactly the ambient actual contact coefficient
exponent along the original endpoint set. -/
theorem actual_contact_endpoint_exponent_restrict
    {n : ℕ} {X Y Z : CMfd.{0} n} (A : MarkedIdeal n X) {k : ℕ}
    (hA : IsInvDomain k A) (U : Opens X) {f : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (P : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hT : IsGeoTestTower (barMarked A) (P.append Q))
    {z : Z} (hzU : P.proj (Q.proj z) ∈ U) (H : Set Z) :
    let V := openPreimage P U
    let z' : openPreimage Q V := ⟨z,hzU⟩
    let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
    divExpAlong n (geoTransformAlong C (restrict V Q)).N (geoTransformAlong C (restrict V Q)).ideal
      ((Subtype.val : openPreimage Q V → Z) ⁻¹' H) z' =
      divExpAlong n (contactCoeffBM A f (P.append Q)).N
        (contactCoeffBM A f (P.append Q)).ideal H z := by
  let V := openPreimage P U
  let W := openPreimage Q V
  let z' : W := ⟨z,hzU⟩
  let C := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
  let L := contactCoeffBM A f (P.append Q)
  have hTA : IsGeoTestTower A (P.append Q) := ((StepOneBridge.barMarked_wEquiv A hA).2 _).1.mp hT
  have hTE := isGeoTestTower_emptyBoundary A (P.append Q) hTA
  have hTC := isGeoTestTower_coeffEmptyBM hA.isWellFormed hA.one_le_d (P.append Q) hTE
  have ⟨hPC,hQC⟩ := (isGeoTestTower_append_iff (coeffEmptyBM A) P Q).mp hTC
  have hRE := restrictEquiv_tail_contactCoeffBM hA.isWellFormed hA.one_le_d U hf P hPC V (fun _ h => h) Q hQC
  have hfull : L.ideal.IsCoherent := by
    rw [contactCoeffBM_ideal]
    exact (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isWellFormed_coeffEmptyBM hA.isWellFormed) (P.append Q) hTC).isCoherent
  have hcos : ∀ e, cosupport n ((Subtype.val : W → Z) ⁻¹' L.N)
      (GermIdeal.pullback (m := n) (Subtype.val : W → Z) L.ideal) e =
        (Subtype.val : W → Z) ⁻¹' cosupport n L.N L.ideal e := by
    intro e
    exact cosupp_pullback_val (⟨L.N,[],L.ideal,e⟩ : MarkedIdeal n Z) (hol_of_isCoherent hfull) W
  have hmap : Filter.map (Subtype.val : W → Z) (𝓝 z') = 𝓝 (z' : Z) :=
    map_nhds_subtype_coe_eq_nhds z'.2 (W.isOpen.mem_nhds z'.2)
  calc
    divExpAlong n (geoTransformAlong C (restrict V Q)).N (geoTransformAlong C (restrict V Q)).ideal
        ((Subtype.val : W → Z) ⁻¹' H) z' =
      divExpAlong n (MarkedIdeal.pullback (Subtype.val : W → Z) L).N
        (MarkedIdeal.pullback (Subtype.val : W → Z) L).ideal ((Subtype.val : W → Z) ⁻¹' H) z' :=
          divExpAlong_eq_of_restrictEquiv hRE _ _
    _ = divExpAlong n L.N L.ideal H z :=
      MonomialInvariantFunctorialAlong.divExpAlong_pullback hcos hmap H

end Hironaka.HironakaG11ActualContactEndpointExponent
