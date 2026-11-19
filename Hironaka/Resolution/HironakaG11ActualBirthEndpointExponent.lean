import Hironaka.Resolution.HironakaG8ActualContactBirthRebase
import Hironaka.Resolution.HironakaG11ActualContactEndpointExponent

set_option autoImplicit false

/-! Exact endpoint exponent across an actual contact birth and its suffix. -/
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG11ActualBirthEndpointExponent
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupRestrictOpen MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen MarkedIdealOperationsAlong.MarkedIdeal DivisorExponentAlong
  HomogenizedGlueingTower TangentDirectionAlong StepOneValue ResolutionInvariantSpec
  HironakaG11InvBMLower HironakaG11InvBMStage HironakaG11InvBMRebase
  HironakaG8ActualContactBirthRebase HironakaG11ActualContactEndpointExponent

/-- The literal restricted birth and suffix retain the exact ambient actual
contact coefficient exponent along any endpoint set. -/
theorem actual_birth_endpoint_exponent
    {n : ℕ} {X Y Z W : CMfd.{0} n} (A : MarkedIdeal n X) {k : ℕ}
    (hA : IsInvDomain k A) (U : Opens X) {f : X → ℂ}
    (hf : IsTangentDirectionAlong A.N A.ideal A.d U f)
    (P : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (Q : BlowupTower Z W)
    (hT : IsGeoTestTower (barMarked A) ((BlowupTower.step P C π hπ).append Q))
    {z : W} (hzU : P.proj (π (Q.proj z)) ∈ U) (H : Set W) :
    let V := openPreimage P U
    let V₁ : Opens Z := ⟨π ⁻¹' (V : Set Y), V.isOpen.preimage hπ.contMDiff.continuous⟩
    let ρ : V₁ → V := fun x => ⟨π x.val,x.2⟩
    let C' := (Subtype.val : V → Y) ⁻¹' C
    let L := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
    let R := geoTransformAlong (L.geoTransform C' ρ) (restrict V₁ Q)
    let z' : openPreimage Q V₁ := ⟨z,hzU⟩
    divExpAlong n R.N R.ideal ((Subtype.val : openPreimage Q V₁ → W) ⁻¹' H) z' =
      divExpAlong n (contactCoeffBM A f ((BlowupTower.step P C π hπ).append Q)).N
        (contactCoeffBM A f ((BlowupTower.step P C π hπ).append Q)).ideal H z := by
  let V := openPreimage P U
  let V₁ : Opens Z := ⟨π ⁻¹' (V : Set Y), V.isOpen.preimage hπ.contMDiff.continuous⟩
  let ρ : V₁ → V := fun x => ⟨π x.val,x.2⟩
  let C' := (Subtype.val : V → Y) ⁻¹' C
  let L := MarkedIdeal.pullback (Subtype.val : V → Y) (contactCoeffBM A f P)
  let L₁ := MarkedIdeal.pullback (Subtype.val : V₁ → Z) (contactCoeffBM A f (.step P C π hπ))
  let H' := (Subtype.val : openPreimage Q V₁ → W) ⁻¹' H
  let z' : openPreimage Q V₁ := ⟨z,hzU⟩
  obtain ⟨_,_,hRE,hLtrans,hL₁,_,hQ⟩ := actual_contact_birth_rebase A hA U hf P C π hπ Q hT
  have hfirst := divExpAlong_geoTransformAlong_eq_of_restrictEquiv hLtrans hL₁.isCoherent hRE (restrict V₁ Q) hQ H' z'
  have hlast := actual_contact_endpoint_exponent_restrict A hA U hf (.step P C π hπ) Q hT hzU H
  exact hfirst.trans hlast
end
end Hironaka.HironakaG11ActualBirthEndpointExponent
