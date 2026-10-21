/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreNearbyIdeal

/-! # Every real nearby original relative layer with its canonical centre scalars
Original geometry/coherence/containment internally provide every whole
ideal-map hypothesis. Actual whole quotient maps restrict to true power
images; independently descended quotient actions are respected on every
degree and the whole associated sum. Mathematics precedes this source.
-/
set_option autoImplicit false
open Set Filter
open scoped DirectSum Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreNearbyCanonicalLayers
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreCanonicalLayers
  HironakaHolomorphicJetRankLoci HironakaRelativeNormalIdeal
  HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalGradedAlgebra
  HironakaRelativeNormalCentreScalars HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations

private theorem actualCentreQuotientRingHomInvPair {R S : Type*} [CommRing R] [CommRing S]
    (J : Ideal R) (K : Ideal S) (E : R ≃+* S) (hK : K = Ideal.map E.toRingHom J) :
    RingHomInvPair (centreQuotientEquiv J K E hK).toRingHom
      (centreQuotientEquiv J K E hK).symm.toRingHom := by
  constructor
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).symm_apply_apply x
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).apply_symm_apply x

private theorem actualCentreQuotientRingHomInvPairSymm {R S : Type*} [CommRing R] [CommRing S]
    (J : Ideal R) (K : Ideal S) (E : R ≃+* S) (hK : K = Ideal.map E.toRingHom J) :
    RingHomInvPair (centreQuotientEquiv J K E hK).symm.toRingHom
      (centreQuotientEquiv J K E hK).toRingHom := by
  constructor
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).apply_symm_apply x
  · apply RingHom.ext
    intro x
    exact (centreQuotientEquiv J K E hK).symm_apply_apply x

attribute [local instance] actualCentreQuotientRingHomInvPair actualCentreQuotientRingHomInvPairSymm

/-- Actual full quotient and canonical layer witnesses; no desired witness is an input. -/
structure NearbyRelativeCanonicalBridge (d t : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)))
    (Ia Ix Kx : Ideal (HolGerm (ComplexModel (d+t))))
    (hK : Kx = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t)) where
  eQuot : ∀ q : ℕ,
    (HolGerm (ComplexModel (d+t)) ⧸ (Ia ⊔ normalIdeal d t ^ (q+1))) ≃+*
      (HolGerm (ComplexModel (d+t)) ⧸ (Ix ⊔ Kx ^ (q+1)))
  eLayer : ∀ q : ℕ,
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalGradedPiece d t Ia q) := (originalNormalGradedPieceCentreModule d t Ia q).toSMul
    letI := originalNormalGradedPieceCentreModule d t Ia q
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ Kx)
      (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
      (idealPowerLayerCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx q).toSMul
    letI := idealPowerLayerCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx q
    LinearEquiv (σ' := (centreQuotientEquiv (normalIdeal d t) Kx E.toRingEquiv hK).symm.toRingHom)
      (centreQuotientEquiv (normalIdeal d t) Kx E.toRingEquiv hK).toRingHom
      (originalNormalGradedPiece d t Ia q) (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q)
  eWhole :
    letI := tangentAlgebra d t
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
      (originalNormalAssociatedGraded d t Ia) := (originalNormalAssociatedGradedCentreModule d t Ia).toSMul
    letI := originalNormalAssociatedGradedCentreModule d t Ia
    letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ Kx)
      (⨁ q : ℕ, layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
      (idealPowerAssociatedCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx).toSMul
    letI := idealPowerAssociatedCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx
    LinearEquiv (σ' := (centreQuotientEquiv (normalIdeal d t) Kx E.toRingEquiv hK).symm.toRingHom)
      (centreQuotientEquiv (normalIdeal d t) Kx E.toRingEquiv hK).toRingHom
      (originalNormalAssociatedGraded d t Ia)
      (⨁ q : ℕ, layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx q)
  quotient_mk : ∀ (q : ℕ) (g : HolGerm (ComplexModel (d+t))),
    eQuot q (Ideal.Quotient.mk (Ia ⊔ normalIdeal d t ^ (q+1)) g) =
      Ideal.Quotient.mk (Ix ⊔ Kx ^ (q+1)) (E g)
  layer_class :
    letI := tangentAlgebra d t
    ∀ (q : ℕ) (g : powerModule (HolGerm (ComplexModel d)) (normalIdeal d t) q),
      (eLayer q (idealPowerLayerMap (HolGerm (ComplexModel d)) Ia (normalIdeal d t) q g)).val =
        Ideal.Quotient.mk (Ix ⊔ Kx ^ (q+1)) (E g.val)
  whole_of :
    letI := tangentAlgebra d t
    ∀ (q : ℕ) (z : originalNormalGradedPiece d t Ia q),
      eWhole (DirectSum.of (fun q => originalNormalGradedPiece d t Ia q) q z) =
        DirectSum.of (layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx) q (eLayer q z)

/-- All fields use the genuine whole quotient, power-image and independently descended scalar maps. -/
def actualCanonicalRelativeBridge (d t : ℕ)
    (E : HolGerm (ComplexModel (d+t)) ≃ₐ[ℂ] HolGerm (ComplexModel (d+t)))
    (Ia Ix Kx : Ideal (HolGerm (ComplexModel (d+t))))
    (hI : Ix = Ideal.map E.toRingEquiv.toRingHom Ia)
    (hK : Kx = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t)) :
    NearbyRelativeCanonicalBridge d t E Ia Ix Kx hK := by
  letI := tangentAlgebra d t
  refine {
    eQuot := fun q => powerLayerQuotientEquiv Ia (normalIdeal d t) Ix Kx E.toRingEquiv hI hK q
    eLayer := fun q => actualPowerLayerCentreEquiv (HolGerm (ComplexModel d)) Ia (normalIdeal d t)
      Ix Kx E.toRingEquiv hI hK q
    eWhole := actualPowerAssociatedCentreEquiv (HolGerm (ComplexModel d)) Ia (normalIdeal d t)
      Ix Kx E.toRingEquiv hI hK
    quotient_mk := fun q g => powerLayerQuotientEquiv_mk Ia (normalIdeal d t) Ix Kx E.toRingEquiv hI hK q g
    layer_class := ?_
    whole_of := ?_ }
  · intro q g
    exact congrArg Subtype.val (actualPowerLayerAddEquiv_class (HolGerm (ComplexModel d))
      Ia (normalIdeal d t) Ix Kx E.toRingEquiv hI hK q g)
  · intro q z
    exact actualPowerAssociatedAddEquiv_of (HolGerm (ComplexModel d))
      Ia (normalIdeal d t) Ix Kx E.toRingEquiv hI hK q z

variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original data internally supply every full actual nearby quotient/layer/canonical-scalar bridge. -/
theorem exists_original_same_open_nearby_canonical_relative_bridge
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧
        ∃ hUT : U ⊆ Φ.target,
        ∀ (a : ComplexModel (d+t)) (ha : a ∈ U), a ∈ complexCoordinatePlane (d+t) d →
          let haT := hUT ha
          let y := actualFlatteningInverseMap x Φ a
          let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a haT
          let E := actualNearbyGermEquiv Φ a haT
          let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a)
          let Ix := wholeChartStalkIdeal A x y hy
          let Kx := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x y hy
          y ∈ C ∧ Ix ≤ Kx ∧
          ∃ _hI : Ix = Ideal.map E.toRingEquiv.toRingHom Ia,
          ∃ hK : Kx = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t),
          Nonempty (NearbyRelativeCanonicalBridge d t E Ia Ix Kx hK) := by
  obtain ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, hBridge⟩ :=
    exists_original_regular_same_open_nearby_relative_ideal_bridge C x hreg A hA hAC
  refine ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, ?_⟩
  intro a ha hPlane
  obtain ⟨hyC, hIK, hI, hK, _hpow⟩ := hBridge a ha hPlane
  exact ⟨hyC, hIK, hI, hK, ⟨actualCanonicalRelativeBridge d t _ _ _ _ hI hK⟩⟩

end
end Hironaka.HironakaSmoothCentreNearbyCanonicalLayers
