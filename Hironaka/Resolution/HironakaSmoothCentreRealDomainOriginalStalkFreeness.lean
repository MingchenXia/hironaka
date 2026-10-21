/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.OriginalFixedFlatteningStalkDictionaryExact
import Hironaka.Resolution.HironakaSmoothCentreRealDomainNearbyFreeness
import Hironaka.Resolution.HironakaSmoothCentreNearbyCanonicalLayers

/-! # Actual original nonlinear stalks on the SAME uniform real free open
Complete three-node mathematics precedes code. A single chosen original
flattening supplies ALL true nonlinear whole stalk dictionaries. Fixed normal
ideals map to the original centre vanishing stalk ONLY at actual plane points.
Canonical original centre actions descend independently on genuine layers.
-/
set_option autoImplicit false
open Set Filter
open scoped DirectSum Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainOriginalStalkFreeness
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreCanonicalLayers HironakaSmoothCentreNearbyCanonicalLayers
  HironakaSmoothCentreRealDomainNearbyFreeness HironakaSmoothCentreRelativeIdeal
  HironakaHolomorphicJetRankLoci HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCentreScalars
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  RelativePrincipalizationSpan InvertibleIdealQuotient HadamardBridge

section Manifold
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]


end Manifold

section Centre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ANY fixed regular-centre flattening supplies the actual WHOLE original ideal/centre/ALL-power/canonical-layer bridge ONLY at true plane points. -/
theorem fixed_flattening_actual_original_centre_bridge
    (C : Set M) (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hAC : A.Le (vanishingIdeal (n := d+t) C)) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d))
    (a : ComplexModel (d+t)) (ha : a ∈ Φ.target) (hPlane : a ∈ complexCoordinatePlane (d+t) d) :
    let y := actualFlatteningInverseMap x Φ a
    let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a ha
    let E := actualNearbyGermEquiv Φ a ha
    let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a)
    let Ix := wholeChartStalkIdeal A x y hy
    let Kx := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x y hy
    y ∈ C ∧ Ix ≤ Kx ∧
    ∃ _hI : Ix = Ideal.map E.toRingEquiv.toRingHom Ia,
    ∃ hK : Kx = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t),
      Nonempty (NearbyRelativeCanonicalBridge d t E Ia Ix Kx hK) ∧
      ∀ q : ℕ, Kx ^ q = Ideal.map E.toRingEquiv.toRingHom (normalIdeal d t ^ q) := by
  have hdom := actualNearbyPoint_mem_flatDomain x Φ hsrc a ha
  have hImg : Φ.toFun (chartAt (ComplexModel (d+t)) x (actualFlatteningInverseMap x Φ a)) = a := by
    rw [actualNearbyPoint_chart_value x Φ hsrc a ha,Φ.right_inv a ha]
  have hyC : actualFlatteningInverseMap x Φ a ∈ C := by
    apply (hflat hdom.1 hdom.2).mpr
    rw [hImg]
    exact hPlane
  have hI := (whole_original_stalk_dictionary_at_actual_target A hA x Φ hsrc a ha).1.symm
  have hK := whole_nearby_vanishing_stalk_eq_map_normalIdeal x C Φ hsrc hflat a ha hPlane
  exact ⟨hyC,wholeChartStalkIdeal_le_of_original_le A _ hAC x _ hdom.1,hI,hK,
    ⟨actualCanonicalRelativeBridge d t _ _ _ _ hI hK⟩,
    fun q => whole_nearby_vanishing_stalk_pow_eq_map x C Φ hsrc hflat a ha hPlane q⟩

private theorem actual_module_flat_of_free {R L : Type*} [CommSemiring R] [AddCommMonoid L]
    [Module R L] (hf : Module.Free R L) : Module.Flat R L := by
  let : Module.Free R L := hf
  infer_instance

private theorem realCentreQuotientRingHomInvPair {R S : Type*} [CommRing R] [CommRing S]
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

private theorem realCentreQuotientRingHomInvPairSymm {R S : Type*} [CommRing R] [CommRing S]
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

attribute [local instance] realCentreQuotientRingHomInvPair realCentreQuotientRingHomInvPairSymm


/-- ONLY original geometry/coherence/containment gives ONE real open where ALL genuine ORIGINAL relative stalk degrees are finite/free/flat. -/
theorem exists_original_regular_real_all_relative_stalks_free_open
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
    ∃ hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
    ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
    ∃ U : Set (ComplexModel d), IsOpen U ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
    ∃ hpoint : ∀ a ∈ U, tangentInclusion d t a ∈ Φ.target ∩ complexCoordinatePlane (d+t) d,
      ∀ a (ha : a ∈ U),
        let a0 := tangentInclusion d t a
        let haT := (hpoint a ha).1
        let y := actualFlatteningInverseMap x Φ a0
        let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a0 haT
        let Ix := wholeChartStalkIdeal A x y hy
        let Kx := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x y hy
        y ∈ C ∧ Ix ≤ Kx ∧
        letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ Kx)
          (⨁ q : ℕ, layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
          (idealPowerAssociatedCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx).toSMul
        letI := idealPowerAssociatedCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx
        (Module.Free (HolGerm (ComplexModel (d+t)) ⧸ Kx)
          (⨁ q : ℕ, layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx q) ∧
         Module.Flat (HolGerm (ComplexModel (d+t)) ⧸ Kx)
          (⨁ q : ℕ, layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx q)) ∧
        ∀ q : ℕ,
          letI : SMul (HolGerm (ComplexModel (d+t)) ⧸ Kx)
            (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
            (idealPowerLayerCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx q).toSMul
          letI := idealPowerLayerCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx q
          Module.Finite (HolGerm (ComplexModel (d+t)) ⧸ Kx)
            (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q) ∧
          Module.Free (HolGerm (ComplexModel (d+t)) ⧸ Kx)
            (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q) ∧
          Module.Flat (HolGerm (ComplexModel (d+t)) ⧸ Kx)
            (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨Φ,hsrc,h0,hflat,U,hU,hmeet,hpoint,hcoord⟩ :=
    exists_original_regular_real_all_degree_canonical_centre_free_open C x hreg A hA
  refine ⟨Φ,hsrc,h0,hflat,U,hU,hmeet,hpoint,?_⟩
  intro a ha
  dsimp only
  let a0 := tangentInclusion d t a
  let haT := (hpoint a ha).1
  let y := actualFlatteningInverseMap x Φ a0
  let hy := actualNearbyPoint_mem_chart_source x Φ hsrc a0 haT
  let E := actualNearbyGermEquiv Φ a0 haT
  let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf A x Φ) a0)
  let Ix := wholeChartStalkIdeal A x y hy
  let Kx := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x y hy
  obtain ⟨hyC,hIK,_hI,hK,⟨bridge⟩,_hpow⟩ :=
    fixed_flattening_actual_original_centre_bridge C A hA hAC x Φ hsrc hflat a0 haT (hpoint a ha).2
  let := realCentreQuotientRingHomInvPair (normalIdeal d t) Kx E.toRingEquiv hK
  let := realCentreQuotientRingHomInvPairSymm (normalIdeal d t) Kx E.toRingEquiv hK
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalAssociatedGraded d t Ia) := (originalNormalAssociatedGradedCentreModule d t Ia).toSMul
  let := originalNormalAssociatedGradedCentreModule d t Ia
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ Kx)
    (⨁ q : ℕ, layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
    (idealPowerAssociatedCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx).toSMul
  let := idealPowerAssociatedCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx
  have hc := hcoord a ha
  let : Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalAssociatedGraded d t Ia) := hc.1.1
  have hfree : Module.Free (HolGerm (ComplexModel (d+t)) ⧸ Kx)
      (⨁ q : ℕ, layerFamily (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
    Module.Free.of_equiv bridge.eWhole
  let := hfree
  refine ⟨hyC,hIK,⟨hfree,actual_module_flat_of_free hfree⟩,?_⟩
  intro q
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalGradedPiece d t Ia q) := (originalNormalGradedPieceCentreModule d t Ia q).toSMul
  let := originalNormalGradedPieceCentreModule d t Ia q
  let : SMul (HolGerm (ComplexModel (d+t)) ⧸ Kx)
    (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
    (idealPowerLayerCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx q).toSMul
  let := idealPowerLayerCentreModule (HolGerm (ComplexModel (d+t))) Ix Kx q
  let : Module.Finite (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalGradedPiece d t Ia q) := (hc.2 q).1
  let : Module.Free (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t)
    (originalNormalGradedPiece d t Ia q) := (hc.2 q).2.1
  have hf : Module.Free (HolGerm (ComplexModel (d+t)) ⧸ Kx)
      (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
    Module.Free.of_equiv (bridge.eLayer q)
  have hfin : Module.Finite (HolGerm (ComplexModel (d+t)) ⧸ Kx)
      (idealPowerLayer (HolGerm (ComplexModel (d+t))) Ix Kx q) :=
    Module.Finite.of_surjective (bridge.eLayer q).toLinearMap (bridge.eLayer q).surjective
  let := hf
  exact ⟨hfin,hf,actual_module_flat_of_free hf⟩

end Centre

end
end Hironaka.HironakaSmoothCentreRealDomainOriginalStalkFreeness
