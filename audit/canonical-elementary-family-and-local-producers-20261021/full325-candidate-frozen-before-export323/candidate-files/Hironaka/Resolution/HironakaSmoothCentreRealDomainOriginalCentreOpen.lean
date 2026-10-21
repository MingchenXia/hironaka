/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothCentreRealDomainOriginalStalkFreeness

/-! # A true relatively open ORIGINAL centre locus for all genuine degrees
Complete two-node mathematics precedes code. One fixed real flattening maps
its nonvanishing base open to an actual relatively open locus in ORIGINAL C,
accumulating at original x. Intrinsic chart/sheaf conclusions remain further
obligations; no origin flatness or every-component density is asserted.
-/
set_option autoImplicit false
open Set Filter
open scoped DirectSum Topology Manifold ContDiff
namespace Hironaka.HironakaSmoothCentreRealDomainOriginalCentreOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks
  HironakaSmoothCentreNearbyIdeal HironakaSmoothCentreRelativeIdeal HironakaSmoothCentreRealDomainOriginalStalkFreeness
  HironakaHolomorphicJetRankLoci HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalGradedAlgebra HironakaRelativeNormalCentreScalars
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  BlowupFlatCoordinates RelativePrincipalizationSpan InvertibleIdealQuotient HadamardBridge

/-- ALL true layers and the ENTIRE associated sum with their independently descended centre action. -/
def allRelativeIdealDegreesFree {R : Type*} [CommRing R] (I J : Ideal R) : Prop :=
  (letI : SMul (R ⧸ J) (⨁ q : ℕ, layerFamily R I J q) :=
      (idealPowerAssociatedCentreModule R I J).toSMul
   letI := idealPowerAssociatedCentreModule R I J
   Module.Free (R ⧸ J) (⨁ q : ℕ, layerFamily R I J q) ∧
     Module.Flat (R ⧸ J) (⨁ q : ℕ, layerFamily R I J q)) ∧
  ∀ q : ℕ,
    letI : SMul (R ⧸ J) (idealPowerLayer R I J q) :=
      (idealPowerLayerCentreModule R I J q).toSMul
    letI := idealPowerLayerCentreModule R I J q
    Module.Finite (R ⧸ J) (idealPowerLayer R I J q) ∧
      Module.Free (R ⧸ J) (idealPowerLayer R I J q) ∧
      Module.Flat (R ⧸ J) (idealPowerLayer R I J q)

section Centre
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- The true ORIGINAL open underlying a fixed coordinate base open. -/
def originalCentreBaseOpen (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (U : Set (ComplexModel d)) : Set M :=
  flatDomain Φ ∩ (fun y => tangentProjection d t
    (Φ.toFun (chartAt (ComplexModel (d+t)) x y))) ⁻¹' U

/-- Local continuity on the actual chart/flattening domain makes this a real ORIGINAL open. -/
theorem isOpen_originalCentreBaseOpen (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (U : Set (ComplexModel d)) (hU : IsOpen U) :
    IsOpen (originalCentreBaseOpen x Φ U) := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  have hF : ContinuousAt (fun y' => Φ.toFun (chartAt (ComplexModel (d+t)) x y')) y :=
    ((Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hy.1.2)).continuousAt).comp
      ((chartAt (ComplexModel (d+t)) x).continuousAt hy.1.1)
  have hp := (tangentProjection d t).continuous.continuousAt.comp hF
  exact Filter.inter_mem ((isOpen_flatDomain Φ).mem_nhds hy.1)
    (hp.preimage_mem_nhds (hU.mem_nhds hy.2))

/-- BOTH complete set inclusions for the real original centre image under the SAME flattening. -/
theorem originalCentreBaseOpen_centre_eq_image (C : Set M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d))
    (U : Set (ComplexModel d)) (hpoint : ∀ a ∈ U, tangentInclusion d t a ∈ Φ.target) :
    C ∩ originalCentreBaseOpen x Φ U =
      (fun a => actualFlatteningInverseMap x Φ (tangentInclusion d t a)) '' U := by
  ext y
  constructor
  · intro hy
    let a := tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x y))
    have hplane := (hflat hy.2.1.1 hy.2.1.2).mp hy.1
    refine ⟨a,hy.2.2,?_⟩
    change actualFlatteningInverseMap x Φ
      (tangentInclusion d t (tangentProjection d t
        (Φ.toFun (chartAt (ComplexModel (d+t)) x y)))) = y
    rw [tangentInclusion_projection_eq_of_mem_plane d t hplane]
    exact flatInverse_flat Φ hy.2.1
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨hdom,hF⟩ := flatInverse_mem Φ (hpoint a ha) hsrc
    have hyC : actualFlatteningInverseMap x Φ (tangentInclusion d t a) ∈ C := by
      apply (hflat hdom.1 hdom.2).mpr
      rw [hF]
      exact tangentInclusion_mem_plane d t a
    refine ⟨hyC,hdom,?_⟩
    change tangentProjection d t (Φ.toFun (chartAt (ComplexModel (d+t)) x
      (actualFlatteningInverseMap x Φ (tangentInclusion d t a)))) ∈ U
    simp only [actualFlatteningInverseMap]
    rw [hF,tangentProjection_tangentInclusion]
    exact ha

/-- Accumulation in the real base open transfers through the actual continuous inverse. -/
theorem originalCentreBaseOpen_mem_closure (C : Set M) (x : M)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d))
    (U : Set (ComplexModel d))
    (hmeet : ∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty)
    (hpoint : ∀ a ∈ U, tangentInclusion d t a ∈ Φ.target) :
    x ∈ closure (C ∩ originalCentreBaseOpen x Φ U) := by
  let f := fun a => actualFlatteningInverseMap x Φ (tangentInclusion d t a)
  have hinv : ContinuousAt (actualFlatteningInverseMap x Φ) (0 : ComplexModel (d+t)) :=
    (actualFlatteningInverseMap_mdifferentiable x Φ hsrc 0
    (actualFlattening_target_zero_mem x Φ h0)).continuousAt
  have hinc : Tendsto (tangentInclusion d t) (𝓝 (0 : ComplexModel d))
      (𝓝 (0 : ComplexModel (d+t))) := by
    simpa only [map_zero] using (tangentInclusion d t).continuous.tendsto (0 : ComplexModel d)
  have ht : Tendsto f (𝓝 (0 : ComplexModel d)) (𝓝 x) := by
    have ht' := hinv.tendsto.comp hinc
    simpa only [f,Function.comp_def,actualFlatteningInverseMap_zero x Φ h0] using ht'
  rw [originalCentreBaseOpen_centre_eq_image C x Φ hsrc hflat U hpoint]
  apply mem_closure_iff_nhds.mpr
  intro V hV
  obtain ⟨a,haV,haU⟩ := hmeet (f ⁻¹' V) (ht.eventually hV)
  exact ⟨f a,haV,⟨a,haU,rfl⟩⟩

/-- Original inputs INTERNALLY give all genuine original degrees on ONE real relatively open centre locus. -/
theorem exists_original_regular_relative_centre_open_all_stalk_degrees_free
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) (hAC : A.Le (vanishingIdeal (n := d+t) C)) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
    ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target,
    ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0,
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
    ∃ O : Set M, IsOpen O ∧
    ∃ hOdom : O ⊆ flatDomain Φ,
      x ∈ closure (C ∩ O) ∧
      ∀ (y : M) (hyCO : y ∈ C ∩ O),
        let hy := (hOdom hyCO.2).1
        let Ix := wholeChartStalkIdeal A x y hy
        let Kx := wholeChartStalkIdeal (vanishingIdeal (n := d+t) C) x y hy
        y ∈ C ∧ Ix ≤ Kx ∧ allRelativeIdealDegreesFree Ix Kx := by
  obtain ⟨Φ,hsrc,h0,hflat,U,hU,hmeet,hpoint,hfree⟩ :=
    exists_original_regular_real_all_relative_stalks_free_open C x hreg A hA hAC
  let O := originalCentreBaseOpen x Φ U
  have hOdom : O ⊆ flatDomain Φ := fun _ hy => hy.1
  refine ⟨Φ,hsrc,h0,hflat,O,isOpen_originalCentreBaseOpen x Φ U hU,hOdom,?_,?_⟩
  · exact originalCentreBaseOpen_mem_closure C x Φ hsrc h0 hflat U hmeet
      (fun a ha => (hpoint a ha).1)
  · intro y hyCO
    have himg : y ∈ (fun a => actualFlatteningInverseMap x Φ (tangentInclusion d t a)) '' U := by
      rw [← originalCentreBaseOpen_centre_eq_image C x Φ hsrc hflat U
        (fun a ha => (hpoint a ha).1)]
      exact hyCO
    obtain ⟨a,ha,rfl⟩ := himg
    exact hfree a ha

end Centre

end
end Hironaka.HironakaSmoothCentreRealDomainOriginalCentreOpen
