/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualSmoothCentreBlowupCoordinates
import Hironaka.Resolution.HironakaActualTangentCutLayers

/-!
# Actual blowup coordinates retaining a supplied centre flattening

The genuine blowup universal property and monomial local inverse construct
the whole source-coordinate square for the supplied target flattening.
No new target flattening is chosen. The original geometric consumer fixes
the normal-free flattening once and uses that very map in the actual blowup
square. Neither theorem assumes the square or a Bennett certificate.

Blueprint: `hironaka-actual-fixed-flattening-blowup-coordinates-extension.tex`.
-/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualFixedFlatteningBlowupCoordinates
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupLocalSurjectivity BlowupFibreDirection BlowupSNCTransform
  HironakaActualAnalyticBlowupTaylor HironakaActualPointBlowupCoordinates
  HironakaActualSmoothCentreBlowupCoordinates

section FixedFlattening
variable {n : ℕ}
variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The supplied genuine target flattening is retained in the actual whole blowup square. -/
theorem exists_actual_fixed_flattening_blowup_coordinates {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (z : Y) (k : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0)
    (hflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n k)) :
    ∃ (j : Fin n) (b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z)),
      Θ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z)=0 ∧ k ≤ j.val ∧
      (∀ i : Fin n, i.val < k → b i=0) ∧ b j=0 ∧
      ∀ y : Y, y ∈ (chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y ∈ Θ.source →
        π y ∈ flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
          actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j b (Θ.toFun (chartAt (ComplexModel n) z y)) := by
  have hzflat : π z ∈ flatDomain Φ := mem_flatDomain_self Φ
  obtain ⟨j,hj,O,hO,hzO,W,hWs,hWeq,hℓW,_⟩ :=
    exists_monomialLocalInverse hπ hΦsrc hflat hzflat
  obtain ⟨ℓ,⟨hℓs,hℓπ⟩,_⟩ := existsUnique_monomialLift hπ hΦsrc hflat hj
  have hWmem : ∀ y ∈ O, W y ∈ monomialDomain Φ k j := by
    intro y hy
    change monomial k j (W y) ∈ Φ.target
    rw [(hWeq y hy).2]
    exact Φ.mapsTo_toFun (hWeq y hy).1.2
  have hFinj := fderiv_complex_monomial_inverse_injective hO hWs hWmem hℓs
    (hℓW ℓ hℓs hℓπ) hzO
  obtain ⟨Θ,hΘsrc,hΘ0,hΘeq⟩ := exists_recentred_coords hO hWs hzO hFinj
  have hWj : W z j=0 := by
    have he := congrArg (fun w : ComplexModel n => w j) (hWeq z hzO).2
    simpa [monomial_apply,hΦ0] using he
  have hWt : ∀ i : Fin n, i.val < k → W z i=0 := by
    intro i hi
    have he := congrArg (fun w : ComplexModel n => w i) (hWeq z hzO).2
    simpa [monomial_apply,not_le.mpr hi,hΦ0] using he
  refine ⟨j,(fun i => W z i),Θ,hΘsrc,hΘ0,hj,hWt,hWj,?_⟩
  intro y hy hyΘ
  obtain ⟨hyO,hcoord⟩ := hΘeq hy hyΘ
  change Θ.toFun (chartAt (ComplexModel n) z y)=W y-W z at hcoord
  refine ⟨(hWeq y hyO).1,?_⟩
  rw [hcoord,← actual_smooth_centre_monomial_recentre k j (W z) (W y) hWt hWj]
  exact (hWeq y hyO).2.symm

end FixedFlattening

section OriginalCentre
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualTangentCutLayers HironakaHolomorphicJetChartInvariance
  HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreCoherentDomain HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalIdeal HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations
variable (d t : ℕ)
variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X]
  [IsComplexManifold (d+t) X] [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y]
  [IsComplexManifold (d+t) Y]
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/-- Original geometry supplies one common target chart for all free normal layers and the actual blowup square. -/
theorem exists_original_hs_constant_centre_free_normal_blowup_coordinates
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong (d+t) C π) (z : Y)
    (hreg : RegularAtDim (n := d+t) C (π z) d)
    (A : GermIdeal (d+t) X) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ, hilbertSamuelAt A y ℓ=hilbertSamuelAt A (π z) ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π z) (π z)),
      ∃ _hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) (π z)).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π z) (π z))=0,
      (∀ {y : X}, y ∈ (chartAt (ComplexModel (d+t)) (π z)).source →
        chartAt (ComplexModel (d+t)) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) (π z) y) ∈ complexCoordinatePlane (d+t) d)) ∧
      (let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A (π z) Φ) 0)
       ∀ q : ℕ,
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q) ∧
        Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t I0 q)) ∧
      ∃ (j : Fin (d+t)) (b : Fin (d+t) → ℂ)
        (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) z z)),
        Θ.source ⊆ (chartAt (ComplexModel (d+t)) z).target ∧
        Θ.toFun (chartAt (ComplexModel (d+t)) z z)=0 ∧ d ≤ j.val ∧
        (∀ i : Fin (d+t), i.val < d → b i=0) ∧ b j=0 ∧
        ∀ y : Y, y ∈ (chartAt (ComplexModel (d+t)) z).source →
          chartAt (ComplexModel (d+t)) z y ∈ Θ.source →
          π y ∈ flatDomain Φ ∧
          Φ.toFun (chartAt (ComplexModel (d+t)) (π z) (π y))=
            actualAnalyticBlowupMap {i : Fin (d+t) | d ≤ i.val} j b
              (Θ.toFun (chartAt (ComplexModel (d+t)) z y)) := by
  obtain ⟨Φ,hsrc,h0,hflat,hG⟩ :=
    exists_original_hs_constant_centre_normal_layers_finite_free d t C (π z) hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,hG,?_⟩
  exact exists_actual_fixed_flattening_blowup_coordinates hπ z d Φ hsrc h0 hflat

end OriginalCentre
end
end Hironaka.HironakaActualFixedFlatteningBlowupCoordinates
