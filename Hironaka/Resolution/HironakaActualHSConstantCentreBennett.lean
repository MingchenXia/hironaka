/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFixedFlatteningHSComparison
import Hironaka.Resolution.HironakaActualReducedCentreBennett
import Hironaka.Resolution.HironakaActualBlowupOffCentreIntrinsicHS
import Hironaka.Resolution.HironakaActualStandardNormalIndependence
import Hironaka.Resolution.HironakaActualHSConstantSingularCentre

/-!
# Intrinsic Bennett nonincrease for an actual constant-HS smooth centre

The fixed-chart intermediate uses genuine canonical reduced normal powers
for the same actual flattened original vanishing ideal. Whole original/model
ideal and HS dictionaries transport the proved model inequality to the
arbitrary original geometric blowup, including exceptional points.
The geometric endpoint obtains those powers internally from the original
HS-constant regular-centre data, retaining the one chosen target flattening.

Blueprint: `hironaka-actual-hs-constant-centre-bennett-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualHSConstantCentreBennett
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaHolomorphicJetChartInvariance HironakaActualFormalInitialDiagram
  HironakaActualCoefficientPresentationCentrePower HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualCoefficientAnalyticBlowup
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalDeformationInitialRelations
  HironakaSmoothCentreCoherentDomain HironakaActualFixedFlatteningHSComparison
  HironakaActualReducedCentreBennett HironakaActualBlowupOffCentreIntrinsicHS
  HironakaActualStandardNormalIndependence

section FixedChart
variable (d t : ℕ) {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]

/-- Genuine canonical normal powers in the supplied chart give actual geometric Bennett at every order. -/
theorem hilbertSamuelAt_actual_fixed_flattening_blowup_le {C : Set X} {π : Y → X}
    (hπ : IsBlowupAlong (d+t) C π) (z : Y)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) (π z) (π z)))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) (π z)).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) (π z) (π z))=0)
    (hflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel (d+t)) (π z)).source →
      chartAt (ComplexModel (d+t)) (π z) y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) (π z) y) ∈ complexCoordinatePlane (d+t) d))
    (W : Set X)
    (hV : let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n := d+t) W) (π z) Φ) 0)
      let K0 := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0
      ∀ a : actualInitialVertices MonomialOrder.degLex K0,
        actualReducedVertexSeries MonomialOrder.degLex K0 a ∈
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val)
    (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) z ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := d+t) W) (π z) ℓ := by
  obtain ⟨J,b,Θ,_hΘsrc,_hΘ0,hJd,_hbt,_hbj,_hsquare,hI,hHS⟩ :=
    exists_actual_fixed_flattening_blowup_hs_comparisons hπ z d Φ hsrc h0 hflat W
  let A := actualFixedFlatteningSet (π z) Φ W
  let P : Ideal (HolGerm (ComplexModel (d+t))) → Prop := fun I =>
    ∀ a : actualInitialVertices MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I),
      actualReducedVertexSeries MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a ∈
          actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
            Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val
  have hVA : P (originalCoherentOriginIdeal (vanishingIdeal (n := d+t) A)) :=
    Eq.mp (congrArg P hI) hV
  let j : Fin t := ⟨J.val-d,by have hjlt := J.isLt; omega⟩
  have hJ : j.natAdd d=J := by
    apply Fin.ext
    change d+(J.val-d)=J.val
    omega
  have hmodel := hilbertSamuelAt_actual_reduced_centre_strict_le d t A hVA j b ℓ
  calc
    _ = hilbertSamuelAt (vanishingIdeal (n := d+t)
        (strictTransform (d+t) (HironakaActualAnalyticBlowupTaylor.actualAnalyticBlowupMap
          {i : Fin (d+t) | d ≤ i.val} J b) A)) 0 ℓ := (hHS ℓ).2
    _ ≤ hilbertSamuelAt (vanishingIdeal (n := d+t) A) 0 ℓ := by
      simpa only [actualTangentCentreVariables_eq_tail,hJ] using hmodel
    _ = _ := ((hHS ℓ).1).symm

end FixedChart

section OriginalCentre
variable (d t : ℕ) {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel (d+t)) X] [IsComplexManifold (d+t) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel (d+t)) Y] [IsComplexManifold (d+t) Y]

/-- Original analytic constant-HS regular-centre geometry alone gives actual intrinsic Bennett. -/
theorem hilbertSamuelAt_actual_hs_constant_centre_blowup_le {C W : Set X} {π : Y → X}
    (hπ : IsBlowupAlong (d+t) C π) (z : Y)
    (hreg : RegularAtDim (n := d+t) C (π z) d)
    (hW : IsComplexAnalyticSubset (n := d+t) W)
    (hhs : ∀ y ∈ C, ∀ ℓ : ℕ,
      hilbertSamuelAt (vanishingIdeal (n := d+t) W) y ℓ=
        hilbertSamuelAt (vanishingIdeal (n := d+t) W) (π z) ℓ)
    (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := d+t) (strictTransform (d+t) π W)) z ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := d+t) W) (π z) ℓ := by
  obtain ⟨Φ,hsrc,h0,hflat,hV⟩ :=
    exists_original_hs_constant_centre_reduced_normal_powers (d := d) (t := t)
      C (π z) hreg (vanishingIdeal (n := d+t) W) (CartanIrreducible.cartanCoherence W hW) hhs
  exact hilbertSamuelAt_actual_fixed_flattening_blowup_le d t hπ z Φ hsrc h0 hflat W hV ℓ

end OriginalCentre

section AllPoints
variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Every actual blowup point satisfies Bennett for an original HS-constant closed smooth centre. -/
theorem hilbertSamuelAt_actual_hs_constant_smooth_centre_blowup_le {C W : Set X} {π : Y → X}
    (hπ : IsBlowupAlong n C π) (hC : IsClosedSubmanifold n C)
    (hW : IsComplexAnalyticSubset (n := n) W)
    (hhs : ∀ x ∈ C, ∀ y ∈ C, ∀ ℓ : ℕ,
      hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ=
        hilbertSamuelAt (vanishingIdeal (n := n) W) y ℓ)
    (z : Y) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := n) W) (π z) ℓ := by
  by_cases hz : π z ∈ C
  · obtain ⟨d,hreg⟩ := hC.2 (π z) hz
    obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hreg.1
    exact hilbertSamuelAt_actual_hs_constant_centre_blowup_le d t hπ z hreg hW
      (fun y hy ℓ => hhs y hy (π z) hz ℓ) ℓ
  · exact (hilbertSamuelAt_actual_strict_blowup_off_centre
      (X := BlowupTowers.CMfd.of X) (Y := BlowupTowers.CMfd.of Y) hπ hW z hz ℓ).le

end AllPoints

section ChosenSingularCentre
open MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SimultaneousNormalCrossings
  BlowupTowers BlowupTowerTransforms ResolutionDriver HironakaActualReferenceHSSingularCentre
  HironakaActualHSConstantSingularCentre AnalyticDimensionBasics
variable {n : ℕ}

/-- Original singular geometry internally selects the same proper first blowup with all-point Bennett and full boundary data. -/
theorem exists_actual_original_singular_centre_proper_blowup_bennett
    {X : CMfd.{u} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ} (hd : d < n)
    (hpure : IsPureDim (n := n) W d) (hns : ¬ IsClosedSubmanifold n W)
    {E : List (Set X)} (hE : IsSNCDivisor n E) :
    ∃ (a : X) (C : Set X) (Y : CMfd.{u} n) (π : Y → X),
      a ∈ W \ regularLocus (n := n) W d ∧ C.Nonempty ∧
      C ⊆ W \ regularLocus (n := n) W d ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      (∀ x ∈ C, ∀ i, hilbertSamuelAt (vanishingIdeal (n := n) W) x i=
        hilbertSamuelAt (vanishingIdeal (n := n) W) a i) ∧
      IsBlowupAlong n C π ∧ IsProperMap π ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (W \ regularLocus (n := n) W d)ᶜ ∧
      IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]) ∧
      (∀ y : Y, π y ∉ C → ∀ i,
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) y i=
          hilbertSamuelAt (vanishingIdeal (n := n) W) (π y) i) ∧
      C=maxLocus ((CanonicalCentres.canonicalInvariant n).inv
        (actualReferenceHSMarked (n := n) W E a) (.refl : BlowupTower X X))
        (actualReferenceHSMarked (n := n) W E a).cosupp ∧
      ∀ y : Y, ∀ ℓ : ℕ,
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) y ℓ ≤
          hilbertSamuelAt (vanishingIdeal (n := n) W) (π y) ℓ := by
  obtain ⟨a,C,Y,π,ha,hCne,hCS,hCadm,hconst,hπ,hproper,hholo,hiso,hE',hoff,hCeq⟩ :=
    exists_actual_original_hs_constant_singular_centre_proper_blowup hW hK hd hpure hns hE
  refine ⟨a,C,Y,π,ha,hCne,hCS,hCadm,hconst,hπ,hproper,hholo,hiso,hE',hoff,hCeq,?_⟩
  intro y ℓ
  exact hilbertSamuelAt_actual_hs_constant_smooth_centre_blowup_le hπ hCadm.1 hW
    (fun x hx z hz i => (hconst x hx i).trans (hconst z hz i).symm) y ℓ

end ChosenSingularCentre
end
end Hironaka.HironakaActualHSConstantCentreBennett
