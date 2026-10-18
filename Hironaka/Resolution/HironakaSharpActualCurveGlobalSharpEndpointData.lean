/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveOriginalGlobalEndpoint
import Hironaka.Resolution.HironakaSharpActualCurveGlobalSmoothStrictSets

/-! Actual global sharp endpoint OUTPUT retains genuine local original
TEST/terminal histories and all ordered boundary readouts, not a loose atlas. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalSharpEndpointData
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveGlobalManifold
  HironakaSharpActualCurveGluedStrictSets HironakaSharpActualCurveGlobalStrictClosure
  HironakaSharpActualCurveGlobalGoodIsomorphism HironakaSharpActualCurveGlobalSmoothStrictSets
  HironakaSharpActualCurveLocallyFiniteBoundary HironakaSharpActualCurveGlobalBoundaryCoordinates
  HironakaSharpActualCurveBirthBoundaryOverlaps HironakaSharpActualCurveGlobalBirthCartierBoundary
  HironakaSharpActualCurveOriginalGlobalEndpoint HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualCurveExceptionalDifference HironakaSharpActualFiniteChronologicalHistory
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Ordinary OUTPUT data near an actual base point. In particular the
original E appears in the true finite full-boundary readout; arbitrary
empty global families cannot replace it. No such record is an input below. -/
structure FiniteOriginalSharpPresentation (W : Set X) (E : List (Set X))
    (π : Y → X) (F : ℕ → Set Y) (x : X) where
  baseOpen : Opens X
  point_mem : x∈baseOpen
  finalSpace : CMfd.{u} n
  history : BlowupTower (CMfd.of (n := n) baseOpen) finalSpace
  original_test : IsGeoTestTower
    (originalMemberProductMarked (X := CMfd.of (n := n) baseOpen)
      ((Subtype.val : baseOpen → X) ⁻¹' W) (E.map ((Subtype.val : baseOpen → X) ⁻¹' ·)) 1) history
  first_defect_empty : chronologicalDistinctDefect
    ((Subtype.val : baseOpen → X) ⁻¹' W) (E.map ((Subtype.val : baseOpen → X) ⁻¹' ·)) history=∅
  difference_empty : actualAmbientExceptionalDifference
    ((Subtype.val : baseOpen → X) ⁻¹' W) (E.map ((Subtype.val : baseOpen → X) ⁻¹' ·)) history=∅
  inclusion : finalSpace → Y
  openEmbedding : Topology.IsOpenEmbedding inclusion
  whole_range : range inclusion=π ⁻¹' (baseOpen : Set X)
  projection : ∀ z,π (inclusion z)=(history.proj z).val
  whole_curve : inclusion ⁻¹' strictTransform n π W=
    strictTransform n history.proj ((Subtype.val : baseOpen → X) ⁻¹' W)
  whole_boundary : ∀ k,inclusion ⁻¹' F k=boundaryReadout
    (geoTransformAlong (geometricTemplate (univ : Set baseOpen)
      (E.map ((Subtype.val : baseOpen → X) ⁻¹' ·))) history).E k

/-- Genuine mathematical OUTPUT geometry. The finite original presentations
couple projection, strict curve and ALL indexed E-readouts to the original
data, so an unrelated empty family is not a replacement conclusion. -/
structure GlobalSharpCurveEndpoint (W : Set X) (E : List (Set X)) where
  ambient : CMfd.{u} n
  projection : ambient → X
  boundary : ℕ → Set ambient
  bornDivisor : EffectiveDivisor n ambient
  surjective : Function.Surjective projection
  proper : IsProperMap projection
  holomorphic : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ projection
  good_isomorphism : IsIsomorphismOver n projection (originalGoodLocus (n := n) W E)
  strict_smooth : IsClosedSubmanifold n (strictTransform n projection W)
  strict_pure : ∀ q∈strictTransform n projection W,RegularAtDim (n := n) (strictTransform n projection W) q 1
  strict_image : projection '' strictTransform n projection W=W
  boundary_closed : ∀ k,IsClosed (boundary k)
  boundary_locallyFinite : LocallyFinite boundary
  boundary_coordinates : ∀ q : ambient,∃ S : ℕ → Finset (Fin n),
    IsCoordinateFamilyAt n boundary S q ∧
      (∀ k,q∈boundary k → (S k).card=1) ∧ Set.InjOn S {k | q∈boundary k}
  transverse_coordinates : ∀ q∈strictTransform n projection W,
    ∃ (S₀ : Finset (Fin n)) (S : ℕ → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option ℕ => o.elim (strictTransform n projection W) boundary)
        (fun o => o.elim S₀ S) q ∧ ∀ k,q∈boundary k → (S k).card=1 ∧ Disjoint (S k) S₀
  born_ideal : bornDivisor.ideal=vanishingIdeal (n := n) (⋃ j,boundary (E.length+j))
  born_support : bornDivisor.support=⋃ j,boundary (E.length+j)
  born_coherent : bornDivisor.ideal.IsCoherent
  born_analytic : IsComplexAnalyticSubset (n := n) bornDivisor.support
  born_reduced : ∀ q g,HolomorphicAt n g q → ∀ k : ℕ,0<k →
    (bornDivisor.ideal.mem q (fun y => g y^k) ↔ bornDivisor.ideal.mem q g)
  exceptional_support : exceptionalLocus n projection⊆bornDivisor.support
  born_over_bad : bornDivisor.support⊆projection ⁻¹' originalSharpBadLocus (n := n) W E
  local_presentation : ∀ x : X,FiniteOriginalSharpPresentation W E projection boundary x

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W⊆closure (W \ ⋃ H∈E,H)) (hr : ∀ x∈W,RegularAtDim (n := n) W x 1)

/-- All actual local original TESTs, terminality and WHOLE readout/map
dictionaries are constructed on the SAME global witnesses internally. -/
def originalFiniteSharpPresentation (x : X) :
    FiniteOriginalSharpPresentation W E (Y := CMfd.of (n := n)
      (originalEndpointManifold hn hW hE hdense hr))
      (originalEndpointProjection hn hW hE hdense hr)
      (originalGluedBoundaryReadout hn hW hE hdense hr) x := by
  apply Classical.choice
  let A := originalEndpointHistories hn hW hE hdense hr
  let hc := originalEndpointHistories_cover hn hW hE hdense hr
  obtain ⟨π,hπ,_hFirst,_hPB,_hSteps,hTest,hZ,hD,_hProper,_hDom,_hSNC,_hTrans,_hIso⟩ :=
    originalEndpointHistories_geometric_dictionary hn hW hE hdense hr x
  exact ⟨{
    baseOpen := A.openSet x
    point_mem := originalEndpointHistories_point_mem hn hW hE hdense hr x
    finalSpace := A.finalSpace x
    history := (A.prefixTower x).append (A.tail x)
    original_test := hTest
    first_defect_empty := hZ
    difference_empty := hD
    inclusion := endpointLocalInclusion A x
    openEmbedding := endpointLocalInclusion_openEmbedding A x
    whole_range := localInclusion_range A x
    projection := gluedProjection_local_full A x
    whole_curve := preimage_strictTransform_gluedProjection A hc x W
    whole_boundary := preimage_originalGluedBoundaryReadout hn hW hE hdense hr x }⟩

/-- ONLY original geometric inputs construct the SAME globally defined
sharp endpoint, with all genuine local original histories as OUTPUTS. -/
def originalGlobalSharpCurveEndpoint : GlobalSharpCurveEndpoint W E := by
  let Yg := CMfd.of (n := n) (originalEndpointManifold hn hW hE hdense hr)
  let π : Yg → X := originalEndpointProjection hn hW hE hdense hr
  let F : ℕ → Set Yg := originalGluedBoundaryReadout hn hW hE hdense hr
  let D : EffectiveDivisor n Yg := originalBornDivisor hn hW hE hdense hr
  let V : Set Yg := originalGluedStrictSet hn hW hE hdense hr W
  have hStrict : V=strictTransform n π W :=
    originalGluedStrictCurve_eq_strictTransform hn hW hE hdense hr
  have hSmooth : IsClosedSubmanifold n (strictTransform n π W) :=
    (congrArg (IsClosedSubmanifold n) hStrict).mp
      (isClosedSubmanifold_originalGluedStrictCurve hn hW hE hdense hr)
  have hPure : ∀ q∈strictTransform n π W,RegularAtDim (n := n) (strictTransform n π W) q 1 := by
    intro q hq
    have hqV : q∈V := (congrArg (fun B : Set Yg => q∈B) hStrict).mpr hq
    exact (congrArg (fun B : Set Yg => RegularAtDim (n := n) B q 1) hStrict).mp
      (originalGluedStrictCurve_regularAtDim hn hW hE hdense hr q hqV)
  let P : Set Yg → Prop := fun B => ∀ q∈B,
    ∃ (S₀ : Finset (Fin n)) (S : ℕ → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option ℕ => o.elim B F) (fun o => o.elim S₀ S) q ∧
        ∀ k,q∈F k → (S k).card=1 ∧ Disjoint (S k) S₀
  have hOldFrame : P V := fun q hq => original_globalBoundary_transverse_coordinates hn hW hE hdense hr q hq
  have hFrame : P (strictTransform n π W) := (congrArg P hStrict).mp hOldFrame
  have hDanalytic : IsComplexAnalyticSubset (n := n) D.support := by
    rw [originalBornDivisor_support hn hW hE hdense hr]
    exact originalBornSupport_isComplexAnalyticSubset hn hW hE hdense hr
  have hSupports := originalBornDivisor_support_inclusions hn hW hE hdense hr
  exact {
    ambient := Yg
    projection := π
    boundary := F
    bornDivisor := D
    surjective := originalEndpointProjection_surjective hn hW hE hdense hr
    proper := originalEndpointProjection_isProperMap hn hW hE hdense hr
    holomorphic := originalEndpointProjection_contMDiff hn hW hE hdense hr
    good_isomorphism := originalEndpointProjection_isIsomorphismOver_good hn hW hE hdense hr
    strict_smooth := hSmooth
    strict_pure := hPure
    strict_image := image_conventionalStrictCurve_eq_original hn hW hE hdense hr
    boundary_closed := isClosed_originalGluedBoundaryReadout hn hW hE hdense hr
    boundary_locallyFinite := locallyFinite_originalGluedBoundaryReadout hn hW hE hdense hr
    boundary_coordinates := original_globalBoundary_snc_coordinates hn hW hE hdense hr
    transverse_coordinates := hFrame
    born_ideal := originalBornDivisor_ideal hn hW hE hdense hr
    born_support := originalBornDivisor_support hn hW hE hdense hr
    born_coherent := originalBornDivisor_coherent hn hW hE hdense hr
    born_analytic := hDanalytic
    born_reduced := fun q g hg k hk => vanishingIdeal_mem_positive_power_iff _ q g hg hk
    exceptional_support := hSupports.1
    born_over_bad := hSupports.2
    local_presentation := originalFiniteSharpPresentation hn hW hE hdense hr }

include hn hW hE hdense hr in
theorem exists_originalGlobalSharpCurveEndpoint : Nonempty (GlobalSharpCurveEndpoint W E) :=
  ⟨originalGlobalSharpCurveEndpoint hn hW hE hdense hr⟩

end OriginalInput
end
end Hironaka.HironakaSharpActualCurveGlobalSharpEndpointData
