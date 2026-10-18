/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveGluedStrictSets

/-! Actual range biholomorphisms descend genuine local regularity. Original
curve purity and original boundary smoothness are supplied internally. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveGlobalSmoothStrictSets
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  BlowupTowerTransforms HironakaSharpActualCurveTopologicalGluing
  HironakaSharpActualCurveGluedProjection HironakaSharpActualCurveStrictSetOverlaps
  HironakaSharpActualCurveGlobalManifold HironakaSharpActualCurveLocalRangeBiholomorphism
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveGluedStrictSets
  MarkedIdealTowerTransport HomogenizedGlueingTower NormalCrossings NormalCrossingsInvariance
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualFirstGoodLowerDimension
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalDeepProductBlowup HironakaSharpActualFiniteChronologicalHistory
  MarkedIdeals MarkedIdeals.MarkedIdeal
attribute [local instance] endpointChartedSpace
variable {n : ℕ} {X : CMfd.{u} n} {J : Type u}

/-- The same actual dimension is transported through the genuine range
biholomorphism and then through the actual open-subtype dictionary. -/
theorem localStrictSet_regularAtDim_iff (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (B : Set X) (hB : IsClosed B)
    (i : J) (z : A.finalSpace i) (k : ℕ) :
    RegularAtDim (n := n) (localStrictSet A B i) z k ↔
      RegularAtDim (n := n) (gluedStrictSet A B : Set (endpointManifold A hc))
        (endpointLocalInclusion A i z) k := by
  have h := CodimOnePartCanonical.regularAtDim_preimage_iff (localBiholomorphism A hc i)
    (A := (Subtype.val : localRangeOpen A hc i → endpointManifold A hc) ⁻¹' gluedStrictSet A B)
    (x := z) (k := k)
  rw [localBiholomorphism_preimage_gluedStrictSet A hc B hB i] at h
  exact h.trans AnalyticSubsetOpens.regularAtDim_preimage_val_iff

/-- Generic actual local smoothness descends using the already CONSTRUCTED
closed global set and a genuine representative of every global point. -/
theorem isClosedSubmanifold_gluedStrictSet (A : ActualEndpointHistories X J)
    (hc : ∀ x : X,∃ i : J,x∈A.openSet i) (B : Set X) (hB : IsClosed B)
    (hLocal : ∀ i : J,IsClosedSubmanifold n (localStrictSet A B i)) :
    IsClosedSubmanifold n (gluedStrictSet A B : Set (endpointManifold A hc)) := by
  refine ⟨isClosed_gluedStrictSet A B hB,?_⟩
  intro q hq
  obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective A q
  have hz := (mem_gluedStrictSet_iff A B hB i z).mp hq
  obtain ⟨k,hk⟩ := (hLocal i).2 z hz
  exact ⟨k,(localStrictSet_regularAtDim_iff A hc B hB i z k).mp hk⟩

section OriginalInput
variable (hn : 0<n) {W : Set X} {E : List (Set X)}
  (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
  (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)

/-- The actual retained original TEST supplies its SAME-map template TEST;
pure dimension one and local carrier smoothness are genuine outputs. -/
theorem original_localStrictSet_curve_geometry (i : X) :
    IsClosedSubmanifold n (localStrictSet (originalEndpointHistories hn hW hE hdense hr) W i) ∧
      ∀ z ∈ localStrictSet (originalEndpointHistories hn hW hE hdense hr) W i,
        RegularAtDim (n := n) (localStrictSet (originalEndpointHistories hn hW hE hdense hr) W i) z 1 := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet i
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let M := originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU 1
  let T := (A.prefixTower i).append (A.tail i)
  obtain ⟨π,hπ,_hFirst,_hPB,_hSteps,hTest,_hZ,_hD,_hProper,hDom,_hSNC,_hTrans,_hIso⟩ :=
    originalEndpointHistories_geometric_dictionary hn hW hE hdense hr i
  have hWU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hWF : M.IsWellFormed := ⟨hWU,isCoherent_originalMemberProduct hn hEU,
    isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hWU⟩
  have hGeom := actual_original_test_history_template M hWF T hTest
  have hPure := actual_template_regular_dimension hWU 1
    (fun (z : U) hz => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hr z.val hz)) T hGeom
  rw [N_geoTransformAlong] at hPure
  have hSM := hDom.isWellFormed.isClosedSubmanifold_N
  rw [N_geoTransformAlong] at hSM
  exact ⟨hSM,hPure⟩

/-- ONLY the original curve data construct the actual globally smooth carrier. -/
theorem isClosedSubmanifold_originalGluedStrictCurve :
    IsClosedSubmanifold n (originalGluedStrictSet hn hW hE hdense hr W) :=
  isClosedSubmanifold_gluedStrictSet _ (originalEndpointHistories_cover hn hW hE hdense hr)
    W hW.1 (fun i => (original_localStrictSet_curve_geometry hn hW hE hdense hr i).1)

/-- Every actual global carrier point has genuine regular dimension ONE. -/
theorem originalGluedStrictCurve_regularAtDim (q : originalEndpointManifold hn hW hE hdense hr)
    (hq : q ∈ originalGluedStrictSet hn hW hE hdense hr W) :
    RegularAtDim (n := n) (originalGluedStrictSet hn hW hE hdense hr W) q 1 := by
  let A := originalEndpointHistories hn hW hE hdense hr
  obtain ⟨i,z,rfl⟩ := endpointLocalInclusion_jointly_surjective A q
  have hz := (mem_gluedStrictSet_iff A W hW.1 i z).mp hq
  exact (localStrictSet_regularAtDim_iff A (originalEndpointHistories_cover hn hW hE hdense hr)
    W hW.1 i z 1).mp ((original_localStrictSet_curve_geometry hn hW hE hdense hr i).2 z hz)

/-- The real full ordered SNC list internally supplies EACH original strict
member's local smoothness, before any global divisor smoothness is asserted. -/
theorem original_localStrictSet_boundary_geometry (H : Set X) (hH : H ∈ E) (i : X) :
    IsClosedSubmanifold n (localStrictSet (originalEndpointHistories hn hW hE hdense hr) H i) := by
  let A := originalEndpointHistories hn hW hE hdense hr
  let U := A.openSet i
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let T := (A.prefixTower i).append (A.tail i)
  let L := EU.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate WU []) T).E
  obtain ⟨π,hπ,_hFirst,_hPB,_hSteps,_hTest,_hZ,_hD,_hProper,_hDom,hSNC,_hTrans,_hIso⟩ :=
    originalEndpointHistories_geometric_dictionary hn hW hE hdense hr i
  have hMem : localStrictSet A H i ∈ L := List.mem_append_left _
    (List.mem_map.mpr ⟨(Subtype.val : U → X) ⁻¹' H,List.mem_map.mpr ⟨H,hH,rfl⟩,rfl⟩)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hMem
  have hs := MonomialPart.isClosedSubmanifold_get hn hSNC j
  rw [hj] at hs
  exact hs

/-- EVERY actual original ordered boundary member yields a true global
smooth closed strict set, on the SAME internally constructed atlas. -/
theorem isClosedSubmanifold_originalGluedStrictBoundary (H : Set X) (hH : H ∈ E) :
    IsClosedSubmanifold n (originalGluedStrictSet hn hW hE hdense hr H) :=
  isClosedSubmanifold_gluedStrictSet _ (originalEndpointHistories_cover hn hW hE hdense hr)
    H (hE.1 H hH) (original_localStrictSet_boundary_geometry hn hW hE hdense hr H hH)

end OriginalInput

end
end Hironaka.HironakaSharpActualCurveGlobalSmoothStrictSets
