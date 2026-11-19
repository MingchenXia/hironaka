import Hironaka.Resolution.HironakaG4CompactWindowTasks
import Hironaka.Resolution.HironakaActualCompactCutComponentCentres
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CompactComponentTasks
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings GlobalComponents HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4GeneralSharpBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaActualCompactCutComponentCentres
  HironakaG4CompactWindowTasks HironakaG4CompactOpenServicePrefix HironakaG4SharpBadFootprint
  HironakaSharpOriginalDynamicGoodPrefixes HironakaActualGeometricCleanupComposition
  HironakaSharpNormalCrossingsOpenLocus RestrictEmptyTower
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The union of the actual compact global analytic components. -/
def compactComponentUnion (B : Set X) : Set X :=
  ⋃ K : {K : globalComponents (n := n) B // IsCompact K.val}, K.val.val

/-- This union is closed, even when other components are noncompact. -/
theorem isClosed_compactComponentUnion {B : Set X} (hB : IsComplexAnalyticSubset (n := n) B) :
    IsClosed (compactComponentUnion B) := by
  unfold compactComponentUnion
  have hLF : LocallyFinite (fun K : {K : globalComponents (n := n) B // IsCompact K.val} => K.val.val) :=
    (locallyFinite_globalComponents hB).comp_injective Subtype.val_injective
  exact hLF.isClosed_iUnion (fun K => K.property.isClosed)

theorem compactComponentUnion_subset {B : Set X} (hB : IsComplexAnalyticSubset (n := n) B) :
    compactComponentUnion B ⊆ B := by
  intro x hx
  obtain ⟨K,hxK⟩ := mem_iUnion.mp hx
  exact subset_of_mem_globalComponents hB K.val.property hxK

/-- A compact task can service exactly its compact original bad components;
noncompact components are not used as support. -/
theorem exists_compact_component_task_after_prefix (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hDisj : Pairwise (fun C D : globalComponents (n := n) (originalSharpBadLocus (n := n) W E) =>
      Disjoint C.val D.val)) (L : Set X) (hL : IsCompact L)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    let B := originalSharpBadLocus (n := n) W E
    let A := compactComponentUnion B
    ∃ (V : Opens X), IsCompact (B ∩ V) ∧ B ∩ V ⊆ A ∧
      ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),
        IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) ∧
        CurrentSharpCentres W E (T.append S) ∧ CentresOver (T.proj ⁻¹' (B ∩ V)) S ∧
        ∀ z ∈ strictAlong (T.append S) W, (T.append S).proj z ∈ L ∩ A →
          normalCrossingsAt (n := n) (strictAlong (T.append S) W)
            (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E z := by
  let B := originalSharpBadLocus (n := n) W E
  let A := compactComponentUnion B
  have hB : IsComplexAnalyticSubset (n := n) B :=
    isComplexAnalyticSubset_originalSharpBadLocus hW hE hdense
  have hA : IsClosed A := isClosed_compactComponentUnion hB
  have hAB : A ⊆ B := compactComponentUnion_subset hB
  have hLA : IsCompact (L ∩ A) := hL.inter_right hA
  have hLoc : ∀ x ∈ B ∩ (L ∩ A), ∃ V : Opens X, x ∈ V ∧ IsCompact (B ∩ V) ∧ B ∩ V ⊆ A := by
    intro x hx
    obtain ⟨K,hxK⟩ := mem_iUnion.mp hx.2.2
    let V := componentWindow hB K.val
    have hBV : B ∩ (V : Set X) = K.val.val := by
      rw [inter_comm]
      exact component_window_cut_eq hB hDisj K.val
    have hcompact : IsCompact (B ∩ V) := hBV ▸ K.property
    refine ⟨V,component_subset_window hB hDisj K.val hxK,hcompact,?_⟩
    rw [hBV]
    intro y hy
    exact mem_iUnion.mpr ⟨K,hy⟩
  obtain ⟨V,hcover,hcompact,hsub⟩ := compact_task_has_compact_bad_window_on_task
    (S := A) hB.isClosed hLA hLoc
  have hLAV : L ∩ A ⊆ V := by
    intro x hx
    exact hcover ⟨hAB hx.2,hx⟩
  obtain ⟨hFoot,_⟩ := currentSharpCentres_original_footprint hW.1 hE.1 T hSharp
  have hGood : ∀ z ∈ strictAlong T W, T.proj z ∈ Bᶜ →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z := by
    intro z hz hzo
    by_contra hnc
    exact hzo (hFoot ⟨hz,hnc⟩)
  obtain ⟨Z,S,hS,hSF,hSS,hOver,hNC⟩ :=
    exists_compact_open_service_after_prefix hn hW hE hdense V hcompact T hT hFull hSharp Bᶜ hGood
  refine ⟨V,hcompact,hsub,Z,S,hS,hSF,hSS,hOver,?_⟩
  intro z hz hzLA
  exact hNC z hz (Or.inr (hLAV hzLA))
end
end Hironaka.HironakaG4CompactComponentTasks
