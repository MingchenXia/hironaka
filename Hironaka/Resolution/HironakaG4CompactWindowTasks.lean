import Hironaka.Resolution.HironakaG4CompactOpenServicePrefix
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CompactWindowTasks
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4CompactOpenServicePrefix
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A compact task admits a compact bad window when its own bad points
have suitable windows; their slices can be kept inside a designated set. -/
theorem compact_task_has_compact_bad_window_on_task {B L S : Set X} (hB : IsClosed B)
    (hL : IsCompact L)
    (hLocal : ∀ x ∈ B ∩ L, ∃ V : Opens X, x ∈ V ∧ IsCompact (B ∩ V) ∧ B ∩ V ⊆ S) :
    ∃ V : Opens X, B ∩ L ⊆ V ∧ IsCompact (B ∩ V) ∧ B ∩ V ⊆ S := by
  let C := B ∩ L
  have hC : IsCompact C := hL.inter_left hB
  let V : C → Opens X := fun x => (hLocal x.val x.property).choose
  have hxV (x : C) : x.val ∈ V x := (hLocal x.val x.property).choose_spec.1
  have hCV (x : C) : IsCompact (B ∩ V x) := (hLocal x.val x.property).choose_spec.2.1
  have hSV (x : C) : B ∩ V x ⊆ S := (hLocal x.val x.property).choose_spec.2.2
  have hcov : C ⊆ ⋃ x : C, (V x : Set X) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  obtain ⟨t,ht⟩ := hC.elim_finite_subcover (fun x : C => (V x : Set X))
    (fun x => (V x).isOpen) hcov
  let U : Opens X := ⟨⋃ x ∈ t, (V x : Set X),isOpen_biUnion (fun x _ => (V x).isOpen)⟩
  refine ⟨U,ht,?_,?_⟩
  · have heq : B ∩ U = ⋃ x ∈ t, (B ∩ V x) := by
      change B ∩ (⋃ x ∈ t, (V x : Set X)) = _
      simp only [inter_iUnion]
    rw [heq]
    exact t.isCompact_biUnion (fun x _ => hCV x)
  · rintro z ⟨hzB,hzU⟩
    change z ∈ ⋃ x ∈ t, (V x : Set X) at hzU
    obtain ⟨x,hx⟩ := mem_iUnion.mp hzU
    obtain ⟨_hxt,hzV⟩ := mem_iUnion.mp hx
    exact hSV x ⟨hzB,hzV⟩

/-- Each compact set meets only a compact open slice if every bad point has
such a slice; no discreteness or component-dimension assumption is needed. -/
theorem compact_task_has_compact_bad_window {B L : Set X} (hB : IsClosed B)
    (hL : IsCompact L)
    (hLocal : ∀ x ∈ B, ∃ V : Opens X, x ∈ V ∧ IsCompact (B ∩ V)) :
    ∃ V : Opens X, B ∩ L ⊆ V ∧ IsCompact (B ∩ V) := by
  obtain ⟨V,hcover,hcompact,_⟩ := compact_task_has_compact_bad_window_on_task
    (S := Set.univ) hB hL (fun x hx => by
      obtain ⟨V,hxV,hc⟩ := hLocal x hx.1
      exact ⟨V,hxV,hc,subset_univ _⟩)
  exact ⟨V,hcover,hcompact⟩
/-- One actual compact task can be served whenever the original bad locus
is locally covered by compact bad slices. The slices may be positive-dimensional. -/
theorem compact_window_full_boundary_service_after_prefix {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hLocal : ∀ x ∈ originalSharpBadLocus (n := n) W E, ∃ V : Opens X,
      x ∈ V ∧ IsCompact (originalSharpBadLocus (n := n) W E ∩ V))
    (L : Set X) (hL : IsCompact L)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    ∃ (V U : Opens X), L ⊆ U ∧
      IsCompact (originalSharpBadLocus (n := n) W E ∩ V) ∧
      ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),
        IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) ∧
        CurrentSharpCentres W E (T.append S) ∧
        CentresOver (T.proj ⁻¹' (originalSharpBadLocus (n := n) W E ∩ V)) S ∧
        ∀ z ∈ strictAlong (T.append S) W, (T.append S).proj z ∈ U →
          normalCrossingsAt (n := n) (strictAlong (T.append S) W)
            (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E z := by
  let B := originalSharpBadLocus (n := n) W E
  have hB : IsClosed B := isClosed_originalSharpBadLocus hW.1 hE.1
  obtain ⟨V,hBV,hK⟩ := compact_task_has_compact_bad_window hB hL hLocal
  let U : Opens X := ⟨Bᶜ ∪ V,hB.isOpen_compl.union V.isOpen⟩
  have hLU : L ⊆ U := by
    intro x hx
    by_cases hxb : x ∈ B
    · exact Or.inr (hBV ⟨hxb,hx⟩)
    · exact Or.inl hxb
  obtain ⟨hFoot,_⟩ :=
    HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hW.1 hE.1 T hSharp
  have hGood : ∀ z ∈ strictAlong T W, T.proj z ∈ Bᶜ →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z := by
    intro z hz hzo
    by_contra hnc
    exact hzo (hFoot ⟨hz,hnc⟩)
  obtain ⟨Z,S,hS,hSF,hSS,hOver,hNC⟩ :=
    exists_compact_open_service_full_boundary_after_prefix hW hE V hK T hT hFull hSharp Bᶜ hGood
  exact ⟨V,U,hLU,hK,Z,S,hS,hSF,hSS,hOver,hNC⟩

set_option linter.unusedVariables false in
theorem compact_window_service_after_prefix (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hLocal : ∀ x ∈ originalSharpBadLocus (n := n) W E, ∃ V : Opens X,
      x ∈ V ∧ IsCompact (originalSharpBadLocus (n := n) W E ∩ V))
    (L : Set X) (hL : IsCompact L)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    ∃ (V U : Opens X), L ⊆ U ∧
      IsCompact (originalSharpBadLocus (n := n) W E ∩ V) ∧
      ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),
        IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
        IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) ∧
        CurrentSharpCentres W E (T.append S) ∧
        CentresOver (T.proj ⁻¹' (originalSharpBadLocus (n := n) W E ∩ V)) S ∧
        ∀ z ∈ strictAlong (T.append S) W, (T.append S).proj z ∈ U →
          normalCrossingsAt (n := n) (strictAlong (T.append S) W)
            (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E z :=
  compact_window_full_boundary_service_after_prefix hW hE hLocal L hL T hT hFull hSharp


end
end Hironaka.HironakaG4CompactWindowTasks
