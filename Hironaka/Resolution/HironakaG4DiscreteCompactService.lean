import Hironaka.Resolution.HironakaG4CompactOpenServicePrefix
import Mathlib.Topology.DiscreteSubset

/-! Compact tasks can be served for an original discrete sharp-bad locus. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4DiscreteCompactService
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4CompactOpenServicePrefix
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- For a discrete original bad locus, an arbitrary compact base set has
an open neighborhood served by one actual finite sharp tail. -/
theorem exists_discrete_compact_service_after_prefix
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hdiscrete : IsDiscrete (originalSharpBadLocus (n := n) W E))
    (L : Set X) (hL : IsCompact L)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    ∃ (U : Opens X), L ⊆ U ∧ ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) ∧
      CurrentSharpCentres W E (T.append S) ∧
      CentresOver (T.proj ⁻¹' (originalSharpBadLocus (n := n) W E ∩ L)) S ∧
      ∀ z ∈ strictAlong (T.append S) W, (T.append S).proj z ∈ U →
        normalCrossingsAt (n := n) (strictAlong (T.append S) W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E z := by
  let B := originalSharpBadLocus (n := n) W E
  have hBclosed : IsClosed B := isClosed_originalSharpBadLocus hW.1 hE.1
  have hBL : IsCompact (B ∩ L) := hL.inter_left hBclosed
  obtain ⟨V,hV,hVB⟩ := isDiscrete_iff_forall_subset_exists_isOpen.mp hdiscrete (B ∩ L) inter_subset_left
  let V₀ : Opens X := ⟨V,hV⟩
  let U : Opens X := ⟨Bᶜ ∪ V, hBclosed.isOpen_compl.union hV⟩
  have hLU : L ⊆ U := by
    intro x hx
    by_cases hxb : x ∈ B
    · right
      have : x ∈ V ∩ B := hVB.symm ▸ ⟨hxb,hx⟩
      exact this.1
    · exact Or.inl hxb
  have hBV : B ∩ V₀ = B ∩ L := by
    rw [inter_comm]
    exact hVB
  have hK : IsCompact (B ∩ V₀) := by
    rw [hBV]
    exact hBL
  obtain ⟨hFoot,_⟩ :=
    HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hW.1 hE.1 T hSharp
  have hGood : ∀ z ∈ strictAlong T W, T.proj z ∈ Bᶜ →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z := by
    intro z hz hzo
    by_contra hnc
    exact hzo (hFoot ⟨hz,hnc⟩)
  obtain ⟨Z,S,hS,hSF,hSS,hOver,hNC⟩ :=
    exists_compact_open_service_after_prefix hn hW hE hdense V₀ hK T hT hFull hSharp Bᶜ hGood
  refine ⟨U,hLU,Z,S,hS,hSF,hSS,?_,hNC⟩
  change CentresOver (T.proj ⁻¹' (B ∩ L)) S
  rw [←hBV]
  exact hOver
end
end Hironaka.HironakaG4DiscreteCompactService
