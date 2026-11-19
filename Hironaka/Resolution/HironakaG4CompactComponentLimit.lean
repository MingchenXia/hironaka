import Hironaka.Resolution.HironakaG4DiscreteLimitReadback
import Hironaka.Resolution.HironakaG4CompactComponentSchedule

/-! Protected geometry of the limit of a compact-component sharp schedule. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4CompactComponentLimit
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings RestrictEmptyTower
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4CompactComponentTasks HironakaG4DiscreteLimitReadback
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteBoundary
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitProtectedOpen
  ResolutionInvariantSeq HironakaLocallyFiniteResolutionSequence
attribute [local instance] limitChartedSpace
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual support of every finite prefix bounds every actual centre image. -/
theorem centreImage_subset_of_stage_support (s : GrowingSeq X) (A : Set X)
    (hOver : ∀ i, CentresOver A (s.stage i).2) : ∀ i, centreImage s i ⊆ A := by
  intro i x hx
  obtain ⟨z,hzC,rfl⟩ := hx
  obtain ⟨π,hπ,hStep⟩ := exists_step_map s i
  have h := hOver (i+1)
  rw [hStep] at h
  exact h.2 hzC

/-- The actual locally finite limit retains its smooth strict carrier and full
indexed SNC boundary, with a proper map that is an isomorphism off the compact
bad-component union. Noncompact components are therefore unchanged. -/
theorem growing_limit_compact_component_geometry {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (s : GrowingSeq X) (hLF : LocallyFinite (centreImage s))
    (hT : ∀ i, IsGeoTestTower (geometricTemplate W []) (s.stage i).2)
    (hFull : ∀ i, IsGeoTestTower (geometricTemplate (univ : Set X) E) (s.stage i).2)
    (hSharp : ∀ i, CurrentSharpCentres W E (s.stage i).2)
    (hOver : ∀ i, CentresOver (compactComponentUnion (originalSharpBadLocus (n := n) W E)) (s.stage i).2) :
    IsClosedSubmanifold n (limitStrictTransform s hLF W) ∧
      IsLocallyFiniteSNCDivisor n (limitBoundaryMember (geometricTemplate (univ : Set X) E) s hLF) ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (gluedProjection s hLF : limitManifold s hLF → X) ∧
      IsProperMap (gluedProjection s hLF : limitManifold s hLF → X) ∧
      IsIsomorphismOver n (gluedProjection s hLF : limitManifold s hLF → X)
        (compactComponentUnion (originalSharpBadLocus (n := n) W E))ᶜ := by
  obtain ⟨hCarrier,hBoundary,hHol,hProper,_hIso⟩ := growing_limit_partial_geometry hW hE s hLF hT hFull hSharp
  exact ⟨hCarrier,hBoundary,hHol,hProper,
    gluedProjection_isIsomorphismOver_compl_of_centreImages_subset s hLF _
      (centreImage_subset_of_stage_support s _ hOver)⟩
end
end Hironaka.HironakaG4CompactComponentLimit
