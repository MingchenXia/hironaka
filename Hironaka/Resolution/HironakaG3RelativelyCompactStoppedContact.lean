import Hironaka.Resolution.HironakaG3LocalStoppedCover
import Hironaka.Resolution.HironakaRelativelyCompact
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3RelativelyCompactStoppedContact
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers CanonicalCentres MaxLocusLocal RestrictEmptyTower MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeReferenceWindow
  HironakaDisjointNativeOpenLift HironakaG3RStoppedOverlap HironakaG3RTowerClass
open ResolutionInvariantSpec (IsInvDomain)

theorem stopped_native_history_over_relatively_compact_window
    {d t : ℕ} {X : CMfd.{0} (d+t)} (N : Set X) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (M : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) (hM : IsInvDomain d M)
    (O : Opens (nativeManifold (Nat.le_add_right d t) N hN))
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ (Y : CMfd.{0} d) (T : BlowupTower (CMfd.of (n := d) (nativeWindow (Nat.le_add_right d t) N hN U)) Y),
      stoppedClass M O (nativeWindow (Nat.le_add_right d t) N hN U) Y T := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  let A := nativeWindow (Nat.le_add_right d t) N hN U
  have hKN : IsCompact ((Subtype.val : N → X) ⁻¹' K) := hNc.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hAK : (A : Set (nativeManifold (Nat.le_add_right d t) N hN)) ⊆ (Subtype.val : N → X) ⁻¹' K := fun p hp => hUK hp
  obtain ⟨Y,T,hc,hr⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (canonicalInvariant d) hM hKN A hAK
  by_cases ha : CentresAvoid (MaxLocusLocal.nestedOpens A O) T
  · exact ⟨Y,T,hc,ha,Or.inr hr⟩
  · obtain ⟨Y',T',-, -,h1,h2,c,hc',hcU⟩ :=
      EmbeddedFromResolution.exists_first_centre _ _ (MaxLocusLocal.nestedOpens A O) T hc ha
    exact ⟨Y',T',h1,h2,Or.inl ⟨c,hc',hcU⟩⟩
end
end Hironaka.HironakaG3RelativelyCompactStoppedContact
