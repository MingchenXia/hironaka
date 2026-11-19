import Hironaka.Resolution.HironakaG8LabelledEmbeddedOriginalOverlap
import Hironaka.Resolution.HironakaEmbeddedBoundary

/-! Original invariant transport on the actual overlap of complete embedded charts. -/

set_option autoImplicit false

open Set TopologicalSpace Classical Filter
open scoped Manifold ContDiff Topology

namespace Hironaka.HironakaG8ProperEmbeddedOriginalOverlap

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HironakaStageCenters
  HironakaG3RTowerClass HironakaG3RChartOfMember HironakaG3EmptyAwareHistory
  HironakaG8LocalMixedPhaseAssembly HironakaG8LabelledEmbeddedAtlas
  HironakaG8LabelledEmbeddedOriginalOverlap HironakaOriginalTerminalOverlapComparison MaxLocusLocal
  HironakaEmbeddedBoundary NormalCrossings NormalCrossingsInvariance

/-- A whole-carrier marked vanishing ideal is in the original invariant
domain exactly when its analytic zero set has empty interior. -/
theorem original_vanishing_domain_iff_empty_interior {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} {E : List (Set X)}
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E) :
    IsInvDomain n (⟨univ, E, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) ↔
      interior W = ∅ := by
  refine ⟨fun hM => eq_empty_iff_forall_notMem.mpr fun x hx => ?_, fun hInt => ?_⟩
  · obtain ⟨g, hg, hFreq⟩ := hM.isNonzeroAlongAt x (mem_univ x)
    have hw := mem_interior_iff_mem_nhds.mp hx
    change HolomorphicAt n g x ∧ (∀ᶠ y in nhds x, y ∈ W → g y = 0) at hg
    obtain ⟨y, ⟨_, hne⟩, hg0, hyw⟩ := (hFreq.and_eventually (hg.2.and hw)).exists
    exact hne (hg0 hyw)
  · exact isInvDomain_boundary hW hInt hE

/-- The literal two-open restriction of the original mark-one record is in
the invariant domain. The ordered boundary is pulled back slot by slot. -/
theorem original_vanishing_domain_on_nested_open {n : ℕ} {X : CMfd.{0} n}
    {W : Set X} {E : List (Set X)}
    (hW : IsComplexAnalyticSubset (n := n) W)
    (hE : IsSNCDivisor n E) (U : Opens X) (V : Opens U)
    (hInt : (fun x : V => x.val.val) ⁻¹' interior W = ∅) :
    IsInvDomain n (⟨univ,
      (E.map ((Subtype.val : U → X) ⁻¹' ·)).map ((Subtype.val : V → U) ⁻¹' ·),
      vanishingIdeal (n := n) {x : V | x.val.val ∈ W}, 1⟩ : MarkedIdeal n V) := by
  have hOpen : IsOpenMap (fun x : V => x.val.val) :=
    U.isOpen.isOpenMap_subtype_val.comp V.isOpen.isOpenMap_subtype_val
  have hInterior : interior {x : V | x.val.val ∈ W} = ∅ := by
    change interior ((fun x : V => x.val.val) ⁻¹' W) = ∅
    apply eq_empty_of_subset_empty
    simpa only [hInt] using hOpen.interior_preimage_subset_preimage_interior (s := W)
  exact isInvDomain_boundary
    (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
      (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW U) V)
    hInterior
    (isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val
      (isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE))

/-- Proper analytic carriers give an unconditional original-domain read on
the literal intersection of adopted embedded charts. -/
theorem labelled_proper_embedded_chart_original_overlap {n : ℕ} (hn : 0 < n)
    {X Z : CMfd.{0} n} {P : Z → X} {W : Set X} {C : SmoothTailCertificate n}
    (hW : IsComplexAnalyticSubset (n := n) W) (hC : SmoothTailHasComparisons C)
    (a b : TowerChart (labelledEmbeddedClass C W) Z P)
    (hInt : Disjoint (interior W) ((a.U ⊓ b.U : Opens X) : Set X)) (j : ℕ) :
    let A := nestedOpens a.U (a.U ⊓ b.U)
    let B := nestedOpens b.U (a.U ⊓ b.U)
    let φ := overlapBaseEquiv (n := n) (show a.U ⊓ b.U ≤ a.U from inf_le_left)
      (show a.U ⊓ b.U ≤ b.U from inf_le_right)
    let L := restrict A a.T
    let R := restrict B b.T
    let Wl : Set A := {x | x.val.val ∈ W}
    let Wr : Set B := {x | x.val.val ∈ W}
    let Ml : MarkedIdeal n A := ⟨univ, [], vanishingIdeal (n := n) Wl, 1⟩
    let Mr : MarkedIdeal n B := ⟨univ, [], vanishingIdeal (n := n) Wr, 1⟩
    ∃ β : CMfd.of (n := n) (openPreimage a.T A)
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage b.T B),
      EmptyAwareTowerIso φ L R β ∧
      (IsCanonical Ml ((canonicalInvariant n).inv Ml) L ↔
        IsCanonical Mr ((canonicalInvariant n).inv Mr) R) ∧
      (IsCanonical Mr ((canonicalInvariant n).inv Mr) R →
        (geoTransformAlong Ml L).cosupp = β ⁻¹' (geoTransformAlong Mr R).cosupp ∧
        maxLocus ((canonicalInvariant n).inv Ml L) (geoTransformAlong Ml L).cosupp =
          β ⁻¹' maxLocus ((canonicalInvariant n).inv Mr R) (geoTransformAlong Mr R).cosupp) ∧
    ∃ i ≤ L.length,
      ∃ η : (split L i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (split R j).1,
        EmptyAwareTowerIso φ (head L i) (head R j) η ∧
        (IsCanonical Ml ((canonicalInvariant n).inv Ml) (head L i) ↔
          IsCanonical Mr ((canonicalInvariant n).inv Mr) (head R j)) ∧
        (IsCanonical Mr ((canonicalInvariant n).inv Mr) (head R j) →
          (geoTransformAlong Ml (head L i)).cosupp = η ⁻¹' (geoTransformAlong Mr (head R j)).cosupp ∧
          maxLocus ((canonicalInvariant n).inv Ml (head L i)) (geoTransformAlong Ml (head L i)).cosupp =
            η ⁻¹' maxLocus ((canonicalInvariant n).inv Mr (head R j)) (geoTransformAlong Mr (head R j)).cosupp) := by
  let V := nestedOpens b.U (a.U ⊓ b.U)
  have hNoInterior : (fun x : V => x.val.val) ⁻¹' interior W = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    exact Set.disjoint_left.mp hInt hx x.property
  exact labelled_embedded_chart_original_overlap hn hW hC a b j
    (original_vanishing_domain_on_nested_open hW isSNCDivisor_nil b.U V hNoInterior)

end Hironaka.HironakaG8ProperEmbeddedOriginalOverlap
