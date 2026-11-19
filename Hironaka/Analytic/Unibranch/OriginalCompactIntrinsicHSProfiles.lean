import Hironaka.Analytic.Unibranch.OriginalLocalEmbeddingStalkHS
import Hironaka.Analytic.Unibranch.OriginalIntrinsicSingularLocus
import Hironaka.Resolution.HironakaOriginalLocalFiniteHSProfiles
import Mathlib.Order.PiLex
import Mathlib.Data.Set.Finite.Lemmas

/-! Finite ENTIRE intrinsic Hilbert--Samuel ranges on actual original compact
sets, and an attained singular lexicographic maximum. The profiles retain the
original structural stalk scalars and every maximal-ideal power quotient.
Blueprint FIRST: original-compact-intrinsic-hs-profiles.tex.
No centre, compatible history, future profile bound or termination is asserted. -/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalCompactIntrinsicHSProfiles

open Hironaka Hironaka
  Hironaka.HolomorphicIdealSheaves
  HironakaReducedComplexAnalyticSpaces HironakaActualAnalyticSubspace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaOriginalLocalFiniteHSProfiles
  HironakaHolomorphicJetRankLoci HironakaHolomorphicJetChartInvariance
  OriginalLocalEmbeddingStalkHS
  OriginalIntrinsicSingularLocus

noncomputable section

/-- Every ORIGINAL point has an actual open with finite ENTIRE intrinsic range. -/
theorem exists_original_stalk_hs_finite_range_window
    (X : SourceReducedComplexSpace) (x : X.obj.left) :
    ∃ U : Opens X.obj.left, x ∈ U ∧
      (originalStalkHS X '' (U : Set X.obj.left)).Finite := by
  classical
  let e := LocalEmbedding.ofPoint X x
  obtain ⟨c, hcx⟩ := LocalEmbedding.mem_range_ofPoint X x
  let A : GermIdeal e.dim e.ambient := vanishingIdeal (n := e.dim) e.carrier
  have hA : A.IsCoherent := CartanIrreducible.cartanCoherence e.carrier e.analytic
  obtain ⟨O, hcO, hf⟩ := exists_original_entire_hs_finite_profile_window
    (fun _ : Unit => A) (fun _ => hA) e.analytic c.val
  have hfin : (hilbertSamuelAt A '' (e.carrier ∩ (O : Set e.ambient))).Finite := by
    simpa only [image_image, Function.comp_def] using hf.image (fun H => H ())
  let D : Opens e.carrier :=
    ⟨(Subtype.val : e.carrier → e.ambient) ⁻¹' (O : Set e.ambient),
      O.isOpen.preimage continuous_subtype_val⟩
  let U : Opens X.obj.left :=
    ⟨e.toPoint '' (D : Set e.carrier),
      e.isOpenEmbedding_toPoint.isOpenMap _ D.isOpen⟩
  refine ⟨U, ⟨c, hcO, hcx⟩, hfin.subset ?_⟩
  rintro _ ⟨y, ⟨d, hd, rfl⟩, rfl⟩
  refine ⟨d.val, ⟨d.property, hd⟩, ?_⟩
  funext ℓ
  exact (originalStalkHS_localEmbedding_eq X e d ℓ).symm

/-- Compactness uses finite original OPEN windows, with no compact-chart premise. -/
theorem original_stalk_hs_finite_range_on_compact
    (X : SourceReducedComplexSpace)
    (K : Set X.obj.left) (hK : IsCompact K) :
    (originalStalkHS X '' K).Finite := by
  classical
  choose U hxU hfin using exists_original_stalk_hs_finite_range_window X
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x => (U x : Set X.obj.left))
    (fun x => (U x).isOpen) (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  have hf : (⋃ x ∈ s, originalStalkHS X '' (U x : Set X.obj.left)).Finite :=
    s.finite_toSet.biUnion (fun x _ => hfin x)
  apply hf.subset
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hs hx)
  exact mem_iUnion₂.mpr ⟨a, ha, x, hxa, rfl⟩

/-- A genuine singular point attains the finite whole-profile lexicographic max. -/
theorem exists_original_compact_singular_hs_lex_maximum
    (X : SourceReducedComplexSpace) [CompactSpace X.obj.left]
    (hns : ¬X.IsSmooth) :
    ∃ a ∈ intrinsicSingularLocus X.obj,
      ∀ x ∈ intrinsicSingularLocus X.obj,
        toLex (originalStalkHS X x) ≤ toLex (originalStalkHS X a) := by
  have hK := isCompact_intrinsicSingularLocus X
  have hne := intrinsicSingularLocus_nonempty_of_not_isSmooth X hns
  have hf : ((fun x => toLex (originalStalkHS X x)) ''
      intrinsicSingularLocus X.obj).Finite := by
    simpa only [image_image, Function.comp_def] using
      (original_stalk_hs_finite_range_on_compact X _ hK).image toLex
  obtain ⟨H, hH, hm⟩ := Set.exists_max_image _ id hf (hne.image _)
  obtain ⟨a, ha, rfl⟩ := hH
  exact ⟨a, ha, fun x hx => hm _ (mem_image_of_mem _ hx)⟩

end
end Hironaka.Analytic.Unibranch.OriginalCompactIntrinsicHSProfiles
