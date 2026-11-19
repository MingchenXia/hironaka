import Hironaka.Resolution.HironakaG8ProperEmbeddedOriginalOverlap

/-! Read original finite-prefix maxima on compact windows of the same glued map. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8AdoptedOriginalPrefixReadback

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HironakaStageCenters
  HironakaG3RTowerClass HironakaG3EmptyAwareHistory
  HironakaG8LocalMixedPhaseAssembly HironakaG8LabelledEmbeddedAtlas
  HironakaG8ProperEmbeddedOriginalOverlap HironakaOriginalTerminalOverlapComparison MaxLocusLocal

/-- The original canonicality predicate is equivalent to the exact
maximum criterion at every recorded stage, with empty stages allowed. -/
theorem original_canonical_iff_stage_maxima {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (T : BlowupTower X Y) :
    IsCanonical M ((canonicalInvariant n).inv M) T ↔
    StageCentres (fun S C => C = ∅ ∨
      C = maxLocus ((canonicalInvariant n).inv M S) (geoTransformAlong M S).cosupp) T := by
  induction T with
  | refl => exact Iff.rfl
  | step T C π hπ ih => exact and_congr_left' ih

/-- A stage criterion on a reference chart induces the original
canonical read on every actual prefix of its literal open restriction. -/
theorem reference_stage_maxima_restrict_prefix {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (hInt : interior W = ∅)
    (O : Opens X) (T : BlowupTower X Y) (j : ℕ) :
    let M : MarkedIdeal n X := ⟨univ, [], vanishingIdeal (n := n) W, 1⟩
    let M₀ : MarkedIdeal n O :=
      ⟨univ, [], vanishingIdeal (n := n) ((Subtype.val : O → X) ⁻¹' W), 1⟩
    StageCentres (fun S D => D = ∅ ∨
      D = maxLocus ((canonicalInvariant n).inv M S) (geoTransformAlong M S).cosupp) T →
    IsCanonical M₀ ((canonicalInvariant n).inv M₀) (head (restrict O T) j) := by
  intro M M₀ hStages
  have hM := (original_vanishing_domain_iff_empty_interior hW NormalCrossings.isSNCDivisor_nil).mpr hInt
  have hCan := (original_canonical_iff_stage_maxima M T).mpr hStages
  have hRestrict := Seq.ResolutionInvariantExt.isCanonical_restrict
    (canonicalInvariant n) hM O T hCan
  have hPull : MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : O → X) M = M₀ := by
    exact HironakaEmbeddedBoundary.pullback_val_mk_vanishingIdeal O [] W
  rw [hPull] at hRestrict
  exact isCanonical_head M₀ ((canonicalInvariant n).inv M₀) (restrict O T) j hRestrict

/-- Every prescribed compact-enclosed window is represented by a chart of
the fixed glued map. Any reference prefix satisfying the original stage
criterion on the literal intersection gives an original canonical prefix
and exact maximum read on that chart of the same map. -/
theorem adopted_compact_chart_original_prefix_readback {n : ℕ} (hn : 0 < n)
    {X Z : CMfd.{0} n} {P : Z → X} {W : Set X} {C : SmoothTailCertificate n}
    (hW : IsComplexAnalyticSubset (n := n) W) (hC : SmoothTailHasComparisons C)
    (hWindows : ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
      ∃ c : TowerChart (labelledEmbeddedClass C W) Z P, c.U = U)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ a : TowerChart (labelledEmbeddedClass C W) Z P, a.U = U ∧
      (a.V : Set Z) = P ⁻¹' (U : Set X) ∧
      ∀ (b : TowerChart (labelledEmbeddedClass C W) Z P) (j : ℕ),
        Disjoint (interior W) ((a.U ⊓ b.U : Opens X) : Set X) →
        let A := nestedOpens a.U (a.U ⊓ b.U)
        let B := nestedOpens b.U (a.U ⊓ b.U)
        let φ := overlapBaseEquiv (n := n) (show a.U ⊓ b.U ≤ a.U from inf_le_left)
          (show a.U ⊓ b.U ≤ b.U from inf_le_right)
        let L := restrict A a.T
        let R := restrict B b.T
        let Ml : MarkedIdeal n A := ⟨univ, [], vanishingIdeal (n := n) {x : A | x.val.val ∈ W}, 1⟩
        let Mr : MarkedIdeal n B := ⟨univ, [], vanishingIdeal (n := n) {x : B | x.val.val ∈ W}, 1⟩
        StageCentres (fun S D => D = ∅ ∨
          D = maxLocus ((canonicalInvariant n).inv Mr S) (geoTransformAlong Mr S).cosupp) (head R j) →
        ∃ i ≤ L.length,
          ∃ η : (split L i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (split R j).1,
            EmptyAwareTowerIso φ (head L i) (head R j) η ∧
            IsCanonical Ml ((canonicalInvariant n).inv Ml) (head L i) ∧
            (geoTransformAlong Ml (head L i)).cosupp = η ⁻¹' (geoTransformAlong Mr (head R j)).cosupp ∧
            maxLocus ((canonicalInvariant n).inv Ml (head L i)) (geoTransformAlong Ml (head L i)).cosupp =
              η ⁻¹' maxLocus ((canonicalInvariant n).inv Mr (head R j)) (geoTransformAlong Mr (head R j)).cosupp := by
  obtain ⟨a, ha⟩ := hWindows U K hK hUK
  refine ⟨a, ha, ?_, ?_⟩
  · simpa only [ha] using a.V_eq
  · intro b j hNoInterior A B φ L R Ml Mr hStages
    obtain ⟨_, _, _, _, i, hi, η, hη, hCan, hRead⟩ :=
      labelled_proper_embedded_chart_original_overlap hn hW hC a b hNoInterior j
    have hRight := (original_canonical_iff_stage_maxima Mr (head R j)).mpr hStages
    exact ⟨i, hi, η, hη, hCan.mpr hRight, hRead hRight⟩

end Hironaka.HironakaG8AdoptedOriginalPrefixReadback
