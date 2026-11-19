import Hironaka.Resolution.HironakaG8LabelledNativeOverlap
import Hironaka.Resolution.HironakaG8OriginalOverlapPrefixTransport

/-! Original finite invariant reads on the actual labelled native overlap. -/

set_option autoImplicit false

open Set TopologicalSpace Classical
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8LabelledNativeOriginalOverlap

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres HironakaStageCenters
  HironakaG3EmptyAwareHistory HironakaG8LabelledNativeHistory HironakaG8LabelledNativeOverlap
  HironakaG8OriginalOverlapPrefixTransport HironakaOriginalCanonicalDimensionList

/-- On the common saturated task of two actual labelled native histories,
every right prefix has a physically aligned left prefix with the original
canonical history and pullback maximum locus. -/
theorem labelled_native_original_overlap_prefix {n : ℕ} (hn : 0 < n)
    {X X' Y Y' : CMfd.{0} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {W : Set X} {W' : Set X'} {E : List (Set X)} {E' : List (Set X')}
    (hCarrier : W' = φ ⁻¹' W)
    (hBoundary : E'.filter (fun B => decide B.Nonempty) =
      (E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty))
    (hDense' : W' ⊆ closure (W' \ ⋃ B ∈ E', B)) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'} {L L' : List (ℕ → ℕ)}
    (hLeft : LabelledNativeTower n W' E' univ T' L') (hRight : LabelledNativeTower n W E univ T L)
    (j : ℕ) :
    let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
    let M' : MarkedIdeal n X' := ⟨univ, E', vanishingIdeal (n := n) W', 1⟩
    IsInvDomain n M →
    IsCanonical M ((canonicalInvariant n).inv M) T →
    ∃ i ≤ T'.length,
      ∃ η : (split T' i).1 ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (split T j).1,
        EmptyAwareTowerIso φ (head T' i) (head T j) η ∧
        IsCanonical M' ((canonicalInvariant n).inv M') (head T' i) ∧
        maxLocus ((canonicalInvariant n).inv M' (head T' i)) (geoTransformAlong M' (head T' i)).cosupp =
          η ⁻¹' maxLocus ((canonicalInvariant n).inv M (head T j)) (geoTransformAlong M (head T j)).cosupp := by
  obtain ⟨χ, hχ⟩ :=
    labelled_native_history_overlap hn φ hCarrier hBoundary hDense' hDense hLeft hRight
  exact original_native_prefix_centres_of_canonical_overlap hn φ W W' E E'
    hCarrier hLeft.source_analytic hBoundary T' T χ hχ j

/-- Original canonicality agrees for the complete histories on the actual overlap. -/
theorem labelled_native_original_overlap_iff {n : ℕ} (hn : 0 < n)
    {X X' Y Y' : CMfd.{0} n}
    (φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {W : Set X} {W' : Set X'} {E : List (Set X)} {E' : List (Set X')}
    (hCarrier : W' = φ ⁻¹' W)
    (hBoundary : E'.filter (fun B => decide B.Nonempty) =
      (E.map (φ ⁻¹' ·)).filter (fun B => decide B.Nonempty))
    (hDense' : W' ⊆ closure (W' \ ⋃ B ∈ E', B)) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'} {L L' : List (ℕ → ℕ)}
    (hLeft : LabelledNativeTower n W' E' univ T' L') (hRight : LabelledNativeTower n W E univ T L) :
    let M : MarkedIdeal n X := ⟨univ, E, vanishingIdeal (n := n) W, 1⟩
    let M' : MarkedIdeal n X' := ⟨univ, E', vanishingIdeal (n := n) W', 1⟩
    IsInvDomain n M →
    ∃ χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y,
      EmptyAwareTowerIso φ T' T χ ∧
      (IsCanonical M' ((canonicalInvariant n).inv M') T' ↔
        IsCanonical M ((canonicalInvariant n).inv M) T) ∧
      (IsCanonical M ((canonicalInvariant n).inv M) T →
        maxLocus ((canonicalInvariant n).inv M' T') (geoTransformAlong M' T').cosupp =
          χ ⁻¹' maxLocus ((canonicalInvariant n).inv M T) (geoTransformAlong M T).cosupp) := by
  intro M M' hM
  obtain ⟨χ, hχ⟩ :=
    labelled_native_history_overlap hn φ hCarrier hBoundary hDense' hDense hLeft hRight
  have hRead := original_native_overlap_prefix_read hn φ W W' E E' hCarrier
    hLeft.source_analytic hBoundary T' T χ hχ hM
  exact ⟨χ, hχ, hRead.1, fun hCan => (hRead.2 hCan).2⟩

end Hironaka.HironakaG8LabelledNativeOriginalOverlap
