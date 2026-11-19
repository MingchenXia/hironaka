import Hironaka.Resolution.HironakaG8StageRankCoherence
import Hironaka.Resolution.HironakaG8NativePhaseCertificate
import Hironaka.Resolution.HironakaActualHilbertSamuelLexOrder

/-! Intrinsic label decrease for intersecting certified phase footprints. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaG8IntersectingPhaseLabels

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaG8NativePhaseCertificate HironakaG8ClosedNativeTestGlobalization
  HironakaHolomorphicJetChartInvariance HironakaActualHilbertSamuelLexOrder

variable {n : ℕ} {X Y Z : CMfd.{0} (n+1)}

/-- At an actual intersection of the projected footprints of two
consecutive certified phases the second label is strictly smaller.
There is no global maximum premise. -/
theorem label_lt_of_intersecting_native_phase_footprints
    {A : Set X} {E : List (Set X)} {E' : List (Set Y)}
    {H J : ℕ → ℕ} {S : BlowupTower X Y} {T : BlowupTower Y Z}
    (hS : ActualNativePhase A E H S)
    (hT : ActualNativePhase (strictTransform (n+1) S.proj A) E' J T)
    (hInter : (baseCentreFootprint S ∩ S.proj '' baseCentreFootprint T).Nonempty) :
    toLex J < toLex H := by
  obtain ⟨_,hx,⟨y,hy,rfl⟩⟩ := hInter
  have hH := (centresOver_iff_baseCentreFootprint_subset S).mp hS.supports hx
  have hJ := (centresOver_iff_baseCentreFootprint_subset T).mp hT.supports hy
  have hDrop := hS.strictDrop y hH
  change hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) S.proj A)) y = J at hJ
  rwa [hJ] at hDrop

/-- Contrapositive form for the dependency graph. In particular, distinct
certified phases carrying the same label cannot have intersecting projected
footprints when they are consecutive. -/
theorem disjoint_native_phase_footprints_of_not_label_lt
    {A : Set X} {E : List (Set X)} {E' : List (Set Y)}
    {H J : ℕ → ℕ} {S : BlowupTower X Y} {T : BlowupTower Y Z}
    (hS : ActualNativePhase A E H S)
    (hT : ActualNativePhase (strictTransform (n+1) S.proj A) E' J T)
    (hLabels : ¬ toLex J < toLex H) :
    Disjoint (baseCentreFootprint S) (S.proj '' baseCentreFootprint T) :=
  disjoint_left.mpr fun x hx hy => hLabels
    (label_lt_of_intersecting_native_phase_footprints hS hT ⟨x,hx,hy⟩)

/-- A later certified phase whose footprint returns to the first
phase's source footprint has smaller label even with intervening stages,
provided the actual intermediate profiles are pointwise nonincreasing. -/
theorem label_lt_of_intersecting_native_phase_footprints_along
    {B : CMfd.{0} (n+1)} {A : Set X} {E : List (Set X)} {E' : List (Set B)}
    {H J : ℕ → ℕ} {S : BlowupTower X Y} {R : BlowupTower Y B} {T : BlowupTower B Z}
    (hS : ActualNativePhase A E H S)
    (hR : ∀ z ℓ, hilbertSamuelAt
      (vanishingIdeal (n := n+1) (strictTransform (n+1) R.proj (strictTransform (n+1) S.proj A))) z ℓ ≤
      hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) S.proj A)) (R.proj z) ℓ)
    (hT : ActualNativePhase
      (strictTransform (n+1) R.proj (strictTransform (n+1) S.proj A)) E' J T)
    (hInter : (baseCentreFootprint S ∩ (S.proj ∘ R.proj) '' baseCentreFootprint T).Nonempty) :
    toLex J < toLex H := by
  obtain ⟨_,hx,⟨y,hy,rfl⟩⟩ := hInter
  have hH := (centresOver_iff_baseCentreFootprint_subset S).mp hS.supports hx
  have hJ := (centresOver_iff_baseCentreFootprint_subset T).mp hT.supports hy
  have hDrop := hS.strictDrop (R.proj y) hH
  have hLe := Pi.toLex_monotone (show hilbertSamuelAt
      (vanishingIdeal (n := n+1) (strictTransform (n+1) R.proj (strictTransform (n+1) S.proj A))) y ≤
      hilbertSamuelAt (vanishingIdeal (n := n+1) (strictTransform (n+1) S.proj A)) (R.proj y) from hR y)
  change hilbertSamuelAt
    (vanishingIdeal (n := n+1) (strictTransform (n+1) R.proj (strictTransform (n+1) S.proj A))) y = J at hJ
  rw [hJ] at hLe
  exact hLe.trans_lt hDrop

/-- The attainable profile order rules out infinite forward dependency
chains. The relation here is explicitly the converse of BEFORE: each
later vertex has smaller label than the earlier one. -/
theorem reverse_before_wellFounded_of_profile_drop
    {ι : Type*} (Before : ι → ι → Prop) (label : ι → ActualAnalyticLexHilbertSamuelProfile (n+1))
    (hBefore : ∀ ⦃a b⦄, Before a b → label b < label a) :
    WellFounded (fun b a => Before a b) := by
  exact Subrelation.wf (fun h => hBefore h)
    (InvImage.wf label (actual_analyticHilbertSamuel_lex_wellFounded (n+1)).wf)

end Hironaka.HironakaG8IntersectingPhaseLabels
