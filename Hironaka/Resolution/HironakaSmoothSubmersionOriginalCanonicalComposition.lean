import Hironaka.Resolution.HironakaSmoothSubmersionOriginalAmbientCanonical
import Hironaka.Resolution.HironakaSmoothSubmersionCartesianTowerComposition
/-! Actual canonical values under composition and primitive blowup choices.
Complete two-node mathematics preceded code. All value comparisons concern
actual original canonical histories on their genuine transformed cosupports.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalCanonicalComposition
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionMonomialOrdering
  HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionCartesianTowerComposition HironakaSmoothSubmersionOrderedChoiceImageTrace
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m ℓ : ℕ} {X D : CMfd.{u} n} {Y D' : CMfd.{u} m} {Z D'' : CMfd.{u} ℓ}
  {f : Y → X} {h : Z → Y} {g₁ : D' → D} {g₂ : D'' → D'}
  {T : BlowupTower X D} {Q : BlowupTower Y D'} {R : BlowupTower Z D''}

private theorem original_base_submersion (H : IsActualTowerPullback f Q T g₁) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f := by
  induction H with
  | refl hf => exact hf
  | step _ _ _ _ ih => exact ih

/-- The iterated and direct ambient maps agree on actual original canonical values. -/
theorem IsActualTowerPullback.original_ambient_composition
    (H₁ : IsActualTowerPullback f Q T g₁) (H₂ : IsActualTowerPullback h R Q g₂)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hcan : IsCanonical M ((canonicalInvariant n).inv M) T) :
    IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) Q ∧
    IsCanonical (markedPullback (m := ℓ) h (markedPullback (m := m) f M))
      ((canonicalInvariant ℓ).inv (markedPullback (m := ℓ) h (markedPullback (m := m) f M))) R ∧
    markedPullback (m := ℓ) (f ∘ h) M = markedPullback (m := ℓ) h (markedPullback (m := m) f M) ∧
    ∀ z : D'', g₁ (g₂ z) ∈ (geoTransformAlong M T).cosupp →
      ∃ (hnm : n ≤ m) (hmℓ : m ≤ ℓ) (hnℓ : n ≤ ℓ),
        (canonicalInvariant ℓ).inv (markedPullback (m := ℓ) h (markedPullback (m := m) f M)) R z =
          ambientDimensionMap hmℓ (ambientDimensionMap hnm ((canonicalInvariant n).inv M T (g₁ (g₂ z)))) ∧
        (canonicalInvariant ℓ).inv (markedPullback (m := ℓ) h (markedPullback (m := m) f M)) R z =
          ambientDimensionMap hnℓ ((canonicalInvariant n).inv M T (g₁ (g₂ z))) := by
  have hf := original_base_submersion H₁
  have hh := original_base_submersion H₂
  have hd := original_ambient_domain_pullback hf M hM
  have hc := IsActualTowerPullback.original_ambient_canonical H₁ M hM hcan
  have hrecord := whole_markedPullback_comp hf.contMDiff hh.contMDiff M hM.isWellFormed.isCoherent
  refine ⟨hc,IsActualTowerPullback.original_ambient_canonical H₂ _ hd hc,hrecord,?_⟩
  intro z hz
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (canonicalInvariant n).isInvValue hM T hcan
  have hcos : g₂ z ∈ (geoTransformAlong (markedPullback (m := m) f M) Q).cosupp := by
    rw [IsActualTowerPullback.relative_cosupport_dictionary H₁ M hM.isWellFormed ht]
    exact hz
  have hn := dimension_le_of_submersionAt (hf.isSubmersionAt (Q.proj (g₂ z)))
  have hm := dimension_le_of_submersionAt (hh.isSubmersionAt (R.proj z))
  refine ⟨hn,hm,hn.trans hm,?_,?_⟩
  · rw [IsActualTowerPullback.original_ambient_value H₂ _ hd hc z hcos,
      IsActualTowerPullback.original_ambient_value H₁ M hM hcan (g₂ z) hz]
  · have hv := IsActualTowerPullback.original_ambient_value (HironakaSmoothSubmersionCartesianTowerComposition.IsActualTowerPullback.comp H₁ H₂) M hM hcan z hz
    rw [hrecord] at hv
    exact hv

/-- All primitive geometric choices are internally proved canonical, with real value compatibility. -/
theorem original_ambient_choice_comparison (β₁ β₂ : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (hcan : IsCanonical M ((canonicalInvariant n).inv M) T) :
    let P := chosenActualTower β₁ hf T
    let S := chosenActualTower β₂ hf T
    let a := choiceComparison β₁ β₂ hf T
    IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) P.2.1 ∧
    IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S.2.1 ∧
    (∀ z, S.2.1.proj (a z) = P.2.1.proj z) ∧
    (∀ z, S.2.2.val (a z) = P.2.2.val z) ∧
    ∀ z ∈ (geoTransformAlong (markedPullback (m := m) f M) P.2.1).cosupp,
      (canonicalInvariant m).inv (markedPullback (m := m) f M) S.2.1 (a z) =
        (canonicalInvariant m).inv (markedPullback (m := m) f M) P.2.1 z := by
  dsimp only
  let P := chosenActualTower β₁ hf T
  let S := chosenActualTower β₂ hf T
  let a := choiceComparison β₁ β₂ hf T
  refine ⟨IsActualTowerPullback.original_ambient_canonical P.2.2.property M hM hcan,
    IsActualTowerPullback.original_ambient_canonical S.2.2.property M hM hcan,
    choiceComparison_source β₁ β₂ hf T,choiceComparison_target β₁ β₂ hf T,?_⟩
  intro z hz
  have ht := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (canonicalInvariant n).isInvValue hM T hcan
  have hy : P.2.2.val z ∈ (geoTransformAlong M T).cosupp := by
    rw [IsActualTowerPullback.relative_cosupport_dictionary P.2.2.property M hM.isWellFormed ht] at hz
    exact hz
  have he : S.2.2.val (a z) = P.2.2.val z := choiceComparison_target β₁ β₂ hf T z
  have hy' : S.2.2.val (a z) ∈ (geoTransformAlong M T).cosupp := he.symm ▸ hy
  rw [IsActualTowerPullback.original_ambient_value S.2.2.property M hM hcan (a z) hy',
    IsActualTowerPullback.original_ambient_value P.2.2.property M hM hcan z hy,he]

end
end Hironaka.HironakaSmoothSubmersionOriginalCanonicalComposition
