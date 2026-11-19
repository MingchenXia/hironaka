import Hironaka.Resolution.HironakaG3EmptyAwareSymmetry
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3AllEmptyComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers HironakaG3EmptyAwareHistory
open ResolutionInvariantExt (IsEmptyTower)
open Hironaka.HolomorphicIdealSheaves MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings HironakaDisjointFiniteControlledHistory
  BlowupTowerTransforms RestrictEmptyTower

/-- Every two actual all-empty histories admit an empty-aware comparison. -/
theorem exists_comparison {n : ℕ} {X₁ X₂ : CMfd.{0} n}
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂)
    {Y₁ Y₂ : CMfd.{0} n} (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (h₁ : IsEmptyTower T₁) (h₂ : IsEmptyTower T₂) :
    ∃ ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂,
      EmptyAwareTowerIso Φ T₁ T₂ ψ := by
  have left : ∀ {Y : CMfd.{0} n} (T : BlowupTower X₁ Y), IsEmptyTower T →
      ∃ ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂,
        EmptyAwareTowerIso Φ T .refl ψ := by
    intro Y T
    induction T with
    | refl => intro _; exact ⟨Φ,.refl⟩
    | step T C π hπ ih =>
      intro h
      obtain ⟨ψ,hψ⟩ := ih h.1
      have hC : C = ∅ := h.2
      subst C
      obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
      exact ⟨φ.trans ψ,.leftEmpty hψ hπ φ hφ⟩
  obtain ⟨ψ,hψ⟩ := left T₁ h₁
  induction T₂ with
  | refl => exact ⟨ψ,hψ⟩
  | step T C π hπ ih =>
    obtain ⟨χ,hχ⟩ := ih h₂.1
    have hC : C = ∅ := h₂.2
    subst C
    obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
    exact ⟨χ.trans φ.symm,.rightEmpty hχ hπ φ hφ⟩
/-- Any actual coupled lifts of two all-empty lower histories compare over the
base and transport the lower endpoint embeddings. -/
theorem exists_ambient_comparison_of_all_empty_lower_histories
    {d t : ℕ} {X : CMfd.{0} (d+t)} {P₁ P₂ Q₁ Q₂ : CMfd.{0} d}
    (Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂)
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    (hT₁ : IsEmptyTower T₁) (hT₂ : IsEmptyTower T₂)
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι₁ : P₁ → X} {ι₂ : P₂ → X} {M₁ : MarkedIdeal d P₁} {M₂ : MarkedIdeal d P₂}
    {Y₁ Y₂ : CMfd.{0} (d+t)} {U₁ : BlowupTower X Y₁} {U₂ : BlowupTower X Y₂}
    {η₁ : Q₁ → Y₁} {η₂ : Q₂ → Y₂}
    (hι : ∀ p, ι₂ (Φ p) = ι₁ p)
    (h₁ : CoupledHistory N B J ι₁ M₁ T₁ U₁ η₁)
    (h₂ : CoupledHistory N B J ι₂ M₂ T₂ U₂ η₂) :
    ∃ (ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂)
      (β : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (d+t)),𝓘(ℂ,ComplexModel (d+t))⟯ Y₂),
      (∀ y, U₂.proj (β y) = U₁.proj y) ∧ ∀ q, β (η₁ q) = η₂ (ψ q) := by
  obtain ⟨ψ,hψ⟩ := exists_comparison Φ T₁ T₂ hT₁ hT₂
  obtain ⟨β,hβ,hη⟩ := exists_ambient_comparison_of_empty_aware_lower_histories Φ hψ hι h₁ h₂
  exact ⟨ψ,β,hβ,hη⟩

/-- Centre avoidance produces an empty-aware comparison on the open restrictions. -/
theorem exists_comparison_of_restricted_histories_avoiding_opens
    {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n} (U₁ : Opens X₁) (U₂ : Opens X₂)
    (Φ : U₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ U₂)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (h₁ : CentresAvoid U₁ T₁) (h₂ : CentresAvoid U₂ T₂) :
    ∃ ψ : (openPreimage T₁ U₁) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (openPreimage T₂ U₂),
      EmptyAwareTowerIso Φ (restrict U₁ T₁) (restrict U₂ T₂) ψ := by
  exact exists_comparison Φ (restrict U₁ T₁) (restrict U₂ T₂)
    ((isEmptyTower_restrict_iff U₁ T₁).mpr h₁) ((isEmptyTower_restrict_iff U₂ T₂).mpr h₂)

end
end Hironaka.HironakaG3AllEmptyComparison
