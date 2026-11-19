import Hironaka.Resolution.HironakaG3EmptyAwareHistory
import Hironaka.Resolution.HironakaOriginalFirstMeetingPrefixUniqueness
set_option autoImplicit false
open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FirstMeetingComparison
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers HironakaG3EmptyAwareHistory RestrictEmptyTower
  HironakaOriginalFirstMeetingPrefixUniqueness Hironaka.HolomorphicIdealSheaves
  HironakaDisjointFiniteControlledHistory
open ResolutionInvariantSpec (IsInvDomain)
open ResolutionDriver (maxLocus IsCanonicalSegment)

/-- Canonical segments at their first meeting with the same open set have an
actual structural alignment, not merely an endpoint isomorphism. -/
theorem exists_emptyAware_comparison_of_first_meeting_segments
    {n : ℕ} {Λ : Type} [LinearOrder Λ] {P Q₁ Q₂ : CMfd.{0} n} {k : ℕ}
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (M : MarkedIdeal n P) (hM : IsInvDomain k M)
    (T₁ : BlowupTower P Q₁) (T₂ : BlowupTower P Q₂)
    (hT₁ : IsCanonicalSegment M (R.inv M) T₁) (hT₂ : IsCanonicalSegment M (R.inv M) T₂)
    (O : Opens P) (hav₁ : CentresAvoid O T₁) (hav₂ : CentresAvoid O T₂)
    (hm₁ : ∃ c ∈ maxLocus (R.inv M T₁) (geoTransformAlong M T₁).cosupp, T₁.proj c ∈ O)
    (hm₂ : ∃ c ∈ maxLocus (R.inv M T₂) (geoTransformAlong M T₂).cosupp, T₂.proj c ∈ O) :
    ∃ ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₂,
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) P ∞) T₁ T₂ ψ := by
  obtain ⟨_hlen,ψ,hψ⟩ := first_meeting_nonempty_lengths_eq R M hM T₁ T₂ hT₁ hT₂ O hav₁ hav₂ hm₁ hm₂
  exact ⟨ψ,emptyAware_of_isTowerIso hψ⟩

/-- The first-meeting condition produces the comparison of actual ambient
coupled lifts for canonical segments over the same lower marked ideal. -/
theorem exists_ambient_comparison_of_first_meeting_segments
    {n t : ℕ} {Λ : Type} [LinearOrder Λ] {P Q₁ Q₂ : CMfd.{0} n} {X : CMfd.{0} (n+t)} {k : ℕ}
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (M : MarkedIdeal n P) (hM : IsInvDomain k M)
    (T₁ : BlowupTower P Q₁) (T₂ : BlowupTower P Q₂)
    (hT₁ : IsCanonicalSegment M (R.inv M) T₁) (hT₂ : IsCanonicalSegment M (R.inv M) T₂)
    (O : Opens P) (hav₁ : CentresAvoid O T₁) (hav₂ : CentresAvoid O T₂)
    (hm₁ : ∃ c ∈ maxLocus (R.inv M T₁) (geoTransformAlong M T₁).cosupp, T₁.proj c ∈ O)
    (hm₂ : ∃ c ∈ maxLocus (R.inv M T₂) (geoTransformAlong M T₂).cosupp, T₂.proj c ∈ O)
    {N : Set X} {B : List (Set X)} {J : GermIdeal (n+t) X} {ι : P → X}
    {Y₁ Y₂ : CMfd.{0} (n+t)} {U₁ : BlowupTower X Y₁} {U₂ : BlowupTower X Y₂}
    {η₁ : Q₁ → Y₁} {η₂ : Q₂ → Y₂}
    (hc₁ : CoupledHistory N B J ι M T₁ U₁ η₁)
    (hc₂ : CoupledHistory N B J ι M T₂ U₂ η₂) :
    ∃ (ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Q₂)
      (β : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel (n+t)),𝓘(ℂ,ComplexModel (n+t))⟯ Y₂),
      (∀ y, U₂.proj (β y) = U₁.proj y) ∧ ∀ q, β (η₁ q) = η₂ (ψ q) := by
  obtain ⟨ψ,hψ⟩ := exists_emptyAware_comparison_of_first_meeting_segments
    R M hM T₁ T₂ hT₁ hT₂ O hav₁ hav₂ hm₁ hm₂
  obtain ⟨β,hβ,hη⟩ := exists_ambient_comparison_of_empty_aware_lower_histories
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) P ∞) hψ (fun _ => rfl) hc₁ hc₂
  exact ⟨ψ,β,hβ,hη⟩

end
end Hironaka.HironakaG3FirstMeetingComparison
