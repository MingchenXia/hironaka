import Hironaka.Resolution.HironakaG3UniverseChartProvenance
import Hironaka.Resolution.HironakaG3UniversePhysicalChartOverlap
import Hironaka.Resolution.HironakaG3UniversePhysicalClassComparisons
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseProvenancePhysical
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism BlowupTowerIsoTail
  HironakaG3RTowerClass HironakaG3UniverseLiftManifold G3UniverseLiftedTower
  G3UniverseOpenDiffeo G3UniverseChartTowerTransport G3UniverseChartProvenance
  G3UniversePhysicalClassComparisons G3UniversePhysicalChartOverlap MarkedIdeals MarkedIdeals.MarkedIdeal
  CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
noncomputable section

/-- Actual physical comparisons for the supplied small class lift to the
provenance class, retaining its literal stagewise tower witnesses. -/
theorem lifted_provenance_hasPhysicalComparisons {n : ℕ}
    {X : CMfd.{u} n} {X₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀)
    (𝒞 : LocalTowerClass X₀) (hsmall : HasPhysicalComparisons 𝒞) :
    HasPhysicalComparisons (liftedProvenanceClass e 𝒞) := by
  intro U₁ U₂ Y₁ Y₂ T₁ T₂ hT₁ hT₂
  obtain ⟨U₀₁,Y₀₁,T₀₁,hT₀₁,hU₁,χ₁,hiso₁⟩ := hT₁
  obtain ⟨U₀₂,Y₀₂,T₀₂,hT₀₂,hU₂,χ₂,hiso₂⟩ := hT₂
  subst U₁
  subst U₂
  have hbase₁ : (opensCongr (rfl : preimageOpens e U₀₁ = preimageOpens e U₀₁)).trans
      (baseLiftDiffeo e U₀₁) = baseLiftDiffeo e U₀₁ := by
    ext p
    rfl
  have hbase₂ : (opensCongr (rfl : preimageOpens e U₀₂ = preimageOpens e U₀₂)).trans
      (baseLiftDiffeo e U₀₂) = baseLiftDiffeo e U₀₂ := by
    ext p
    rfl
  rw [hbase₁] at hiso₁
  rw [hbase₂] at hiso₂
  obtain ⟨θ,hθ⟩ := hsmall U₀₁ U₀₂ Y₀₁ Y₀₂ T₀₁ T₀₂ hT₀₁ hT₀₂
  exact lifted_physical_overlap_of_isos e U₀₁ U₀₂ T₀₁ T₀₂ T₁ T₂ χ₁ χ₂ hiso₁ hiso₂ θ hθ

/-- A supplied physically compatible small atlas retains both its atlas and
its pairwise actual physical tower comparisons after literal universe lift. -/
theorem lifted_provenance_physical_atlas {n : ℕ}
    {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀)
    {P : Y₀ → X₀} {𝒞 : LocalTowerClass X₀}
    (hG : IsGluedFrom 𝒞 Y₀ P) (hsmall : HasPhysicalComparisons 𝒞) :
    IsGluedFrom (liftedProvenanceClass e 𝒞) (liftCMfd.{u} Y₀)
      (e.symm ∘ P ∘ (liftDiffeomorph.{u} Y₀).symm) ∧
    HasPhysicalComparisons (liftedProvenanceClass e 𝒞) :=
  ⟨lifted_provenance_atlas e hG, lifted_provenance_hasPhysicalComparisons e 𝒞 hsmall⟩

/-- If the supplied small class also gives actual canonical marked records,
the same lifted provenance class has canonical members and physical overlaps. -/
theorem lifted_provenance_canonical_physical_atlas {n r : ℕ} (hn : 0 < n)
    {X : CMfd.{u} n} {X₀ Y₀ : CMfd.{0} n}
    (e : X ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₀)
    {P : Y₀ → X₀} {𝒞 : LocalTowerClass X₀}
    (hG : IsGluedFrom 𝒞 Y₀ P) (hsmall : HasPhysicalComparisons 𝒞)
    (hcan : ∀ (U₀ : Opens X₀) (Y₀ : CMfd.{0} n) (T₀ : BlowupTower (CMfd.of (n := n) U₀) Y₀), 𝒞 U₀ Y₀ T₀ →
      ∃ M : MarkedIdeal n (CMfd.of (n := n) U₀), IsInvDomain r M ∧
        IsCanonical M ((invFamily.{0} hn r).inv M) T₀) :
    IsGluedFrom (liftedProvenanceClass e 𝒞) (liftCMfd.{u} Y₀)
      (e.symm ∘ P ∘ (liftDiffeomorph.{u} Y₀).symm) ∧
    HasPhysicalComparisons (liftedProvenanceClass e 𝒞) ∧
    (∀ (U : Opens X) (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y), liftedProvenanceClass e 𝒞 U Y T →
      ∃ M : MarkedIdeal n (CMfd.of (n := n) U), IsInvDomain r M ∧
        IsCanonical M ((invFamily.{u} hn r).inv M) T) := by
  refine ⟨lifted_provenance_atlas e hG, lifted_provenance_hasPhysicalComparisons e 𝒞 hsmall, ?_⟩
  intro U Y T hT
  exact provenance_is_canonical hn e 𝒞 hcan hT

end
end Hironaka.G3UniverseProvenancePhysical
