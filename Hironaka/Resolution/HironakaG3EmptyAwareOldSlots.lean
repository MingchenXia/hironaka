import Hironaka.Resolution.HironakaG3GeometricLiftStructural
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Invariant.MemberInterTowerAlong
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG3EmptyAwareOldSlots
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupStrictSubmanifold
  HomogenizedGlueingTower BlowupTowerIsomorphism HironakaG3EmptyAwareHistory MemberInterTowerAlong

/-- A physical empty-aware tower comparison carries every original closed
boundary slot, even when empty steps occur on only one side. -/
theorem emptyAware_strictAlong_eq {d : ℕ} {P₁ P₂ Q₁ Q₂ : CMfd.{u} d}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (A : Set P₂) (hA : IsClosed A) :
    strictAlong T₁ (Φ ⁻¹' A) = ψ ⁻¹' strictAlong T₂ A := by
  induction h with
  | refl => rfl
  | @step Y₁ Y₂ Z₁ Z₂ T₁ T₂ ψ h C₁ π₁ hπ₁ C₂ π₂ hπ₂ χ hcomm hC ih =>
    show geoStrictTransform π₁ C₁ (strictAlong T₁ (Φ ⁻¹' A)) = χ ⁻¹' geoStrictTransform π₂ C₂ (strictAlong T₂ A)
    rw [ih, ← hC, ← BlowupBiholomorphismLift.geoStrictTransform_comp_diffeo χ π₂ C₂]
    have hfun : ψ ∘ π₁ = π₂ ∘ χ := funext fun p => (hcomm p).symm
    unfold geoStrictTransform
    rw [← preimage_sdiff, ← preimage_comp, hfun]
  | @leftEmpty Y₁ Y₂ Z₁ T₁ T₂ ψ h π hπ χ hχ ih =>
    show geoStrictTransform π ∅ (strictAlong T₁ (Φ ⁻¹' A)) = (χ.trans ψ) ⁻¹' strictAlong T₂ A
    rw [ContactCanonicalAlong.geoStrictTransform_empty hπ.contMDiff.continuous (isClosed_strictAlong T₁ (hA.preimage Φ.continuous)), ih]
    ext z
    change ψ (π z) ∈ strictAlong T₂ A ↔ ψ (χ z) ∈ strictAlong T₂ A
    rw [hχ]
  | @rightEmpty Y₁ Y₂ Z₂ T₁ T₂ ψ h π hπ χ hχ ih =>
    show strictAlong T₁ (Φ ⁻¹' A) = (ψ.trans χ.symm) ⁻¹' geoStrictTransform π ∅ (strictAlong T₂ A)
    rw [ih, ContactCanonicalAlong.geoStrictTransform_empty hπ.contMDiff.continuous (isClosed_strictAlong T₂ hA)]
    ext z
    change ψ z ∈ strictAlong T₂ A ↔ π (χ.symm (ψ z)) ∈ strictAlong T₂ A
    rw [← hχ, χ.apply_symm_apply]
/-- All original closed slots retain their order and multiplicity. -/
theorem emptyAware_old_boundary_eq {d : ℕ} {P₁ P₂ Q₁ Q₂ : CMfd.{u} d}
    {Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂}
    {T₁ : BlowupTower P₁ Q₁} {T₂ : BlowupTower P₂ Q₂}
    {ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (E : List (Set P₂))
    (hE : ∀ H ∈ E, IsClosed H) :
    (E.map (Φ ⁻¹' ·)).map (strictAlong T₁) =
      (E.map (strictAlong T₂)).map (ψ ⁻¹' ·) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro H hH
  exact emptyAware_strictAlong_eq h H (hE H hH)

end
end Hironaka.HironakaG3EmptyAwareOldSlots
