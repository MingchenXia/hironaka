import Hironaka.Resolution.HironakaG3EmptyAwareOpenRestriction
import Hironaka.Resolution.HironakaG3EmptyAwareComposition
import Hironaka.Resolution.HironakaG3EmptyAwareSymmetry
import Hironaka.Invariant.MaxLocusLocal
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3EmptyAwareNestedRestriction
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HironakaG3EmptyAwareHistory HironakaG3EmptyAwareOpenRestriction HironakaG3EmptyAwareComposition
  HironakaSharpActualCurveComparisonRestriction MaxLocusLocal

theorem emptyAware_nested_restriction {n : ℕ} {X Y₁ Y₂ : CMfd.{0} n}
    (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂) {R U : Opens X} (hUR : U ≤ R)
    (ψ : (CMfd.of (n := n) (openPreimage T₁ R)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ R)))
    (hψ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) R) ∞)
      (restrict R T₁) (restrict R T₂) ψ) :
    ∃ χ : (CMfd.of (n := n) (openPreimage T₁ U)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ U)),
      EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) U) ∞)
        (restrict U T₁) (restrict U T₂) χ := by
  let V : Opens R := nestedOpens R U
  have h' := emptyAware_open_restriction hψ V
  have h₁ := emptyAware_of_isTowerIso (isTowerIso_restrict_nestedOpens hUR T₁)
  have h₂ := emptyAware_of_isTowerIso (isTowerIso_restrict_nestedOpens hUR T₂)
  have hc := HironakaG3EmptyAwareComposition.trans (HironakaG3EmptyAwareSymmetry.symm h₁)
    (HironakaG3EmptyAwareComposition.trans h' h₂)
  let e₁ := nestedDiffeo (n := n) (openPreimage T₁ R) (openPreimage (restrict R T₁) V)
    (openPreimage T₁ U) (mem_openPreimage_restrict_nestedOpens R U T₁) (openPreimage_mono T₁ hUR)
  let e₂ := nestedDiffeo (n := n) (openPreimage T₂ R) (openPreimage (restrict R T₂) V)
    (openPreimage T₂ U) (mem_openPreimage_restrict_nestedOpens R U T₂) (openPreimage_mono T₂ hUR)
  let ψ' := openRestriction ψ (openPreimage (restrict R T₁)
      (preimageOpen (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) R) ∞) V))
    (openPreimage (restrict R T₂) V) (emptyAware_openPreimage_eq hψ V)
  refine ⟨e₁.symm.trans (ψ'.trans e₂),?_⟩
  convert hc using 1 <;> ext z <;> rfl
end
end Hironaka.HironakaG3EmptyAwareNestedRestriction
