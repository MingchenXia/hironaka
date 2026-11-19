import Hironaka.Resolution.HironakaG3RGluedBoundary
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3RestrictEndpointComparison
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsoTail HironakaG3RGluedBoundary

theorem restrict_endpoint_comparison {n : ℕ} {X Y₁ Y₂ : CMfd.{u} n}
    (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂)
    (β : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂)
    (hβ : ∀ y, T₂.proj (β y) = T₁.proj y) (U : Opens X) :
    ∃ ψ : (CMfd.of (n := n) (openPreimage T₁ U)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ U)),
      (∀ z, (ψ z).val = β z.val) ∧
      ∀ z, T₂.proj (ψ z).val = T₁.proj z.val := by
  have hEq : preimageOpens β (openPreimage T₂ U) = openPreimage T₁ U := by
    apply Opens.ext
    ext y
    change T₂.proj (β y) ∈ U ↔ T₁.proj y ∈ U
    rw [hβ]
  let ψ := (opensCongr hEq.symm).trans (preimageDiffeo β (openPreimage T₂ U)).symm
  refine ⟨ψ, ?_, ?_⟩
  · intro z
    rfl
  · intro z
    exact hβ z.val


theorem restrict_endpoint_comparison_nested {n : ℕ} {X Y₁ Y₂ : CMfd.{u} n}
    (T₁ : BlowupTower X Y₁) (T₂ : BlowupTower X Y₂) {R U : Opens X} (hUR : U ≤ R)
    (β : (CMfd.of (n := n) (openPreimage T₁ R)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ R)))
    (hβ : ∀ y, T₂.proj (β y).val = T₁.proj y.val) :
    ∃ ψ : (CMfd.of (n := n) (openPreimage T₁ U)) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage T₂ U)),
      ∀ z, T₂.proj (ψ z).val = T₁.proj z.val := by
  let U' : Opens R := MaxLocusLocal.nestedOpens R U
  have hβ' : ∀ y, (restrict R T₂).proj (β y) = (restrict R T₁).proj y := by
    intro y
    apply Subtype.ext
    simpa only [proj_restrict] using hβ y
  obtain ⟨ψ,_hψ,hψproj⟩ := restrict_endpoint_comparison (restrict R T₁) (restrict R T₂) β hβ' U'
  let e₁ := MaxLocusLocal.nestedDiffeo (n := n) (openPreimage T₁ R) (openPreimage (restrict R T₁) U')
    (openPreimage T₁ U) (MaxLocusLocal.mem_openPreimage_restrict_nestedOpens R U T₁)
    (MaxLocusLocal.openPreimage_mono T₁ hUR)
  let e₂ := MaxLocusLocal.nestedDiffeo (n := n) (openPreimage T₂ R) (openPreimage (restrict R T₂) U')
    (openPreimage T₂ U) (MaxLocusLocal.mem_openPreimage_restrict_nestedOpens R U T₂)
    (MaxLocusLocal.openPreimage_mono T₂ hUR)
  refine ⟨e₁.symm.trans (ψ.trans e₂), ?_⟩
  intro z
  have h := congrArg Subtype.val (hψproj (e₁.symm z))
  change T₂.proj ((ψ (e₁.symm z)).val).val = T₁.proj z.val
  have heq : ((e₁.symm z).val).val = z.val := rfl
  simpa only [proj_restrict, heq] using h
end
end Hironaka.HironakaG3RestrictEndpointComparison
