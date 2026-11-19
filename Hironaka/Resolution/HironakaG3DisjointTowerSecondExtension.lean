import Hironaka.Resolution.HironakaG3CentresOverGenericFactor
import Hironaka.Resolution.HironakaClosedFootprintOpenTowerExtension
import Hironaka.Resolution.HironakaOriginalOldBranchEmptyProjection
import Hironaka.Blowup.BlowupTowerIsomorphism
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG3DisjointTowerSecondExtension
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupRestrictOpen RestrictEmptyTower
  BlowupTowerIsomorphism MarkedIdealTowerTransport
  HironakaClosedFootprintOpenTowerExtension HironakaOriginalOldBranchEmptyProjection
variable {n : ℕ} {X : CMfd.{u} n}
theorem second_tower_extension_of_disjoint_closed_supports
    {Y₁ Y₂ : CMfd.{u} n} (F₁ F₂ : Set X) (hF₁ : IsClosed F₁) (hF₂ : IsClosed F₂)
    (hDis : Disjoint F₁ F₂) (T₁ : BlowupTower X Y₁) (hT₁ : CentresOver F₁ T₁)
    (T₂ : BlowupTower X Y₂) (hT₂ : CentresOver F₂ T₂) :
    let R : Opens X := ⟨F₁ᶜ, hF₁.isOpen_compl⟩
    let V : Opens Y₁ := openPreimage T₁ R
    ∃ β : (CMfd.of (n := n) V) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) R),
      (∀ y, β y = (restrict R T₁).proj y) ∧
      ∃ (Y : CMfd.{u} n) (Q : BlowupTower Y₁ Y), CentresOver (T₁.proj ⁻¹' F₂) Q ∧
        ∃ e : (transport β (restrict R T₂)).target ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q V,
          IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) V ∞)
            (transport β (restrict R T₂)).tower (restrict V Q) e := by
  dsimp only
  let R : Opens X := ⟨F₁ᶜ, hF₁.isOpen_compl⟩
  let V : Opens Y₁ := openPreimage T₁ R
  have hR : Disjoint (R : Set X) F₁ := by
    exact disjoint_compl_left
  have he := isEmptyTower_restrict_of_centresOver R hR T₁ hT₁
  obtain ⟨β, hβ⟩ := exists_empty_tower_projection (restrict R T₁) he
  refine ⟨β, hβ, ?_⟩
  have hF₂R : F₂ ⊆ R := by
    intro x hx₂ hx₁
    exact Set.disjoint_left.mp hDis hx₁ hx₂
  have hKV : T₁.proj ⁻¹' F₂ ⊆ V := fun y hy => hF₂R hy
  have hK : IsClosed (T₁.proj ⁻¹' F₂) := hF₂.preimage T₁.contMDiff_proj.continuous
  have hPre : β ⁻¹' ((Subtype.val : R → X) ⁻¹' F₂) =
      (Subtype.val : V → Y₁) ⁻¹' (T₁.proj ⁻¹' F₂) := by
    ext y
    change (β y).val ∈ F₂ ↔ T₁.proj y.val ∈ F₂
    rw [hβ, proj_restrict]
  have ht := HironakaG3CentresOverGenericFactor.centresOver_of_isTowerIso
    (transport_isTowerIso β (restrict R T₂)) ((Subtype.val : R → X) ⁻¹' F₂)
    (HironakaG3CentresOverGenericFactor.centresOver_restrict R F₂ T₂ hT₂)
  rw [hPre] at ht
  obtain ⟨Y,Q,hQ,e,he,_,_⟩ := exists_closed_footprint_extension V (T₁.proj ⁻¹' F₂)
    hK hKV (transport β (restrict R T₂)).tower ht
  exact ⟨Y,Q,hQ,e,he⟩
end
end Hironaka.HironakaG3DisjointTowerSecondExtension
