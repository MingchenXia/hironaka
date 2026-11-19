import Hironaka.Resolution.HironakaG3UniverseEmptyAwareAlgebra
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseEmptyAwareOpenRestriction
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism G3UniverseEmptyAwareCore HironakaSharpActualCurveComparisonRestriction

theorem emptyAware_openPreimage_eq {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{u} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (U : Opens X₂) :
    (openPreimage T₁ (preimageOpen Φ U) : Set Y₁) = ψ ⁻¹' (openPreimage T₂ U : Set Y₂) := by
  ext z
  change Φ (T₁.proj z) ∈ U ↔ T₂.proj (ψ z) ∈ U
  rw [emptyAware_proj_comm h z]

theorem emptyAware_open_restriction {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{u} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (U : Opens X₂) :
    EmptyAwareTowerIso (openRestriction Φ (preimageOpen Φ U) U rfl)
      (restrict (preimageOpen Φ U) T₁) (restrict U T₂)
      (openRestriction ψ (openPreimage T₁ (preimageOpen Φ U)) (openPreimage T₂ U)
        (emptyAware_openPreimage_eq h U)) := by
  induction h with
  | refl => exact EmptyAwareTowerIso.refl
  | @step Y₁ Y₂ Z₁ Z₂ T₁ T₂ ψ h C₁ π₁ hπ₁ C₂ π₂ hπ₂ ψnew hcomm hC ih =>
    refine EmptyAwareTowerIso.step ih _ _ _ (fun p => Subtype.ext (hcomm p.val)) ?_
    ext p
    change ψ p.val ∈ C₂ ↔ p.val ∈ C₁
    change p.val ∈ ψ ⁻¹' C₂ ↔ p.val ∈ C₁
    rw [hC]
  | @leftEmpty Y₁ Y₂ Z₁ T₁ T₂ ψ h π hπ φ hφ ih =>
    have hOpen : (openPreimage (.step T₁ ∅ π hπ) (preimageOpen Φ U) : Set Z₁) =
        φ ⁻¹' (openPreimage T₁ (preimageOpen Φ U) : Set Y₁) := by
      ext z
      change T₁.proj (π z) ∈ preimageOpen Φ U ↔ T₁.proj (φ z) ∈ preimageOpen Φ U
      rw [hφ]
    let φ' := openRestriction φ (openPreimage (.step T₁ ∅ π hπ) (preimageOpen Φ U))
      (openPreimage T₁ (preimageOpen Φ U)) hOpen
    have hφ' : ∀ z, φ' z = ⟨π z.val,z.property⟩ := by
      intro z
      apply Subtype.ext
      exact hφ z.val
    have hπ' : IsBlowupAlong n (∅ : Set (openPreimage T₁ (preimageOpen Φ U)))
        (fun z : openPreimage (.step T₁ ∅ π hπ) (preimageOpen Φ U) => (⟨π z.val,z.property⟩ : openPreimage T₁ (preimageOpen Φ U))) := by
      have hMap : (fun z : openPreimage (.step T₁ ∅ π hπ) (preimageOpen Φ U) =>
          (⟨π z.val,z.property⟩ : openPreimage T₁ (preimageOpen Φ U))) = φ' :=
        funext (fun z => (hφ' z).symm)
      rw [hMap]
      exact MarkedIdealBiholomorphism.isBlowupAlong_empty_of_inverse φ'.symm.contMDiff φ'.contMDiff
        φ'.symm_apply_apply φ'.apply_symm_apply
    have hh := EmptyAwareTowerIso.leftEmpty ih hπ' φ' hφ'
    convert hh using 1 <;> simp only [BlowupTowerTransforms.restrict, Set.preimage_empty] <;> try rfl
  | @rightEmpty Y₁ Y₂ Z₂ T₁ T₂ ψ h π hπ φ hφ ih =>
    have hOpen : (openPreimage (.step T₂ ∅ π hπ) U : Set Z₂) =
        φ ⁻¹' (openPreimage T₂ U : Set Y₂) := by
      ext z
      change T₂.proj (π z) ∈ U ↔ T₂.proj (φ z) ∈ U
      rw [hφ]
    let φ' := openRestriction φ (openPreimage (.step T₂ ∅ π hπ) U) (openPreimage T₂ U) hOpen
    have hφ' : ∀ z, φ' z = ⟨π z.val,z.property⟩ := by
      intro z
      apply Subtype.ext
      exact hφ z.val
    have hπ' : IsBlowupAlong n (∅ : Set (openPreimage T₂ U))
        (fun z : openPreimage (.step T₂ ∅ π hπ) U => (⟨π z.val,z.property⟩ : openPreimage T₂ U)) := by
      have hMap : (fun z : openPreimage (.step T₂ ∅ π hπ) U =>
          (⟨π z.val,z.property⟩ : openPreimage T₂ U)) = φ' :=
        funext (fun z => (hφ' z).symm)
      rw [hMap]
      exact MarkedIdealBiholomorphism.isBlowupAlong_empty_of_inverse φ'.symm.contMDiff φ'.contMDiff
        φ'.symm_apply_apply φ'.apply_symm_apply
    have hh := EmptyAwareTowerIso.rightEmpty ih hπ' φ' hφ'
    convert hh using 1 <;> simp only [BlowupTowerTransforms.restrict, Set.preimage_empty] <;> try rfl
end
end Hironaka.G3UniverseEmptyAwareOpenRestriction
