import Hironaka.Resolution.HironakaG3EmptyAwareHistory
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.G3UniverseEmptyAwareCore
open Hironaka.BlowupSequences BlowupTowers BlowupTowerIsomorphism
noncomputable section

/-- The original empty-aware relation, generalized in its existing namespace. -/
abbrev EmptyAwareTowerIso {d : ℕ} {P₁ P₂ : CMfd.{u} d}
    (Φ : P₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ P₂)
    {Q₁ Q₂ : CMfd.{u} d} (T₁ : BlowupTower P₁ Q₁) (T₂ : BlowupTower P₂ Q₂)
    (ψ : Q₁ ≃ₘ⟮𝓘(ℂ,ComplexModel d),𝓘(ℂ,ComplexModel d)⟯ Q₂) : Prop :=
  HironakaG3EmptyAwareHistory.EmptyAwareTowerIso Φ T₁ T₂ ψ

namespace EmptyAwareTowerIso
export HironakaG3EmptyAwareHistory.EmptyAwareTowerIso (refl step leftEmpty rightEmpty)
end EmptyAwareTowerIso
export HironakaG3EmptyAwareHistory (emptyAware_of_isTowerIso emptyAware_proj_comm)

/-- Reversing an empty-aware comparison exchanges left and right empty stages. -/
theorem symm {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{u} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂}
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) : EmptyAwareTowerIso Φ.symm T₂ T₁ ψ.symm := by
  induction h with
  | refl => exact .refl
  | @step Q₁ Q₂ R₁ R₂ T₁ T₂ ψ h C₁ ρ₁ hρ₁ C₂ ρ₂ hρ₂ ψnew hComm hCentre ih =>
    apply EmptyAwareTowerIso.step ih hρ₂ hρ₁ ψnew.symm
    · intro q
      apply ψ.injective
      change ψ (ρ₁ (ψnew.symm q)) = ψ (ψ.symm (ρ₂ q))
      rw [ψ.apply_symm_apply, ← hComm, ψnew.apply_symm_apply]
    · ext q
      constructor
      · intro hq
        have hq' : ψ.symm q ∈ ψ ⁻¹' C₂ := by rw [hCentre]; exact hq
        simpa only [mem_preimage, ψ.apply_symm_apply] using hq'
      · intro hq
        rw [← hCentre]
        change ψ (ψ.symm q) ∈ C₂
        simpa only [ψ.apply_symm_apply] using hq
  | @leftEmpty Q₁ Q₂ R₁ T₁ T₂ ψ h ρ hρ φ hφ ih =>
    have heq : (φ.trans ψ).symm = ψ.symm.trans φ.symm := by ext q; rfl
    rw [heq]
    exact EmptyAwareTowerIso.rightEmpty ih hρ φ hφ
  | @rightEmpty Q₁ Q₂ R₂ T₁ T₂ ψ h ρ hρ φ hφ ih =>
    have heq : (ψ.trans φ.symm).symm = φ.trans ψ.symm := by ext q; rfl
    rw [heq]
    exact EmptyAwareTowerIso.leftEmpty ih hρ φ hφ
/-- Cancel an actual final empty blowup on the right while retaining its endpoint map. -/
theorem strip_right_empty {n : ℕ} {X₁ X₂ Y₁ Y₂ Z₂ : CMfd.{u} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂} {ρ : Z₂ → Y₂}
    (hρ : IsBlowupAlong n (∅ : Set Y₂) ρ)
    (φ : Z₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂) (hφ : ∀ z, φ z = ρ z)
    {ψ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    (h : EmptyAwareTowerIso Φ T₁ (.step T₂ ∅ ρ hρ) ψ) :
    EmptyAwareTowerIso Φ T₁ T₂ (ψ.trans φ) := by
  cases h with
  | @step Q₁ _ R₁ _ T₁ _ ψold h C₁ ρ₁ hπ₁ _ _ _ _ hComm hCentre =>
    have hC : C₁ = ∅ := by simpa only [preimage_empty] using hCentre.symm
    subst C₁
    obtain ⟨φ₁,hφ₁⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ₁
    have heq : ψ.trans φ = φ₁.trans ψold := by
      ext p
      change φ (ψ p) = ψold (φ₁ p)
      rw [hφ, hComm, hφ₁]
    rw [heq]
    exact .leftEmpty h hπ₁ φ₁ hφ₁
  | @leftEmpty Q₁ _ R₁ T₁ _ ψold h ρ₁ hπ₁ φ₁ hφ₁ =>
    have hi := strip_right_empty hρ φ hφ h
    have heq : (φ₁.trans ψold).trans φ = φ₁.trans (ψold.trans φ) := by ext p; rfl
    rw [heq]
    exact .leftEmpty hi hπ₁ φ₁ hφ₁
  | @rightEmpty _ _ _ _ _ ψold h _ hπ₂ φ₂ hφ₂ =>
    have heq : φ₂ = φ := by ext p; rw [hφ₂, hφ]
    subst φ₂
    have heq' : (ψold.trans φ.symm).trans φ = ψold := by ext p; simp
    rw [heq']
    exact h
termination_by T₁.length

private theorem postcompose_refl {n : ℕ} {X₁ X₂ X₃ Y₁ : CMfd.{u} n}
    {Φ₁ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    (Φ₂ : X₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₃)
    {T₁ : BlowupTower X₁ Y₁}
    {ψ₁ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    (h₁ : EmptyAwareTowerIso Φ₁ T₁ .refl ψ₁) :
    EmptyAwareTowerIso (Φ₁.trans Φ₂) T₁ .refl (ψ₁.trans Φ₂) := by
  cases h₁ with
  | refl => exact .refl
  | @leftEmpty Q₁ _ R₁ T₁ _ ψold h ρ₁ hπ₁ φ₁ hφ₁ =>
    have hi := postcompose_refl Φ₂ h
    have heq : (φ₁.trans ψold).trans Φ₂ = φ₁.trans (ψold.trans Φ₂) := by ext p; rfl
    rw [heq]
    exact .leftEmpty hi hπ₁ φ₁ hφ₁
termination_by T₁.length


private theorem compose_step {n : ℕ} {X₁ X₂ X₃ Y₁ Y₂ Y₃ Z₂ Z₃ : CMfd.{u} n}
    {Φ₁ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {Φ₂ : X₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₃}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂} {T₃ : BlowupTower X₃ Y₃}
    {ψ₁ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₂}
    {ψ₂ : Y₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₃}
    {C₂ : Set Y₂} {ρ₂ : Z₂ → Y₂} (hρ₂ : IsBlowupAlong n C₂ ρ₂)
    {C₃ : Set Y₃} {ρ₃ : Z₃ → Y₃} (hρ₃ : IsBlowupAlong n C₃ ρ₃)
    (ψnew : Z₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z₃)
    (hComm : ∀ p, ρ₃ (ψnew p) = ψ₂ (ρ₂ p)) (hCentre : ψ₂ ⁻¹' C₃ = C₂)
    (h₁ : EmptyAwareTowerIso Φ₁ T₁ (.step T₂ C₂ ρ₂ hρ₂) ψ₁)
    (ih : ∀ {Y : CMfd.{u} n} {T : BlowupTower X₁ Y}
      {ψ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂},
      EmptyAwareTowerIso Φ₁ T T₂ ψ → EmptyAwareTowerIso (Φ₁.trans Φ₂) T T₃ (ψ.trans ψ₂)) :
    EmptyAwareTowerIso (Φ₁.trans Φ₂) T₁ (.step T₃ C₃ ρ₃ hρ₃) (ψ₁.trans ψnew) := by
  cases h₁ with
  | @step Q₁ _ R₁ _ T₁ _ ψold h C₁ ρ₁ hπ₁ _ _ _ _ hComm₁ hCentre₁ =>
    apply EmptyAwareTowerIso.step (ih h) hπ₁ hρ₃ (ψ₁.trans ψnew)
    · intro p
      change ρ₃ (ψnew (ψ₁ p)) = ψ₂ (ψold (ρ₁ p))
      rw [hComm, hComm₁]
    · ext p
      change ψ₂ (ψold p) ∈ C₃ ↔ p ∈ C₁
      change ψold p ∈ ψ₂ ⁻¹' C₃ ↔ p ∈ C₁
      rw [hCentre]
      change p ∈ ψold ⁻¹' C₂ ↔ p ∈ C₁
      rw [hCentre₁]
  | @leftEmpty Q₁ _ R₁ T₁ _ ψold h ρ₁ hπ₁ φ₁ hφ₁ =>
    have hp := compose_step hρ₂ hρ₃ ψnew hComm hCentre h ih
    have heq : (φ₁.trans ψold).trans ψnew = φ₁.trans (ψold.trans ψnew) := by ext p; rfl
    rw [heq]
    exact .leftEmpty hp hπ₁ φ₁ hφ₁
  | @rightEmpty _ _ _ _ _ ψold h _ hπ₂ φ₂ hφ₂ =>
    have hC : C₃ = ∅ := by
      ext y
      constructor
      · intro hy
        have hx : ψ₂.symm y ∈ ψ₂ ⁻¹' C₃ := by simpa only [mem_preimage, ψ₂.apply_symm_apply] using hy
        rw [hCentre] at hx
        exact hx
      · intro hy
        exact hy.elim
    subst C₃
    obtain ⟨φ₃,hφ₃⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hρ₃
    have heq : (ψold.trans φ₂.symm).trans ψnew = (ψold.trans ψ₂).trans φ₃.symm := by
      ext p
      change ψnew (φ₂.symm (ψold p)) = φ₃.symm (ψ₂ (ψold p))
      apply φ₃.injective
      change φ₃ (ψnew (φ₂.symm (ψold p))) = φ₃ (φ₃.symm (ψ₂ (ψold p)))
      rw [φ₃.apply_symm_apply, hφ₃, hComm, ← hφ₂, φ₂.apply_symm_apply]
    rw [heq]
    exact .rightEmpty (ih h) hρ₃ φ₃ hφ₃
termination_by T₁.length


/-- Empty-aware comparisons compose with their literal endpoint maps. -/
theorem trans {n : ℕ} {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CMfd.{u} n}
    {Φ₁ : X₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₂}
    {Φ₂ : X₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X₃}
    {T₁ : BlowupTower X₁ Y₁} {T₂ : BlowupTower X₂ Y₂} {T₃ : BlowupTower X₃ Y₃}
    {ψ₁ : Y₁ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₂}
    {ψ₂ : Y₂ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y₃}
    (h₁ : EmptyAwareTowerIso Φ₁ T₁ T₂ ψ₁) (h₂ : EmptyAwareTowerIso Φ₂ T₂ T₃ ψ₂) :
    EmptyAwareTowerIso (Φ₁.trans Φ₂) T₁ T₃ (ψ₁.trans ψ₂) := by
  induction h₂ generalizing Y₁ with
  | refl => exact postcompose_refl Φ₂ h₁
  | step h hπ₁ hπ₂ ψnew hComm hCentre ih =>
    exact compose_step hπ₁ hπ₂ ψnew hComm hCentre h₁ ih
  | @leftEmpty Q₁ Q₂ R₁ T₂ T₃ ψold h ρ hπ φ hφ ih =>
    have hp := strip_right_empty hπ φ hφ h₁
    have hc := ih hp
    have heq : (ψ₁.trans φ).trans ψold = ψ₁.trans (φ.trans ψold) := by ext p; rfl
    rw [← heq]
    exact hc
  | @rightEmpty Q₁ Q₂ R₂ T₂ T₃ ψold h ρ hπ φ hφ ih =>
    have hc := EmptyAwareTowerIso.rightEmpty (ih h₁) hπ φ hφ
    have heq : (ψ₁.trans ψold).trans φ.symm = ψ₁.trans (ψold.trans φ.symm) := by ext p; rfl
    rw [← heq]
    exact hc

end
end Hironaka.G3UniverseEmptyAwareCore
