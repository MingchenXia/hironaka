import Hironaka.Analytic.Unibranch.OriginalNativeHSShrinkingSuccessor

/-! Actual structural histories restrict to matching genuine base opens.
Blueprint FIRST: original-native-hs-tower-iso-restriction.tex.
Input is a TRUE old IsTowerIso, never an endpoint-only isomorphism. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSTowerIsoRestriction
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism

variable {n : ℕ} {X X' : CMfd.{0} n}
  (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (U : Opens X)

def basePreimage : Opens X' := ⟨Φ ⁻¹' (U : Set X), U.isOpen.preimage Φ.continuous⟩

def baseEquiv : basePreimage Φ U ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ U where
  toEquiv :=
    { toFun := fun p => ⟨Φ p.val, p.property⟩
      invFun := fun p => ⟨Φ.symm p.val, by
        change Φ (Φ.symm p.val) ∈ U
        rw [Φ.apply_symm_apply]
        exact p.property⟩
      left_inv := fun p => Subtype.ext (Φ.symm_apply_apply p.val)
      right_inv := fun p => Subtype.ext (Φ.apply_symm_apply p.val) }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact Φ.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (basePreimage Φ U) _).mp
    exact Φ.symm.contMDiff.comp contMDiff_subtype_val

variable {Φ} {Y' Y : CMfd.{0} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
  {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
  (h : IsTowerIso Φ T' T χ)

/-- Restrict the TRUE terminal map to the actual entire tower inverse opens. -/
def terminalEquiv : openPreimage T' (basePreimage Φ U) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ openPreimage T U where
  toEquiv :=
    { toFun := fun p => ⟨χ p.val, by
        change T.proj (χ p.val) ∈ U
        rw [← h.proj_comm p.val]
        exact p.property⟩
      invFun := fun p => ⟨χ.symm p.val, by
        change Φ (T'.proj (χ.symm p.val)) ∈ U
        rw [h.proj_comm, χ.apply_symm_apply]
        exact p.property⟩
      left_inv := fun p => Subtype.ext (χ.symm_apply_apply p.val)
      right_inv := fun p => Subtype.ext (χ.apply_symm_apply p.val) }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (openPreimage T U) _).mp
    exact χ.contMDiff.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (openPreimage T' (basePreimage Φ U)) _).mp
    exact χ.symm.contMDiff.comp contMDiff_subtype_val

theorem terminal_point (p : openPreimage T' (basePreimage Φ U)) :
    (terminalEquiv U h p).val = χ p.val := rfl

theorem terminal_projection (p : openPreimage T' (basePreimage Φ U)) :
    baseEquiv Φ U ((restrict (basePreimage Φ U) T').proj p) =
      (restrict U T).proj (terminalEquiv U h p) := by
  apply Subtype.ext
  exact (congrArg Φ (proj_restrict (basePreimage Φ U) T' p)).trans
    ((h.proj_comm p.val).trans (proj_restrict U T (terminalEquiv U h p)).symm)

/-- Every real physical step and centre is retained by the structural induction. -/
theorem isTowerIso : IsTowerIso (baseEquiv Φ U)
    (restrict (basePreimage Φ U) T') (restrict U T) (terminalEquiv U h) := by
  induction h with
  | refl => exact IsTowerIso.refl
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    refine IsTowerIso.step
      (Z' := CMfd.of (n := n) (openPreimage (.step T' C' π' hπ') (basePreimage Φ U)))
      (Z := CMfd.of (n := n) (openPreimage (.step T C π hπ) U))
      ih _ _ (terminalEquiv U (.step h hπ' hπ χ₁ hcomm hC)) ?_ ?_
    · intro p
      apply Subtype.ext
      exact hcomm p.val
    · ext p
      exact Set.ext_iff.mp hC p.val

include h in
theorem length_eq : (restrict (basePreimage Φ U) T').length = (restrict U T).length :=
  (isTowerIso U h).length_eq

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSTowerIsoRestriction
