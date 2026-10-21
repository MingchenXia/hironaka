/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalNearbyUniformRanks
import Hironaka.Resolution.HironakaLocalSymbolRegularity
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Canonical residue scalars for actual tangent germ rings

Origin evaluation identifies the canonical local residue field with the actual
complex residue algebra. Its tensor equivalence is natural for every genuine
base-linear map, so complex-fibre symbol injectivity is exactly the canonical
residue-field hypothesis in the local filtered-cut criterion. The criterion
retains its explicit finite-free and actual symbol-injectivity hypotheses;
this module does not produce general centre-normal flatness or resolve G8.
-/

set_option autoImplicit false
open scoped TensorProduct

namespace Hironaka.HironakaActualBaseResidueField
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalNearbyUniformRanks HironakaStrictFilteredGradedQuotient
attribute [local instance] baseGermResidueAlgebra

/-- The full origin-evaluation map on the canonical residue field of the actual base. -/
def baseResidueFieldHom (d : ℕ) :
    IsLocalRing.ResidueField (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)] ℂ where
  toRingHom := Ideal.Quotient.lift _ HolGerm.eval (fun g hg =>
    (HolGerm.mem_maximalIdeal_iff g).mp hg)
  commutes' _ := rfl

@[simp] theorem baseResidueFieldHom_residue (d : ℕ) (g : HolGerm (ComplexModel d)) :
    baseResidueFieldHom d (IsLocalRing.residue _ g) = HolGerm.eval g := rfl

/-- Canonical residue scalars are the actual origin-valued complex scalars. -/
def baseResidueFieldEquiv (d : ℕ) :
    IsLocalRing.ResidueField (HolGerm (ComplexModel d)) ≃ₐ[HolGerm (ComplexModel d)] ℂ :=
  AlgEquiv.ofBijective (baseResidueFieldHom d)
    ⟨(baseResidueFieldHom d).toRingHom.injective, fun c =>
      ⟨IsLocalRing.residue (HolGerm (ComplexModel d)) (HolGerm.constHom c),
        HolGerm.eval_constHom (E := ComplexModel d) c⟩⟩

@[simp] theorem baseResidueFieldEquiv_residue (d : ℕ) (g : HolGerm (ComplexModel d)) :
    baseResidueFieldEquiv d (IsLocalRing.residue _ g) = HolGerm.eval g := rfl

@[simp] theorem baseResidueFieldEquiv_symm (d : ℕ) (c : ℂ) :
    (baseResidueFieldEquiv d).symm c = IsLocalRing.residue _ (HolGerm.constHom c) := by
  apply (baseResidueFieldEquiv d).injective
  rw [AlgEquiv.apply_symm_apply, baseResidueFieldEquiv_residue, HolGerm.eval_constHom]

variable (d : ℕ) (P Q : Type*) [AddCommGroup P] [AddCommGroup Q]
  [Module (HolGerm (ComplexModel d)) P] [Module (HolGerm (ComplexModel d)) Q]

/-- Tensoring the genuine canonical residue dictionary retains all original module members. -/
def residueTensorEquiv :
    (IsLocalRing.ResidueField (HolGerm (ComplexModel d)) ⊗[HolGerm (ComplexModel d)] P) ≃ₗ[HolGerm (ComplexModel d)]
      (ℂ ⊗[HolGerm (ComplexModel d)] P) :=
  TensorProduct.congr (baseResidueFieldEquiv d).toLinearEquiv (LinearEquiv.refl _ P)

@[simp] theorem residueTensorEquiv_tmul
    (a : IsLocalRing.ResidueField (HolGerm (ComplexModel d))) (p : P) :
    residueTensorEquiv d P (a ⊗ₜ[HolGerm (ComplexModel d)] p) =
      baseResidueFieldEquiv d a ⊗ₜ[HolGerm (ComplexModel d)] p := rfl

variable {P Q}

theorem residueTensorEquiv_natural (f : P →ₗ[HolGerm (ComplexModel d)] Q)
    (z : IsLocalRing.ResidueField (HolGerm (ComplexModel d)) ⊗[HolGerm (ComplexModel d)] P) :
    residueTensorEquiv d Q (f.lTensor _ z) = f.lTensor ℂ (residueTensorEquiv d P z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a p => simp only [LinearMap.lTensor_tmul, residueTensorEquiv_tmul]
  | add z w hz hw => simpa only [map_add] using congrArg₂ (· + ·) hz hw

theorem residue_lTensor_injective_iff_complex (f : P →ₗ[HolGerm (ComplexModel d)] Q) :
    Function.Injective (f.lTensor (IsLocalRing.ResidueField (HolGerm (ComplexModel d)))) ↔
      Function.Injective (f.lTensor ℂ) := by
  constructor
  · intro hf x y hxy
    obtain ⟨a, rfl⟩ := (residueTensorEquiv d P).surjective x
    obtain ⟨b, rfl⟩ := (residueTensorEquiv d P).surjective y
    apply congrArg (residueTensorEquiv d P)
    apply hf
    apply (residueTensorEquiv d Q).injective
    rw [residueTensorEquiv_natural, residueTensorEquiv_natural, hxy]
  · intro hf x y hxy
    apply (residueTensorEquiv d P).injective
    apply hf
    rw [← residueTensorEquiv_natural, ← residueTensorEquiv_natural, hxy]

theorem adicLayer_after_parameter_finite_free_of_complex
    {R : Type*} [CommRing R] [Algebra (HolGerm (ComplexModel d)) R]
    (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hfinite : ∀ q : ℕ, Module.Finite (HolGerm (ComplexModel d)) (adicLayer I N q))
    (hfree : ∀ q : ℕ, Module.Free (HolGerm (ComplexModel d)) (adicLayer I N q))
    (hfibre : ∀ q : ℕ, Function.Injective
      (((adicSymbolMul I N v hv q).restrictScalars (HolGerm (ComplexModel d))).lTensor ℂ))
    (q : ℕ) :
    Module.Finite (HolGerm (ComplexModel d)) (adicLayer (I ⊔ Ideal.span ({v} : Set R)) N q) ∧
      Module.Free (HolGerm (ComplexModel d)) (adicLayer (I ⊔ Ideal.span ({v} : Set R)) N q) := by
  apply HironakaLocalSymbolRegularity.adicLayer_after_parameter_finite_free I N v hv hfinite hfree
  intro r
  exact (residue_lTensor_injective_iff_complex d _).mpr (hfibre r)

end
end Hironaka.HironakaActualBaseResidueField
