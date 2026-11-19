import Hironaka.Resolution.HironakaChowNormalSupportProjection
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Flat.Stability

/-! The actual analytic normal-support retract gives ENTIRE base-ideal
intersection, canonical original quotient injection, and native flat base
change. No supplied projection/purity/flatness dictionary is input.
Blueprint FIRST: `hironaka-g10-normal-support-base-change.tex`. -/
set_option autoImplicit false
open Set Classical
open scoped TensorProduct
namespace Hironaka.HironakaChowNormalSupportBaseChange
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaChowNormalSupportProjection

variable (d t : ℕ)
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/-- The actual analytic inclusion pulls the entire base scalar ideal back
to the corresponding actual scalar submodule, derived from its OWN retract. -/
theorem normal_support_comap_base_ideal (Delta : Set (Fin t →₀ ℕ))
    (a : Ideal (HolGerm (ComplexModel d))) :
    (a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))))).comap
        (normalSupportSubmodule d t Delta).subtype =
      a • (⊤ : Submodule (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Delta)) := by
  let N := normalSupportSubmodule d t Delta
  let r := normalSupportRetraction d t Delta
  apply le_antisymm
  · intro x hx
    have hm : r (x : HolGerm (ComplexModel (d+t))) ∈
        (a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))))).map r :=
      Submodule.mem_map_of_mem hx
    rw [Submodule.map_smul''] at hm
    have hle : a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)))).map r ≤
        a • (⊤ : Submodule (HolGerm (ComplexModel d)) N) := smul_mono_right a le_top
    have he : r (x : HolGerm (ComplexModel (d+t))) = x :=
      congrArg (fun f => f x) (normalSupportRetraction_comp_subtype d t Delta)
    rw [he] at hm
    exact hle hm
  · intro x hx
    have hm := Submodule.mem_map_of_mem (f := N.subtype) hx
    rw [Submodule.map_smul''] at hm
    exact (smul_mono_right a (show (⊤ : Submodule (HolGerm (ComplexModel d)) N).map N.subtype ≤ ⊤
      from le_top)) hm

/-- The literal whole original extended ideal, not a radical or completion. -/
theorem normal_support_inf_base_ideal (Delta : Set (Fin t →₀ ℕ))
    (a : Ideal (HolGerm (ComplexModel d))) :
    normalSupportSubmodule d t Delta ⊓
        (Ideal.map (tangentPullback d t).toRingHom a).restrictScalars (HolGerm (ComplexModel d)) =
      (a • (⊤ : Submodule (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Delta))).map
        (normalSupportSubmodule d t Delta).subtype := by
  rw [← normal_support_comap_base_ideal d t Delta a, Submodule.map_comap_eq,
    Submodule.range_subtype, Ideal.smul_top_eq_map]
  rfl

/-- The SAME native ideal-torsion quotient module. -/
abbrev normalSupportQuotient (Delta : Set (Fin t →₀ ℕ))
    (a : Ideal (HolGerm (ComplexModel d))) :=
  normalSupportSubmodule d t Delta ⧸
    (a • (⊤ : Submodule (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Delta)))

/-- Native quotient algebra of the ORIGINAL ambient analytic ring. -/
instance ambientSupportQuotientAlgebra (a : Ideal (HolGerm (ComplexModel d))) :
    Algebra (HolGerm (ComplexModel d) ⧸ a)
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.map (tangentPullback d t).toRingHom a) :=
  Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map : a ≤
    (Ideal.map (tangentPullback d t).toRingHom a).comap (tangentPullback d t).toRingHom)

instance ambientSupportQuotientTower (a : Ideal (HolGerm (ComplexModel d))) :
    IsScalarTower (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d) ⧸ a)
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.map (tangentPullback d t).toRingHom a) :=
  IsScalarTower.of_algebraMap_eq (R := HolGerm (ComplexModel d))
    (S := HolGerm (ComplexModel d) ⧸ a)
    (A := HolGerm (ComplexModel (d+t)) ⧸ Ideal.map (tangentPullback d t).toRingHom a)
    (fun _ => rfl)

/-- The actual module quotient is the ORIGINAL ring quotient, preserving
each actual original representative and the native quotient-base action. -/
def ambientSupportQuotientEquiv (a : Ideal (HolGerm (ComplexModel d))) :
    (HolGerm (ComplexModel (d+t)) ⧸
      (a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)))))) ≃ₗ[
      HolGerm (ComplexModel d) ⧸ a]
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.map (tangentPullback d t).toRingHom a) :=
  ((Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map a)).trans
    (Submodule.Quotient.restrictScalarsEquiv (HolGerm (ComplexModel d))
      (Ideal.map (tangentPullback d t).toRingHom a))).extendScalarsOfSurjective
        Ideal.Quotient.mk_surjective

@[simp] theorem ambientSupportQuotientEquiv_mk (a : Ideal (HolGerm (ComplexModel d)))
    (f : HolGerm (ComplexModel (d+t))) :
    ambientSupportQuotientEquiv d t a (Submodule.Quotient.mk f) =
      Ideal.Quotient.mk (Ideal.map (tangentPullback d t).toRingHom a) f := rfl

private def nativeQuotientMap (Delta : Set (Fin t →₀ ℕ))
    (a : Ideal (HolGerm (ComplexModel d))) :
    normalSupportQuotient d t Delta a →ₗ[HolGerm (ComplexModel d) ⧸ a]
      (HolGerm (ComplexModel (d+t)) ⧸
        (a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)))))) :=
  ((a • (⊤ : Submodule (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Delta))).mapQ
    (a • (⊤ : Submodule (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)))))
    (normalSupportSubmodule d t Delta).subtype (normal_support_comap_base_ideal d t Delta a).ge
      ).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- Canonical injection into the ORIGINAL ring quotient, on actual germs. -/
def normalSupportQuotientInclusion (Delta : Set (Fin t →₀ ℕ))
    (a : Ideal (HolGerm (ComplexModel d))) :
    normalSupportQuotient d t Delta a →ₗ[HolGerm (ComplexModel d) ⧸ a]
      (HolGerm (ComplexModel (d+t)) ⧸ Ideal.map (tangentPullback d t).toRingHom a) :=
  (ambientSupportQuotientEquiv d t a).toLinearMap.comp (nativeQuotientMap d t Delta a)

@[simp] theorem normalSupportQuotientInclusion_mk (Delta : Set (Fin t →₀ ℕ))
    (a : Ideal (HolGerm (ComplexModel d))) (f : normalSupportSubmodule d t Delta) :
    normalSupportQuotientInclusion d t Delta a (Submodule.Quotient.mk f) =
      Ideal.Quotient.mk (Ideal.map (tangentPullback d t).toRingHom a) f.val := rfl

theorem normalSupportQuotientInclusion_injective (Delta : Set (Fin t →₀ ℕ))
    (a : Ideal (HolGerm (ComplexModel d))) :
    Function.Injective (normalSupportQuotientInclusion d t Delta a) := by
  intro x y hxy
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective
    (a • (⊤ : Submodule (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Delta))) x
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective
    (a • (⊤ : Submodule (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Delta))) y
  apply (Submodule.Quotient.eq _).mpr
  change (ambientSupportQuotientEquiv d t a) (nativeQuotientMap d t Delta a (Submodule.Quotient.mk u)) =
    (ambientSupportQuotientEquiv d t a) (nativeQuotientMap d t Delta a (Submodule.Quotient.mk v)) at hxy
  have hNative := (ambientSupportQuotientEquiv d t a).injective hxy
  have hMem := (Submodule.Quotient.eq _).mp hNative
  exact (normal_support_comap_base_ideal d t Delta a).le hMem

/-- Flatness is an OUTPUT for EVERY actual base quotient, by native tensor
base change of the genuinely constructed analytic support module. -/
theorem flat_normalSupportQuotient (Delta : Set (Fin t →₀ ℕ))
    (a : Ideal (HolGerm (ComplexModel d))) :
    Module.Flat (HolGerm (ComplexModel d) ⧸ a) (normalSupportQuotient d t Delta a) := by
  let : Module.Flat (HolGerm (ComplexModel d)) (normalSupportSubmodule d t Delta) :=
    flat_normalSupportSubmodule d t Delta
  let : IsScalarTower (HolGerm (ComplexModel d)) (HolGerm (ComplexModel d) ⧸ a)
      ((HolGerm (ComplexModel d) ⧸ a) ⊗[HolGerm (ComplexModel d)]
        normalSupportSubmodule d t Delta) := TensorProduct.isScalarTower_left
  let e : ((HolGerm (ComplexModel d) ⧸ a) ⊗[HolGerm (ComplexModel d)]
      normalSupportSubmodule d t Delta) ≃ₗ[HolGerm (ComplexModel d) ⧸ a]
      normalSupportQuotient d t Delta a :=
    (TensorProduct.quotTensorEquivQuotSMul (normalSupportSubmodule d t Delta) a
    ).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  exact Module.Flat.of_linearEquiv e.symm

end
end Hironaka.HironakaChowNormalSupportBaseChange
