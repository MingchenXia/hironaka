import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Actual algebraic constants in a separably generated extension

An internal zero specialization and Gauss's lemma preserve minimal
polynomials across the actual purely transcendental intermediate field.
Separability of the relative algebraic closure is then proved elementwise.
-/

noncomputable section

open Polynomial IntermediateField
open scoped IntermediateField.algebraAdjoinAdjoin

namespace DeJongAlterations.Algebra.SteinSeparability

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K F : Type u} [Field K] [Field F] [Algebra K F]
  {ι : Type v} {v : ι → F} (hv : AlgebraicIndependent K v)

include hv in
/-- Algebraic minimal polynomials are unchanged by adjoining the given independent family. -/
theorem minpoly_adjoin (a : F) (ha : IsIntegral K a) :
    minpoly (IntermediateField.adjoin K (Set.range v)) a =
      (minpoly K a).map (algebraMap K (IntermediateField.adjoin K (Set.range v))) := by
  let A := Algebra.adjoin K (Set.range v)
  let B := IntermediateField.adjoin K (Set.range v)
  let r : A →ₐ[K] K :=
    (MvPolynomial.aeval (fun _ : ι => (0 : K))).comp hv.aevalEquiv.symm.toAlgHom
  have hr : r.toRingHom.comp (algebraMap K A) = RingHom.id K := r.comp_algebraMap
  have hm : ((minpoly K a).map (algebraMap K A)).Monic := (minpoly.monic ha).map _
  have hiA : Irreducible ((minpoly K a).map (algebraMap K A)) := by
    apply hm.irreducible_of_irreducible_map r.toRingHom
    simpa only [Polynomial.map_map, hr, Polynomial.map_id] using minpoly.irreducible ha
  let : UniqueFactorizationMonoid A := hv.aevalEquiv.uniqueFactorizationMonoid inferInstance
  let : IsIntegrallyClosed A := inferInstance
  have hiB : Irreducible ((minpoly K a).map (algebraMap K B)) := by
    have h := hm.irreducible_iff_irreducible_map_fraction_map (K := B) |>.mp hiA
    simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K A B] using h
  exact (minpoly.eq_of_irreducible_of_monic hiB
    (by rw [Polynomial.aeval_map_algebraMap, minpoly.aeval]) ((minpoly.monic ha).map _)).symm

variable [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) F]

include hv in
/-- The original algebraic constant is separable, with no separability certificate supplied. -/
theorem isSeparable_of_isIntegral (a : F) (ha : IsIntegral K a) : IsSeparable K a := by
  have hs := Algebra.IsSeparable.isSeparable
    (IntermediateField.adjoin K (Set.range v)) a
  change (minpoly (IntermediateField.adjoin K (Set.range v)) a).Separable at hs
  rw [minpoly_adjoin hv a ha, Polynomial.separable_map] at hs
  exact hs

include hv in
/-- The actual native relative algebraic closure is a separable extension of the original field. -/
theorem algebraicClosure_isSeparable : Algebra.IsSeparable K (algebraicClosure K F) := by
  refine ⟨fun a => ?_⟩
  apply (isSeparable_map_iff (algebraicClosure K F).val Subtype.val_injective).mp
  exact isSeparable_of_isIntegral hv a a.property

end DeJongAlterations.Algebra.SteinSeparability
