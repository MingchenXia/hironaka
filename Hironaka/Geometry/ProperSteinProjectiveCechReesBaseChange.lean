/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
Adapted closed native proof from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesIdealBaseChange.lean`,
SHA256 9cc42de452ae6eafff2f8d1716c254e151c8fe268657ad8dbe8a0c1f8ab663a5.
Only native Mathlib and owned actual original Rees helper modules are imported.
The geometric finite cohomology/formal-functions comparison remains separate.


# Genuine Rees algebras under arbitrary coefficient extension

The canonical tensor map onto the Rees algebra of the extended ideal is
surjective without a flatness hypothesis. It retains every original
coefficient and homogeneous monomial. This constructs the affine pieces of
the coherent Rees algebra used in proper formal functions.
-/

open scoped TensorProduct Polynomial
noncomputable section
universe u

namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesBaseChange

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (I : Ideal R)

/-- The actual coefficient polynomial map restricts to the actual Rees
algebras of the original and extended ideals. -/
def reesMap : reesAlgebra I →ₐ[R] reesAlgebra (I.map (algebraMap R A)) :=
  (((Polynomial.mapAlgHom (Algebra.ofId R A)).comp (reesAlgebra I).val).codRestrict
    ((reesAlgebra (I.map (algebraMap R A))).restrictScalars R) fun p n => by
      rw [AlgHom.comp_apply, Polynomial.coeff_mapAlgHom_apply]
      change algebraMap R A ((p : R[X]).coeff n) ∈ I.map (algebraMap R A) ^ n
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (p.2 n))

/-- The canonical actual tensor map onto the extended Rees algebra. -/
def baseChangeMap : A ⊗[R] reesAlgebra I →ₐ[A] reesAlgebra (I.map (algebraMap R A)) :=
  Algebra.TensorProduct.lift (Algebra.ofId A _) (reesMap (A := A) I)
    fun _ _ => Commute.all _ _

/-- The entire coefficient polynomial is the literal coefficient extension,
multiplied by the actual tensor coefficient. -/
theorem baseChangeMap_tmul_val (a : A) (p : reesAlgebra I) :
    (baseChangeMap I (a ⊗ₜ[R] p) : A[X]) =
      Polynomial.C a * Polynomial.map (algebraMap R A) (p : R[X]) := by
  rw [baseChangeMap, Algebra.TensorProduct.lift_tmul]
  rfl

/-- Every original homogeneous monomial and every new coefficient retain
their full degree and value under the actual tensor map. -/
theorem baseChangeMap_tmul_monomial_val (a : A) (n : ℕ) (r : R) (hr : r ∈ I ^ n) :
    (baseChangeMap I (a ⊗ₜ[R] (⟨Polynomial.monomial n r,
      reesAlgebra.monomial_mem.mpr hr⟩ : reesAlgebra I)) : A[X]) =
      Polynomial.monomial n (a * algebraMap R A r) := by
  rw [baseChangeMap_tmul_val, Polynomial.map_monomial, Polynomial.C_mul_monomial]

/-- Every polynomial in the actual extended Rees algebra comes from the
actual coefficient tensor. No flatness or injectivity is required. -/
theorem baseChangeMap_surjective : Function.Surjective (baseChangeMap (A := A) I) := by
  let ambient := (reesAlgebra (I.map (algebraMap R A))).val.comp (baseChangeMap I)
  have hspan : I.map (algebraMap R A) ≤
      Submodule.comap (Polynomial.monomial 1 : A →ₗ[A] A[X]) ambient.range.toSubmodule := by
    change Submodule.span A ((algebraMap R A) '' (I : Set R)) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨1 ⊗ₜ[R] (⟨Polynomial.monomial 1 r,
      reesAlgebra.monomial_mem.mpr (by simpa using hr)⟩ : reesAlgebra I), ?_⟩
    change (baseChangeMap I ((1 : A) ⊗ₜ[R] (⟨Polynomial.monomial 1 r,
      reesAlgebra.monomial_mem.mpr (by simpa using hr)⟩ : reesAlgebra I)) : A[X]) = _
    simpa only [one_mul] using baseChangeMap_tmul_monomial_val I (1 : A) 1 r (by simpa using hr)
  intro p
  have hp : (p : A[X]) ∈ ambient.range := by
    have hmem := (adjoin_monomial_eq_reesAlgebra (I := I.map (algebraMap R A))).ge p.2
    refine Algebra.adjoin_le ?_ hmem
    rintro _ ⟨a, ha, rfl⟩
    exact hspan ha
  obtain ⟨q, hq⟩ := hp
  exact ⟨q, Subtype.ext hq⟩

/-- The whole original Rees coefficient map is the right tensor inclusion
followed by the actual base-change map. -/
theorem baseChangeMap_comp_includeRight :
    ((baseChangeMap (A := A) I).restrictScalars R).comp
        Algebra.TensorProduct.includeRight = reesMap (A := A) I := by
  apply AlgHom.ext
  intro p
  change baseChangeMap I ((1 : A) ⊗ₜ[R] p) = reesMap I p
  rw [baseChangeMap, Algebra.TensorProduct.lift_tmul]
  simp

/-- The entire original A coefficient triangle commutes as actual ring
homomorphisms, not merely on selected generators. -/
theorem baseChangeMap_comp_algebraMap :
    (baseChangeMap (A := A) I).toRingHom.comp (algebraMap A (A ⊗[R] reesAlgebra I)) =
      algebraMap A (reesAlgebra (I.map (algebraMap R A))) := by
  apply RingHom.ext
  intro a
  exact (baseChangeMap I).commutes a

/-- The actual extended Rees affine scheme is a closed subscheme of the
literal tensor base extension. -/
theorem spec_baseChangeMap_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (baseChangeMap (A := A) I).toRingHom)) :=
  AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ (baseChangeMap_surjective I)

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesBaseChange
