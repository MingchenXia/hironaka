import DeJongAlterations.Algebra.ReesLocalization
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Flat base change of the actual Rees algebra

The actual coefficient map extends to a surjective tensor-product map.
Flatness makes it injective by tensoring the native Rees inclusion.
-/

open Polynomial
open scoped TensorProduct

noncomputable section

namespace DeJongAlterations.Algebra.ReesFlatBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The actual coefficient homomorphism as an algebra homomorphism over the source ring. -/
def reesCoefficientAlgHom (I : Ideal R) :
    reesAlgebra I →ₐ[R] reesAlgebra (I.map (algebraMap R S)) where
  __ := ReesLocalization.reesMap I (algebraMap R S)
  commutes' r := by
    change ReesLocalization.reesMap I (algebraMap R S)
      (algebraMap R (reesAlgebra I) r) = _
    rw [ReesLocalization.reesMap_algebraMap]
    exact (IsScalarTower.algebraMap_apply R S _ r).symm

/-- The actual coefficient map extended by the tensor-product universal property. -/
def reesBaseChangeMap (I : Ideal R) :
    S ⊗[R] reesAlgebra I →ₐ[S] reesAlgebra (I.map (algebraMap R S)) :=
  AlgHom.liftEquiv R S _ _ (reesCoefficientAlgHom (S := S) I)

@[simp]
theorem reesBaseChangeMap_tmul (I : Ideal R) (s : S) (p : reesAlgebra I) :
    reesBaseChangeMap (S := S) I (s ⊗ₜ[R] p) =
      s • ReesLocalization.reesMap I (algebraMap R S) p := rfl

/-- Every coefficient in an extended ideal power gives an actual tensor-image monomial. -/
theorem monomial_mem_range (I : Ideal R) (n : ℕ) (b : S)
    (hb : b ∈ (I.map (algebraMap R S)) ^ n) :
    monomial n b ∈
      ((reesAlgebra (I.map (algebraMap R S))).val.comp
        (reesBaseChangeMap (S := S) I)).range := by
  rw [← Ideal.map_pow] at hb
  change b ∈ Submodule.span S ((algebraMap R S) '' ((I ^ n : Ideal R) : Set R)) at hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨r, hr, rfl⟩ := hb
    refine ⟨(1 : S) ⊗ₜ[R] (⟨monomial n r, reesAlgebra.monomial_mem.mpr hr⟩ :
      reesAlgebra I), ?_⟩
    change (1 : S) • Polynomial.map (algebraMap R S) (monomial n r) = _
    simp
  | zero =>
    simp
  | add b c hb hc ihb ihc =>
    simpa only [map_add] using Subalgebra.add_mem _ ihb ihc
  | smul c b hb ih =>
    simpa only [map_smul] using Subalgebra.smul_mem _ ih c

/-- Finite polynomial support makes the actual tensor Rees map surjective without flatness. -/
theorem reesBaseChangeMap_surjective (I : Ideal R) :
    Function.Surjective (reesBaseChangeMap (S := S) I) := by
  intro p
  have hp : (p : S[X]) ∈
      ((reesAlgebra (I.map (algebraMap R S))).val.comp
        (reesBaseChangeMap (S := S) I)).range := by
    rw [(p : S[X]).as_sum_support]
    exact Subalgebra.sum_mem _ (fun n _ => monomial_mem_range I n _ (p.property n))
  obtain ⟨x, hx⟩ := hp
  exact ⟨x, Subtype.ext hx⟩

/-- The actual tensor Rees map is the tensor of the inclusion, followed by polynomial base change. -/
theorem reesBaseChangeMap_toPolynomial (I : Ideal R) :
    (reesAlgebra (I.map (algebraMap R S))).val.toLinearMap ∘ₗ
        (reesBaseChangeMap (S := S) I).toLinearMap =
      (polyEquivTensor' R S).symm.toLinearMap ∘ₗ
        (reesAlgebra I).val.toLinearMap.baseChange S := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s p
  change s • Polynomial.map (algebraMap R S) (p : R[X]) =
    (polyEquivTensor' R S).symm (s ⊗ₜ[R] (p : R[X]))
  exact (polyEquivTensor_symm_apply_tmul_eq_smul R S s p).symm

/-- Flatness preserves the genuine Rees inclusion into the polynomial ring. -/
theorem reesBaseChangeMap_injective [Module.Flat R S] (I : Ideal R) :
    Function.Injective (reesBaseChangeMap (S := S) I) := by
  have hinc : Function.Injective ((reesAlgebra I).val.toLinearMap.baseChange S) :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (reesAlgebra I).val.toLinearMap Subtype.val_injective
  have hcomp := (polyEquivTensor' R S).symm.injective.comp hinc
  intro x y hxy
  apply hcomp
  change ((polyEquivTensor' R S).symm.toLinearMap ∘ₗ
      (reesAlgebra I).val.toLinearMap.baseChange S) x =
    ((polyEquivTensor' R S).symm.toLinearMap ∘ₗ
      (reesAlgebra I).val.toLinearMap.baseChange S) y
  rw [← reesBaseChangeMap_toPolynomial]
  exact congrArg (fun z : reesAlgebra (I.map (algebraMap R S)) => (z : S[X])) hxy

/-- The actual coefficient map gives the flat base change isomorphism of native Rees rings. -/
def reesFlatBaseChange [Module.Flat R S] (I : Ideal R) :
    S ⊗[R] reesAlgebra I ≃ₐ[S] reesAlgebra (I.map (algebraMap R S)) :=
  AlgEquiv.ofBijective (reesBaseChangeMap (S := S) I)
    ⟨reesBaseChangeMap_injective I, reesBaseChangeMap_surjective I⟩

@[simp]
theorem reesFlatBaseChange_tmul [Module.Flat R S] (I : Ideal R) (s : S)
    (p : reesAlgebra I) :
    reesFlatBaseChange (S := S) I (s ⊗ₜ[R] p) =
      s • ReesLocalization.reesMap I (algebraMap R S) p := rfl

/-- Coefficient mapping as a native graded algebra map with restricted source scalars. -/
def reesCoefficientGradedAlgHom (I : Ideal R) :
    reesGrading I →ₐᵍ[R]
      (fun n => (reesGrading (I.map (algebraMap R S)) n).restrictScalars R) where
  __ := reesCoefficientAlgHom (S := S) I
  map_mem := by
    intro n p hp
    exact (ReesLocalization.reesGradedMap I (algebraMap R S)).map_mem hp

/-- The actual tensor coefficient map respects the native base-changed Rees grading. -/
def reesBaseChangeGradedMap (I : Ideal R) :
    (fun n => (reesGrading I n).baseChange S) →ₐᵍ[S]
      reesGrading (I.map (algebraMap R S)) :=
  GradedAlgHom.liftEquiv (reesGrading I) (reesGrading (I.map (algebraMap R S)))
    (reesCoefficientGradedAlgHom (S := S) I)

@[simp]
theorem reesBaseChangeGradedMap_toAlgHom (I : Ideal R) :
    (reesBaseChangeGradedMap (S := S) I).toAlgHom = reesBaseChangeMap (S := S) I := rfl

/-- Under the flat isomorphism, a tensor is homogeneous exactly when its actual image is. -/
theorem reesFlatBaseChange_mem_grade_iff [Module.Flat R S] (I : Ideal R)
    (n : ℕ) (x : S ⊗[R] reesAlgebra I) :
    reesFlatBaseChange (S := S) I x ∈ reesGrading (I.map (algebraMap R S)) n ↔
      x ∈ (reesGrading I n).baseChange S := by
  let g := (reesBaseChangeGradedMap (S := S) I).toGradedRingHom
  constructor
  · intro hx
    have hproj : reesBaseChangeMap (S := S) I
        (DirectSum.decompose (fun i => (reesGrading I i).baseChange S) x n) =
        reesBaseChangeMap (S := S) I x := by
      change g (DirectSum.decompose (fun i => (reesGrading I i).baseChange S) x n) = g x
      rw [g.map_directSumDecompose]
      exact DirectSum.decompose_of_mem_same (reesGrading (I.map (algebraMap R S))) hx
    rw [← reesBaseChangeMap_injective I hproj]
    exact (DirectSum.decompose (fun i => (reesGrading I i).baseChange S) x n).property
  · intro hx
    exact (reesBaseChangeGradedMap (S := S) I).map_mem hx

end DeJongAlterations.Algebra.ReesFlatBaseChange
