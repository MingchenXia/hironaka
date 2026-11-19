import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Lifting the same residue vectors at the generic rank

For finite modules over a local ring embedded in a field, equality of the
generic and residue dimensions produces a basis, with no flatness premise.
The basis-lifting form retains prescribed vectors, as required for the actual
normal standard monomials in relative standardness.
-/

set_option autoImplicit false

namespace Hironaka.HironakaActualRelativeStandardnessLocalBasis

noncomputable section

open TensorProduct

variable {B L M : Type*} [CommRing B] [IsLocalRing B] [Field L] [Algebra B L]
  [AddCommGroup M] [Module B M] [Module.Finite B M]

/-- Numeric generic rank and a residue basis produce a basis retaining the same lifts. -/
theorem exists_basis_of_residue_basis_of_generic_rank
    (hBL : Function.Injective (algebraMap B L))
    {ι : Type*} [Fintype ι] (v : ι → M)
    (bk : Module.Basis ι (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField B ⊗[B] M))
    (hv : ∀ i, (1 : IsLocalRing.ResidueField B) ⊗ₜ[B] v i = bk i)
    (hrank : Module.finrank L (L ⊗[B] M) = Fintype.card ι) :
    ∃ b : Module.Basis ι B M, ∀ i, b i = v i := by
  classical
  let f : (ι →₀ B) →ₗ[B] M := Finsupp.linearCombination B v
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v bk hv
  let e : Module.Basis ι L (L ⊗[B] (ι →₀ B)) :=
    (Finsupp.basisSingleOne : Module.Basis ι B (ι →₀ B)).baseChange L
  have hdim : Module.finrank L (L ⊗[B] (ι →₀ B)) =
      Module.finrank L (L ⊗[B] M) :=
    (Module.finrank_eq_card_basis e).trans hrank.symm
  have hsurjL : Function.Surjective (f.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact f.lTensor_surjective L hsurj
  have hinjL : Function.Injective (f.baseChange L) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurjL
  have he (i : ι) : f.baseChange L (e i) = (1 : L) ⊗ₜ[B] v i := by
    simp [e, Module.Basis.baseChange_apply, LinearMap.baseChange_tmul, f]
  have hliL : LinearIndependent L (fun i => (1 : L) ⊗ₜ[B] v i) := by
    have h := e.linearIndependent.map' (f.baseChange L) (LinearMap.ker_eq_bot.mpr hinjL)
    simpa only [Function.comp_def, he] using h
  have hscalar : Function.Injective (fun b : B => b • (1 : L)) := by
    simpa only [Algebra.smul_def, mul_one] using hBL
  have hliB : LinearIndependent B v :=
    LinearIndependent.of_comp (TensorProduct.mk B L M 1)
      (LinearIndependent.restrict_scalars hscalar hliL)
  let ef : (ι →₀ B) ≃ₗ[B] M := LinearEquiv.ofBijective f ⟨hliB, hsurj⟩
  refine ⟨Finsupp.basisSingleOne.map ef, ?_⟩
  intro i
  change f (Finsupp.single i 1) = v i
  simp [f]

/-- Equality of generic and residue dimensions forces a finite module to be free. -/
theorem free_of_generic_rank_eq_residue_dimension
    (hBL : Function.Injective (algebraMap B L))
    (hrank : Module.finrank L (L ⊗[B] M) =
      Module.finrank (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B ⊗[B] M)) :
    Module.Free B M := by
  let k := IsLocalRing.ResidueField B
  let bk := Module.Free.chooseBasis k (k ⊗[B] M)
  let := Module.Free.ChooseBasisIndex.fintype k (k ⊗[B] M)
  obtain ⟨v, hv⟩ :=
    (TensorProduct.mk_surjective B M k Ideal.Quotient.mk_surjective).comp_left bk
  have hv' : ∀ i, (1 : k) ⊗ₜ[B] v i = bk i := fun i => congrFun hv i
  obtain ⟨b, _hb⟩ := exists_basis_of_residue_basis_of_generic_rank hBL v bk hv'
    (hrank.trans (Module.finrank_eq_card_basis bk))
  exact Module.Free.of_basis b

omit [Module.Finite B M] in
/-- Any field fibre killing the maximal ideal has the same dimension as the canonical residue fibre. -/
theorem residue_tensor_finrank_eq_of_maximalIdeal_le_ker
    {k : Type*} [Field k] [Algebra B k]
    (hmax : IsLocalRing.maximalIdeal B ≤ RingHom.ker (algebraMap B k)) :
    Module.finrank k (k ⊗[B] M) =
      Module.finrank (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField B ⊗[B] M) := by
  let k₀ := IsLocalRing.ResidueField B
  let f : k₀ →ₐ[B] k := Ideal.Quotient.liftₐ _ (Algebra.ofId B k) hmax
  let : Algebra k₀ k := f.toRingHom.toAlgebra
  let : IsScalarTower B k₀ k :=
    IsScalarTower.of_algebraMap_eq (fun b => (f.commutes b).symm)
  let e := AlgebraTensorModule.cancelBaseChange B k₀ k k M
  exact e.finrank_eq.symm.trans
    (Module.finrank_baseChange (R := k) (S := k₀) (M' := k₀ ⊗[B] M))

/-- Numeric equality with the actual field fibre produces freeness without a supplied flatness premise. -/
theorem free_of_generic_rank_eq_field_fibre_dimension
    (hBL : Function.Injective (algebraMap B L))
    {k : Type*} [Field k] [Algebra B k]
    (hmax : IsLocalRing.maximalIdeal B ≤ RingHom.ker (algebraMap B k))
    (hrank : Module.finrank L (L ⊗[B] M) = Module.finrank k (k ⊗[B] M)) :
    Module.Free B M := by
  apply free_of_generic_rank_eq_residue_dimension hBL
  exact hrank.trans (residue_tensor_finrank_eq_of_maximalIdeal_le_ker hmax)

end

end Hironaka.HironakaActualRelativeStandardnessLocalBasis
