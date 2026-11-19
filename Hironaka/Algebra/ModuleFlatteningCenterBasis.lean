import Hironaka.Algebra.ModuleFlatteningCenterMatrix
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The original cleared coordinate matrix factors through actual selected local basis columns

Local bases are selected internally from the original tensor generator
family. The original generic basis fixes the same rank and original
cleared coordinate matrix. The exact factorization uses actual module
basis expansions and original tensor coefficient maps.
-/

noncomputable section

open Module TensorProduct
open scoped TensorProduct BigOperators

namespace Hironaka.Algebra.ModuleFlatteningCenter

open ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R M S : Type u} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
  [CommRing S] [Algebra R S] [Algebra S (FractionRing R)]
  [IsScalarTower R S (FractionRing R)]

/-- The original coefficient tensor map to the original generic module for an actual coefficient algebra. -/
def coefficientTensorMap : S ⊗[R] M →ₗ[S] FractionRing R ⊗[R] M :=
  AlgebraTensorModule.map (Algebra.linearMap S (FractionRing R)) (LinearMap.id : M →ₗ[R] M)

omit [IsDomain R] in
/-- The actual original tensor generator keeps its original generic value. -/
@[simp]
theorem coefficientTensorMap_one_tmul (m : M) :
    coefficientTensorMap (S := S) ((1 : S) ⊗ₜ[R] m) = (1 : FractionRing R) ⊗ₜ[R] m := by
  simp [coefficientTensorMap]

/-- A local flat original tensor module internally selects an original-generator basis
with exactly the original generic rank, by actual base change and tensor cancellation. -/
theorem exists_original_generator_basis [IsLocalRing S]
    [Module.FinitePresentation S (S ⊗[R] M)] [Module.Flat S (S ⊗[R] M)]
    {n r : ℕ} (m : Fin n → M) (hm : Submodule.span R (Set.range m) = ⊤)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M)) :
    ∃ (s : Fin r → Fin n) (c : Basis (Fin r) S (S ⊗[R] M)),
      ∀ j, c j = (1 : S) ⊗ₜ[R] m (s j) := by
  classical
  let v : ULift.{u} (Fin n) → S ⊗[R] M := fun j ↦ 1 ⊗ₜ[R] m j.down
  have hbase : Submodule.span S (Set.range fun j : Fin n ↦ (1 : S) ⊗ₜ[R] m j) = ⊤ := by
    have h := congrArg (fun p : Submodule R M ↦ p.baseChange S) hm
    simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp,
      Function.comp_def, TensorProduct.mk_apply] using h
  have hv : Submodule.span S (Set.range v) = ⊤ := by
    have heq : Set.range v = Set.range fun j : Fin n ↦ (1 : S) ⊗ₜ[R] m j := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨j.down, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨⟨j⟩, rfl⟩
    rwa [heq]
  obtain ⟨κ, a, c, hc⟩ := Module.exists_basis_of_span_of_flat v hv
  let cK := (c.baseChange (FractionRing R)).map
    (AlgebraTensorModule.cancelBaseChange R S (FractionRing R) (FractionRing R) M)
  let e : κ ≃ Fin r := cK.indexEquiv b
  refine ⟨fun j ↦ (a (e.symm j)).down, c.reindex e, fun j ↦ ?_⟩
  rw [Basis.reindex_apply, hc]

omit [IsDomain R] in
/-- The original cleared coordinate matrix factors through the actual selected local basis block. -/
theorem coordinateMatrix_factorization
    {n r : ℕ} (m : Fin n → M)
    (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
    (δ : R) (V : Matrix (Fin r) (Fin n) R)
    (hcoord : ∀ i j, algebraMap R (FractionRing R) (V i j) =
      algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i)
    (s : Fin r → Fin n) (c : Basis (Fin r) S (S ⊗[R] M))
    (hc : ∀ j, c j = (1 : S) ⊗ₜ[R] m (s j))
    (hinj : Function.Injective (algebraMap S (FractionRing R))) :
    V.map (algebraMap R S) =
      @HMul.hMul (Matrix (Fin r) (Fin r) S) (Matrix (Fin r) (Fin n) S)
        (Matrix (Fin r) (Fin n) S) inferInstance
        (selectedMatrix (V.map (algebraMap R S)) s)
        (fun j a ↦ c.repr ((1 : S) ⊗ₜ[R] m a) j) := by
  classical
  ext i a
  apply hinj
  have hrel : (1 : FractionRing R) ⊗ₜ[R] m a =
      ∑ j, algebraMap S (FractionRing R) (c.repr ((1 : S) ⊗ₜ[R] m a) j) •
        ((1 : FractionRing R) ⊗ₜ[R] m (s j)) := by
    have h := congrArg (coefficientTensorMap (R := R) (M := M) (S := S))
      (c.sum_repr ((1 : S) ⊗ₜ[R] m a))
    simp only [map_sum, map_smul, hc, coefficientTensorMap_one_tmul] at h
    simpa only [IsScalarTower.algebraMap_smul] using h.symm
  have hcoords := congrArg (fun x ↦ b.repr x i) hrel
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul] at hcoords
  change algebraMap S (FractionRing R) (algebraMap R S (V i a)) =
    algebraMap S (FractionRing R)
      (∑ j, algebraMap R S (V i (s j)) * c.repr ((1 : S) ⊗ₜ[R] m a) j)
  simp only [map_sum, map_mul, ← IsScalarTower.algebraMap_apply R S (FractionRing R), hcoord]
  rw [hcoords, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Hironaka.Algebra.ModuleFlatteningCenter
