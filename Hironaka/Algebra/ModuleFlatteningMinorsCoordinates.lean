import Hironaka.Algebra.ModuleFlatteningMinors
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.Integer

/-!
# Original finite module generators and an internally cleared generic matrix

The basis is selected from the actual generic images of the original finite
module generators. One actual common denominator clears all coordinates.
The original selected basis columns give a nonzero maximal minor internally.
-/

noncomputable section

open Module
open scoped TensorProduct

namespace Hironaka.Algebra.ModuleFlatteningMinorsCoordinates

open ModuleFlatteningMinors

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R M : Type u) [CommRing R] [IsDomain R] [AddCommGroup M]
  [Module R M] [Module.Finite R M]

/-- Original finite generation internally selects an actual generic basis among
original module generator images. -/
theorem exists_generator_generic_basis :
    ∃ (n r : ℕ) (m : Fin n → M)
      (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M)) (s : Fin r → Fin n),
      Submodule.span R (Set.range m) = ⊤ ∧
      ∀ i, (1 : FractionRing R) ⊗ₜ[R] m (s i) = b i := by
  classical
  let K := FractionRing R
  obtain ⟨n, m, hm⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let v : Fin n → K ⊗[R] M := fun j ↦ 1 ⊗ₜ[R] m j
  have hs : Submodule.span K (Set.range v) = ⊤ := by
    have h := congrArg (fun p : Submodule R M ↦ p.baseChange K) hm
    simpa only [Submodule.baseChange_span, Submodule.baseChange_top, ← Set.range_comp,
      Function.comp_def, TensorProduct.mk_apply, v] using h
  let J : Set (K ⊗[R] M) :=
    (linearIndepOn_empty K id).extend (Set.empty_subset (Set.range v))
  have hJ : J ⊆ Set.range v :=
    (linearIndepOn_empty K id).extend_subset (Set.empty_subset (Set.range v))
  let : Fintype J := ((Set.finite_range v).subset hJ).fintype
  let b : Basis J K (K ⊗[R] M) := Basis.ofSpan hs.ge
  let r := Fintype.card J
  let b' : Basis (Fin r) K (K ⊗[R] M) := b.reindex (Fintype.equivFin J)
  have hb (i : Fin r) : b' i ∈ Set.range v := by
    rw [show b' i = b ((Fintype.equivFin J).symm i) from Basis.reindex_apply b _ i]
    rw [show b ((Fintype.equivFin J).symm i) = ((Fintype.equivFin J).symm i).val from
      Basis.ofSpan_apply_self hs.ge _]
    exact hJ ((Fintype.equivFin J).symm i).property
  choose s hsgen using hb
  exact ⟨n, r, m, b', s, hm, hsgen⟩

/-- The original finite module internally supplies generators, a generic basis,
one nonzero coordinate denominator, and an actual integral matrix with a nonzero minor. -/
theorem exists_integral_generic_coordinates :
    ∃ (n r : ℕ) (m : Fin n → M)
      (b : Basis (Fin r) (FractionRing R) (FractionRing R ⊗[R] M))
      (s : Fin r → Fin n) (δ : R) (A : Matrix (Fin r) (Fin n) R),
      Submodule.span R (Set.range m) = ⊤ ∧
      (∀ i, (1 : FractionRing R) ⊗ₜ[R] m (s i) = b i) ∧ δ ≠ 0 ∧
      (∀ i j, algebraMap R (FractionRing R) (A i j) =
        algebraMap R (FractionRing R) δ * b.repr ((1 : FractionRing R) ⊗ₜ[R] m j) i) ∧
      columnMinor A s ≠ 0 := by
  classical
  let K := FractionRing R
  obtain ⟨n, r, m, b, s, hm, hs⟩ := exists_generator_generic_basis R M
  obtain ⟨δ, hδ⟩ := IsLocalization.exist_integer_multiples_of_finite
    (S := K) (nonZeroDivisors R)
      (fun p : Fin r × Fin n ↦ b.repr ((1 : K) ⊗ₜ[R] m p.2) p.1)
  choose a ha using hδ
  let A : Matrix (Fin r) (Fin n) R := fun i j ↦ a (i, j)
  have hcoord (i : Fin r) (j : Fin n) : algebraMap R K (A i j) =
      algebraMap R K δ.val * b.repr ((1 : K) ⊗ₜ[R] m j) i := by
    simpa only [Algebra.smul_def] using ha (i, j)
  have hmat : (algebraMap R K).mapMatrix (selectedMatrix A s) =
      algebraMap R K δ.val • (1 : Matrix (Fin r) (Fin r) K) := by
    ext i j
    change algebraMap R K (A i (s j)) = _
    rw [hcoord, hs j]
    simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]
  have hdet : algebraMap R K (columnMinor A s) = algebraMap R K δ.val ^ r := by
    have h := (algebraMap R K).map_det (selectedMatrix A s)
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h
    exact h
  have hδ0 : δ.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp δ.property
  have hminor : columnMinor A s ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hdet
    exact (pow_ne_zero r ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hδ0)) hdet.symm
  exact ⟨n, r, m, b, s, δ.val, A, hm, hs, hδ0, hcoord, hminor⟩

end Hironaka.Algebra.ModuleFlatteningMinorsCoordinates
