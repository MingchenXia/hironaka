import Hironaka.Algebra.PluckerQuotTransitionMatrix
import Hironaka.Algebra.PluckerQuotTransitionRelabel
import Hironaka.Algebra.ProjectiveIdealChartAlgebra

/-!
# Whole original pivot coordinate quotient and its actual matrix coordinates

All coordinates below are elements of the literal dehomogenization of the
original homogeneous minor-relation ideal. No radical, reduced quotient, or
pointwise replacement is used.
-/

noncomputable section

open MvPolynomial

namespace Hironaka.Algebra.PluckerQuot

open ModuleFlatteningMinors Geometry.ProjectiveIdeal

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {ι κ η : Type u}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] {n : ℕ}
  (β : Fin (n + 1) ≃ (ι → η)) (e : (ι ⊕ κ) ≃ η)

/-- The index of the literal original pivot selector. -/
def pivotIndex : Fin (n + 1) := β.symm (e ∘ Sum.inl)

/-- The whole original homogeneous relation ideal after actual dehomogenization. -/
def pivotDehomIdeal : Ideal (CoordinateRing R (pivotIndex β e)) :=
  (minorRelationIdeal R ι η (Fin (n + 1)) β).toIdeal.map
    (coordinateDehom (pivotIndex β e)).toRingHom

/-- The whole coordinate ring of the original dehomogenized closed model. -/
abbrev PivotCoordinateRing := CoordinateRing R (pivotIndex β e) ⧸ pivotDehomIdeal R β e

/-- Actual dehomogenization followed by the literal original whole-ideal quotient. -/
def pivotDehom : MvPolynomial (Fin (n + 1)) R →ₐ[R] PivotCoordinateRing R β e :=
  (Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e)).comp (coordinateDehom (pivotIndex β e))

/-- The original projective coordinate ratio as an element of the whole actual chart ring. -/
def pivotCoordinate (t : ι → η) : PivotCoordinateRing R β e :=
  pivotDehom R β e (X (β.symm t))

omit [Fintype κ] [DecidableEq κ] in
/-- Every whole original ideal relation vanishes in the literal pivot coordinate quotient. -/
theorem pivotDehom_eq_zero {F : MvPolynomial (Fin (n + 1)) R}
    (hF : F ∈ (minorRelationIdeal R ι η (Fin (n + 1)) β).toIdeal) :
    pivotDehom R β e F = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_map_of_mem _ hF

omit [Fintype κ] [DecidableEq κ] in
@[simp]
theorem pivotCoordinate_pivot : pivotCoordinate R β e (e ∘ Sum.inl) = 1 := by
  change (Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e))
    (coordinateDehom (pivotIndex β e) (X (pivotIndex β e))) = 1
  rw [coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord_self, map_one]

omit [Fintype κ] [DecidableEq κ] in
/-- An actual repeated selector already vanishes in the original whole ideal quotient. -/
theorem pivotCoordinate_eq_zero_of_not_injective (t : ι → η)
    (ht : ¬ Function.Injective t) : pivotCoordinate R β e t = 0 := by
  apply pivotDehom_eq_zero
  apply X_mem_minorRelationIdeal_of_not_injective R ι η (Fin (n + 1)) β
  simpa using ht

omit [Fintype κ] [DecidableEq κ] in
/-- Replacing a pivot column by another original pivot column gives the exact Kronecker entry. -/
theorem pivotCoordinate_pivot_replacement (i k : ι) :
    pivotCoordinate R β e (Function.update (e ∘ Sum.inl) i (e (Sum.inl k))) =
      (1 : Matrix ι ι (PivotCoordinateRing R β e)) i k := by
  classical
  by_cases hik : i = k
  · subst k
    have hu : Function.update (e ∘ Sum.inl) i (e (Sum.inl i)) = e ∘ Sum.inl := by
      exact Function.update_eq_self i (e ∘ Sum.inl)
    rw [hu, pivotCoordinate_pivot]
    simp
  · have ht : ¬ Function.Injective
        (Function.update (e ∘ Sum.inl) i (e (Sum.inl k))) := by
      intro hinj
      apply hik
      apply hinj
      simp [Function.update, Ne.symm hik]
    rw [pivotCoordinate_eq_zero_of_not_injective R β e _ ht]
    simp [hik]

/-- The actual matrix entries extracted from the original replacement-coordinate ratios. -/
def pivotMatrix : Matrix ι κ (PivotCoordinateRing R β e) :=
  fun i j ↦ pivotCoordinate R β e (Function.update (e ∘ Sum.inl) i (e (Sum.inr j)))

/-- Every actual replacement-coordinate entry is the corresponding entry of the same matrix. -/
theorem pivotCoordinate_replacement (i : ι) (k : η) :
    pivotCoordinate R β e (Function.update (e ∘ Sum.inl) i k) =
      splitNormalizedMatrix e (pivotMatrix R β e) i k := by
  obtain ⟨k, rfl⟩ := e.surjective k
  cases k with
  | inl k => simpa using pivotCoordinate_pivot_replacement R β e i k
  | inr j => simp [pivotMatrix]

omit [Fintype κ] [DecidableEq κ] in
/-- The whole original Cramer relation becomes its literal determinant identity in this ring. -/
theorem pivotCoordinate_cramer [Nonempty ι] (t : ι → η) :
    Matrix.det (fun i j ↦ pivotCoordinate R β e
      (Function.update (e ∘ Sum.inl) i (t j))) = pivotCoordinate R β e t := by
  let E := (pivotDehom R β e).comp (MvPolynomial.rename β.symm)
  have hz : E (cramerRelation (R := R) (e ∘ Sum.inl) t) = 0 :=
    pivotDehom_eq_zero R β e (renamed_cramerRelation_mem R ι η β _ t)
  have hx (s : ι → η) : E (X s) = pivotCoordinate R β e s := by
    simp [E, pivotCoordinate]
  let M : Matrix ι ι (MvPolynomial (ι → η) R) :=
    fun i j ↦ X (Function.update (e ∘ Sum.inl) i (t j))
  have hd := E.map_det M
  change E (M.det - X (e ∘ Sum.inl) ^ (Fintype.card ι - 1) * X t) = 0 at hz
  rw [map_sub, map_mul, map_pow, hd] at hz
  have hm : E.mapMatrix M =
      (fun i j ↦ pivotCoordinate R β e (Function.update (e ∘ Sum.inl) i (t j))) := by
    ext i j
    exact hx _
  rw [hm, hx, hx, pivotCoordinate_pivot, one_pow, one_mul] at hz
  exact sub_eq_zero.mp hz

/-- Every original projective coordinate ratio equals the actual minor of the same matrix.
This is an equality in the whole coordinate ring, including all nilpotent structure. -/
theorem pivotCoordinate_eq_minor (t : ι → η) :
    pivotCoordinate R β e t = columnMinor (splitNormalizedMatrix e (pivotMatrix R β e)) t := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    have ht : t = e ∘ Sum.inl := Subsingleton.elim _ _
    rw [ht, pivotCoordinate_pivot, columnMinor_splitNormalized_pivot]
  | inr h =>
    rw [← pivotCoordinate_cramer R β e t]
    apply congrArg Matrix.det
    ext i j
    exact pivotCoordinate_replacement R β e i (t j)

end Hironaka.Algebra.PluckerQuot
