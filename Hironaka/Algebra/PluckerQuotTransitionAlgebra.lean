import Hironaka.Algebra.PluckerQuotTransitionCoordinates

/-!
# Actual two-sided inverse maps of whole original pivot coordinate algebras

Both maps below preserve the original coefficients. The inverse factors
through the whole dehomogenized ideal because every original homogeneous
relation vanishes on the same normalized universal matrix.
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

/-- The same original normalized matrix with the original polynomial variables as entries. -/
def pivotUniversalMatrix : Matrix ι η (MvPolynomial (ι × κ) R) :=
  splitNormalizedMatrix e (fun i j ↦ X (i, j))

/-- The actual whole affine polynomial algebra maps to the original projective ratio ring. -/
def polynomialToPivot : MvPolynomial (ι × κ) R →ₐ[R] PivotCoordinateRing R β e :=
  MvPolynomial.aeval fun ij ↦ pivotMatrix R β e ij.1 ij.2

/-- The original affine projective coordinates map to the same actual universal matrix minors. -/
def minorBack : CoordinateRing R (pivotIndex β e) →ₐ[R] MvPolynomial (ι × κ) R :=
  MvPolynomial.aeval fun j ↦ columnMinor (pivotUniversalMatrix R e) (β j.1)

/-- The actual inverse candidate preserves original dehomogenization, coefficient by coefficient. -/
theorem minorBack_comp_dehom :
    (minorBack R β e).comp (coordinateDehom (pivotIndex β e)) =
      MvPolynomial.aeval (R := R) (fun j ↦ columnMinor (pivotUniversalMatrix R e) (β j)) := by
  ext j : 1
  by_cases hj : j = pivotIndex β e
  · subst j
    simp [minorBack, coordinateDehom, pivotIndex, pivotUniversalMatrix,
      columnMinor_splitNormalized_pivot]
  · simp [minorBack, coordinateDehom, coordinateDehomCoord, hj]

/-- The whole original dehomogenized ideal lies in the actual inverse map's kernel. -/
theorem pivotDehomIdeal_le_ker_minorBack :
    pivotDehomIdeal R β e ≤ RingHom.ker (minorBack R β e).toRingHom := by
  rw [pivotDehomIdeal, Ideal.map_le_iff_le_comap]
  intro F hF
  change minorBack R β e (coordinateDehom (pivotIndex β e) F) = 0
  rw [← AlgHom.comp_apply, minorBack_comp_dehom]
  exact minorRelationIdeal_aeval_eq_zero R ι η (Fin (n + 1)) β
    (pivotUniversalMatrix R e) hF

/-- The actual inverse algebra map on the entire original whole-ideal quotient. -/
def pivotToPolynomial : PivotCoordinateRing R β e →ₐ[R] MvPolynomial (ι × κ) R :=
  Ideal.Quotient.liftₐ (pivotDehomIdeal R β e) (minorBack R β e)
    (fun _ hF ↦ pivotDehomIdeal_le_ker_minorBack R β e hF)

/-- The actual inverse agrees with original minor evaluation on every homogeneous polynomial. -/
theorem pivotToPolynomial_comp_dehom :
    (pivotToPolynomial R β e).comp (pivotDehom R β e) =
      MvPolynomial.aeval (R := R) (fun j ↦ columnMinor (pivotUniversalMatrix R e) (β j)) := by
  rw [pivotDehom, ← AlgHom.comp_assoc]
  rw [pivotToPolynomial, Ideal.Quotient.liftₐ_comp, minorBack_comp_dehom]

/-- Every original ratio is sent to its actual minor of the original universal matrix. -/
theorem pivotToPolynomial_coordinate (t : ι → η) :
    pivotToPolynomial R β e (pivotCoordinate R β e t) =
      columnMinor (pivotUniversalMatrix R e) t := by
  have h := AlgHom.congr_fun (pivotToPolynomial_comp_dehom R β e) (X (β.symm t))
  simpa [pivotCoordinate] using h

/-- The composite on the original polynomial ring is the identity on the whole ring. -/
theorem pivotToPolynomial_comp_polynomialToPivot :
    (pivotToPolynomial R β e).comp (polynomialToPivot R β e) =
      AlgHom.id R (MvPolynomial (ι × κ) R) := by
  ext ij : 1
  simp only [AlgHom.comp_apply, polynomialToPivot, MvPolynomial.aeval_X, AlgHom.id_apply]
  exact (pivotToPolynomial_coordinate R β e _).trans
    (columnMinor_splitNormalized_replacement e (fun i j ↦ (X (i, j) :
      MvPolynomial (ι × κ) R)) ij.1 ij.2)

/-- Original substitution carries the entire normalized universal matrix to the extracted matrix. -/
theorem polynomialToPivot_mapMatrix :
    (pivotUniversalMatrix R e).map (polynomialToPivot R β e) =
      splitNormalizedMatrix e (pivotMatrix R β e) := by
  ext i k
  obtain ⟨k, rfl⟩ := e.surjective k
  cases k with
  | inl k =>
    simp [pivotUniversalMatrix, Matrix.one_apply]
  | inr j =>
    simp [pivotUniversalMatrix, polynomialToPivot]

/-- Original substitution preserves every actual selected minor, on the whole rings. -/
theorem polynomialToPivot_minor (t : ι → η) :
    polynomialToPivot R β e (columnMinor (pivotUniversalMatrix R e) t) =
      columnMinor (splitNormalizedMatrix e (pivotMatrix R β e)) t := by
  have hm : (polynomialToPivot R β e).mapMatrix
      (selectedMatrix (pivotUniversalMatrix R e) t) =
      selectedMatrix (splitNormalizedMatrix e (pivotMatrix R β e)) t := by
    ext i j
    exact congrFun (congrFun (polynomialToPivot_mapMatrix R β e) i) (t j)
  exact ((polynomialToPivot R β e).map_det _).trans (congrArg Matrix.det hm)

/-- The composite on the literal original quotient ring is the identity on its whole ring. -/
theorem polynomialToPivot_comp_pivotToPolynomial :
    (polynomialToPivot R β e).comp (pivotToPolynomial R β e) =
      AlgHom.id R (PivotCoordinateRing R β e) := by
  apply Ideal.Quotient.algHom_ext
  ext j : 1
  have hc : (Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e)) (X j) =
      pivotCoordinate R β e (β j.1) := by
    unfold pivotCoordinate pivotDehom
    rw [β.symm_apply_apply]
    change (Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e)) (X j) =
      (Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e))
        (coordinateDehom (pivotIndex β e) (X j.1))
    rw [coordinateDehom, MvPolynomial.aeval_X, coordinateDehomCoord_ne]
  change polynomialToPivot R β e (pivotToPolynomial R β e
    ((Ideal.Quotient.mkₐ R (pivotDehomIdeal R β e)) (X j))) = _
  rw [hc, pivotToPolynomial_coordinate, polynomialToPivot_minor, ← pivotCoordinate_eq_minor]
  exact hc.symm

/-- The original normalized polynomial matrix chart is isomorphic to the entire original
pivot coordinate algebra, preserving the actual original coefficient maps. -/
def pivotCoordinateAlgEquiv : MvPolynomial (ι × κ) R ≃ₐ[R] PivotCoordinateRing R β e :=
  AlgEquiv.ofAlgHom (polynomialToPivot R β e) (pivotToPolynomial R β e)
    (polynomialToPivot_comp_pivotToPolynomial R β e)
    (pivotToPolynomial_comp_polynomialToPivot R β e)

end Hironaka.Algebra.PluckerQuot
