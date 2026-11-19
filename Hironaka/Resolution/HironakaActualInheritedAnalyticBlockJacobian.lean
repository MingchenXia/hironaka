import Hironaka.Resolution.HironakaActualCanonicalBlockJacobian
import Hironaka.Resolution.HironakaActualRelativeNormalJetDivision
import Hironaka.Resolution.HironakaActualOriginalTaylorDerivatives
import Mathlib.Data.Finsupp.Multiset

/-! Genuine analytic derivatives and internally nonzero selected block
Jacobians for the CURRENT inherited analytic monic family. No supplied
Jacobian, rank, analytic lift or contact flag is an input. This is the
analytic and inherited-family foundation for the initial nested flag;
it does not construct that flag itself. -/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualInheritedAnalyticBlockJacobian

noncomputable section

open HolGerm HironakaRelativeNormalIdeal
  HironakaRelativeNormalTaylorCoefficients HironakaActualCoefficientPresentationCentrePower
  HironakaActualOriginalFormalTaylor HironakaActualOriginalTaylorDerivatives
  HironakaActualFormalInitialDiagram HironakaActualCanonicalBlockJacobian
  HironakaActualRelativeNormalJetDivision HironakaActualCauchyCoefficientLimits
  HironakaActualRelativeStandardnessBlockSupport HolomorphicTaylorTail

variable {n : ℕ}

/-- The actual analytic first coordinate derivative on the whole germ ring. -/
def actualAnalyticCoordinateDerivative (i : Fin n) :
    HolGerm (ComplexModel n) →ₗ[ℂ] HolGerm (ComplexModel n) :=
  iteratedDerivativeGerm [EuclideanSpace.single i 1]

/-- The original genuine coordinate-derivative theorem survives the literal
dimension reassociation used by the actual unshifted Taylor map. -/
theorem actualTaylor_actualAnalyticCoordinateDerivative (i : Fin n)
    (F : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n (actualAnalyticCoordinateDerivative i F) =
      MvPowerSeries.pderiv ℂ i (actualUnshiftedTaylorAlgHom n F) := by
  have transport (s : ℕ) (e : s = n)
      (f : HolGerm (ComplexModel s) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
      (hf : ∀ g : HolGerm (ComplexModel s),
        f (iteratedDerivativeGerm [EuclideanSpace.single (Fin.cast e.symm i) 1] g) =
          MvPowerSeries.pderiv ℂ i (f g)) :
      (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) e) f) (actualAnalyticCoordinateDerivative i F) =
        MvPowerSeries.pderiv ℂ i
          ((cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
            MvPowerSeries (Fin n) ℂ) e) f) F) := by
    subst s
    exact hf F
  change (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
    MvPowerSeries (Fin n) ℂ) (Nat.zero_add n)) (originalTaylorAlgHom n))
      (actualAnalyticCoordinateDerivative i F) = _
  apply transport (0+n) (Nat.zero_add n) (originalTaylorAlgHom n)
  intro g
  have hi : Fin.cast (Nat.zero_add n).symm i = i.natAdd 0 := by
    apply Fin.ext
    simp
  rw [hi]
  exact originalTaylorAlgHom_coordinate_derivative n i g

/-- The true exponent counted by a finite coordinate derivative word. -/
def actualCoordinateWordExponent (L : List (Fin n)) : Fin n →₀ ℕ :=
  (L : Multiset (Fin n)).toFinsupp

theorem actualCoordinateWordExponent_nil :
    actualCoordinateWordExponent ([] : List (Fin n)) = 0 := by
  simp [actualCoordinateWordExponent]

theorem actualCoordinateWordExponent_cons (i : Fin n) (L : List (Fin n)) :
    actualCoordinateWordExponent (i :: L) =
      actualCoordinateWordExponent L + Finsupp.single i 1 := by
  ext j
  by_cases hij : i = j
  · subst j
    simp [actualCoordinateWordExponent, Multiset.toFinsupp_apply]
  · simp [actualCoordinateWordExponent, Multiset.toFinsupp_apply,
      List.count_cons_of_ne hij,
      Finsupp.single_eq_of_ne (show j ≠ i from fun hji => hij hji.symm)]

/-- A finite actual coordinate word carrying exactly the given exponent. -/
def actualCoordinateDerivativeWord (β : Fin n →₀ ℕ) : List (Fin n) :=
  β.toMultiset.toList

theorem actualCoordinateDerivativeWord_exponent (β : Fin n →₀ ℕ) :
    actualCoordinateWordExponent (actualCoordinateDerivativeWord β) = β := by
  simp [actualCoordinateWordExponent, actualCoordinateDerivativeWord]

/-- Iteration of the genuine analytic coordinate derivative along a finite word. -/
def actualAnalyticWordDerivative (L : List (Fin n)) :
    HolGerm (ComplexModel n) →ₗ[ℂ] HolGerm (ComplexModel n) :=
  iteratedDerivativeGerm (L.map (fun i => EuclideanSpace.single i 1))

theorem actualAnalyticWordDerivative_cons (i : Fin n) (L : List (Fin n))
    (F : HolGerm (ComplexModel n)) :
    actualAnalyticWordDerivative (i :: L) F =
      actualAnalyticCoordinateDerivative i (actualAnalyticWordDerivative L F) := by
  induction F using HolGerm.induction_on with
  | h f hf => rfl

theorem actualTaylor_actualAnalyticWordDerivative (L : List (Fin n))
    (F : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n (actualAnalyticWordDerivative L F) =
      actualFormalMultiDerivative (actualCoordinateWordExponent L)
        (actualUnshiftedTaylorAlgHom n F) := by
  induction L with
  | nil =>
      rw [actualCoordinateWordExponent_nil, actualFormalMultiDerivative_zero]
      induction F using HolGerm.induction_on with
      | h f hf => rfl
  | cons i L ih =>
      rw [actualAnalyticWordDerivative_cons, actualTaylor_actualAnalyticCoordinateDerivative,
        ih, actualCoordinateWordExponent_cons, actualFormalMultiDerivative_add_single]

/-- A genuine actual analytic multi-derivative, with its finite word constructed internally. -/
def actualAnalyticMultiDerivative (β : Fin n →₀ ℕ) :
    HolGerm (ComplexModel n) →ₗ[ℂ] HolGerm (ComplexModel n) :=
  actualAnalyticWordDerivative (actualCoordinateDerivativeWord β)

/-- Literal whole Taylor naturality for the genuine analytic multi-derivative. -/
theorem actualTaylor_actualAnalyticMultiDerivative (β : Fin n →₀ ℕ)
    (F : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n (actualAnalyticMultiDerivative β F) =
      actualFormalMultiDerivative β (actualUnshiftedTaylorAlgHom n F) := by
  rw [actualAnalyticMultiDerivative, actualTaylor_actualAnalyticWordDerivative,
    actualCoordinateDerivativeWord_exponent]

variable {K : Ideal (MvPowerSeries (Fin n) ℂ)}

/-- The SAME fixed original vertex choice is used for every current family
and every cutoff. This is an actual analytic derivative germ. -/
def actualInheritedEssentialDerivative (G : ActualAnalyticInheritedFamily n 0 K)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K) : HolGerm (ComplexModel n) :=
  actualAnalyticMultiDerivative (actualCanonicalDerivativeExponent MonomialOrder.degLex K j)
    (G.germs (actualCanonicalDerivativeVertex MonomialOrder.degLex K j))

theorem actualTaylor_actualInheritedEssentialDerivative (G : ActualAnalyticInheritedFamily n 0 K)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K) :
    actualUnshiftedTaylorAlgHom n (actualInheritedEssentialDerivative G j) =
      actualFormalMultiDerivative (actualCanonicalDerivativeExponent MonomialOrder.degLex K j)
        (actualUnshiftedTaylorAlgHom n
          (G.germs (actualCanonicalDerivativeVertex MonomialOrder.degLex K j))) :=
  actualTaylor_actualAnalyticMultiDerivative _ _

theorem actualInheritedEssentialDerivative_eval_zero (G : ActualAnalyticInheritedFamily n 0 K)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K) :
    HolGerm.eval (actualInheritedEssentialDerivative G j) = 0 := by
  rw [← actualTaylor_coeff_zero, actualTaylor_actualInheritedEssentialDerivative]
  change MvPowerSeries.constantCoeff
    (actualFormalMultiDerivative (actualCanonicalDerivativeExponent MonomialOrder.degLex K j)
      (actualUnshiftedTaylorAlgHom n
        (G.germs (actualCanonicalDerivativeVertex MonomialOrder.degLex K j)))) = 0
  rw [constantCoeff_actualFormalMultiDerivative]
  have hle : actualCanonicalDerivativeExponent MonomialOrder.degLex K j ≤
      (actualCanonicalDerivativeVertex MonomialOrder.degLex K j).val := tsub_le_self
  have hne : actualCanonicalDerivativeExponent MonomialOrder.degLex K j ≠
      (actualCanonicalDerivativeVertex MonomialOrder.degLex K j).val := by
    intro he
    have h := actualCanonicalDerivativeExponent_add_single MonomialOrder.degLex K j
    rw [he] at h
    have hz : Finsupp.single j.val 1 = 0 := add_eq_left.mp h
    have hc := congrArg (fun α : Fin n →₀ ℕ => α j.val) hz
    simp at hc
  have hc := G.lower (actualCanonicalDerivativeVertex MonomialOrder.degLex K j)
    (actualCanonicalDerivativeExponent MonomialOrder.degLex K j)
    (MonomialOrder.degLex.toSyn_strictMono (lt_of_le_of_ne hle hne))
  change MvPowerSeries.coeff (actualCanonicalDerivativeExponent MonomialOrder.degLex K j)
    (actualUnshiftedTaylorAlgHom n
      (G.germs (actualCanonicalDerivativeVertex MonomialOrder.degLex K j))) = 0 at hc
  rw [hc, zero_mul]

/-- Every entry of the actual analytic Jacobian is an original whole Taylor coefficient. -/
theorem actualInheritedEssentialDerivative_jacobian_coefficient
    (G : ActualAnalyticInheritedFamily n 0 K)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K) (i : Fin n) :
    HolGerm.eval (actualAnalyticCoordinateDerivative i (actualInheritedEssentialDerivative G j)) =
      MvPowerSeries.coeff
        (actualCanonicalDerivativeExponent MonomialOrder.degLex K j + Finsupp.single i 1)
        (actualUnshiftedTaylorAlgHom n
          (G.germs (actualCanonicalDerivativeVertex MonomialOrder.degLex K j))) *
      actualExponentFactorial
        (actualCanonicalDerivativeExponent MonomialOrder.degLex K j + Finsupp.single i 1) := by
  rw [← actualTaylor_coeff_zero, actualTaylor_actualAnalyticCoordinateDerivative,
    actualTaylor_actualInheritedEssentialDerivative]
  exact constantCoeff_pderiv_actualFormalMultiDerivative _ _ _

theorem actualInheritedEssentialDerivative_jacobian_diagonal
    (G : ActualAnalyticInheritedFamily n 0 K)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K) :
    HolGerm.eval (actualAnalyticCoordinateDerivative j.val (actualInheritedEssentialDerivative G j)) =
      actualExponentFactorial (actualCanonicalDerivativeVertex MonomialOrder.degLex K j).val := by
  rw [actualInheritedEssentialDerivative_jacobian_coefficient,
    actualCanonicalDerivativeExponent_add_single]
  have hc := G.monic (actualCanonicalDerivativeVertex MonomialOrder.degLex K j)
  change MvPowerSeries.coeff (actualCanonicalDerivativeVertex MonomialOrder.degLex K j).val
    (actualUnshiftedTaylorAlgHom n
      (G.germs (actualCanonicalDerivativeVertex MonomialOrder.degLex K j))) = 1 at hc
  rw [hc, one_mul]

theorem actualInheritedEssentialDerivative_jacobian_lower_coordinate
    (G : ActualAnalyticInheritedFamily n 0 K)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K) (i : Fin n)
    (hi : MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
      MonomialOrder.degLex.toSyn (Finsupp.single j.val 1)) :
    HolGerm.eval (actualAnalyticCoordinateDerivative i (actualInheritedEssentialDerivative G j)) = 0 := by
  rw [actualInheritedEssentialDerivative_jacobian_coefficient]
  have hlt : MonomialOrder.degLex.toSyn
      (actualCanonicalDerivativeExponent MonomialOrder.degLex K j + Finsupp.single i 1) <
      MonomialOrder.degLex.toSyn (actualCanonicalDerivativeVertex MonomialOrder.degLex K j).val := by
    rw [← actualCanonicalDerivativeExponent_add_single MonomialOrder.degLex K j, map_add, map_add]
    simpa only [add_comm] using add_lt_add_left hi
      (MonomialOrder.degLex.toSyn (actualCanonicalDerivativeExponent MonomialOrder.degLex K j))
  have hc := G.lower (actualCanonicalDerivativeVertex MonomialOrder.degLex K j) _ hlt
  change MvPowerSeries.coeff
    (actualCanonicalDerivativeExponent MonomialOrder.degLex K j + Finsupp.single i 1)
    (actualUnshiftedTaylorAlgHom n
      (G.germs (actualCanonicalDerivativeVertex MonomialOrder.degLex K j))) = 0 at hc
  rw [hc, zero_mul]

/-- The literal Jacobian of the genuine current analytic derivative germs. -/
def actualInheritedBlockJacobian (G : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) :
    Matrix (actualDegreePrefixVariables MonomialOrder.degLex K k)
      (actualDegreePrefixVariables MonomialOrder.degLex K k) ℂ :=
  fun j i => HolGerm.eval (actualAnalyticCoordinateDerivative i.val
    (actualInheritedEssentialDerivative G
      (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k j)))

theorem actualInheritedBlockJacobian_det (G : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) :
    (actualInheritedBlockJacobian G k).det =
      ∏ j : actualDegreePrefixVariables MonomialOrder.degLex K k,
        actualExponentFactorial (actualCanonicalDerivativeVertex MonomialOrder.degLex K
          (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k j)).val := by
  let m : MonomialOrder (Fin n) := MonomialOrder.degLex
  have hinj : Function.Injective (fun j : actualDegreePrefixVariables m K k =>
      m.toSyn (Finsupp.single j.val 1)) := by
    intro i j hij
    apply Subtype.ext
    exact Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) (m.toSyn.injective hij)
  let ord : LinearOrder (actualDegreePrefixVariables m K k) :=
    LinearOrder.lift' (fun j => m.toSyn (Finsupp.single j.val 1)) hinj
  let : LinearOrder (actualDegreePrefixVariables m K k) := ord
  have htri : @Matrix.IsUpperTriangular (actualDegreePrefixVariables m K k) ℂ
      inferInstance ord.toLT (actualInheritedBlockJacobian G k) := by
    intro j i hij
    change m.toSyn (Finsupp.single i.val 1) < m.toSyn (Finsupp.single j.val 1) at hij
    exact actualInheritedEssentialDerivative_jacobian_lower_coordinate G
      (actualCanonicalBlockEssentialVariable m K k j) i.val hij
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_congr rfl
  intro j _
  exact actualInheritedEssentialDerivative_jacobian_diagonal G
    (actualCanonicalBlockEssentialVariable m K k j)

/-- Only the current concrete analytic monic family and its cutoff are inputs;
the determinant, its triangularity and its nonvanishing are produced internally. -/
theorem actualInheritedBlockJacobian_det_ne_zero
    (G : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) :
    (actualInheritedBlockJacobian G k).det ≠ 0 := by
  rw [actualInheritedBlockJacobian_det]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => actualExponentFactorial_ne_zero _)

end

end Hironaka.HironakaActualInheritedAnalyticBlockJacobian
