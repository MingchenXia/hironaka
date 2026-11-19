import Hironaka.Resolution.HironakaActualInheritedNestedContactFlag

/-! Fixed selector provenance contains only structural monomial data.
Contact and the actual Jacobian are defined from actual analytic members;
nonzero determinant is produced from their genuine monic/lower coefficients.
Fresh initial choice is used only to construct the initial selector. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFixedInheritedSelector
noncomputable section

open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
  HironakaActualRelativeNormalJetDivision HironakaActualCanonicalBlockJacobian
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualRelativeStandardnessBlockSupport
  HironakaActualAnalyticBlockGraphTranslation HironakaActualCauchyCoefficientLimits

variable {n : ℕ}

def fixedSelectorEssential (V : Finset (Fin n →₀ ℕ)) : Set (Fin n) :=
  {j | ∃ a : V, a.val j ≠ 0}

def fixedSelectorBlock (V : Finset (Fin n →₀ ℕ)) (k : ℕ) : Set (Fin n) :=
  {j | ∃ a : V, normalExponentDegree a.val ≤ k ∧ a.val j ≠ 0}

/-- No contact, Jacobian, rank, basis, HS or target-order field is assumed. -/
structure ActualFixedInheritedSelector (V : Finset (Fin n →₀ ℕ)) where
  selected : fixedSelectorEssential V → V
  positive : ∀ j, (selected j).val j.val ≠ 0
  least_degree : ∀ j (a : V), a.val j.val ≠ 0 →
    normalExponentDegree (selected j).val ≤ normalExponentDegree a.val

variable {V : Finset (Fin n →₀ ℕ)}

def fixedSelectorBeta (S : ActualFixedInheritedSelector V) (j : fixedSelectorEssential V) : Fin n →₀ ℕ :=
  (S.selected j).val - Finsupp.single j.val 1

def fixedSelectorBlockEssential (k : ℕ) (j : fixedSelectorBlock V k) : fixedSelectorEssential V :=
  ⟨j.val, by obtain ⟨a, _, ha⟩ := j.property; exact ⟨a, ha⟩⟩

theorem fixedSelector_beta_add_single (S : ActualFixedInheritedSelector V) (j : fixedSelectorEssential V) :
    fixedSelectorBeta S j + Finsupp.single j.val 1 = (S.selected j).val := by
  apply tsub_add_cancel_of_le
  intro i
  by_cases hi : i = j.val
  · subst i
    simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr (S.positive j)
  · simp [Finsupp.single_eq_of_ne hi]

theorem fixedSelector_beta_degree (S : ActualFixedInheritedSelector V) (j : fixedSelectorEssential V) :
    normalExponentDegree (fixedSelectorBeta S j) + 1 = normalExponentDegree (S.selected j).val := by
  have h := congrArg normalExponentDegree (fixedSelector_beta_add_single S j)
  simpa [normalExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib] using h

theorem fixedSelector_selected_degree_le (S : ActualFixedInheritedSelector V)
    (k : ℕ) (j : fixedSelectorBlock V k) :
    normalExponentDegree (S.selected (fixedSelectorBlockEssential k j)).val ≤ k := by
  obtain ⟨a, ha, haj⟩ := j.property
  exact (S.least_degree (fixedSelectorBlockEssential k j) a haj).trans ha

theorem fixedSelector_beta_support (S : ActualFixedInheritedSelector V)
    (k : ℕ) (j : fixedSelectorBlock V k) (i : Fin n) (hi : i ∉ fixedSelectorBlock V k) :
    fixedSelectorBeta S (fixedSelectorBlockEssential k j) i = 0 := by
  have hz : (S.selected (fixedSelectorBlockEssential k j)).val i = 0 := by
    by_contra h
    exact hi ⟨S.selected (fixedSelectorBlockEssential k j), fixedSelector_selected_degree_le S k j, h⟩
  simp only [fixedSelectorBeta, Finsupp.tsub_apply, hz, zero_tsub]

/-- The accepted actual initial choice is made once, not after coordinate actions. -/
def actualInitialFixedInheritedSelector (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K) where
  selected := actualCanonicalDerivativeVertex MonomialOrder.degLex K
  positive j := (actualCanonicalDerivativeVertex_spec MonomialOrder.degLex K j).1
  least_degree j a ha := (actualCanonicalDerivativeVertex_spec MonomialOrder.degLex K j).2 a ha

/-- Genuine analytic higher derivative of the SAME selected actual numerator. -/
def actualFixedSelectorDerivative (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n)) (j : fixedSelectorEssential V) : HolGerm (ComplexModel n) :=
  actualAnalyticMultiDerivative (fixedSelectorBeta S j) (G (S.selected j))

def actualFixedSelectorContactAt (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n)) (k : ℕ) : Prop :=
  ∀ j : fixedSelectorBlock V k,
    actualFixedSelectorDerivative S G (fixedSelectorBlockEssential k j) ∈
      actualAnalyticCoordinateBlockIdeal (fixedSelectorBlock V k)

def actualFixedSelectorJacobian (S : ActualFixedInheritedSelector V)
    (G : V → HolGerm (ComplexModel n)) (k : ℕ) :
    Matrix (fixedSelectorBlock V k) (fixedSelectorBlock V k) ℂ :=
  fun j i => HolGerm.eval (actualAnalyticCoordinateDerivative i.val
    (actualFixedSelectorDerivative S G (fixedSelectorBlockEssential k j)))

theorem actualFixedSelectorDerivative_jacobian_coefficient
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n))
    (j : fixedSelectorEssential V) (i : Fin n) :
    HolGerm.eval (actualAnalyticCoordinateDerivative i (actualFixedSelectorDerivative S G j)) =
      MvPowerSeries.coeff (fixedSelectorBeta S j + Finsupp.single i 1)
        (actualUnshiftedTaylorAlgHom n (G (S.selected j))) *
      actualExponentFactorial (fixedSelectorBeta S j + Finsupp.single i 1) := by
  rw [← actualTaylor_coeff_zero, actualTaylor_actualAnalyticCoordinateDerivative,
    actualFixedSelectorDerivative, actualTaylor_actualAnalyticMultiDerivative]
  exact constantCoeff_pderiv_actualFormalMultiDerivative _ _ _

theorem actualFixedSelectorJacobian_diagonal
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n))
    (hmonic : ∀ a, MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G a)) = 1)
    (j : fixedSelectorEssential V) :
    HolGerm.eval (actualAnalyticCoordinateDerivative j.val (actualFixedSelectorDerivative S G j)) =
      actualExponentFactorial (S.selected j).val := by
  rw [actualFixedSelectorDerivative_jacobian_coefficient, fixedSelector_beta_add_single, hmonic, one_mul]

theorem actualFixedSelectorJacobian_lower
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n))
    (hlower : ∀ a β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a.val →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (G a)) = 0)
    (j : fixedSelectorEssential V) (i : Fin n)
    (hi : MonomialOrder.degLex.toSyn (Finsupp.single i 1) <
      MonomialOrder.degLex.toSyn (Finsupp.single j.val 1)) :
    HolGerm.eval (actualAnalyticCoordinateDerivative i (actualFixedSelectorDerivative S G j)) = 0 := by
  rw [actualFixedSelectorDerivative_jacobian_coefficient]
  have hlt : MonomialOrder.degLex.toSyn (fixedSelectorBeta S j + Finsupp.single i 1) <
      MonomialOrder.degLex.toSyn (S.selected j).val := by
    rw [← fixedSelector_beta_add_single S j, map_add, map_add]
    simpa only [add_comm] using add_lt_add_left hi (MonomialOrder.degLex.toSyn (fixedSelectorBeta S j))
  rw [hlower _ _ hlt, zero_mul]

/-- True triangular determinant, with no Jacobian certificate input. -/
theorem actualFixedSelectorJacobian_det
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n))
    (hmonic : ∀ a, MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G a)) = 1)
    (hlower : ∀ a β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a.val →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (G a)) = 0) (k : ℕ) :
    (actualFixedSelectorJacobian S G k).det =
      ∏ j : fixedSelectorBlock V k, actualExponentFactorial (S.selected (fixedSelectorBlockEssential k j)).val := by
  let m : MonomialOrder (Fin n) := MonomialOrder.degLex
  have hinj : Function.Injective (fun j : fixedSelectorBlock V k => m.toSyn (Finsupp.single j.val 1)) := by
    intro i j hij
    apply Subtype.ext
    exact Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0) (m.toSyn.injective hij)
  let ord : LinearOrder (fixedSelectorBlock V k) :=
    LinearOrder.lift' (fun j => m.toSyn (Finsupp.single j.val 1)) hinj
  let : LinearOrder (fixedSelectorBlock V k) := ord
  have htri : @Matrix.IsUpperTriangular (fixedSelectorBlock V k) ℂ inferInstance ord.toLT
      (actualFixedSelectorJacobian S G k) := by
    intro j i hij
    change m.toSyn (Finsupp.single i.val 1) < m.toSyn (Finsupp.single j.val 1) at hij
    exact actualFixedSelectorJacobian_lower S G hlower (fixedSelectorBlockEssential k j) i.val hij
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_congr rfl
  intro j _
  exact actualFixedSelectorJacobian_diagonal S G hmonic (fixedSelectorBlockEssential k j)

theorem actualFixedSelectorJacobian_det_ne_zero
    (S : ActualFixedInheritedSelector V) (G : V → HolGerm (ComplexModel n))
    (hmonic : ∀ a, MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G a)) = 1)
    (hlower : ∀ a β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a.val →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (G a)) = 0) (k : ℕ) :
    (actualFixedSelectorJacobian S G k).det ≠ 0 := by
  rw [actualFixedSelectorJacobian_det S G hmonic hlower]
  exact Finset.prod_ne_zero_iff.mpr (fun j _ => actualExponentFactorial_ne_zero _)

/-- Exact old-selector specialization; no fresh choice is used by transport. -/
theorem actualInitialFixedInheritedSelector_derivative
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (G : ActualAnalyticInheritedFamily n 0 K)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K) :
    actualFixedSelectorDerivative (actualInitialFixedInheritedSelector K) G.germs j =
      actualInheritedEssentialDerivative G j := rfl

theorem actualInitialFixedInheritedSelector_contact
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (G : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) :
    actualFixedSelectorContactAt (actualInitialFixedInheritedSelector K) G.germs k ↔
      HironakaActualInheritedNestedContactFlag.ActualInheritedContactAt G k := Iff.rfl

end
end Hironaka.HironakaActualFixedInheritedSelector
