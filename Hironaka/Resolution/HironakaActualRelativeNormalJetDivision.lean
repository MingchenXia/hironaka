import Hironaka.Resolution.HironakaActualAnalyticCanonicalVertices
import Hironaka.Resolution.HironakaActualRelativeTaylorCoefficients
import Hironaka.Resolution.HironakaActualRelativeStandardnessInheritedDivision
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Block

/-! Genuine relative finite normal-jet division from a concrete analytic
inherited monic family. Its original coefficients internally construct a
unit matrix determinant, the whole normal quotient equivalence, and a
unique actual supported polynomial division tuple. No desired relative
basis/rank, Jacobian or convergence certificate is supplied as input. -/
set_option autoImplicit false
open Set Classical
open scoped Matrix

namespace Hironaka.HironakaActualRelativeNormalJetDivision

noncomputable section

open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualTaylorCoordinateNaturality
  HironakaActualRelativeCoefficientGerms HironakaActualRelativeTaylorCoefficients
  HironakaActualCauchyCoefficientLimits HironakaActualFormalInitialDiagram
  HironakaActualSelectedVertexHomogeneousBasis HironakaActualRelativeStandardnessInheritedDivision
  HironakaActualAnalyticCanonicalVertices

/-- Evaluation of the actual whole normal quotient coordinate is the literal
coefficient of the original entire Taylor series. -/
theorem eval_actualNormalJetCoordinates (d t q : ℕ)
    (F : HolGerm (ComplexModel (d+t))) (γ : normalExponentIndex t q) :
    HolGerm.eval (actualNormalJetCoordinates d t q F γ) =
      MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val)
        (actualUnshiftedTaylorAlgHom (d+t) F) := by
  have hγ : actualNormalJetCoordinates d t q F γ =
      actualNormalAnalyticCoefficientGerm d t F γ.val := by
    rw [← actualNormalTaylorPolynomial_coefficient,
      actualNormalTaylorPolynomial_coefficient_eq_germ d t q F γ.val γ.property]
  rw [hγ, ← actualTaylor_coeff_zero]
  have h := congrArg (MvPowerSeries.coeff 0)
    (actualFormalNormalCoefficient_actualTaylor d t F γ.val)
  exact h.symm

/-- Concrete analytic germs with genuine initial coefficients. There is no
relative basis, rank, Jacobian, or formal-to-analytic lift certificate here. -/
structure ActualAnalyticInheritedFamily (d t : ℕ)
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)) where
  germs : actualInitialVertices MonomialOrder.degLex K → HolGerm (ComplexModel (d+t))
  monic : ∀ a, MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom (d+t) (germs a)) = 1
  lower : ∀ a b, MonomialOrder.degLex.toSyn b < MonomialOrder.degLex.toSyn a.val →
    MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom (d+t) (germs a)) = 0

variable {d t : ℕ} {K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)}

def ActualAnalyticInheritedFamily.formal (G : ActualAnalyticInheritedFamily d t K) :
    InheritedMonicFamily MonomialOrder.degLex K :=
  ⟨fun a => actualUnshiftedTaylorAlgHom (d+t) (G.germs a), G.monic, G.lower⟩

def actualNormalHeadPrefix (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)) (k : ℕ) :
    Set (actualInitialVertices MonomialOrder.degLex K) :=
  {a | normalExponentDegree a.val ≤ k ∧ ∀ i : Fin d, a.val (i.castAdd t) = 0}

private theorem joined_normal_head (k : ℕ)
    (a : actualInitialVertices MonomialOrder.degLex K) (ha : a ∈ actualNormalHeadPrefix K k) :
    actualJoinedExponent (0 : Fin d →₀ ℕ) (actualNormalExponent a.val) = a.val := by
  have ht : actualTangentExponent a.val = 0 := by
    ext i
    exact ha.2 i
  simpa only [ht] using actualJoinedExponent_split a.val

private theorem joined_zero_injective :
    Function.Injective (actualJoinedExponent (0 : Fin d →₀ ℕ) :
      (Fin t →₀ ℕ) → (Fin (d+t) →₀ ℕ)) := by
  intro α β h
  ext j
  have he := congrArg (fun γ : Fin (d+t) →₀ ℕ => γ (j.natAdd d)) h
  simpa [actualJoinedExponent] using he

/-- Actual normal-monomial multiples of the same whole analytic members. -/
def actualNormalSelectedColumn (G : ActualAnalyticInheritedFamily d t K)
    (k : ℕ) (α : Fin t →₀ ℕ) : HolGerm (ComplexModel (d+t)) :=
  if h : actualJoinedExponent (0 : Fin d →₀ ℕ) α ∈
      actualSelectedVertexDiagram K (actualNormalHeadPrefix K k) then
    let a := actualSelectedVertexOwner K (actualNormalHeadPrefix K k)
      (actualJoinedExponent (0 : Fin d →₀ ℕ) α) h
    normalExponentMonomial d t (α - actualNormalExponent a.val) * G.germs a
  else normalExponentMonomial d t α

private theorem actualNormalSelectedColumn_spec (G : ActualAnalyticInheritedFamily d t K)
    (k : ℕ) (α : Fin t →₀ ℕ) :
    ∃ hne : actualUnshiftedTaylorAlgHom (d+t) (actualNormalSelectedColumn G k α) ≠ 0,
      actualInitialExponent MonomialOrder.degLex
        (actualUnshiftedTaylorAlgHom (d+t) (actualNormalSelectedColumn G k α)) hne =
          actualJoinedExponent (0 : Fin d →₀ ℕ) α ∧
      MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) α)
        (actualUnshiftedTaylorAlgHom (d+t) (actualNormalSelectedColumn G k α)) = 1 := by
  by_cases h : actualJoinedExponent (0 : Fin d →₀ ℕ) α ∈
      actualSelectedVertexDiagram K (actualNormalHeadPrefix K k)
  · rw [actualNormalSelectedColumn, dif_pos h]
    dsimp only
    let a := actualSelectedVertexOwner K (actualNormalHeadPrefix K k)
      (actualJoinedExponent (0 : Fin d →₀ ℕ) α) h
    have ha := actualSelectedVertexOwner_spec K (actualNormalHeadPrefix K k)
      (actualJoinedExponent (0 : Fin d →₀ ℕ) α) h
    have hle : actualNormalExponent a.val ≤ α := by
      intro i
      have hh : a.val (i.natAdd d) ≤
          actualJoinedExponent (0 : Fin d →₀ ℕ) α (i.natAdd d) := ha.2.1 (i.natAdd d)
      simpa [actualNormalExponent, actualJoinedExponent] using hh
    have hsplit : actualJoinedExponent (0 : Fin d →₀ ℕ)
        (α - actualNormalExponent a.val) + a.val =
          actualJoinedExponent (0 : Fin d →₀ ℕ) α := by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have haz : a.val (j.castAdd t) = 0 := ha.1.2 j
        simp [actualJoinedExponent, haz]
      · simpa [actualJoinedExponent, actualNormalExponent, Finsupp.tsub_apply] using
          Nat.sub_add_cancel (hle j)
    have hGa : actualUnshiftedTaylorAlgHom (d+t) (G.germs a) ≠ 0 := by
      intro hz
      have hc := G.monic a
      rw [hz, map_zero] at hc
      exact zero_ne_one hc
    have hmin := actualInitialExponent_eq_of_coefficients MonomialOrder.degLex
      (actualUnshiftedTaylorAlgHom (d+t) (G.germs a)) hGa a.val
      (by rw [G.monic]; exact one_ne_zero) (G.lower a)
    rw [map_mul, actualUnshiftedTaylor_normalExponentMonomial]
    have hm := actualMonomial_ne_zero
      (actualJoinedExponent (0 : Fin d →₀ ℕ) (α - actualNormalExponent a.val))
    refine ⟨mul_ne_zero hm hGa, ?_, ?_⟩
    · rw [actualInitialExponent_mul MonomialOrder.degLex _ _ hm hGa,
        actualInitialExponent_monomial, hmin, hsplit]
    · have hc := coeff_mul_actualInitialExponent MonomialOrder.degLex
        (MvPowerSeries.monomial (actualJoinedExponent (0 : Fin d →₀ ℕ)
          (α - actualNormalExponent a.val)) 1)
        (actualUnshiftedTaylorAlgHom (d+t) (G.germs a)) hm hGa
      rw [actualInitialExponent_monomial, hmin, hsplit,
        MvPowerSeries.coeff_monomial_same, G.monic, one_mul] at hc
      exact hc
  · rw [actualNormalSelectedColumn, dif_neg h, actualUnshiftedTaylor_normalExponentMonomial]
    exact ⟨actualMonomial_ne_zero _, actualInitialExponent_monomial MonomialOrder.degLex _,
      MvPowerSeries.coeff_monomial_same _ 1⟩

private theorem actualNormalSelectedColumn_triangular (G : ActualAnalyticInheritedFamily d t K)
    (k : ℕ) (α : Fin t →₀ ℕ) :
    MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) α)
        (actualUnshiftedTaylorAlgHom (d+t) (actualNormalSelectedColumn G k α)) = 1 ∧
      ∀ β : Fin t →₀ ℕ,
        MonomialOrder.degLex.toSyn (actualJoinedExponent (0 : Fin d →₀ ℕ) β) <
          MonomialOrder.degLex.toSyn (actualJoinedExponent (0 : Fin d →₀ ℕ) α) →
        MvPowerSeries.coeff (actualJoinedExponent (0 : Fin d →₀ ℕ) β)
          (actualUnshiftedTaylorAlgHom (d+t) (actualNormalSelectedColumn G k α)) = 0 := by
  obtain ⟨hne, hmin, hc⟩ := actualNormalSelectedColumn_spec G k α
  refine ⟨hc, fun β hβ => ?_⟩
  apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hne
  rwa [hmin]

/-- The literal whole-base-germ coefficient matrix of the actual analytic columns. -/
def actualNormalSelectedColumnMatrix (G : ActualAnalyticInheritedFamily d t K) (k q : ℕ) :
    let := normalExponentFintype t q
    Matrix (normalExponentIndex t q) (normalExponentIndex t q) (HolGerm (ComplexModel d)) :=
  let := normalExponentFintype t q
  fun γ α => actualNormalJetCoordinates d t q (actualNormalSelectedColumn G k α.val) γ

/-- Every such relative finite matrix has unit determinant, proved without rank/basis inputs. -/
theorem actualNormalSelectedColumnMatrix_det_isUnit (G : ActualAnalyticInheritedFamily d t K)
    (k q : ℕ) :
    let := normalExponentFintype t q
    IsUnit (actualNormalSelectedColumnMatrix G k q).det := by
  let := normalExponentFintype t q
  let M := actualNormalSelectedColumnMatrix G k q
  let E := HolGerm.eval.mapMatrix M
  have hi : Function.Injective (fun α : normalExponentIndex t q =>
      MonomialOrder.degLex.toSyn (actualJoinedExponent (0 : Fin d →₀ ℕ) α.val)) := by
    intro α β h
    exact Subtype.ext (joined_zero_injective (MonomialOrder.degLex.toSyn.injective h))
  let ord : LinearOrder (normalExponentIndex t q) := LinearOrder.lift'
    (fun α => MonomialOrder.degLex.toSyn (actualJoinedExponent (0 : Fin d →₀ ℕ) α.val)) hi
  let : LinearOrder (normalExponentIndex t q) := ord
  have ht : @Matrix.IsLowerTriangular (normalExponentIndex t q) ℂ inferInstance ord.toLT E := by
    intro γ α hαγ
    change MonomialOrder.degLex.toSyn (actualJoinedExponent (0 : Fin d →₀ ℕ) γ.val) <
      MonomialOrder.degLex.toSyn (actualJoinedExponent (0 : Fin d →₀ ℕ) α.val) at hαγ
    change HolGerm.eval (actualNormalJetCoordinates d t q (actualNormalSelectedColumn G k α.val) γ) = 0
    rw [eval_actualNormalJetCoordinates]
    exact (actualNormalSelectedColumn_triangular G k α.val).2 γ.val hαγ
  have hd (α : normalExponentIndex t q) : E α α = 1 := by
    change HolGerm.eval (actualNormalJetCoordinates d t q (actualNormalSelectedColumn G k α.val) α) = 1
    rw [eval_actualNormalJetCoordinates]
    exact (actualNormalSelectedColumn_triangular G k α.val).1
  apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
  have hdet : HolGerm.eval M.det = 1 := by
    rw [RingHom.map_det, Matrix.det_of_isLowerTriangular E ht]
    simp only [hd, Finset.prod_const_one]
  rw [hdet]
  exact one_ne_zero

/-- True inverse of the internally constructed whole-base coefficient matrix. -/
def actualNormalSelectedColumnCoordinateEquiv (G : ActualAnalyticInheritedFamily d t K)
    (k q : ℕ) :
    let := normalExponentFintype t q
    (normalExponentIndex t q → HolGerm (ComplexModel d)) ≃ₗ[HolGerm (ComplexModel d)]
      (normalExponentIndex t q → HolGerm (ComplexModel d)) :=
  let := normalExponentFintype t q
  let M := actualNormalSelectedColumnMatrix G k q
  { __ := M.mulVecLin
    invFun := (M⁻¹).mulVec
    left_inv := by
      intro c
      change M⁻¹ *ᵥ (M *ᵥ c) = c
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M
        (actualNormalSelectedColumnMatrix_det_isUnit G k q), Matrix.one_mulVec]
    right_inv := by
      intro c
      change M *ᵥ (M⁻¹ *ᵥ c) = c
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M
        (actualNormalSelectedColumnMatrix_det_isUnit G k q), Matrix.one_mulVec] }

/-- The actual selected analytic columns give a genuine equivalence onto the
WHOLE original normal-power quotient, not only a quotient of the chosen ideal. -/
def actualNormalSelectedColumnEquiv (G : ActualAnalyticInheritedFamily d t K) (k q : ℕ) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    (normalExponentIndex t q → HolGerm (ComplexModel d)) ≃ₗ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+t)) ⧸ normalIdeal d t ^ q) :=
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  (actualNormalSelectedColumnCoordinateEquiv G k q).trans (normalPowerLinearEquiv d t q)

theorem actualNormalSelectedColumnEquiv_apply (G : ActualAnalyticInheritedFamily d t K) (k q : ℕ)
    (c : normalExponentIndex t q → HolGerm (ComplexModel d)) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualNormalSelectedColumnEquiv G k q c =
      ∑ α : normalExponentIndex t q, c α •
        Ideal.Quotient.mk (normalIdeal d t ^ q) (actualNormalSelectedColumn G k α.val) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  have hc : (actualNormalSelectedColumnMatrix G k q) *ᵥ c =
      ∑ α : normalExponentIndex t q, c α •
        actualNormalJetCoordinates d t q (actualNormalSelectedColumn G k α.val) := by
    funext γ
    simp only [Matrix.mulVec, dotProduct, actualNormalSelectedColumnMatrix,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro α _
    exact mul_comm (actualNormalJetCoordinates d t q (actualNormalSelectedColumn G k α.val) γ) (c α)
  change normalPowerLinearEquiv d t q
    ((actualNormalSelectedColumnMatrix G k q) *ᵥ c) = _
  rw [hc, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [map_smul]
  congr 1
  exact (normalPowerLinearEquiv d t q).apply_symm_apply
    (Ideal.Quotient.mk (normalIdeal d t ^ q) (actualNormalSelectedColumn G k α.val))

/-- Each basis coordinate retains precisely the original selected analytic column. -/
theorem actualNormalSelectedColumnEquiv_single (G : ActualAnalyticInheritedFamily d t K)
    (k q : ℕ) (α : normalExponentIndex t q) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualNormalSelectedColumnEquiv G k q (Pi.single α 1) =
      Ideal.Quotient.mk (normalIdeal d t ^ q) (actualNormalSelectedColumn G k α.val) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  rw [actualNormalSelectedColumnEquiv_apply]
  simp [Pi.single_apply]

/-- The existing least selected owner, read on the literal normal exponent. -/
def actualNormalSelectedOwner (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (k : ℕ) (α : Fin t →₀ ℕ) : Option (actualInitialVertices MonomialOrder.degLex K) :=
  if h : actualJoinedExponent (0 : Fin d →₀ ℕ) α ∈
      actualSelectedVertexDiagram K (actualNormalHeadPrefix K k) then
    some (actualSelectedVertexOwner K (actualNormalHeadPrefix K k)
      (actualJoinedExponent (0 : Fin d →₀ ℕ) α) h)
  else none

theorem actualNormalSelectedOwner_some_spec (k : ℕ) (α : Fin t →₀ ℕ)
    (a : actualInitialVertices MonomialOrder.degLex K)
    (h : actualNormalSelectedOwner K k α = some a) :
    a ∈ actualNormalHeadPrefix K k ∧ actualNormalExponent a.val ≤ α := by
  unfold actualNormalSelectedOwner at h
  split_ifs at h with hα
  · have he := Option.some.inj h
    subst a
    have hs := actualSelectedVertexOwner_spec K (actualNormalHeadPrefix K k)
      (actualJoinedExponent (0 : Fin d →₀ ℕ) α) hα
    refine ⟨hs.1, ?_⟩
    intro i
    have hh := hs.2.1 (i.natAdd d)
    simpa [actualNormalExponent, actualJoinedExponent] using hh

private theorem actualNormalSelectedColumn_of_owner (G : ActualAnalyticInheritedFamily d t K)
    (k : ℕ) (α : Fin t →₀ ℕ) (a : actualInitialVertices MonomialOrder.degLex K)
    (h : actualNormalSelectedOwner K k α = some a) :
    actualNormalSelectedColumn G k α =
      normalExponentMonomial d t (α - actualNormalExponent a.val) * G.germs a := by
  unfold actualNormalSelectedOwner at h
  split_ifs at h with hα
  · have he := Option.some.inj h
    subst a
    rw [actualNormalSelectedColumn, dif_pos hα]

private theorem actualNormalSelectedColumn_of_no_owner (G : ActualAnalyticInheritedFamily d t K)
    (k : ℕ) (α : Fin t →₀ ℕ) (h : actualNormalSelectedOwner K k α = none) :
    actualNormalSelectedColumn G k α = normalExponentMonomial d t α := by
  unfold actualNormalSelectedOwner at h
  split_ifs at h with hα
  rw [actualNormalSelectedColumn, dif_neg hα]

/-- The quotient polynomial uses only its true owner-labelled exponent image. -/
def actualNormalSelectedQuotientPolynomial (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (k q : ℕ) (c : normalExponentIndex t q → HolGerm (ComplexModel d))
    (a : actualInitialVertices MonomialOrder.degLex K) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  let := normalExponentFintype t q
  ∑ α : normalExponentIndex t q,
    if actualNormalSelectedOwner K k α.val = some a then
      MvPolynomial.monomial (α.val - actualNormalExponent a.val) (c α)
    else 0

/-- The remainder polynomial retains exactly the unowned original exponents. -/
def actualNormalSelectedRemainderPolynomial (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ))
    (k q : ℕ) (c : normalExponentIndex t q → HolGerm (ComplexModel d)) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  let := normalExponentFintype t q
  ∑ α : normalExponentIndex t q,
    if actualNormalSelectedOwner K k α.val = none then MvPolynomial.monomial α.val (c α) else 0

/-- Regrouping true selected columns gives an identity of WHOLE analytic germs. -/
theorem actualNormalSelectedPolynomials_reconstruct (G : ActualAnalyticInheritedFamily d t K)
    (k q : ℕ) (c : normalExponentIndex t q → HolGerm (ComplexModel d)) :
    let := normalExponentFintype t q
    (∑ a : actualInitialVertices MonomialOrder.degLex K,
      normalPolynomialEval d t (actualNormalSelectedQuotientPolynomial K k q c a) * G.germs a) +
      normalPolynomialEval d t (actualNormalSelectedRemainderPolynomial K k q c) =
        ∑ α : normalExponentIndex t q, tangentPullback d t (c α) * actualNormalSelectedColumn G k α.val := by
  let := normalExponentFintype t q
  simp only [actualNormalSelectedQuotientPolynomial, actualNormalSelectedRemainderPolynomial,
    map_sum, Finset.sum_mul, apply_ite, map_zero, ite_mul, zero_mul,
    normalPolynomialEval_monomial]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  cases ho : actualNormalSelectedOwner K k α.val with
  | none =>
      rw [actualNormalSelectedColumn_of_no_owner G k α.val ho]
      simp
  | some a =>
      rw [actualNormalSelectedColumn_of_owner G k α.val a ho]
      simp [mul_assoc]

/-- The internally inverted class of the SAME original numerator. -/
def actualNormalDivisionCoordinates (G : ActualAnalyticInheritedFamily d t K)
    (k q : ℕ) (F : HolGerm (ComplexModel (d+t))) :
    normalExponentIndex t q → HolGerm (ComplexModel d) :=
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  (actualNormalSelectedColumnEquiv G k q).symm (Ideal.Quotient.mk (normalIdeal d t ^ q) F)

/-- The actual supported correction and actual remainder retain the WHOLE
normal-power class of the original numerator. -/
theorem actualNormalDivisionCoordinates_remainder (G : ActualAnalyticInheritedFamily d t K)
    (k q : ℕ) (F : HolGerm (ComplexModel (d+t))) :
    let := normalExponentFintype t q
    let c := actualNormalDivisionCoordinates G k q F
    F - ((∑ a : actualInitialVertices MonomialOrder.degLex K,
      normalPolynomialEval d t (actualNormalSelectedQuotientPolynomial K k q c a) * G.germs a) +
        normalPolynomialEval d t (actualNormalSelectedRemainderPolynomial K k q c)) ∈
      normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  let c := actualNormalDivisionCoordinates G k q F
  dsimp only
  rw [actualNormalSelectedPolynomials_reconstruct]
  apply Ideal.Quotient.eq.mp
  have h := (actualNormalSelectedColumnEquiv G k q).apply_symm_apply
    (Ideal.Quotient.mk (normalIdeal d t ^ q) F)
  rw [actualNormalSelectedColumnEquiv_apply] at h
  have he : Ideal.Quotient.mk (normalIdeal d t ^ q)
      (∑ α : normalExponentIndex t q, tangentPullback d t (c α) * actualNormalSelectedColumn G k α.val) =
        ∑ α : normalExponentIndex t q, c α •
          Ideal.Quotient.mk (normalIdeal d t ^ q) (actualNormalSelectedColumn G k α.val) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro α _
    exact (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).toLinearMap.map_smul
      (c α) (actualNormalSelectedColumn G k α.val)
  exact (he.trans h).symm

/-- Every nonzero quotient coefficient comes from its actual finite owned image. -/
theorem actualNormalSelectedQuotientPolynomial_support (k q : ℕ)
    (c : normalExponentIndex t q → HolGerm (ComplexModel d))
    (a : actualInitialVertices MonomialOrder.degLex K) (β : Fin t →₀ ℕ)
    (hβ : MvPolynomial.coeff β (actualNormalSelectedQuotientPolynomial K k q c a) ≠ 0) :
    ∃ α : normalExponentIndex t q,
      actualNormalSelectedOwner K k α.val = some a ∧ α.val - actualNormalExponent a.val = β := by
  let := normalExponentFintype t q
  by_contra h
  apply hβ
  rw [actualNormalSelectedQuotientPolynomial, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro α _
  by_cases ho : actualNormalSelectedOwner K k α.val = some a
  · rw [if_pos ho]
    have hne : α.val - actualNormalExponent a.val ≠ β := by
      intro he
      exact h ⟨α, ho, he⟩
    simp [MvPolynomial.coeff_monomial, hne]
  · rw [if_neg ho, MvPolynomial.coeff_zero]

theorem actualNormalSelectedRemainderPolynomial_support (k q : ℕ)
    (c : normalExponentIndex t q → HolGerm (ComplexModel d)) (β : Fin t →₀ ℕ)
    (hβ : MvPolynomial.coeff β (actualNormalSelectedRemainderPolynomial K k q c) ≠ 0) :
    ∃ α : normalExponentIndex t q,
      actualNormalSelectedOwner K k α.val = none ∧ α.val = β := by
  let := normalExponentFintype t q
  by_contra h
  apply hβ
  rw [actualNormalSelectedRemainderPolynomial, MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro α _
  by_cases ho : actualNormalSelectedOwner K k α.val = none
  · rw [if_pos ho]
    have hne : α.val ≠ β := by
      intro he
      exact h ⟨α, ho, he⟩
    simp [MvPolynomial.coeff_monomial, hne]
  · rw [if_neg ho, MvPolynomial.coeff_zero]

theorem actualNormalSelectedQuotientPolynomial_coefficient_owned (k q : ℕ)
    (c : normalExponentIndex t q → HolGerm (ComplexModel d))
    (a : actualInitialVertices MonomialOrder.degLex K) (α : normalExponentIndex t q)
    (ho : actualNormalSelectedOwner K k α.val = some a) :
    MvPolynomial.coeff (α.val - actualNormalExponent a.val)
      (actualNormalSelectedQuotientPolynomial K k q c a) = c α := by
  let := normalExponentFintype t q
  rw [actualNormalSelectedQuotientPolynomial, MvPolynomial.coeff_sum, Finset.sum_eq_single α]
  · simp only [if_pos ho, MvPolynomial.coeff_monomial, ite_true]
  · intro γ _ hγα
    by_cases hg : actualNormalSelectedOwner K k γ.val = some a
    · rw [if_pos hg]
      have hne : γ.val - actualNormalExponent a.val ≠ α.val - actualNormalExponent a.val := by
        intro he
        apply hγα
        apply Subtype.ext
        have hleγ := (actualNormalSelectedOwner_some_spec k γ.val a hg).2
        have hleα := (actualNormalSelectedOwner_some_spec k α.val a ho).2
        exact (tsub_add_cancel_of_le hleγ).symm.trans
          ((congrArg (fun β : Fin t →₀ ℕ => β + actualNormalExponent a.val) he).trans
            (tsub_add_cancel_of_le hleα))
      simp [MvPolynomial.coeff_monomial, hne]
    · rw [if_neg hg, MvPolynomial.coeff_zero]
  · intro hα
    exact (hα (Finset.mem_univ α)).elim

theorem actualNormalSelectedRemainderPolynomial_coefficient_unowned (k q : ℕ)
    (c : normalExponentIndex t q → HolGerm (ComplexModel d)) (α : normalExponentIndex t q)
    (ho : actualNormalSelectedOwner K k α.val = none) :
    MvPolynomial.coeff α.val (actualNormalSelectedRemainderPolynomial K k q c) = c α := by
  let := normalExponentFintype t q
  rw [actualNormalSelectedRemainderPolynomial, MvPolynomial.coeff_sum, Finset.sum_eq_single α]
  · simp only [if_pos ho, MvPolynomial.coeff_monomial, ite_true]
  · intro γ _ hγα
    by_cases hg : actualNormalSelectedOwner K k γ.val = none
    · rw [if_pos hg]
      have hne : γ.val ≠ α.val := fun he => hγα (Subtype.ext he)
      simp [MvPolynomial.coeff_monomial, hne]
    · rw [if_neg hg, MvPolynomial.coeff_zero]
  · intro hα
    exact (hα (Finset.mem_univ α)).elim

/-- Finite actual polynomials with their literal least-owner support constraints.
This records the output coefficient positions, with no division/basis assertion. -/
structure ActualNormalSupportedTuple
    (K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)) (k q : ℕ) where
  quotients : actualInitialVertices MonomialOrder.degLex K →
    MvPolynomial (Fin t) (HolGerm (ComplexModel d))
  remainder : MvPolynomial (Fin t) (HolGerm (ComplexModel d))
  quotient_support : ∀ a β, MvPolynomial.coeff β (quotients a) ≠ 0 →
    ∃ α : normalExponentIndex t q,
      actualNormalSelectedOwner K k α.val = some a ∧ α.val - actualNormalExponent a.val = β
  remainder_support : ∀ β, MvPolynomial.coeff β remainder ≠ 0 →
    ∃ α : normalExponentIndex t q, actualNormalSelectedOwner K k α.val = none ∧ α.val = β

private theorem ActualNormalSupportedTuple.ext {k q : ℕ}
    {P Q : ActualNormalSupportedTuple K k q}
    (hq : P.quotients = Q.quotients) (hr : P.remainder = Q.remainder) : P = Q := by
  cases P
  cases Q
  cases hq
  cases hr
  rfl

def actualNormalSupportedTupleOfCoefficients (k q : ℕ)
    (c : normalExponentIndex t q → HolGerm (ComplexModel d)) : ActualNormalSupportedTuple K k q where
  quotients := actualNormalSelectedQuotientPolynomial K k q c
  remainder := actualNormalSelectedRemainderPolynomial K k q c
  quotient_support := actualNormalSelectedQuotientPolynomial_support k q c
  remainder_support := actualNormalSelectedRemainderPolynomial_support k q c

def actualNormalSupportedTupleCoordinates {k q : ℕ} (P : ActualNormalSupportedTuple K k q)
    (α : normalExponentIndex t q) : HolGerm (ComplexModel d) :=
  match actualNormalSelectedOwner K k α.val with
  | some a => MvPolynomial.coeff (α.val - actualNormalExponent a.val) (P.quotients a)
  | none => MvPolynomial.coeff α.val P.remainder

private theorem actualNormalSupportedTuple_coordinates_construct (k q : ℕ)
    (c : normalExponentIndex t q → HolGerm (ComplexModel d)) :
    actualNormalSupportedTupleCoordinates (actualNormalSupportedTupleOfCoefficients (K := K) k q c) = c := by
  funext α
  cases ho : actualNormalSelectedOwner K k α.val with
  | none =>
      change (match actualNormalSelectedOwner K k α.val with
        | some a => _
        | none => _) = c α
      rw [ho]
      exact actualNormalSelectedRemainderPolynomial_coefficient_unowned k q c α ho
  | some a =>
      change (match actualNormalSelectedOwner K k α.val with
        | some a => _
        | none => _) = c α
      rw [ho]
      exact actualNormalSelectedQuotientPolynomial_coefficient_owned k q c a α ho

private theorem actualNormalSupportedTuple_construct_coordinates {k q : ℕ}
    (P : ActualNormalSupportedTuple K k q) :
    actualNormalSupportedTupleOfCoefficients k q (actualNormalSupportedTupleCoordinates P) = P := by
  apply ActualNormalSupportedTuple.ext
  · funext a
    apply MvPolynomial.ext
    intro β
    by_cases h : ∃ α : normalExponentIndex t q,
        actualNormalSelectedOwner K k α.val = some a ∧ α.val - actualNormalExponent a.val = β
    · obtain ⟨α, ho, hβ⟩ := h
      change MvPolynomial.coeff β
        (actualNormalSelectedQuotientPolynomial K k q (actualNormalSupportedTupleCoordinates P) a) = _
      rw [← hβ, actualNormalSelectedQuotientPolynomial_coefficient_owned k q
        (actualNormalSupportedTupleCoordinates P) a α ho]
      simp only [actualNormalSupportedTupleCoordinates, ho]
    · have hzP : MvPolynomial.coeff β (P.quotients a) = 0 := by
        by_contra hne
        exact h (P.quotient_support a β hne)
      have hzC : MvPolynomial.coeff β (actualNormalSelectedQuotientPolynomial K k q
          (actualNormalSupportedTupleCoordinates P) a) = 0 := by
        by_contra hne
        exact h (actualNormalSelectedQuotientPolynomial_support k q _ a β hne)
      exact hzC.trans hzP.symm
  · apply MvPolynomial.ext
    intro β
    by_cases h : ∃ α : normalExponentIndex t q,
        actualNormalSelectedOwner K k α.val = none ∧ α.val = β
    · obtain ⟨α, ho, hβ⟩ := h
      change MvPolynomial.coeff β
        (actualNormalSelectedRemainderPolynomial K k q (actualNormalSupportedTupleCoordinates P)) = _
      rw [← hβ, actualNormalSelectedRemainderPolynomial_coefficient_unowned k q
        (actualNormalSupportedTupleCoordinates P) α ho]
      simp only [actualNormalSupportedTupleCoordinates, ho]
    · have hzP : MvPolynomial.coeff β P.remainder = 0 := by
        by_contra hne
        exact h (P.remainder_support β hne)
      have hzC : MvPolynomial.coeff β (actualNormalSelectedRemainderPolynomial K k q
          (actualNormalSupportedTupleCoordinates P)) = 0 := by
        by_contra hne
        exact h (actualNormalSelectedRemainderPolynomial_support k q _ β hne)
      exact hzC.trans hzP.symm

/-- The actual finite owner partition is an exact coefficient correspondence. -/
def actualNormalSupportedTupleEquiv (k q : ℕ) :
    (normalExponentIndex t q → HolGerm (ComplexModel d)) ≃ ActualNormalSupportedTuple K k q where
  toFun := actualNormalSupportedTupleOfCoefficients k q
  invFun := actualNormalSupportedTupleCoordinates
  left_inv := actualNormalSupportedTuple_coordinates_construct k q
  right_inv := actualNormalSupportedTuple_construct_coordinates

def actualNormalSupportedTupleValue (G : ActualAnalyticInheritedFamily d t K) {k q : ℕ}
    (P : ActualNormalSupportedTuple K k q) : HolGerm (ComplexModel (d+t)) :=
  (∑ a : actualInitialVertices MonomialOrder.degLex K,
    normalPolynomialEval d t (P.quotients a) * G.germs a) + normalPolynomialEval d t P.remainder

private theorem actualNormalSelectedColumnEquiv_eq_class
    (G : ActualAnalyticInheritedFamily d t K) (k q : ℕ)
    (c : normalExponentIndex t q → HolGerm (ComplexModel d)) :
    let := tangentAlgebra d t
    let := normalExponentFintype t q
    actualNormalSelectedColumnEquiv G k q c = Ideal.Quotient.mk (normalIdeal d t ^ q)
      (actualNormalSupportedTupleValue G (actualNormalSupportedTupleOfCoefficients k q c)) := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  rw [actualNormalSelectedColumnEquiv_apply]
  change _ = Ideal.Quotient.mk (normalIdeal d t ^ q)
    ((∑ a : actualInitialVertices MonomialOrder.degLex K,
      normalPolynomialEval d t (actualNormalSelectedQuotientPolynomial K k q c a) * G.germs a) +
        normalPolynomialEval d t (actualNormalSelectedRemainderPolynomial K k q c))
  rw [actualNormalSelectedPolynomials_reconstruct, map_sum]
  apply Finset.sum_congr rfl
  intro α _
  exact ((Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (normalIdeal d t ^ q)).toLinearMap.map_smul
    (c α) (actualNormalSelectedColumn G k α.val)).symm

/-- Every original analytic numerator has a UNIQUE supported finite normal
division tuple, with the whole normal-power remainder proved internally. -/
theorem actual_relative_normal_jet_division (G : ActualAnalyticInheritedFamily d t K)
    (k q : ℕ) (F : HolGerm (ComplexModel (d+t))) :
    ∃! P : ActualNormalSupportedTuple K k q,
      F - actualNormalSupportedTupleValue G P ∈ normalIdeal d t ^ q := by
  let := tangentAlgebra d t
  let := normalExponentFintype t q
  let c := actualNormalDivisionCoordinates G k q F
  let P := actualNormalSupportedTupleOfCoefficients (K := K) k q c
  refine ⟨P, actualNormalDivisionCoordinates_remainder G k q F, ?_⟩
  intro Q hQ
  apply (actualNormalSupportedTupleEquiv (K := K) k q).symm.injective
  change actualNormalSupportedTupleCoordinates Q = actualNormalSupportedTupleCoordinates P
  change actualNormalSupportedTupleCoordinates Q =
    actualNormalSupportedTupleCoordinates (actualNormalSupportedTupleOfCoefficients k q c)
  rw [actualNormalSupportedTuple_coordinates_construct]
  apply (actualNormalSelectedColumnEquiv G k q).injective
  have hEq : Ideal.Quotient.mk (normalIdeal d t ^ q) F =
      Ideal.Quotient.mk (normalIdeal d t ^ q) (actualNormalSupportedTupleValue G Q) :=
    Ideal.Quotient.eq.mpr hQ
  have hQcoords := actualNormalSupportedTuple_construct_coordinates Q
  calc
    actualNormalSelectedColumnEquiv G k q (actualNormalSupportedTupleCoordinates Q) =
        Ideal.Quotient.mk (normalIdeal d t ^ q)
          (actualNormalSupportedTupleValue G
            (actualNormalSupportedTupleOfCoefficients k q (actualNormalSupportedTupleCoordinates Q))) :=
      actualNormalSelectedColumnEquiv_eq_class G k q _
    _ = Ideal.Quotient.mk (normalIdeal d t ^ q) (actualNormalSupportedTupleValue G Q) := by
      rw [hQcoords]
    _ = Ideal.Quotient.mk (normalIdeal d t ^ q) F := hEq.symm
    _ = actualNormalSelectedColumnEquiv G k q c :=
      ((actualNormalSelectedColumnEquiv G k q).apply_symm_apply
        (Ideal.Quotient.mk (normalIdeal d t ^ q) F)).symm

end

end Hironaka.HironakaActualRelativeNormalJetDivision
