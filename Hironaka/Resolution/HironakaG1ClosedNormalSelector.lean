import Hironaka.Resolution.HironakaG11PresLineContact

/-! The inherited vertex labels after adjoining the actual linear normal equation. -/
set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaG1ClosedNormalSelector
noncomputable section

open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaG11PresLineFormal HironakaG11PresLineContact HironakaHolomorphicJetMonomialSpan
  HironakaActualFixedInheritedSelector HironakaActualHistoricalMovingPrefixSupport
  HironakaActualOriginalFormalHSTransfer HironakaActualRelativeTaylorCoefficients
  HironakaActualCoefficientPresentationCentrePower HironakaActualInheritedAnalyticBlockJacobian
  HironakaActualCanonicalBlockJacobian HironakaActualAnalyticBlockGraphTranslation
  HironakaActualAnalyticFormalNormalPowers

variable {n : ℕ}

abbrev normalExponent (n : ℕ) : Fin (n+1) →₀ ℕ := Finsupp.single (Fin.last n) 1

theorem normalExponent_degree (n : ℕ) : normalExponentDegree (normalExponent n) = 1 := by
  simp [normalExponentDegree]

def normalVertices (V : Finset (Fin n →₀ ℕ)) : Finset (Fin (n+1) →₀ ℕ) :=
  insert (normalExponent n) (liftVertices V)

variable {V : Finset (Fin n →₀ ℕ)}

def normalVertex (V : Finset (Fin n →₀ ℕ)) : normalVertices V :=
  ⟨normalExponent n, Finset.mem_insert_self _ _⟩

def oldVertex (v : V) : normalVertices V :=
  ⟨liftExp v.val, Finset.mem_insert_of_mem ((liftVertexEquiv V) v).property⟩

theorem normalVertex_ne_old (v : V) : normalVertex V ≠ oldVertex v := by
  intro h
  have hlast := congrArg (fun a : normalVertices V => a.val (Fin.last n)) h
  simp [normalVertex, oldVertex] at hlast

theorem normalVertices_cases (a : normalVertices V) :
    a = normalVertex V ∨ ∃ v : V, a = oldVertex v := by
  rcases Finset.mem_insert.mp a.property with h | h
  · exact Or.inl (Subtype.ext h)
  · let b : liftVertices V := ⟨a.val,h⟩
    exact Or.inr ⟨(liftVertexEquiv V).symm b, Subtype.ext (liftVertexEquiv_symm_val b).symm⟩

/-- Actual germ family with the genuine last-coordinate equation and the
holomorphic projection pullbacks of every inherited numerator. -/
def normalGerms (Γ : V → HolGerm (ComplexModel n)) : normalVertices V → HolGerm (ComplexModel (n+1)) :=
  fun a => if h : a.val = normalExponent n then coordinateGerm (Fin.last n) else
    liftGerms Γ ⟨a.val, (Finset.mem_insert.mp a.property).resolve_left h⟩

@[simp] theorem normalGerms_normal (Γ : V → HolGerm (ComplexModel n)) :
    normalGerms Γ (normalVertex V) = coordinateGerm (Fin.last n) := by
  simp [normalGerms, normalVertex]

@[simp] theorem normalGerms_old (Γ : V → HolGerm (ComplexModel n)) (v : V) :
    normalGerms Γ (oldVertex v) = tangentPullback n 1 (Γ v) := by
  have h : (oldVertex v).val ≠ normalExponent n :=
    fun h => normalVertex_ne_old v (Subtype.ext h.symm)
  rw [normalGerms, dif_neg h]
  exact liftGerms_liftVertexEquiv Γ v

/-- Whole prefix support for literal Taylor series of the extended analytic
family. The degree-one equation has no lower positive prefix. Its cone is
avoided by every pulled-back original germ. -/
theorem historicalWholePrefixSupport_normalGerms (Γ : V → HolGerm (ComplexModel n))
    (hp : ∀ v : V, 0 < normalExponentDegree v.val)
    (hΓ : HistoricalWholePrefixSupport V (fun v => actualUnshiftedTaylorAlgHom n (Γ v))) :
    HistoricalWholePrefixSupport (normalVertices V)
      (fun v => actualUnshiftedTaylorAlgHom (n+1) (normalGerms Γ v)) := by
  intro k a ha b hb β hβ
  rcases normalVertices_cases a with rfl | ⟨a,rfl⟩
  · change k < normalExponentDegree (normalExponent n) at ha
    rw [normalExponent_degree] at ha
    rcases normalVertices_cases b with rfl | ⟨b,rfl⟩
    · change normalExponentDegree (normalExponent n) ≤ k at hb
      rw [normalExponent_degree] at hb
      omega
    · change normalExponentDegree (liftExp b.val) ≤ k at hb
      rw [normalExponentDegree_liftExp] at hb
      have h := hp b
      omega
  · change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (n+1) (normalGerms Γ (oldVertex a))) = 0
    rw [normalGerms_old, actualTaylor_tangentPullback_one]
    by_cases hl : ∃ α, liftExp α = β
    · obtain ⟨α,rfl⟩ := hl
      rw [coeff_rename_liftExp]
      rcases normalVertices_cases b with rfl | ⟨b,rfl⟩
      · change normalExponent n ≤ liftExp α at hβ
        rw [Finsupp.single_le_iff, liftExp_apply_last] at hβ
        omega
      · change k < normalExponentDegree (liftExp a.val) at ha
        change normalExponentDegree (liftExp b.val) ≤ k at hb
        change liftExp b.val ≤ liftExp α at hβ
        rw [normalExponentDegree_liftExp] at ha hb
        exact hΓ k a ha b hb α (liftExp_le_liftExp_iff.mp hβ)
    · exact coeff_rename_of_notMem _ (fun α h => hl ⟨α,h⟩)

theorem castSucc_mem_normalEssential (i : Fin n) :
    Fin.castSucc i ∈ fixedSelectorEssential (normalVertices V) ↔ i ∈ fixedSelectorEssential V := by
  constructor
  · rintro ⟨a,ha⟩
    rcases normalVertices_cases a with rfl | ⟨v,rfl⟩
    · exact (ha (Finsupp.single_eq_of_ne (Fin.castSucc_lt_last i).ne)).elim
    · exact ⟨v, by simpa only [oldVertex, liftExp_apply_castSucc] using ha⟩
  · rintro ⟨v,hv⟩
    exact ⟨oldVertex v, by simpa only [oldVertex, liftExp_apply_castSucc] using hv⟩

def normalEssential (V : Finset (Fin n →₀ ℕ)) : fixedSelectorEssential (normalVertices V) :=
  ⟨Fin.last n, normalVertex V, by simp [normalVertex]⟩

def oldEssential (j : fixedSelectorEssential V) : fixedSelectorEssential (normalVertices V) :=
  ⟨Fin.castSucc j.val, (castSucc_mem_normalEssential j.val).mpr j.property⟩

private def normalSelected (S : ActualFixedInheritedSelector V)
    (j : fixedSelectorEssential (normalVertices V)) : normalVertices V :=
  if h : j.val = Fin.last n then normalVertex V else
    oldVertex (S.selected ⟨j.val.castPred h, by
      apply (castSucc_mem_normalEssential (j.val.castPred h)).mp
      rw [Fin.castSucc_castPred]
      exact j.property⟩)

@[simp] private theorem normalSelected_normal (S : ActualFixedInheritedSelector V) :
    normalSelected S (normalEssential V) = normalVertex V := by
  simp [normalSelected, normalEssential]

@[simp] private theorem normalSelected_old (S : ActualFixedInheritedSelector V)
    (j : fixedSelectorEssential V) :
    normalSelected S (oldEssential j) = oldVertex (S.selected j) := by
  unfold normalSelected
  have h : (oldEssential j).val ≠ Fin.last n := (Fin.castSucc_lt_last j.val).ne
  rw [dif_neg h]
  congr 2

theorem normalEssential_cases (j : fixedSelectorEssential (normalVertices V)) :
    j = normalEssential V ∨ ∃ i : fixedSelectorEssential V, j = oldEssential i := by
  by_cases h : j.val = Fin.last n
  · exact Or.inl (Subtype.ext h)
  · let i := j.val.castPred h
    have hi : i ∈ fixedSelectorEssential V := by
      apply (castSucc_mem_normalEssential i).mp
      exact Fin.castSucc_castPred j.val h ▸ j.property
    exact Or.inr ⟨⟨i,hi⟩, Subtype.ext (Fin.castSucc_castPred j.val h).symm⟩

/-- The normal variable selects its literal linear equation, and the old
variables keep their old selected numerators and least degrees. -/
def normalSelector (S : ActualFixedInheritedSelector V) :
    ActualFixedInheritedSelector (normalVertices V) where
  selected := normalSelected S
  positive j := by
    rcases normalEssential_cases j with rfl | ⟨i,rfl⟩
    · rw [normalSelected_normal]
      simp [normalVertex, normalEssential]
    · rw [normalSelected_old]
      simpa [oldVertex, oldEssential] using S.positive i
  least_degree j a ha := by
    rcases normalEssential_cases j with rfl | ⟨i,rfl⟩
    · rw [normalSelected_normal]
      rcases normalVertices_cases a with rfl | ⟨v,rfl⟩
      · exact le_rfl
      · exact (ha (liftExp_apply_last v.val)).elim
    · rw [normalSelected_old]
      rcases normalVertices_cases a with rfl | ⟨v,rfl⟩
      · exact (ha (Finsupp.single_eq_of_ne (Fin.castSucc_lt_last i.val).ne)).elim
      · have hv : v.val i.val ≠ 0 := by simpa [oldVertex, oldEssential] using ha
        simpa [oldVertex, normalExponentDegree_liftExp] using S.least_degree i v hv

@[simp] theorem normalSelector_selected_normal (S : ActualFixedInheritedSelector V) :
    (normalSelector S).selected (normalEssential V) = normalVertex V := normalSelected_normal S

@[simp] theorem normalSelector_selected_old (S : ActualFixedInheritedSelector V)
    (j : fixedSelectorEssential V) :
    (normalSelector S).selected (oldEssential j) = oldVertex (S.selected j) := normalSelected_old S j

theorem normalSelector_beta_normal (S : ActualFixedInheritedSelector V) :
    fixedSelectorBeta (normalSelector S) (normalEssential V) = 0 := by
  rw [fixedSelectorBeta, normalSelector_selected_normal]
  exact tsub_self _

theorem normalSelector_beta_old (S : ActualFixedInheritedSelector V) (j : fixedSelectorEssential V) :
    fixedSelectorBeta (normalSelector S) (oldEssential j) = liftExp (fixedSelectorBeta S j) := by
  rw [fixedSelectorBeta, normalSelector_selected_old, fixedSelectorBeta, liftExp_tsub, liftExp_single]
  rfl

theorem normalSelector_derivative_normal (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) :
    actualFixedSelectorDerivative (normalSelector S) (normalGerms Γ) (normalEssential V) =
      coordinateGerm (Fin.last n) := by
  rw [actualFixedSelectorDerivative, normalSelector_beta_normal, normalSelector_selected_normal,
    normalGerms_normal]
  apply actualUnshiftedTaylorAlgHom_injective (n+1)
  rw [actualTaylor_actualAnalyticMultiDerivative, actualFormalMultiDerivative_zero]

theorem normalSelector_derivative_old (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (j : fixedSelectorEssential V) :
    actualFixedSelectorDerivative (normalSelector S) (normalGerms Γ) (oldEssential j) =
      tangentPullback n 1 (actualFixedSelectorDerivative S Γ j) := by
  rw [actualFixedSelectorDerivative, normalSelector_beta_old, normalSelector_selected_old,
    normalGerms_old, actualAnalyticMultiDerivative_liftExp]
  rfl

theorem castSucc_mem_normalBlock (q : ℕ) (i : Fin n) :
    Fin.castSucc i ∈ fixedSelectorBlock (normalVertices V) q ↔ i ∈ fixedSelectorBlock V q := by
  constructor
  · rintro ⟨a,hq,ha⟩
    rcases normalVertices_cases a with rfl | ⟨v,rfl⟩
    · exact (ha (Finsupp.single_eq_of_ne (Fin.castSucc_lt_last i).ne)).elim
    · exact ⟨v, by simpa only [oldVertex, normalExponentDegree_liftExp] using hq,
        by simpa only [oldVertex, liftExp_apply_castSucc] using ha⟩
  · rintro ⟨v,hq,hv⟩
    exact ⟨oldVertex v, by simpa only [oldVertex, normalExponentDegree_liftExp] using hq,
      by simpa only [oldVertex, liftExp_apply_castSucc] using hv⟩

/-- The genuine analytic selected derivatives still lie in their full
degree-cutoff coordinate block ideals after closed normal adjoining. -/
theorem normalSelector_contact (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (q : ℕ)
    (h : actualFixedSelectorContactAt S Γ q) :
    actualFixedSelectorContactAt (normalSelector S) (normalGerms Γ) q := by
  intro j
  rcases normalEssential_cases (fixedSelectorBlockEssential q j) with hj | ⟨i,hi⟩
  · rw [hj, normalSelector_derivative_normal]
    apply Ideal.subset_span
    refine ⟨Fin.last n, ?_, rfl⟩
    have hval := congrArg Subtype.val hj
    change j.val = Fin.last n at hval
    exact hval ▸ j.property
  · rw [hi, normalSelector_derivative_old]
    have hval := congrArg Subtype.val hi
    change j.val = Fin.castSucc i.val at hval
    have hiBlock : i.val ∈ fixedSelectorBlock V q :=
      (castSucc_mem_normalBlock q i.val).mp (hval ▸ j.property)
    let i' : fixedSelectorBlock V q := ⟨i.val,hiBlock⟩
    exact tangentPullback_mem_blockIdeal (h i') _
      (fun l hl => (castSucc_mem_normalBlock q l).mpr hl)

private def normalBlock (q : ℕ) (hq : 1 ≤ q) :
    fixedSelectorBlock (normalVertices V) q :=
  ⟨Fin.last n, normalVertex V, by simpa only [normalVertex, normalExponent_degree] using hq,
    by simp [normalVertex]⟩

private def oldBlock (q : ℕ) (j : fixedSelectorBlock V q) :
    fixedSelectorBlock (normalVertices V) q :=
  ⟨Fin.castSucc j.val, (castSucc_mem_normalBlock q j.val).mpr j.property⟩

private def closedBlockEquiv (q : ℕ) (hq : 1 ≤ q) :
    (Unit ⊕ fixedSelectorBlock V q) ≃ fixedSelectorBlock (normalVertices V) q := by
  let f := Sum.elim (fun _ : Unit => normalBlock (V := V) q hq) (oldBlock q)
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    cases x with
    | inl a =>
      cases y with
      | inl b => simp
      | inr b => exact ((Fin.castSucc_lt_last b.val).ne (congrArg Subtype.val h).symm).elim
    | inr a =>
      cases y with
      | inl b => exact ((Fin.castSucc_lt_last a.val).ne (congrArg Subtype.val h)).elim
      | inr b =>
        exact congrArg Sum.inr (Subtype.ext
          (Fin.castSucc_injective n (congrArg Subtype.val h)))
  · intro j
    by_cases hj : j.val = Fin.last n
    · exact ⟨Sum.inl (), Subtype.ext hj.symm⟩
    · let i := j.val.castPred hj
      have he : Fin.castSucc i = j.val := Fin.castSucc_castPred j.val hj
      have hmem : i ∈ fixedSelectorBlock V q :=
        (castSucc_mem_normalBlock q i).mp (he ▸ j.property)
      exact ⟨Sum.inr ⟨i,hmem⟩, Subtype.ext he⟩

/-- The new selector Jacobian has the original determinant. In a positive
cutoff it is block diagonal with the added unit normal entry. -/
theorem normalSelector_jacobian_det (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (q : ℕ)
    (hPos : ∀ v : V, 0 < normalExponentDegree v.val) :
    (actualFixedSelectorJacobian (normalSelector S) (normalGerms Γ) q).det =
      (actualFixedSelectorJacobian S Γ q).det := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have : IsEmpty (fixedSelectorBlock V 0) := ⟨fun j => by
      obtain ⟨v,hv,_⟩ := j.property
      exact (Nat.not_le_of_gt (hPos v)) hv⟩
    have : IsEmpty (fixedSelectorBlock (normalVertices V) 0) := ⟨fun j => by
      obtain ⟨a,ha,_⟩ := j.property
      rcases normalVertices_cases a with rfl | ⟨v,rfl⟩
      · change normalExponentDegree (normalExponent n) ≤ 0 at ha
        rw [normalExponent_degree] at ha
        omega
      · change normalExponentDegree (liftExp v.val) ≤ 0 at ha
        rw [normalExponentDegree_liftExp] at ha
        exact (Nat.not_le_of_gt (hPos v)) ha⟩
    rw [Matrix.det_isEmpty, Matrix.det_isEmpty]
  · let e := closedBlockEquiv (V := V) q hq
    let A := actualFixedSelectorJacobian S Γ q
    let B := actualFixedSelectorJacobian (normalSelector S) (normalGerms Γ) q
    have hB : B.submatrix e e = Matrix.fromBlocks (1 : Matrix Unit Unit ℂ) 0 0 A := by
      ext i j
      rcases i with i | i <;> rcases j with j | j
      · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁]
        change HolGerm.eval (actualAnalyticCoordinateDerivative (Fin.last n)
          (actualFixedSelectorDerivative (normalSelector S) (normalGerms Γ) (normalEssential V))) = _
        rw [actualFixedSelectorDerivative_jacobian_coefficient, normalSelector_beta_normal,
          normalSelector_selected_normal, normalGerms_normal, actualUnshiftedTaylor_coordinate,
          zero_add, MvPowerSeries.coeff_X, if_pos rfl]
        cases i
        cases j
        simp only [one_mul, Matrix.one_apply_eq, actualExponentFactorial]
        apply Finset.prod_eq_one
        intro l _
        by_cases hl : l = Fin.last n
        · subst l
          simp
        · simp [Finsupp.single_eq_of_ne hl]
      · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂]
        change HolGerm.eval (actualAnalyticCoordinateDerivative (Fin.castSucc j.val)
          (actualFixedSelectorDerivative (normalSelector S) (normalGerms Γ) (normalEssential V))) = 0
        rw [actualFixedSelectorDerivative_jacobian_coefficient, normalSelector_beta_normal,
          normalSelector_selected_normal, normalGerms_normal, actualUnshiftedTaylor_coordinate,
          zero_add, MvPowerSeries.coeff_X, if_neg, zero_mul]
        intro h
        have hh := congrArg (fun a : Fin (n+1) →₀ ℕ => a (Fin.last n)) h
        simp [Finsupp.single_eq_of_ne (Fin.castSucc_lt_last j.val).ne'] at hh
      · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁]
        change HolGerm.eval (actualAnalyticCoordinateDerivative (Fin.last n)
          (actualFixedSelectorDerivative (normalSelector S) (normalGerms Γ)
            (oldEssential (fixedSelectorBlockEssential q i)))) = 0
        rw [actualFixedSelectorDerivative_jacobian_coefficient, normalSelector_beta_old,
          normalSelector_selected_old, normalGerms_old, actualTaylor_tangentPullback_one]
        rw [coeff_rename_of_notMem, zero_mul]
        intro α ha
        have hh := congrArg (fun a : Fin (n+1) →₀ ℕ => a (Fin.last n)) ha
        simp at hh
      · rw [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂]
        change HolGerm.eval (actualAnalyticCoordinateDerivative (Fin.castSucc j.val)
          (actualFixedSelectorDerivative (normalSelector S) (normalGerms Γ)
            (oldEssential (fixedSelectorBlockEssential q i)))) =
          HolGerm.eval (actualAnalyticCoordinateDerivative j.val
            (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential q i)))
        rw [actualFixedSelectorDerivative_jacobian_coefficient,
          actualFixedSelectorDerivative_jacobian_coefficient, normalSelector_beta_old,
          normalSelector_selected_old, normalGerms_old, actualTaylor_tangentPullback_one,
          ← liftExp_single, ← liftExp_add, coeff_rename_liftExp, actualExponentFactorial_liftExp]
    rw [← Matrix.det_submatrix_equiv_self e B, hB, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, one_mul]

#print axioms historicalWholePrefixSupport_normalGerms
#print axioms normalSelector_contact
#print axioms normalSelector_jacobian_det

end
end Hironaka.HironakaG1ClosedNormalSelector
