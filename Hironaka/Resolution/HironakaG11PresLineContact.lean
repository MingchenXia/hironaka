import Hironaka.Resolution.HironakaG11PresLineDivision
import Hironaka.Resolution.HironakaActualSameFamilyZeroSectionContact

/-!
# Adding a variable to the native five-law data: selector contact, Jacobian and the five laws (goal G11, step (3a-lines))

Law 5 of the native point presentation: for every degree `R`, the selector derivatives `∂^{β_j} Γ_{S(j)}` of the members lie in
the ideal of the coordinate block of degree `R`, and their Jacobian on that block at the origin is invertible. For the lifted
family `Γ' = Γ ∘ proj` (`tangentPullback n 1`), with the lifted vertices and selector (`HironakaG11PresLineFormal`):

* the selector derivatives of `Γ'` are the pullbacks of those of `Γ` (`actualAnalyticMultiDerivative_tangentPullback`);
* the coordinate blocks of the lifted vertices are the old blocks (`liftBlockEquiv`); pullback maps block ideals into the lifted
  block ideals (`tangentPullback (z_i) = z_i`);
* the Jacobian of `Γ'` is the Jacobian of `Γ` reindexed along `liftBlockEquiv` (Taylor coefficients of renamed series).

Together with laws 1, 2, 3, 6 (`HironakaG11PresLineFormal`, `…LineJet`, `…LinePrefix`) and law 4 (`…LineDivision`):
**`actualHistoricalFivePointLaws_lift`** — the five point laws pass to the lifted data in `n + 1` variables.

Nothing here proves or assumes G11. Blueprint: `hironaka-g11-pres-line-state.tex`.
-/

set_option autoImplicit false

open Set Classical

namespace Hironaka.HironakaG11PresLineContact

noncomputable section

open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualInheritedAnalyticBlockJacobian
  HironakaActualCanonicalBlockJacobian HironakaActualFixedInheritedSelector HironakaActualRelativeTaylorCoefficients
  HironakaActualTaylorCoordinateNaturality HironakaActualAnalyticBlockGraphTranslation HironakaHolomorphicJetMonomialSpan
  HironakaActualSameFamilyZeroSectionContact HironakaActualHistoricalNormalizedWeakPresentation
  HironakaActualCauchyMonomialDivision HironakaActualOriginalFormalHSTransfer
  HironakaG11PresLineFormal HironakaG11PresLineJet HironakaG11PresLinePrefix HironakaG11PresLineDivision

variable {n : ℕ}

/-! ### Germs and Taylor series -/

theorem liftExp_eq_joined (β : Fin n →₀ ℕ) : liftExp β = actualJoinedExponent β (0 : Fin 1 →₀ ℕ) := by
  rw [actualJoinedExponent_tangent_embedding]
  rfl

/-- The Taylor series of a germ pulled back along the projection `ℂ^{n+1} → ℂ^n`. -/
theorem actualTaylor_tangentPullback_one (G : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom (n + 1) (tangentPullback n 1 G) =
      MvPowerSeries.rename (Fin.castAdd 1) (actualUnshiftedTaylorAlgHom n G) :=
  DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback n 1) G

theorem actualAnalyticMultiDerivative_liftExp (β : Fin n →₀ ℕ) (G : HolGerm (ComplexModel n)) :
    actualAnalyticMultiDerivative (liftExp β) (tangentPullback n 1 G) =
      tangentPullback n 1 (actualAnalyticMultiDerivative β G) := by
  rw [liftExp_eq_joined]
  exact actualAnalyticMultiDerivative_tangentPullback n 1 β G

theorem liftExp_tsub (α β : Fin n →₀ ℕ) : liftExp (α - β) = liftExp α - liftExp β := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · simp

theorem actualExponentFactorial_liftExp (α : Fin n →₀ ℕ) :
    actualExponentFactorial (liftExp α) = actualExponentFactorial α := by
  unfold actualExponentFactorial
  rw [Fin.prod_univ_castSucc]
  simp

/-- **The lifted germ family**: `Γ' (ι v) = Γ v ∘ proj`. -/
def liftGerms {V : Finset (Fin n →₀ ℕ)} (Γ : V → HolGerm (ComplexModel n)) :
    liftVertices V → HolGerm (ComplexModel (n + 1)) :=
  fun v' => tangentPullback n 1 (Γ ((liftVertexEquiv V).symm v'))

theorem liftGerms_liftVertexEquiv {V : Finset (Fin n →₀ ℕ)} (Γ : V → HolGerm (ComplexModel n)) (v : V) :
    liftGerms Γ (liftVertexEquiv V v) = tangentPullback n 1 (Γ v) := by
  simp only [liftGerms, Equiv.symm_apply_apply]

/-! ### Coordinate blocks -/

theorem castSucc_mem_fixedSelectorBlock_iff {V : Finset (Fin n →₀ ℕ)} (R : ℕ) (i : Fin n) :
    Fin.castSucc i ∈ fixedSelectorBlock (liftVertices V) R ↔ i ∈ fixedSelectorBlock V R := by
  constructor
  · rintro ⟨a', hdeg, ha'⟩
    refine ⟨(liftVertexEquiv V).symm a', ?_, ?_⟩
    · rwa [← normalExponentDegree_liftExp, liftVertexEquiv_symm_val]
    · rwa [← liftExp_apply_castSucc, liftVertexEquiv_symm_val]
  · rintro ⟨a, hdeg, ha⟩
    exact ⟨liftVertexEquiv V a, by rwa [liftVertexEquiv_val, normalExponentDegree_liftExp],
      by rwa [liftVertexEquiv_val, liftExp_apply_castSucc]⟩

theorem ne_last_of_mem_fixedSelectorBlock {V : Finset (Fin n →₀ ℕ)} {R : ℕ}
    (j : fixedSelectorBlock (liftVertices V) R) : j.val ≠ Fin.last n := by
  obtain ⟨a, _, ha⟩ := j.property
  intro h
  rw [h, ← liftVertexEquiv_symm_val a, liftExp_apply_last] at ha
  exact ha rfl

/-- The coordinate block of degree `R` of the lifted vertices is the old block. -/
def liftBlockEquiv (V : Finset (Fin n →₀ ℕ)) (R : ℕ) :
    fixedSelectorBlock (liftVertices V) R ≃ fixedSelectorBlock V R where
  toFun j := ⟨j.val.castPred (ne_last_of_mem_fixedSelectorBlock j), by
    rw [← castSucc_mem_fixedSelectorBlock_iff, Fin.castSucc_castPred]
    exact j.property⟩
  invFun i := ⟨Fin.castSucc i.val, (castSucc_mem_fixedSelectorBlock_iff R i.val).mpr i.property⟩
  left_inv j := Subtype.ext (Fin.castSucc_castPred j.val (ne_last_of_mem_fixedSelectorBlock j))
  right_inv i := Subtype.ext (Fin.castPred_castSucc (Fin.castSucc_lt_last i.val).ne)

theorem castSucc_liftBlockEquiv {V : Finset (Fin n →₀ ℕ)} {R : ℕ} (j : fixedSelectorBlock (liftVertices V) R) :
    Fin.castSucc (liftBlockEquiv V R j).val = j.val :=
  Fin.castSucc_castPred j.val (ne_last_of_mem_fixedSelectorBlock j)

theorem essentialPred_blockEssential {V : Finset (Fin n →₀ ℕ)} (R : ℕ) (j : fixedSelectorBlock (liftVertices V) R) :
    essentialPred (fixedSelectorBlockEssential R j) = fixedSelectorBlockEssential R (liftBlockEquiv V R j) :=
  Subtype.ext rfl

/-! ### Selector derivatives, contact and Jacobian -/

theorem fixedSelectorBeta_liftSelector {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (j : fixedSelectorEssential (liftVertices V)) :
    fixedSelectorBeta (liftSelector S) j = liftExp (fixedSelectorBeta S (essentialPred j)) := by
  unfold fixedSelectorBeta
  rw [liftExp_tsub, liftExp_single, castSucc_essentialPred]
  rfl

/-- **Selector derivatives of the lifted family** are the pullbacks of the old selector derivatives. -/
theorem actualFixedSelectorDerivative_lift {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (j : fixedSelectorEssential (liftVertices V)) :
    actualFixedSelectorDerivative (liftSelector S) (liftGerms Γ) j =
      tangentPullback n 1 (actualFixedSelectorDerivative S Γ (essentialPred j)) := by
  unfold actualFixedSelectorDerivative
  rw [fixedSelectorBeta_liftSelector]
  change actualAnalyticMultiDerivative _ (liftGerms Γ (liftVertexEquiv V (S.selected (essentialPred j)))) = _
  rw [liftGerms_liftVertexEquiv, actualAnalyticMultiDerivative_liftExp]

/-- Pullback along the projection maps coordinate block ideals into the lifted block ideals. -/
theorem tangentPullback_mem_blockIdeal {G : HolGerm (ComplexModel n)} {B : Set (Fin n)}
    (h : G ∈ actualAnalyticCoordinateBlockIdeal B) (B' : Set (Fin (n + 1))) (hB : ∀ i ∈ B, Fin.castSucc i ∈ B') :
    tangentPullback n 1 G ∈ actualAnalyticCoordinateBlockIdeal B' := by
  have hm := Ideal.mem_map_of_mem (tangentPullback n 1) h
  unfold actualAnalyticCoordinateBlockIdeal at hm ⊢
  rw [Ideal.map_span] at hm
  refine Ideal.span_mono ?_ hm
  rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
  exact ⟨Fin.castSucc i, hB i hi, (tangentPullback_coordinateGerm n 1 i).symm⟩

/-- **Law 5, contact, under a new variable.** -/
theorem actualFixedSelectorContactAt_lift {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (R : ℕ) (h : actualFixedSelectorContactAt S Γ R) :
    actualFixedSelectorContactAt (liftSelector S) (liftGerms Γ) R := by
  intro j
  rw [actualFixedSelectorDerivative_lift, essentialPred_blockEssential]
  exact tangentPullback_mem_blockIdeal (h (liftBlockEquiv V R j)) _
    (fun i hi => (castSucc_mem_fixedSelectorBlock_iff R i).mpr hi)

/-- **Law 5, Jacobian, under a new variable**: the lifted Jacobian is the old one reindexed. -/
theorem actualFixedSelectorJacobian_lift {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (R : ℕ) :
    actualFixedSelectorJacobian (liftSelector S) (liftGerms Γ) R =
      (actualFixedSelectorJacobian S Γ R).submatrix (liftBlockEquiv V R) (liftBlockEquiv V R) := by
  ext j i
  simp only [Matrix.submatrix_apply]
  unfold actualFixedSelectorJacobian
  rw [actualFixedSelectorDerivative_jacobian_coefficient, actualFixedSelectorDerivative_jacobian_coefficient]
  have hsel : (liftSelector S).selected (fixedSelectorBlockEssential R j) =
      liftVertexEquiv V (S.selected (fixedSelectorBlockEssential R (liftBlockEquiv V R j))) := by
    change liftVertexEquiv V (S.selected (essentialPred _)) = _
    rw [essentialPred_blockEssential]
  have hidx : fixedSelectorBeta (liftSelector S) (fixedSelectorBlockEssential R j) + Finsupp.single i.val 1 =
      liftExp (fixedSelectorBeta S (fixedSelectorBlockEssential R (liftBlockEquiv V R j)) +
        Finsupp.single (liftBlockEquiv V R i).val 1) := by
    rw [fixedSelectorBeta_liftSelector, essentialPred_blockEssential, liftExp_add, liftExp_single,
      castSucc_liftBlockEquiv]
  rw [hsel, hidx, liftGerms_liftVertexEquiv, actualTaylor_tangentPullback_one, coeff_rename_liftExp,
    actualExponentFactorial_liftExp]

theorem actualFixedSelectorJacobian_lift_det {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (R : ℕ) :
    (actualFixedSelectorJacobian (liftSelector S) (liftGerms Γ) R).det = (actualFixedSelectorJacobian S Γ R).det := by
  rw [actualFixedSelectorJacobian_lift, Matrix.det_submatrix_equiv_self]

/-! ### The five laws -/

/-- **The five point laws under a new variable**: the lifted selector, enumeration, words and germ family satisfy the five
point laws in `n + 1` variables. -/
theorem actualHistoricalFivePointLaws_lift {V : Finset (Fin n →₀ ℕ)} {k : ℕ} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n) (Γ : V → HolGerm (ComplexModel n))
    (h : ActualHistoricalFivePointLaws S a w Γ) :
    ActualHistoricalFivePointLaws (liftSelector S) (a.trans (liftVertexEquiv V)) (fun i => liftWord (w i))
      (liftGerms Γ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hfam : (fun i => actualUnshiftedTaylorAlgHom (n + 1) (liftGerms Γ ((a.trans (liftVertexEquiv V)) i))) =
      fun i => MvPowerSeries.rename (Fin.castAdd 1) (actualUnshiftedTaylorAlgHom n (Γ (a i))) := by
    funext i
    rw [Equiv.trans_apply, liftGerms_liftVertexEquiv, actualTaylor_tangentPullback_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [Equiv.trans_apply, liftGerms_liftVertexEquiv, actualTaylor_tangentPullback_one, wordExponent_liftWord,
      normalExponentDegree_liftExp, rename_mem_genuineFormalVariables_pow_iff, rename_mem_genuineFormalVariables_pow_iff]
    exact h1 i
  · intro q
    rw [hfam]
    exact historicalWholeJetMap_lift_bijective _ _ h2 q
  · intro m
    rw [hfam]
    exact historicalDegreePrefixFrames_lift _ _ m (h3 m)
  · rw [hfam]
    exact historicalWholeSupportedDivision_lift _ _ h4
  · intro R
    exact ⟨actualFixedSelectorContactAt_lift S Γ R (h5 R).1, by
      rw [actualFixedSelectorJacobian_lift_det]
      exact (h5 R).2⟩
  · have hfam6 : (fun v' => actualUnshiftedTaylorAlgHom (n + 1) (liftGerms Γ v')) =
        fun v' => MvPowerSeries.rename (Fin.castAdd 1) (actualUnshiftedTaylorAlgHom n (Γ ((liftVertexEquiv V).symm v'))) := by
      funext v'
      exact actualTaylor_tangentPullback_one _
    rw [hfam6]
    exact historicalWholePrefixSupport_lift h6

end

end Hironaka.HironakaG11PresLineContact
