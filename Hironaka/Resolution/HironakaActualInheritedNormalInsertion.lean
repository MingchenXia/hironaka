import Hironaka.Resolution.HironakaActualInheritedSourcePermutationFamily
import Hironaka.Resolution.HironakaActualRelativeStandardnessNormalPivotPriority

/-! The SAME inherited member heads under the SPECIFIC normal stable insertion.
Only the pivot coordinate of each old head is zero; earlier head coordinates
need not vanish. This is not arbitrary permutation covariance. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedNormalInsertion
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualInheritedSourceOwnerPermutation HironakaActualInheritedSourcePermutationFamily
  HironakaActualFixedInheritedSelector HironakaActualFixedInheritedSelectorPermutation
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualInheritedNestedContactFlag
  HironakaActualInheritedCurrentSourceRelabel HironakaActualRelativeNormalJetDivision
  HironakaActualRelativeStandardnessNormalPivotPriority
  HironakaActualCoefficientPresentationCentrePower
variable {n : ℕ}

private theorem normalInsertion_normal_ge (q f : Fin (n+1)) (hqf : q ≤ f)
    (i : Fin (n+1)) (hi : q ≤ i) : q ≤ normalPivotEquiv q f i := by
  by_contra h
  have hlt : normalPivotEquiv q f i < q := lt_of_not_ge h
  have he := normalPivotEquiv_tangent q f hqf (normalPivotEquiv q f i) hlt
  have hself : normalPivotEquiv q f i = i := (normalPivotEquiv q f).injective he
  rw [hself] at hlt
  exact (not_lt_of_ge hi) hlt

private theorem normalInsertion_other_order (q f : Fin (n+1)) (hqf : q ≤ f)
    (i j : Fin (n+1)) (hif : i ≠ f) (hjf : j ≠ f) (hij : i < j) :
    normalPivotEquiv q f i < normalPivotEquiv q f j := by
  by_cases hiq : i < q
  · rw [normalPivotEquiv_tangent q f hqf i hiq]
    by_cases hjq : j < q
    · rw [normalPivotEquiv_tangent q f hqf j hjq]
      exact hij
    · exact hiq.trans_le (normalInsertion_normal_ge q f hqf j (le_of_not_gt hjq))
  · exact normalPivotEquiv_normal_order q f hqf i j (le_of_not_gt hiq)
      ((le_of_not_gt hiq).trans hij.le) hif hjf hij

private theorem normalInsertion_after (q f : Fin (n+1)) (hqf : q ≤ f)
    (i : Fin (n+1)) (hfi : f < i) : normalPivotEquiv q f f < normalPivotEquiv q f i := by
  rw [normalPivotEquiv_pivot q f hqf]
  apply lt_of_le_of_ne (normalInsertion_normal_ge q f hqf i (hqf.trans hfi.le))
  intro he
  have hp : normalPivotEquiv q f f = normalPivotEquiv q f i :=
    (normalPivotEquiv_pivot q f hqf).trans he
  exact (ne_of_lt hfi) ((normalPivotEquiv q f).injective hp)

/-- A zero head coordinate can move only LEFT while the complement keeps its order. -/
private theorem leftMove_strict_of_zero_head (p : Fin n ≃ Fin n) (f : Fin n)
    (hord : ∀ i j, i ≠ f → j ≠ f → i < j → p i < p j)
    (hafter : ∀ i, f < i → p f < p i)
    (a β : Fin n →₀ ℕ) (haf : a f = 0)
    (h : MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn β) :
    MonomialOrder.degLex.toSyn (Finsupp.domCongr p a) <
      MonomialOrder.degLex.toSyn (Finsupp.domCongr p β) := by
  have hd (α : Fin n →₀ ℕ) : Finsupp.degree (Finsupp.domCongr p α) = Finsupp.degree α := by
    simpa only [normalExponentDegree, ← Finsupp.degree_eq_sum] using sourceExponentPermutation_degree p α
  have hreflect {i j : Fin n} (hif : i ≠ f) (hjf : j ≠ f) (hp : p i < p j) : i < j := by
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact hlt
    · exact False.elim ((ne_of_lt hp) (congrArg p he))
    · exact False.elim (lt_asymm hp (hord j i hjf hif hgt))
  have hreflectf {i : Fin n} (hp : p i < p f) : i < f := by
    rcases lt_trichotomy i f with hlt | he | hgt
    · exact hlt
    · exact False.elim ((ne_of_lt hp) (congrArg p he))
    · exact False.elim (lt_asymm hp (hafter i hgt))
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  rcases Finsupp.DegLex.lt_iff.mp (MonomialOrder.degLex_lt_iff.mp h) with hdegree | ⟨hdegree,hlex⟩
  · left
    simpa only [ofDegLex_toDegLex, hd] using hdegree
  · right
    refine ⟨by simpa only [ofDegLex_toDegLex, hd] using hdegree, ?_⟩
    apply Finsupp.Lex.lt_iff.mpr
    obtain ⟨j, hbefore, hj⟩ := Finsupp.Lex.lt_iff.mp hlex
    simp only [ofDegLex_toDegLex, ofLex_toLex] at hbefore hj
    by_cases hβf : β f = 0
    · have hjf : j ≠ f := by
        intro he
        rw [he, haf, hβf] at hj
        exact (lt_irrefl 0) hj
      refine ⟨p j, ?_, ?_⟩
      · intro i hi
        let l := p.symm i
        have hpl : p l = i := p.apply_symm_apply i
        by_cases hlf : l = f
        · simp only [ofDegLex_toDegLex, ofLex_toLex, sourceExponentPermutation_apply, l, hlf, haf, hβf]
        · have hlj : l < j := hreflect hlf hjf (by rwa [hpl])
          simpa only [ofDegLex_toDegLex, ofLex_toLex, sourceExponentPermutation_apply] using hbefore l hlj
      · simpa only [ofDegLex_toDegLex, ofLex_toLex, sourceExponentPermutation_apply,
          Equiv.symm_apply_apply] using hj
    · by_cases hpfj : p f ≤ p j
      · refine ⟨p f, ?_, ?_⟩
        · intro i hi
          let l := p.symm i
          have hpl : p l = i := p.apply_symm_apply i
          have hlf : l ≠ f := by
            intro he
            rw [he] at hpl
            exact (ne_of_lt hi) hpl.symm
          have hlj : l < j := by
            by_cases hjf : j = f
            · rw [hjf]
              exact hreflectf (by rwa [hpl])
            · exact hreflect hlf hjf (by rw [hpl]; exact hi.trans_le hpfj)
          simpa only [ofDegLex_toDegLex, ofLex_toLex, sourceExponentPermutation_apply] using hbefore l hlj
        · simpa only [ofDegLex_toDegLex, ofLex_toLex, sourceExponentPermutation_apply,
            Equiv.symm_apply_apply, haf] using Nat.pos_of_ne_zero hβf
      · have hpjf : p j < p f := lt_of_not_ge hpfj
        have hjf : j ≠ f := fun he => (ne_of_lt hpjf) (congrArg p he)
        refine ⟨p j, ?_, ?_⟩
        · intro i hi
          let l := p.symm i
          have hpl : p l = i := p.apply_symm_apply i
          have hlf : l ≠ f := by
            intro he
            rw [he] at hpl
            exact (ne_of_lt (hi.trans hpjf)) hpl.symm
          have hlj : l < j := hreflect hlf hjf (by rwa [hpl])
          simpa only [ofDegLex_toDegLex, ofLex_toLex, sourceExponentPermutation_apply] using hbefore l hlj
        · simpa only [ofDegLex_toDegLex, ofLex_toLex, sourceExponentPermutation_apply,
            Equiv.symm_apply_apply] using hj

theorem normalInsertion_strict_of_zero_head (q f : Fin (n+1)) (hqf : q ≤ f)
    (a β : Fin (n+1) →₀ ℕ) (haf : a f = 0)
    (h : MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn β) :
    MonomialOrder.degLex.toSyn (Finsupp.domCongr (normalPivotEquiv q f) a) <
      MonomialOrder.degLex.toSyn (Finsupp.domCongr (normalPivotEquiv q f) β) :=
  leftMove_strict_of_zero_head (normalPivotEquiv q f) f
    (normalInsertion_other_order q f hqf) (normalInsertion_after q f hqf) a β haf h

/-- Reusable only after a genuine strict-comparison proof for the given head. -/
theorem source_member_monic_of_strict_comparison (p : Fin n ≃ Fin n)
    (a : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hc : MvPowerSeries.coeff a F = 1)
    (hl : ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a → MvPowerSeries.coeff β F = 0)
    (hcmp : ∀ β, MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn β →
      MonomialOrder.degLex.toSyn (Finsupp.domCongr p a) < MonomialOrder.degLex.toSyn (Finsupp.domCongr p β)) :
    MvPowerSeries.coeff (Finsupp.domCongr p a) (MvPowerSeries.rename p F) = 1 ∧
      ∀ γ, MonomialOrder.degLex.toSyn γ < MonomialOrder.degLex.toSyn (Finsupp.domCongr p a) →
        MvPowerSeries.coeff γ (MvPowerSeries.rename p F) = 0 := by
  constructor
  · rw [sourceExponentPermutation_coeff, hc]
  · intro γ hγ
    obtain ⟨β,rfl⟩ := (Finsupp.domCongr p).surjective γ
    rw [sourceExponentPermutation_coeff]
    by_contra hb
    have haβ : MonomialOrder.degLex.toSyn a ≤ MonomialOrder.degLex.toSyn β := by
      by_contra h
      exact hb (hl β (lt_of_not_ge h))
    rcases lt_or_eq_of_le haβ with hlt | heq
    · exact (not_lt_of_ge (hcmp β hlt).le) hγ
    · have he : β = a := (MonomialOrder.degLex.toSyn.injective heq).symm
      rw [he] at hγ
      exact (lt_irrefl _) hγ

theorem normalInsertion_same_member_monic (q f : Fin (n+1)) (hqf : q ≤ f)
    (a : Fin (n+1) →₀ ℕ) (F : MvPowerSeries (Fin (n+1)) ℂ) (haf : a f = 0)
    (hc : MvPowerSeries.coeff a F = 1)
    (hl : ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a → MvPowerSeries.coeff β F = 0) :
    MvPowerSeries.coeff (Finsupp.domCongr (normalPivotEquiv q f) a) (normalPivotRename q f F) = 1 ∧
      ∀ γ, MonomialOrder.degLex.toSyn γ < MonomialOrder.degLex.toSyn (Finsupp.domCongr (normalPivotEquiv q f) a) →
        MvPowerSeries.coeff γ (normalPivotRename q f F) = 0 :=
  source_member_monic_of_strict_comparison (normalPivotEquiv q f) a F hc hl
    (normalInsertion_strict_of_zero_head q f hqf a · haf)

variable {K : Ideal (MvPowerSeries (Fin (n+1)) ℂ)}

theorem normalInsertion_family_lower (G : ActualAnalyticInheritedFamily (n+1) 0 K)
    (q f : Fin (n+1)) (hqf : q ≤ f)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0) :
    ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr (normalPivotEquiv q f) a.val) →
      MvPowerSeries.coeff γ (normalPivotRename q f (actualUnshiftedTaylorAlgHom (n+1) (G.germs a))) = 0 := by
  intro a
  exact (normalInsertion_same_member_monic q f hqf a.val
    (actualUnshiftedTaylorAlgHom (n+1) (G.germs a)) (hf a) (G.monic a) (G.lower a)).2

theorem actual_initial_diagram_normalInsertion_same_family
    (G : ActualAnalyticInheritedFamily (n+1) 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom (n+1) (G.germs a) ∈ K)
    (q f : Fin (n+1)) (hqf : q ≤ f)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0) :
    actualInitialDiagram MonomialOrder.degLex (Ideal.map (normalPivotRename q f).toRingHom K) =
      Finsupp.domCongr (normalPivotEquiv q f) '' actualInitialDiagram MonomialOrder.degLex K :=
  actual_initial_diagram_rename_of_same_family_heads K (actualSourceFormalFamily G hmem)
    (normalPivotEquiv q f) (normalInsertion_family_lower G q f hqf hf)

/-- Full current/support/provenance output, with all member-head conditions internal. -/
theorem actual_normalInsertion_same_family_transport
    (G : ActualAnalyticInheritedFamily (n+1) 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom (n+1) (G.germs a) ∈ K)
    (q f : Fin (n+1)) (hqf : q ≤ f)
    (hf : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K)) :
    let hl := normalInsertion_family_lower G q f hqf hf
    let G' := actualSourcePermutedInheritedFamily G hmem (normalPivotEquiv q f) hl
    let S' := actualSourcePermutedFixedSelector G hmem (normalPivotEquiv q f) hl S
    actualInheritedCurrentSourceIdeal (Ideal.span (Set.range G'.germs)) =
        Ideal.map (normalPivotRename q f).toRingHom K ∧
      (∀ k, ActualInheritedPrefixReducedAt G k → ActualInheritedPrefixReducedAt G' k) ∧
      (∀ k, actualFixedSelectorContactAt S G.germs k → actualFixedSelectorContactAt S' G'.germs k) ∧
      ∀ k, (actualFixedSelectorJacobian S' G'.germs k).det = (actualFixedSelectorJacobian S G.germs k).det := by
  dsimp only
  exact ⟨actualSourcePermutedInheritedFamily_current_ideal G hmem (normalPivotEquiv q f) _,
    actualSourcePermutedInheritedFamily_prefix_reduced G hmem (normalPivotEquiv q f) _,
    actualSourcePermutedFixedSelector_contact G hmem (normalPivotEquiv q f) _ S,
    actualSourcePermutedFixedSelector_jacobian_det G hmem (normalPivotEquiv q f) _ S⟩

end
end Hironaka.HironakaActualInheritedNormalInsertion
