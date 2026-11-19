import Hironaka.Resolution.HironakaActualInheritedNormalInsertion
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

/-! All nonessential coordinates FIRST, with the old order kept inside both
parts. This is a genuine finite permutation, not a nearby free translation. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedEssentialPriority
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualInheritedSourceOwnerPermutation HironakaActualInheritedSourcePermutationFamily
  HironakaActualInheritedNormalInsertion HironakaActualFixedInheritedSelector
  HironakaActualFixedInheritedSelectorPermutation HironakaActualInheritedAnalyticBlockJacobian
  HironakaActualInheritedNestedContactFlag HironakaActualInheritedCurrentSourceRelabel
  HironakaActualRelativeNormalJetDivision HironakaActualCanonicalBlockJacobian
  HironakaActualCoefficientPresentationCentrePower
  HironakaActualRelativeStandardnessBlockSupport
variable {n : ℕ}

private theorem complement_card (B : Set (Fin n)) : Fintype.card (↥(Bᶜ)) + Fintype.card B = n := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using
    Fintype.card_congr ((Equiv.sumComm (↥(Bᶜ)) B).trans (Equiv.Set.sumCompl B))

/-- The actual increasing finite enumerations give a specified inverse as well. -/
def essentialFreeFirstEquiv (B : Set (Fin n)) : Fin n ≃ Fin n :=
  ((Equiv.Set.sumCompl B).symm.trans (Equiv.sumComm _ _)).trans
    ((Equiv.sumCongr (Fintype.orderIsoFinOfCardEq (↥(Bᶜ)) rfl).symm.toEquiv
      (Fintype.orderIsoFinOfCardEq B rfl).symm.toEquiv).trans
        (finSumFinEquiv.trans (finCongr (complement_card B))))

private theorem essentialFreeFirst_val_free (B : Set (Fin n)) (i : Fin n) (hi : i ∉ B) :
    (essentialFreeFirstEquiv B i).val =
      ((Fintype.orderIsoFinOfCardEq (↥(Bᶜ)) rfl).symm ⟨i,hi⟩).val := by
  unfold essentialFreeFirstEquiv
  simp only [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_notMem hi]
  rfl

private theorem essentialFreeFirst_val_block (B : Set (Fin n)) (i : Fin n) (hi : i ∈ B) :
    (essentialFreeFirstEquiv B i).val = Fintype.card (↥(Bᶜ)) +
      ((Fintype.orderIsoFinOfCardEq B rfl).symm ⟨i,hi⟩).val := by
  unfold essentialFreeFirstEquiv
  simp only [Equiv.trans_apply, Equiv.Set.sumCompl_symm_apply_of_mem hi]
  rfl

theorem essentialFreeFirstEquiv_free_before (B : Set (Fin n))
    (i j : Fin n) (hi : i ∉ B) (hj : j ∈ B) :
    essentialFreeFirstEquiv B i < essentialFreeFirstEquiv B j := by
  apply Fin.lt_def.mpr
  rw [essentialFreeFirst_val_free B i hi, essentialFreeFirst_val_block B j hj]
  have h := ((Fintype.orderIsoFinOfCardEq (↥(Bᶜ)) rfl).symm ⟨i,hi⟩).isLt
  omega

theorem essentialFreeFirstEquiv_block_order (B : Set (Fin n))
    (i j : Fin n) (hi : i ∈ B) (hj : j ∈ B) (hij : i < j) :
    essentialFreeFirstEquiv B i < essentialFreeFirstEquiv B j := by
  apply Fin.lt_def.mpr
  rw [essentialFreeFirst_val_block B i hi, essentialFreeFirst_val_block B j hj]
  exact Nat.add_lt_add_left
    ((Fintype.orderIsoFinOfCardEq B rfl).symm.strictMono (show (⟨i,hi⟩ : B) < ⟨j,hj⟩ from hij)) _

theorem essentialFreeFirstEquiv_free_order (B : Set (Fin n))
    (i j : Fin n) (hi : i ∉ B) (hj : j ∉ B) (hij : i < j) :
    essentialFreeFirstEquiv B i < essentialFreeFirstEquiv B j := by
  apply Fin.lt_def.mpr
  rw [essentialFreeFirst_val_free B i hi, essentialFreeFirst_val_free B j hj]
  exact (Fintype.orderIsoFinOfCardEq (↥(Bᶜ)) rfl).symm.strictMono (show (⟨i,hi⟩ : (↥(Bᶜ))) < ⟨j,hj⟩ from hij)

/-- The entire essential block is a true terminal coordinate block. -/
theorem essentialFreeFirstEquiv_block_image (B : Set (Fin n)) :
    essentialFreeFirstEquiv B '' B = {i | Fintype.card (↥(Bᶜ)) ≤ i.val} := by
  ext i
  constructor
  · rintro ⟨j,hj,rfl⟩
    change Fintype.card (↥(Bᶜ)) ≤ (essentialFreeFirstEquiv B j).val
    rw [essentialFreeFirst_val_block B j hj]
    omega
  · intro hi
    let j := (essentialFreeFirstEquiv B).symm i
    have hj : j ∈ B := by
      by_contra h
      have hv := essentialFreeFirst_val_free B j h
      have hlt := ((Fintype.orderIsoFinOfCardEq (↥(Bᶜ)) rfl).symm ⟨j,h⟩).isLt
      have he : essentialFreeFirstEquiv B j = i := (essentialFreeFirstEquiv B).apply_symm_apply i
      rw [he] at hv
      change Fintype.card (↥(Bᶜ)) ≤ i.val at hi
      omega
    exact ⟨j,hj,(essentialFreeFirstEquiv B).apply_symm_apply i⟩

/-- Comparisons are preserved FROM a block-supported head, not for arbitrary heads. -/
theorem essentialPriority_strict_of_supported_head (B : Set (Fin n))
    (a β : Fin n →₀ ℕ) (ha : ∀ i ∉ B, a i = 0)
    (h : MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn β) :
    MonomialOrder.degLex.toSyn (Finsupp.domCongr (essentialFreeFirstEquiv B) a) <
      MonomialOrder.degLex.toSyn (Finsupp.domCongr (essentialFreeFirstEquiv B) β) := by
  let p := essentialFreeFirstEquiv B
  have hd (α : Fin n →₀ ℕ) : Finsupp.degree (Finsupp.domCongr (essentialFreeFirstEquiv B) α) = Finsupp.degree α := by
    simpa only [normalExponentDegree, ← Finsupp.degree_eq_sum] using sourceExponentPermutation_degree p α
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  rcases Finsupp.DegLex.lt_iff.mp (MonomialOrder.degLex_lt_iff.mp h) with hdegree | ⟨hdegree,hlex⟩
  · left
    simpa only [ofDegLex_toDegLex,hd] using hdegree
  · right
    refine ⟨by simpa only [ofDegLex_toDegLex,hd] using hdegree, ?_⟩
    apply Finsupp.Lex.lt_iff.mpr
    by_cases hβ : ∀ i ∉ B, β i = 0
    · obtain ⟨j,hbefore,hj⟩ := Finsupp.Lex.lt_iff.mp hlex
      simp only [ofDegLex_toDegLex,ofLex_toLex] at hbefore hj
      have hjB : j ∈ B := by
        by_contra h
        rw [ha j h,hβ j h] at hj
        exact (lt_irrefl 0) hj
      refine ⟨p j, ?_, ?_⟩
      · intro i hi
        let l := p.symm i
        have hpl : p l = i := p.apply_symm_apply i
        by_cases hl : l ∈ B
        · have hlj : l < j := by
            rcases lt_trichotomy l j with hlt | he | hgt
            · exact hlt
            · rw [he] at hpl
              exact False.elim ((ne_of_lt hi) hpl.symm)
            · have hp : p j < p l := essentialFreeFirstEquiv_block_order B j l hjB hl hgt
              rw [hpl] at hp
              exact False.elim (lt_asymm hi hp)
          simpa only [ofDegLex_toDegLex,ofLex_toLex,sourceExponentPermutation_apply] using hbefore l hlj
        · simp only [ofDegLex_toDegLex,ofLex_toLex,sourceExponentPermutation_apply]
          exact (ha l hl).trans (hβ l hl).symm
      · simpa only [ofDegLex_toDegLex,ofLex_toLex,sourceExponentPermutation_apply, p,
          Equiv.symm_apply_apply] using hj
    · push Not at hβ
      obtain ⟨i,hi,hβi⟩ := hβ
      let T : Finset (Fin n) := Finset.univ.filter (fun i => i ∉ B ∧ β i ≠ 0)
      have hT : T.Nonempty := ⟨i,by simp only [T,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hi,hβi⟩⟩
      obtain ⟨j,hj,hmin⟩ := T.exists_min_image p hT
      have hj' : j ∉ B ∧ β j ≠ 0 := by
        simpa only [T,Finset.mem_filter,Finset.mem_univ,true_and] using hj
      refine ⟨p j, ?_, ?_⟩
      · intro i hi
        let l := p.symm i
        have hpl : p l = i := p.apply_symm_apply i
        have hl : l ∉ B := by
          intro hl
          have hp : p j < p l := essentialFreeFirstEquiv_free_before B j l hj'.1 hl
          rw [hpl] at hp
          exact lt_asymm hi hp
        have hβl : β l = 0 := by
          by_contra hn
          have hlT : l ∈ T := by simp only [T,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hl,hn⟩
          have hm := hmin l hlT
          rw [hpl] at hm
          exact (not_le_of_gt hi) hm
        simp only [ofDegLex_toDegLex,ofLex_toLex,sourceExponentPermutation_apply]
        exact (ha l hl).trans hβl.symm
      · simpa only [ofDegLex_toDegLex,ofLex_toLex,sourceExponentPermutation_apply, p,
          Equiv.symm_apply_apply,ha j hj'.1] using Nat.pos_of_ne_zero hj'.2

variable {K : Ideal (MvPowerSeries (Fin n) ℂ)}

/-- The whole essential set is exactly a saturated genuine degree-prefix block. -/
theorem sourceEssential_eq_max_prefix (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K) =
      actualDegreePrefixVariables MonomialOrder.degLex K
        ((actualInitialVertices MonomialOrder.degLex K).sup normalExponentDegree) := by
  ext j
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Finset.le_sup a.property,ha⟩
  · rintro ⟨a,_ha,haj⟩
    exact ⟨a,haj⟩

theorem essentialPriority_family_lower (G : ActualAnalyticInheritedFamily n 0 K) :
    ∀ a γ, MonomialOrder.degLex.toSyn γ < MonomialOrder.degLex.toSyn
        (Finsupp.domCongr (essentialFreeFirstEquiv (fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K))) a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename
        (essentialFreeFirstEquiv (fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K)))
        (actualUnshiftedTaylorAlgHom n (G.germs a))) = 0 := by
  intro a
  exact (source_member_monic_of_strict_comparison _ a.val _ (G.monic a) (G.lower a)
    (fun β h => essentialPriority_strict_of_supported_head _ a.val β
      (fun i hi => by by_contra hai; exact hi ⟨a,hai⟩) h)).2

/-- The priority is internally chosen from the full actual vertex set. -/
theorem actual_initial_diagram_essentialFreeFirst (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K) :
    let p := essentialFreeFirstEquiv (fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K))
    actualInitialDiagram MonomialOrder.degLex (Ideal.map (MvPowerSeries.rename p).toRingHom K) =
      Finsupp.domCongr p '' actualInitialDiagram MonomialOrder.degLex K := by
  dsimp only
  exact actual_initial_diagram_rename_of_same_family_heads K (actualSourceFormalFamily G hmem) _
    (essentialPriority_family_lower G)

/-- Actual current presentation, all whole prefixes and historical contact data. -/
theorem actual_essentialFreeFirst_same_family_transport
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K)) :
    let B := fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K)
    let p := essentialFreeFirstEquiv B
    let G' := actualSourcePermutedInheritedFamily G hmem p (essentialPriority_family_lower G)
    let S' := actualSourcePermutedFixedSelector G hmem p (essentialPriority_family_lower G) S
    (p '' B = {i | Fintype.card (↥(Bᶜ)) ≤ i.val}) ∧
      actualInheritedCurrentSourceIdeal (Ideal.span (Set.range G'.germs)) = Ideal.map (MvPowerSeries.rename p).toRingHom K ∧
      (∀ k, ActualInheritedPrefixReducedAt G k → ActualInheritedPrefixReducedAt G' k) ∧
      (∀ k, actualFixedSelectorContactAt S G.germs k → actualFixedSelectorContactAt S' G'.germs k) ∧
      ∀ k, (actualFixedSelectorJacobian S' G'.germs k).det = (actualFixedSelectorJacobian S G.germs k).det := by
  dsimp only
  exact ⟨essentialFreeFirstEquiv_block_image _,
    actualSourcePermutedInheritedFamily_current_ideal G hmem _ _,
    actualSourcePermutedInheritedFamily_prefix_reduced G hmem _ _,
    actualSourcePermutedFixedSelector_contact G hmem _ _ S,
    actualSourcePermutedFixedSelector_jacobian_det G hmem _ _ S⟩

end
end Hironaka.HironakaActualInheritedEssentialPriority
