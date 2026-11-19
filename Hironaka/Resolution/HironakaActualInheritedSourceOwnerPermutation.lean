import Hironaka.Resolution.HironakaActualRelativeStandardnessInheritedDivision
import Hironaka.Resolution.HironakaActualFixedInheritedSelectorPermutation

/-! Whole source diagrams from the SAME owner-supported division. Renamed
quotients use their actual new heads, not renamed old quotient heads. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedSourceOwnerPermutation
noncomputable section
attribute [local instance] Classical.propDecidable
open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualRelativeStandardnessInheritedDivision HironakaActualReducedBasisDivision
variable {n : ℕ}

theorem sourceExponentPermutation_apply (p : Fin n ≃ Fin n) (α : Fin n →₀ ℕ) (i : Fin n) :
    Finsupp.domCongr p α i = α (p.symm i) := by
  simp only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.mapDomain_equiv_apply]

theorem sourceExponentPermutation_degree (p : Fin n ≃ Fin n) (α : Fin n →₀ ℕ) :
    normalExponentDegree (Finsupp.domCongr p α) = normalExponentDegree α := by
  unfold normalExponentDegree
  exact Fintype.sum_equiv p.symm _ _ (fun i => sourceExponentPermutation_apply p α i)

theorem sourceExponentPermutation_coeff (p : Fin n ≃ Fin n)
    (F : MvPowerSeries (Fin n) ℂ) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.domCongr p α) (MvPowerSeries.rename p F) =
      MvPowerSeries.coeff α F := by
  simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding] using
    MvPowerSeries.coeff_embDomain_rename p.toEmbedding F α

theorem sourceExponentPermutation_le_iff (p : Fin n ≃ Fin n) (α β : Fin n →₀ ℕ) :
    Finsupp.domCongr p α ≤ Finsupp.domCongr p β ↔ α ≤ β := by
  constructor
  · intro h i
    have hi := h (p i)
    simpa only [sourceExponentPermutation_apply, Equiv.symm_apply_apply] using hi
  · intro h i
    simp only [sourceExponentPermutation_apply]
    exact h (p.symm i)

/-- The actual SAME renamed member head follows from its actual lower coefficients. -/
theorem renamed_same_member_initial
    (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily MonomialOrder.degLex K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (B.series a)) = 0)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    ∃ h : MvPowerSeries.rename p (B.series a) ≠ 0,
      actualInitialExponent MonomialOrder.degLex (MvPowerSeries.rename p (B.series a)) h =
        Finsupp.domCongr p a.val := by
  have hc : MvPowerSeries.coeff (Finsupp.domCongr p a.val)
      (MvPowerSeries.rename p (B.series a)) = 1 := by
    rw [sourceExponentPermutation_coeff, B.monic]
  have h : MvPowerSeries.rename p (B.series a) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    exact zero_ne_one hc
  exact ⟨h, actualInitialExponent_eq_of_coefficients MonomialOrder.degLex _ h _
    (by rw [hc]; exact one_ne_zero) (hlower a)⟩

private theorem strict_minimum_initial_sum {ι : Type*} [Fintype ι]
    (P : ι → MvPowerSeries (Fin n) ℂ) (a : ι) (ha : P a ≠ 0)
    (hmin : ∀ b, b ≠ a → ∀ hb : P b ≠ 0,
      MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P a) ha) <
        MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P b) hb)) :
    ∃ hs : (∑ b, P b) ≠ 0,
      actualInitialExponent MonomialOrder.degLex (∑ b, P b) hs =
        actualInitialExponent MonomialOrder.degLex (P a) ha := by
  let α := actualInitialExponent MonomialOrder.degLex (P a) ha
  have hc : MvPowerSeries.coeff α (∑ b, P b) = MvPowerSeries.coeff α (P a) := by
    rw [map_sum]
    apply Finset.sum_eq_single a
    · intro b _ hba
      by_cases hb : P b = 0
      · rw [hb, map_zero]
      · exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex (P b) hb α (hmin b hba hb)
    · intro h
      exact (h (Finset.mem_univ a)).elim
  have hl : ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn α →
      MvPowerSeries.coeff β (∑ b, P b) = 0 := by
    intro β hβ
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : P b = 0
    · rw [hb, map_zero]
    · by_cases hba : b = a
      · subst b
        exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex (P a) ha β hβ
      · exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex (P b) hb β
          (lt_trans hβ (hmin b hba hb))
  have hs : (∑ b, P b) ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    exact (actualInitialExponent_spec MonomialOrder.degLex (P a) ha).1 hc.symm
  refine ⟨hs, actualInitialExponent_eq_of_coefficients MonomialOrder.degLex _ hs α ?_ hl⟩
  rw [hc]
  exact (actualInitialExponent_spec MonomialOrder.degLex (P a) ha).1

private theorem distinct_initial_sum {ι : Type*} [Fintype ι]
    (P : ι → MvPowerSeries (Fin n) ℂ) (hs : (∑ a, P a) ≠ 0)
    (hd : ∀ a b, a ≠ b → ∀ ha : P a ≠ 0, ∀ hb : P b ≠ 0,
      actualInitialExponent MonomialOrder.degLex (P a) ha ≠
        actualInitialExponent MonomialOrder.degLex (P b) hb) :
    ∃ a, ∃ ha : P a ≠ 0,
      actualInitialExponent MonomialOrder.degLex (∑ b, P b) hs =
        actualInitialExponent MonomialOrder.degLex (P a) ha := by
  have hsome : ∃ a, P a ≠ 0 := by
    by_contra h
    push Not at h
    exact hs (by simp only [h, Finset.sum_const_zero])
  let T := {a : ι // P a ≠ 0}
  let : Fintype T := Fintype.ofFinite T
  have hT : (Finset.univ : Finset T).Nonempty := by
    obtain ⟨a, ha⟩ := hsome
    exact ⟨⟨a, ha⟩, Finset.mem_univ _⟩
  let w (a : T) := MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P a.val) a.property)
  obtain ⟨a, _ha, hmin⟩ := (Finset.univ : Finset T).exists_min_image w hT
  have hstrict : ∀ b, b ≠ a.val → ∀ hb : P b ≠ 0,
      MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P a.val) a.property) <
        MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex (P b) hb) := by
    intro b hba hb
    apply lt_of_le_of_ne (hmin (⟨b, hb⟩ : T) (Finset.mem_univ _))
    intro he
    exact hd a.val b hba.symm a.property hb (MonomialOrder.degLex.toSyn.injective he)
  obtain ⟨hs', hhead⟩ := strict_minimum_initial_sum P a.val a.property hstrict
  exact ⟨a.val, a.property, hhead⟩

/-- Each product uses the actual NEW quotient head. Only old owner support is reused. -/
theorem actual_renamed_member_initial_from_owner
    (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily MonomialOrder.degLex K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (B.series a)) = 0)
    (F : MvPowerSeries (Fin n) ℂ) (hFK : F ∈ K) (hne : F ≠ 0) :
    let B0 : InheritedMonicFamily MonomialOrder.degLex K :=
      { series := B.series, monic := B.monic, lower := B.lower }
    ∃ a : actualInitialVertices MonomialOrder.degLex K, ∃ β : Fin n →₀ ℕ,
      MvPowerSeries.coeff β (inheritedFormalQuotient MonomialOrder.degLex K B0 F a) ≠ 0 ∧
      inheritedDivisionOwner MonomialOrder.degLex K (β + a.val) = some a ∧
        ∃ hσ : MvPowerSeries.rename p F ≠ 0,
          actualInitialExponent MonomialOrder.degLex (MvPowerSeries.rename p F) hσ =
            Finsupp.domCongr p (β + a.val) := by
  let σ := MvPowerSeries.rename (R := ℂ) p
  let E : (Fin n →₀ ℕ) ≃+ (Fin n →₀ ℕ) := Finsupp.domCongr p
  let B0 : InheritedMonicFamily MonomialOrder.degLex K :=
    { series := B.series, monic := B.monic, lower := B.lower }
  let Q := inheritedFormalQuotient MonomialOrder.degLex K B0 F
  obtain ⟨hdiv, hsupport⟩ := inherited_formal_ideal_member_division
    MonomialOrder.degLex K B0 K rfl B.mem F hFK
  let P (a : actualInitialVertices MonomialOrder.degLex K) := σ (Q a) * σ (B.series a)
  have hsum : (∑ a, P a) = σ F := by
    rw [hdiv]
    simp only [map_sum, map_mul, P, Q, B0]
  have hσF : σ F ≠ 0 := by
    intro hz
    exact hne ((MvPowerSeries.renameEquiv ℂ p).injective (hz.trans (map_zero _).symm))
  have hP (a : actualInitialVertices MonomialOrder.degLex K) (ha : P a ≠ 0) :
      ∃ β : Fin n →₀ ℕ, MvPowerSeries.coeff β (Q a) ≠ 0 ∧
        actualInitialExponent MonomialOrder.degLex (P a) ha = E (β + a.val) := by
    have hq : σ (Q a) ≠ 0 := by
      intro hz
      exact ha (by simp only [P, hz, zero_mul])
    let γ := actualInitialExponent MonomialOrder.degLex (σ (Q a)) hq
    let β := E.symm γ
    have hEβ : E β = γ := E.apply_symm_apply γ
    have hβ : MvPowerSeries.coeff β (Q a) ≠ 0 := by
      have hc := sourceExponentPermutation_coeff p (Q a) β
      change MvPowerSeries.coeff (E β) (σ (Q a)) = _ at hc
      rw [hEβ] at hc
      rw [← hc]
      exact (actualInitialExponent_spec MonomialOrder.degLex (σ (Q a)) hq).1
    obtain ⟨hg, heg⟩ := renamed_same_member_initial K B p hlower a
    refine ⟨β, hβ, ?_⟩
    rw [actualInitialExponent_mul MonomialOrder.degLex _ _ hq hg, heg]
    change γ + E a.val = E (β + a.val)
    rw [map_add, hEβ]
  have hdistinct : ∀ a b, a ≠ b → ∀ ha : P a ≠ 0, ∀ hb : P b ≠ 0,
      actualInitialExponent MonomialOrder.degLex (P a) ha ≠
        actualInitialExponent MonomialOrder.degLex (P b) hb := by
    intro a b hab ha hb he
    obtain ⟨β, hβ, hpβ⟩ := hP a ha
    obtain ⟨γ, hγ, hpγ⟩ := hP b hb
    rw [hpβ, hpγ] at he
    have hδ := E.injective he
    have hoa := hsupport a β hβ
    have hob := hsupport b γ hγ
    rw [hδ, hob] at hoa
    exact hab (Option.some.inj hoa.symm)
  have hsumne : (∑ a, P a) ≠ 0 := by rw [hsum]; exact hσF
  obtain ⟨a, ha, hhead⟩ := distinct_initial_sum P hsumne hdistinct
  obtain ⟨β, hβ, hPa⟩ := hP a ha
  have hσhead : actualInitialExponent MonomialOrder.degLex (σ F) hσF = E (β + a.val) := by
    have hsame : actualInitialExponent MonomialOrder.degLex (σ F) hσF =
        actualInitialExponent MonomialOrder.degLex (∑ a, P a) hsumne := by
      congr 1
      exact hsum.symm
    exact hsame.trans (hhead.trans hPa)
  exact ⟨a, β, hβ, hsupport a β hβ, hσF, hσhead⟩

/-- A whole mapped SOURCE diagram, produced from actual full supported division. -/
theorem actual_initial_diagram_rename_of_same_family_heads
    (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : ActualMonicVertexFamily MonomialOrder.degLex K) (p : Fin n ≃ Fin n)
    (hlower : ∀ a γ, MonomialOrder.degLex.toSyn γ <
        MonomialOrder.degLex.toSyn (Finsupp.domCongr p a.val) →
      MvPowerSeries.coeff γ (MvPowerSeries.rename p (B.series a)) = 0) :
    actualInitialDiagram MonomialOrder.degLex (Ideal.map (MvPowerSeries.rename p).toRingHom K) =
      Finsupp.domCongr p '' actualInitialDiagram MonomialOrder.degLex K := by
  apply le_antisymm
  · rintro α ⟨F, hF, hne, hα⟩
    obtain ⟨F, hFK, rfl⟩ := (Ideal.mem_map_iff_of_surjective (MvPowerSeries.rename p).toRingHom
      (MvPowerSeries.renameEquiv ℂ p).surjective).mp hF
    have hFne : F ≠ 0 := by
      intro hz
      exact hne (by rw [hz, map_zero])
    obtain ⟨a, β, _hquotient, _howner, hσ, hhead⟩ :=
      actual_renamed_member_initial_from_owner K B p hlower F hFK hFne
    refine ⟨β + a.val, ?_, hhead.symm.trans hα⟩
    apply (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K _).mpr
    refine ⟨a.val, a.property, ?_⟩
    intro i
    simp only [Finsupp.add_apply]
    omega
  · rintro α ⟨γ, hγ, rfl⟩
    obtain ⟨a, ha, hle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K γ).mp hγ
    let v : actualInitialVertices MonomialOrder.degLex K := ⟨a, ha⟩
    obtain ⟨hg, hhead⟩ := renamed_same_member_initial K B p hlower v
    apply actualInitialDiagram_upper MonomialOrder.degLex _ (Finsupp.domCongr p a)
      (Finsupp.domCongr p γ)
      ⟨MvPowerSeries.rename p (B.series v), Ideal.mem_map_of_mem _ (B.mem v), hg, hhead⟩
    exact (sourceExponentPermutation_le_iff p a γ).mpr hle

end
end Hironaka.HironakaActualInheritedSourceOwnerPermutation
