import Hironaka.Resolution.HironakaActualCanonicalPointDirectionOrder
import Hironaka.Resolution.HironakaActualPointNormalizedExponents
import Hironaka.Resolution.HironakaActualRelativeStandardnessPointRename

/-!
# Inherited heads at a first-priority point pivot

Coordinate zero is the largest variable in mathlib's degree-first lexicographic
order. The pivot restriction is essential: an arbitrary old coordinate order
need not retain its diagram after a point blowup with unchanged HS function.
The actual cylindrical-pivot promotion is a separate coordinate dictionary.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualRelativeStandardnessPointLeadingDiagram

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalStandardMonomialHS
  HironakaActualReducedFormalStandardBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalStrictGenerators
  HironakaActualCoefficientReducedStrictGenerators HironakaActualPointCentreStrictGenerators
  HironakaActualPointNormalizedExponents HironakaActualCanonicalPointDirectionOrder
  HironakaActualRelativeStandardnessPivotPriority HironakaActualRelativeStandardnessPointRename

variable {n : ℕ}

private theorem degree_split (e : Fin n) (α : Fin n →₀ ℕ) :
    normalExponentDegree α = α e + normalExponentDegree (α.erase e) := by
  have he : Finsupp.single e (α e) + α.erase e = α := by
    ext i
    by_cases hi : i = e
    · subst i
      simp
    · simp [hi]
  have h := (congrArg normalExponentDegree he).symm
  simpa only [normalExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib,
    ← Finsupp.degree_eq_sum, Finsupp.degree_single] using h

/-- Genuine bounded complement inclusion and all actual HS dimensions detect
the whole diagram; the underlying ideals need not be included. -/
theorem actualInitialDiagram_eq_of_subset_of_hs_eq
    (I J : Ideal (MvPowerSeries (Fin n) ℂ))
    (hIJ : actualInitialDiagram MonomialOrder.degLex I ⊆
      actualInitialDiagram MonomialOrder.degLex J)
    (hHS : ∀ q, genuineFormalHilbertSamuelValue n J q = genuineFormalHilbertSamuelValue n I q) :
    actualInitialDiagram MonomialOrder.degLex J = actualInitialDiagram MonomialOrder.degLex I := by
  apply le_antisymm ?_ hIJ
  intro α hαJ
  by_contra hαI
  let q := normalExponentDegree α
  let f : actualStandardIndex n J (q + 1) → actualStandardIndex n I (q + 1) :=
    fun a => ⟨a.val, fun h => a.property (hIJ h)⟩
  have hf : Function.Injective f := by
    intro a b h
    have hv := congrArg (fun c : actualStandardIndex n I (q + 1) => c.val) h
    change a.val = b.val at hv
    exact Subtype.ext hv
  have hcard : Fintype.card (actualStandardIndex n J (q + 1)) =
      Fintype.card (actualStandardIndex n I (q + 1)) := by
    rw [← genuineFormalHilbertSamuelValue_eq_card_standardIndex J q,
      ← genuineFormalHilbertSamuelValue_eq_card_standardIndex I q]
    exact hHS q
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩).2
  let a : actualStandardIndex n I (q + 1) := ⟨⟨α, Nat.lt_succ_self _⟩, hαI⟩
  obtain ⟨b, hb⟩ := hsurj a
  have hβα : b.val.val = α := congrArg (fun c : actualStandardIndex n I (q + 1) => c.val.val) hb
  exact b.property (by rwa [hβα])

variable {n : ℕ}

/-- A genuine first-priority point normalization with its original marked order
has the SAME actual monic head. No claim for an arbitrary pivot is made. -/
theorem actualNormalizedFormalMember_first_pivot_monic
    (F : MvPowerSeries (Fin (n + 1)) ℂ) (a : Fin (n + 1) →₀ ℕ)
    (ha0 : a 0 = 0) (hc : MvPowerSeries.coeff a F = 1)
    (hlower : ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a →
      MvPowerSeries.coeff β F = 0)
    (hF : F ∈ actualFormalCoordinateIdeal (n + 1) Set.univ ^ normalExponentDegree a)
    (horder : actualNormalizedFormalMember Set.univ 0 (mem_univ 0) (fun _ => 0)
      (normalExponentDegree a) F hF ∈ genuineFormalVariables (n + 1) ^ normalExponentDegree a) :
    MvPowerSeries.coeff a (actualNormalizedFormalMember Set.univ 0 (mem_univ 0) (fun _ => 0)
      (normalExponentDegree a) F hF) = 1 ∧
      ∀ γ, MonomialOrder.degLex.toSyn γ < MonomialOrder.degLex.toSyn a →
        MvPowerSeries.coeff γ (actualNormalizedFormalMember Set.univ 0 (mem_univ 0) (fun _ => 0)
          (normalExponentDegree a) F hF) = 0 := by
  let μ := normalExponentDegree a
  let H := actualNormalizedFormalMember Set.univ 0 (mem_univ 0) (fun _ => 0) μ F hF
  have hmap : actualPointNormalizedExponent 0 μ a = a := by
    simp only [actualPointNormalizedExponent, μ, Nat.sub_self, Finsupp.single_zero, add_zero]
    exact Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr ha0)
  constructor
  · have h := actualNormalizedFormalMember_zero_coefficient 0 μ F hF a le_rfl
    rw [hmap, hc] at h
    exact h
  · intro γ hγ
    by_contra hne
    have hle : normalExponentDegree γ ≤ μ := actual_degree_le_of_deglex_lt γ a hγ
    have hge : μ ≤ normalExponentDegree γ := by
      by_contra h
      exact hne ((mem_genuineFormalVariables_pow_iff_coefficients_zero (n + 1) μ H).mp
        horder γ (lt_of_not_ge h))
    have hdegree : normalExponentDegree γ = μ := le_antisymm hle hge
    have hγ0 : γ 0 = 0 := by
      by_contra h
      have hpos : 0 < γ 0 := Nat.pos_of_ne_zero h
      have hlt : MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn γ := by
        apply MonomialOrder.degLex_lt_iff.mpr
        apply Finsupp.DegLex.lt_iff.mpr
        right
        refine ⟨?_, ?_⟩
        · simpa only [μ, ofDegLex_toDegLex, Finsupp.degree_eq_sum, normalExponentDegree] using hdegree.symm
        · apply Finsupp.Lex.lt_iff.mpr
          refine ⟨0, fun i hi => False.elim ((not_lt_of_ge (Fin.zero_le i)) hi), ?_⟩
          simpa only [ofLex_toLex, ofDegLex_toDegLex, ha0] using hpos
      exact (not_lt_of_ge hlt.le) hγ
    obtain ⟨β, ⟨hβγ, hcoeff⟩, _⟩ :=
      exists_unique_original_exponent_of_normalized_coefficient_ne_zero 0 μ F hF γ hne
    have hβdeg : normalExponentDegree β.val = μ := by
      have h := congrArg (fun δ : Fin (n + 1) →₀ ℕ => δ 0) hβγ
      rw [actualPointNormalizedExponent_exceptional, hγ0] at h
      have hbound := β.property
      omega
    have herase : β.val.erase 0 = γ := by
      simpa only [actualPointNormalizedExponent, hβdeg, Nat.sub_self,
        Finsupp.single_zero, add_zero] using hβγ
    have hβ0 : β.val 0 = 0 := by
      have hsplit := degree_split 0 β.val
      rw [herase, hdegree, hβdeg] at hsplit
      omega
    have hβeq : β.val = γ :=
      (Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr hβ0)).symm.trans herase
    have hzero : MvPowerSeries.coeff β.val F = 0 := hlower β.val (by rwa [hβeq])
    exact hne (hcoeff.symm.trans hzero)

private theorem point_weight_eq_degree (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight Set.univ) α = normalExponentDegree α := by
  simp only [Finsupp.weight_eq_sum, actualCoordinateWeight, Set.mem_univ,
    if_true, smul_eq_mul, mul_one, normalExponentDegree]

private theorem normalized_point_member_congr_degree
    (e : Fin n) (μ ν : ℕ) (hμν : μ = ν) (F : MvPowerSeries (Fin n) ℂ)
    (hμ : F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ)
    (hν : F ∈ actualFormalCoordinateIdeal n Set.univ ^ ν) :
    actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) μ F hμ =
      actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) ν F hν := by
  subst ν
  rfl

/-- Whole genuine HS equality supplies the required marked orders internally;
all SAME canonical normalized members retain their heads at the first pivot. -/
theorem actualNormalizedReducedFormalVertex_first_pivot_monic_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val 0 = 0)
    (hHS : ∀ q, genuineFormalHilbertSamuelValue (n + 1)
      (actualFormalStrictTransform K Set.univ 0 (mem_univ 0) (fun _ => 0)) q =
        genuineFormalHilbertSamuelValue (n + 1) K q)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    let H := actualNormalizedReducedFormalVertex MonomialOrder.degLex K Set.univ 0
      (mem_univ 0) (fun _ => 0) (actualReducedVertexSeries_mem_point_power (n + 1) K) a
    MvPowerSeries.coeff a.val H = 1 ∧
      ∀ γ, MonomialOrder.degLex.toSyn γ < MonomialOrder.degLex.toSyn a.val →
        MvPowerSeries.coeff γ H = 0 := by
  have hpow := actualReducedVertexSeries_mem_point_power (n + 1) K a
  have horder := actualNormalizedReducedFormalVertex_mem_degree_power_of_point_hs_eq
    K 0 (fun _ => 0) hHS a
  simp only [point_weight_eq_degree] at hpow
  simp only [actualNormalizedReducedFormalVertex] at horder
  have hNorm := normalized_point_member_congr_degree (0 : Fin (n + 1))
    (Finsupp.weight (actualCoordinateWeight Set.univ) a.val) (normalExponentDegree a.val)
    (point_weight_eq_degree a.val) (actualReducedVertexSeries MonomialOrder.degLex K a)
    (actualReducedVertexSeries_mem_point_power (n + 1) K a) hpow
  rw [hNorm] at horder
  dsimp only [actualNormalizedReducedFormalVertex]
  rw [hNorm]
  exact actualNormalizedFormalMember_first_pivot_monic (actualReducedVertexSeries MonomialOrder.degLex K a)
    a.val (hv a) (actualReducedVertexSeries_coefficient MonomialOrder.degLex K a)
    (actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex K a) hpow horder

/-- The actual SAME inherited heads give one whole diagram inclusion, and the
true all-order HS equality gives the other by finite complement cardinalities. -/
theorem actualInitialDiagram_point_strict_eq_of_first_pivot_hs_eq
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val 0 = 0)
    (hHS : ∀ q, genuineFormalHilbertSamuelValue (n + 1)
      (actualFormalStrictTransform K Set.univ 0 (mem_univ 0) (fun _ => 0)) q =
        genuineFormalHilbertSamuelValue (n + 1) K q) :
    actualInitialDiagram MonomialOrder.degLex
      (actualFormalStrictTransform K Set.univ 0 (mem_univ 0) (fun _ => 0)) =
        actualInitialDiagram MonomialOrder.degLex K := by
  apply actualInitialDiagram_eq_of_subset_of_hs_eq K _ ?_ hHS
  intro α hα
  obtain ⟨a, ha, hle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K α).mp hα
  let v : actualInitialVertices MonomialOrder.degLex K := ⟨a, ha⟩
  let H := actualNormalizedReducedFormalVertex MonomialOrder.degLex K Set.univ 0
    (mem_univ 0) (fun _ => 0) (actualReducedVertexSeries_mem_point_power (n + 1) K) v
  have hm := actualNormalizedReducedFormalVertex_first_pivot_monic_of_hs_eq K hv hHS v
  have hne : H ≠ 0 := by
    intro h
    have hc := hm.1
    change MvPowerSeries.coeff v.val H = 1 at hc
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  have hmem : H ∈ actualFormalStrictTransform K Set.univ 0 (mem_univ 0) (fun _ => 0) := by
    rw [actualFormalStrictTransform_eq_reduced_vertex_span MonomialOrder.degLex K Set.univ 0
      (mem_univ 0) (fun _ => 0) (actualReducedVertexSeries_mem_point_power (n + 1) K)]
    exact Ideal.subset_span ⟨v, rfl⟩
  have hinitial : actualInitialExponent MonomialOrder.degLex H hne = a :=
    actualInitialExponent_eq_of_coefficients MonomialOrder.degLex H hne a
      (by rw [hm.1]; exact one_ne_zero) hm.2
  exact actualInitialDiagram_upper MonomialOrder.degLex _ a α ⟨H, hmem, hne, hinitial⟩ hle

/-- An actual cylindrical original point chart produces the promoted SAME-family
membership, monic heads and whole diagram equality. The promoted HS equality
and normalized marked orders are derived internally from the original one. -/
theorem actualPivotFirstInheritedFamily_monic_diagram_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (f : Fin (n + 1))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0)
    (hHS : ∀ q, genuineFormalHilbertSamuelValue (n + 1)
      (actualFormalStrictTransform K Set.univ f (mem_univ f) (fun _ => 0)) q =
        genuineFormalHilbertSamuelValue (n + 1) K q) :
    let Kp := Ideal.map (pivotFirstRename f).toRingHom K
    let Jp := actualFormalStrictTransform Kp Set.univ 0 (mem_univ 0) (fun _ => 0)
    (∀ a : actualInitialVertices MonomialOrder.degLex Kp,
      let H := actualNormalizedReducedFormalVertex MonomialOrder.degLex Kp Set.univ 0
        (mem_univ 0) (fun _ => 0) (actualReducedVertexSeries_mem_point_power (n + 1) Kp) a
      H ∈ Jp ∧ MvPowerSeries.coeff a.val H = 1 ∧
        ∀ γ, MonomialOrder.degLex.toSyn γ < MonomialOrder.degLex.toSyn a.val →
          MvPowerSeries.coeff γ H = 0) ∧
      actualInitialDiagram MonomialOrder.degLex Jp = actualInitialDiagram MonomialOrder.degLex Kp := by
  let Kp := Ideal.map (pivotFirstRename f).toRingHom K
  have hvp : ∀ a : actualInitialVertices MonomialOrder.degLex Kp, a.val 0 = 0 := by
    intro a
    obtain ⟨b, rfl⟩ := pivotFirstVertex_surjective K f hv a
    exact pivotFirstVertex_zero K f hv b
  have hHSp := point_strict_hs_eq_after_pivotFirst K f hHS
  refine ⟨?_, actualInitialDiagram_point_strict_eq_of_first_pivot_hs_eq Kp hvp hHSp⟩
  intro a
  refine ⟨?_, actualNormalizedReducedFormalVertex_first_pivot_monic_of_hs_eq Kp hvp hHSp a⟩
  rw [actualFormalStrictTransform_eq_reduced_vertex_span MonomialOrder.degLex Kp Set.univ 0
    (mem_univ 0) (fun _ => 0) (actualReducedVertexSeries_mem_point_power (n + 1) Kp)]
  exact Ideal.subset_span ⟨a, rfl⟩

end

end Hironaka.HironakaActualRelativeStandardnessPointLeadingDiagram
