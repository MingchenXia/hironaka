import Hironaka.Resolution.HironakaActualInheritedNextBlockGraph
import Hironaka.Resolution.HironakaActualAnalyticFormalNormalPowers

/-! The SAME internally solved next graph preserves an already flattened
normal centre. Source marked normal powers force every selected equation to
vanish along that centre. The actual inverse law then forces the extracted
graph to vanish there. No new centre flattening or canonical reduction is
chosen, and no conclusion about a future marked order is supplied as input. -/

set_option autoImplicit false
open Set Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualInheritedNextBlockCentreGraph

noncomputable section

open HolGerm OkaRelationSheaf HironakaHolomorphicJetMonomialSpan
  HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
  HironakaActualInheritedNextBlockGraph HironakaActualAnalyticBlockGraphTranslation
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualCanonicalBlockJacobian
  HironakaActualRelativeNormalJetDivision HironakaActualRelativeStandardnessBlockSupport
  HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualAnalyticFormalNormalPowers HironakaHolomorphicJetChartInvariance

variable {n : ℕ} {K : Ideal (MvPowerSeries (Fin n) ℂ)}

private theorem coordinate_weight_le_degree (A : Set (Fin n)) (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight A) α ≤ normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum, normalExponentDegree]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ A <;> simp [actualCoordinateWeight, hi]

private theorem coordinate_weight_sum_compl (A : Set (Fin n)) (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight A) α +
      Finsupp.weight (actualCoordinateWeight Aᶜ) α = normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ A <;> simp [actualCoordinateWeight, hi]

private theorem coordinate_outside_le_compl_weight (A : Set (Fin n))
    (α : Fin n →₀ ℕ) (i : Fin n) (hi : i ∉ A) :
    α i ≤ Finsupp.weight (actualCoordinateWeight Aᶜ) α := by
  rw [Finsupp.weight_eq_sum]
  have h := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (α j • actualCoordinateWeight Aᶜ j))
    (Finset.mem_univ i)
  simpa only [actualCoordinateWeight, Set.mem_compl_iff, if_pos hi, smul_eq_mul, mul_one] using h

private theorem actualTaylor_mem_coordinate_power
    (A : Set (Fin n)) (q : ℕ) (F : HolGerm (ComplexModel n))
    (hF : F ∈ actualAnalyticCoordinateBlockIdeal A ^ q) :
    actualUnshiftedTaylorAlgHom n F ∈ actualFormalCoordinateIdeal n A ^ q := by
  rw [← map_actualAnalyticCoordinateBlockIdeal_actualTaylor, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hF

private theorem coordinate_ideal_of_actualTaylor
    (A : Set (Fin n)) (F : HolGerm (ComplexModel n))
    (hF : actualUnshiftedTaylorAlgHom n F ∈ actualFormalCoordinateIdeal n A) :
    F ∈ actualAnalyticCoordinateBlockIdeal A := by
  apply (mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero A F).mpr
  apply actualUnshiftedTaylorAlgHom_injective n
  rw [map_zero]
  have hT := congrArg
    (fun f : HolGerm (ComplexModel n) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ => f F)
    (actualTaylor_blockProjection Aᶜ)
  change actualUnshiftedTaylorAlgHom n (actualBlockProjectionGermHom Aᶜ F) =
    actualFormalBlockCoordinateProjection Aᶜ (actualUnshiftedTaylorAlgHom n F) at hT
  change actualUnshiftedTaylorAlgHom n (actualBlockProjectionGermHom Aᶜ F) = 0
  rw [hT]
  apply MvPowerSeries.ext
  intro α
  rw [coeff_actualFormalBlockCoordinateProjection, map_zero]
  by_cases hα : ∀ i ∉ Aᶜ, α i = 0
  · rw [if_pos hα]
    have hw : Finsupp.weight (actualCoordinateWeight A) α = 0 := by
      rw [Finsupp.weight_eq_sum]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i ∈ A
      · rw [hα i (by simpa using hi), zero_smul]
      · simp [actualCoordinateWeight, hi]
    apply (mem_actualFormalCoordinateIdeal_pow_iff A 1 _).mp (by simpa using hF) α
    omega
  · rw [if_neg hα]

/-- Every actual source head is forced to be supported in the same normal
centre by its monic coefficient and actual marked normal-power membership. -/
theorem actualDegreePrefixVariables_subset_of_normal_powers
    (G : ActualAnalyticInheritedFamily n 0 K) (A : Set (Fin n))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateBlockIdeal A ^ normalExponentDegree a.val)
    (k : ℕ) : actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A := by
  intro i hi
  obtain ⟨a, _hak, hai⟩ := hi
  by_contra hiA
  have hTa := actualTaylor_mem_coordinate_power A (normalExponentDegree a.val) (G.germs a) (hpower a)
  have hw : normalExponentDegree a.val ≤ Finsupp.weight (actualCoordinateWeight A) a.val := by
    by_contra hnot
    have hc := (mem_actualFormalCoordinateIdeal_pow_iff A (normalExponentDegree a.val) _).mp
      hTa a.val (Nat.lt_of_not_ge hnot)
    have hm := G.monic a
    change MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (G.germs a)) = 1 at hm
    rw [hm] at hc
    exact one_ne_zero hc
  have hsum := coordinate_weight_sum_compl A a.val
  have hpos := coordinate_outside_le_compl_weight A a.val i hiA
  have hz : a.val i = 0 := by omega
  exact hai hz

/-- True source normal powers internally make every selected actual analytic
derivative an equation vanishing on the SAME normal centre. -/
theorem actualInheritedEssentialDerivative_mem_coordinate_ideal_of_powers
    (G : ActualAnalyticInheritedFamily n 0 K) (A : Set (Fin n))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateBlockIdeal A ^ normalExponentDegree a.val)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K) :
    actualInheritedEssentialDerivative G j ∈ actualAnalyticCoordinateBlockIdeal A := by
  let a := actualCanonicalDerivativeVertex MonomialOrder.degLex K j
  let β := actualCanonicalDerivativeExponent MonomialOrder.degLex K j
  have hdegree : normalExponentDegree β + 1 = normalExponentDegree a.val := by
    have h := congrArg normalExponentDegree
      (actualCanonicalDerivativeExponent_add_single MonomialOrder.degLex K j)
    simpa [normalExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib] using h
  have hTa := actualTaylor_mem_coordinate_power A (normalExponentDegree a.val) (G.germs a) (hpower a)
  apply coordinate_ideal_of_actualTaylor A
  rw [actualTaylor_actualInheritedEssentialDerivative]
  rw [← pow_one (actualFormalCoordinateIdeal n A)]
  apply (mem_actualFormalCoordinateIdeal_pow_iff A 1 _).mpr
  intro γ hγ
  rw [coeff_actualFormalMultiDerivative]
  have hwγ : Finsupp.weight (actualCoordinateWeight A) γ = 0 := by omega
  have hwβ := coordinate_weight_le_degree A β
  have hsmall : Finsupp.weight (actualCoordinateWeight A) (γ+β) < normalExponentDegree a.val := by
    rw [map_add, hwγ, zero_add]
    omega
  rw [(mem_actualFormalCoordinateIdeal_pow_iff A (normalExponentDegree a.val) _).mp hTa _ hsmall,
    zero_mul]

private theorem projection_compl_subset (A B : Set (Fin n)) (hBA : B ⊆ A)
    (z : ComplexModel n) :
    actualBlockCoordinateProjection Bᶜ (actualBlockCoordinateProjection Aᶜ z) =
      actualBlockCoordinateProjection Aᶜ z := by
  ext i
  by_cases hi : i ∈ A
  · by_cases hiB : i ∈ B <;> simp [actualBlockCoordinateProjection_apply, hi, hiB]
  · have hiB : i ∉ B := fun h => hi (hBA h)
    simp [actualBlockCoordinateProjection_apply, hi, hiB]

private theorem equation_map_fix_centre
    (G : ActualAnalyticInheritedFamily n 0 K) (A : Set (Fin n))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateBlockIdeal A ^ normalExponentDegree a.val)
    (kprev k : ℕ)
    (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
    (hf : ∀ j, HolAt (f j) 0)
    (he : ∀ j, HolGerm.mk (f j) (hf j) = actualNextBlockDerivativeGerm G kprev k j) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel n),
      actualNextBlockEquationMap kprev k f (actualBlockCoordinateProjection Aᶜ z) =
        actualBlockCoordinateProjection Aᶜ z := by
  have hzero (j : actualNextBlockCoordinates (K := K) kprev k) :
      ∀ᶠ z in 𝓝 (0 : ComplexModel n), f j (actualBlockCoordinateProjection Aᶜ z) = 0 := by
    have hmem := actualInheritedEssentialDerivative_mem_coordinate_ideal_of_powers G A hpower
      (actualNextBlockEssentialIndex kprev k j)
    have hker := (mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero A _).mp hmem
    change actualBlockProjectionGermHom Aᶜ (actualNextBlockDerivativeGerm G kprev k j) = 0 at hker
    rw [← he j] at hker
    unfold actualBlockProjectionGermHom at hker
    rw [compAlgHom_mk, ← HolGerm.mk_zero] at hker
    exact HolGerm.mk_eq_mk_iff.mp hker
  have hall := eventually_all.mpr hzero
  filter_upwards [hall] with z hz
  ext i
  rw [actualNextBlockEquationMap_apply,
    projection_compl_subset A _ (actualDegreePrefixVariables_subset_of_normal_powers G A hpower kprev)]
  split_ifs with hi
  · rw [hz ⟨i, hi⟩]
    have hiA := actualDegreePrefixVariables_subset_of_normal_powers G A hpower k hi.1
    simp [actualBlockCoordinateProjection_apply, hiA]
  · rfl

/-- The very inverse graph used by the real next-block construction vanishes
on the same centre by the actual local inverse uniqueness law. -/
theorem actualInverseFreeBlockGraphData_value_mem_coordinate_ideal
    (G : ActualAnalyticInheritedFamily n 0 K) (A : Set (Fin n))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateBlockIdeal A ^ normalExponentDegree a.val)
    (kprev k : ℕ)
    (f : actualNextBlockCoordinates (K := K) kprev k → ComplexModel n → ℂ)
    (hf : ∀ j, HolAt (f j) 0)
    (he : ∀ j, HolGerm.mk (f j) (hf j) = actualNextBlockDerivativeGerm G kprev k j)
    (Φ : LocalHolomorphicEquivAt (n := n) (0 : ComplexModel n))
    (hΦ : Φ.toFun = actualNextBlockEquationMap kprev k f) (hΦ0 : Φ.toFun 0 = 0)
    (j : actualNextBlockCoordinates (K := K) kprev k) :
    actualBlockGraphValueGerm
      (actualInverseFreeBlockGraphData
        (actualDegreePrefixVariables MonomialOrder.degLex K k)
        (actualNextBlockCoordinates (K := K) kprev k) (fun _ hi => hi.1) Φ hΦ0) j.val ∈
      actualAnalyticCoordinateBlockIdeal A := by
  let B := actualDegreePrefixVariables MonomialOrder.degLex K k
  let C := actualNextBlockCoordinates (K := K) kprev k
  let D := actualInverseFreeBlockGraphData B C (fun _ hi => hi.1) Φ hΦ0
  have hBA : B ⊆ A := actualDegreePrefixVariables_subset_of_normal_powers G A hpower k
  have hfix := equation_map_fix_centre G A hpower kprev k f hf he
  have hsrc : ∀ᶠ z in 𝓝 (0 : ComplexModel n), actualBlockCoordinateProjection Aᶜ z ∈ Φ.source := by
    apply (Φ.isOpen_source.preimage (actualBlockCoordinateProjection Aᶜ).continuous).mem_nhds
    simpa only [Set.mem_preimage, map_zero] using Φ.center_mem_source
  apply (mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero A _).mpr
  unfold actualBlockGraphValueGerm actualBlockProjectionGermHom
  rw [compAlgHom_mk, ← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  filter_upwards [hfix, hsrc] with z hz hzs
  have hfixed : Φ.toFun (actualBlockCoordinateProjection Aᶜ z) =
      actualBlockCoordinateProjection Aᶜ z := by rwa [hΦ]
  have hinv : Φ.invFun (actualBlockCoordinateProjection Aᶜ z) =
      actualBlockCoordinateProjection Aᶜ z := by
    calc
      Φ.invFun (actualBlockCoordinateProjection Aᶜ z) =
          Φ.invFun (Φ.toFun (actualBlockCoordinateProjection Aᶜ z)) :=
        congrArg Φ.invFun hfixed.symm
      _ = actualBlockCoordinateProjection Aᶜ z := Φ.left_inv _ hzs
  change Φ.invFun (actualBlockCoordinateProjection Bᶜ
    (actualBlockCoordinateProjection Aᶜ z)) j.val = 0
  rw [projection_compl_subset A B hBA, hinv]
  simp [actualBlockCoordinateProjection_apply, hBA j.property.1]

private theorem map_projection_coordinate_ideal_le (A B : Set (Fin n)) :
    Ideal.map (actualBlockProjectionGermHom B).toRingHom (actualAnalyticCoordinateBlockIdeal A) ≤
      actualAnalyticCoordinateBlockIdeal A := by
  rw [actualAnalyticCoordinateBlockIdeal, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro F ⟨G, ⟨i, hi, rfl⟩, rfl⟩
  change actualBlockProjectionGermHom B (coordinateGerm i) ∈ Ideal.span (coordinateGerm '' A)
  rw [actualBlockProjectionGermHom_coordinate]
  by_cases hiB : i ∈ B
  · rw [if_pos hiB]
    exact Ideal.subset_span ⟨i, hi, rfl⟩
  · rw [if_neg hiB]
    exact Ideal.zero_mem _

private theorem map_graph_coordinate_ideal_le
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (A : Set (Fin n))
    (hvalue : ∀ j ∈ C, actualBlockGraphValueGerm D j ∈ actualAnalyticCoordinateBlockIdeal A) :
    Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
        (actualAnalyticCoordinateBlockIdeal A) ≤ actualAnalyticCoordinateBlockIdeal A := by
  rw [actualAnalyticCoordinateBlockIdeal, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro F ⟨G, ⟨i, hi, rfl⟩, rfl⟩
  change actualBlockGraphGermEquiv D (coordinateGerm i) ∈ Ideal.span (coordinateGerm '' A)
  rw [actualBlockGraphGermEquiv_coordinate]
  refine (Ideal.span (coordinateGerm '' A)).add_mem
    (Ideal.subset_span (show coordinateGerm i ∈ coordinateGerm '' A from ⟨i, hi, rfl⟩)) ?_
  rw [actualBlockGraphShiftGerm]
  by_cases hiC : i ∈ C
  · rw [if_pos hiC]
    exact map_projection_coordinate_ideal_le A Bᶜ
      (Ideal.mem_map_of_mem _ (hvalue i hiC))
  · rw [if_neg hiC]
    exact Ideal.zero_mem _

theorem map_actualAnalyticCoordinateBlockIdeal_graph_of_value_mem
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (A : Set (Fin n))
    (hvalue : ∀ j ∈ C, actualBlockGraphValueGerm D j ∈ actualAnalyticCoordinateBlockIdeal A) :
    Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
        (actualAnalyticCoordinateBlockIdeal A) = actualAnalyticCoordinateBlockIdeal A := by
  have hneg : ∀ j ∈ C, actualBlockGraphValueGerm D.neg j ∈ actualAnalyticCoordinateBlockIdeal A := by
    intro j hj
    rw [actualBlockGraphValueGerm_neg]
    exact (actualAnalyticCoordinateBlockIdeal A).neg_mem (hvalue j hj)
  apply le_antisymm (map_graph_coordinate_ideal_le D A hvalue)
  intro F hF
  have hmem := Ideal.mem_map_of_mem (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
    (map_graph_coordinate_ideal_le D.neg A hneg
      (Ideal.mem_map_of_mem (actualBlockGraphGermEquiv D.neg).toRingEquiv.toRingHom hF))
  change actualBlockGraphGermEquiv D (actualBlockGraphGermEquiv D.neg F) ∈
    Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
      (actualAnalyticCoordinateBlockIdeal A) at hmem
  rwa [actualBlockGraphGermEquiv_comp_neg] at hmem

theorem actualBlockGraphGermEquiv_mem_coordinate_power_iff
    {B C : Set (Fin n)} (D : ActualBlockGraphData B C) (A : Set (Fin n))
    (hvalue : ∀ j ∈ C, actualBlockGraphValueGerm D j ∈ actualAnalyticCoordinateBlockIdeal A)
    (q : ℕ) (F : HolGerm (ComplexModel n)) :
    actualBlockGraphGermEquiv D F ∈ actualAnalyticCoordinateBlockIdeal A ^ q ↔
      F ∈ actualAnalyticCoordinateBlockIdeal A ^ q := by
  have hneg : ∀ j ∈ C, actualBlockGraphValueGerm D.neg j ∈ actualAnalyticCoordinateBlockIdeal A := by
    intro j hj
    rw [actualBlockGraphValueGerm_neg]
    exact (actualAnalyticCoordinateBlockIdeal A).neg_mem (hvalue j hj)
  have hmap : Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
      (actualAnalyticCoordinateBlockIdeal A ^ q) = actualAnalyticCoordinateBlockIdeal A ^ q := by
    rw [Ideal.map_pow, map_actualAnalyticCoordinateBlockIdeal_graph_of_value_mem D A hvalue]
  have hmapneg : Ideal.map (actualBlockGraphGermEquiv D.neg).toRingEquiv.toRingHom
      (actualAnalyticCoordinateBlockIdeal A ^ q) = actualAnalyticCoordinateBlockIdeal A ^ q := by
    rw [Ideal.map_pow, map_actualAnalyticCoordinateBlockIdeal_graph_of_value_mem D.neg A hneg]
  constructor
  · intro hF
    have h := Ideal.mem_map_of_mem (actualBlockGraphGermEquiv D.neg).toRingEquiv.toRingHom hF
    rw [hmapneg] at h
    change actualBlockGraphGermEquiv D.neg (actualBlockGraphGermEquiv D F) ∈
      actualAnalyticCoordinateBlockIdeal A ^ q at h
    rwa [actualBlockGraphGermEquiv_neg_comp] at h
  · intro hF
    have h := Ideal.mem_map_of_mem (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom hF
    rwa [hmap] at h

private theorem block_projection_idempotent (B : Set (Fin n)) (z : ComplexModel n) :
    actualBlockCoordinateProjection B (actualBlockCoordinateProjection B z) =
      actualBlockCoordinateProjection B z := by
  ext i
  by_cases hi : i ∈ B <;> simp [actualBlockCoordinateProjection_apply, hi]

private theorem degree_prefix_block_mono {kprev k : ℕ} (hcut : kprev ≤ k) :
    actualDegreePrefixVariables MonomialOrder.degLex K kprev ⊆
      actualDegreePrefixVariables MonomialOrder.degLex K k := by
  intro i hi
  obtain ⟨a, ha, hai⟩ := hi
  exact ⟨a, ha.trans hcut, hai⟩

/-- The SAME original-centre graph is internally produced from current source
normal powers. Its genuine normal ideal image and ALL powers are outputs,
along with the actual old next-graph priority and new derivative memberships. -/
theorem exists_actual_inherited_next_block_centre_graph
    (G : ActualAnalyticInheritedFamily n 0 K) (A : Set (Fin n))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateBlockIdeal A ^ normalExponentDegree a.val)
    (kprev k : ℕ) (hcut : kprev ≤ k) :
    ∃ D : ActualBlockGraphData
        (actualDegreePrefixVariables MonomialOrder.degLex K k)
        (actualNextBlockCoordinates (K := K) kprev k),
      ActualBlockGraphLinearPriority D ∧
      (∀ j : actualNextBlockCoordinates (K := K) kprev k,
        actualBlockGraphGermEquiv D (actualNextBlockDerivativeGerm G kprev k j) ∈
          actualAnalyticCoordinateBlockIdeal (actualDegreePrefixVariables MonomialOrder.degLex K k)) ∧
      Ideal.map (actualBlockGraphGermEquiv D).toRingEquiv.toRingHom
          (actualAnalyticCoordinateBlockIdeal A) = actualAnalyticCoordinateBlockIdeal A ∧
      ∀ (q : ℕ) (F : HolGerm (ComplexModel n)),
        actualBlockGraphGermEquiv D F ∈ actualAnalyticCoordinateBlockIdeal A ^ q ↔
          F ∈ actualAnalyticCoordinateBlockIdeal A ^ q := by
  obtain ⟨f, hf, he, Φ, hΦ, hΦ0, hdiag, htri⟩ :=
    exists_actual_next_block_equation_local_equiv G kprev k
  let B := actualDegreePrefixVariables MonomialOrder.degLex K k
  let Bprev := actualDegreePrefixVariables MonomialOrder.degLex K kprev
  let C := actualNextBlockCoordinates (K := K) kprev k
  have hCB : C ⊆ B := fun _ hi => hi.1
  let D := actualInverseFreeBlockGraphData B C hCB Φ hΦ0
  have hpriority : ActualBlockGraphLinearPriority D :=
    actualInverseFreeBlockGraphData_linear_priority B C hCB Φ hΦ0 hdiag htri
  have hvalue : ∀ j ∈ C, actualBlockGraphValueGerm D j ∈ actualAnalyticCoordinateBlockIdeal A := by
    intro j hj
    exact actualInverseFreeBlockGraphData_value_mem_coordinate_ideal G A hpower kprev k f hf he
      Φ hΦ hΦ0 ⟨j, hj⟩
  refine ⟨D, hpriority, ?_, map_actualAnalyticCoordinateBlockIdeal_graph_of_value_mem D A hvalue,
    actualBlockGraphGermEquiv_mem_coordinate_power_iff D A hvalue⟩
  intro j
  apply (mem_actualAnalyticCoordinateBlockIdeal_iff_projection_zero B _).mpr
  rw [← he j]
  unfold actualBlockProjectionGermHom
  rw [actualBlockGraphGermEquiv_mk, compAlgHom_mk, ← HolGerm.mk_zero]
  apply HolGerm.mk_eq_mk_iff.mpr
  have h0tar : (0 : ComplexModel n) ∈ Φ.target := by
    simpa only [hΦ0] using Φ.mapsTo_toFun Φ.center_mem_source
  have hN : IsOpen (actualBlockCoordinateProjection Bᶜ ⁻¹' Φ.target) :=
    Φ.isOpen_target.preimage (actualBlockCoordinateProjection Bᶜ).continuous
  have h0N : (0 : ComplexModel n) ∈ actualBlockCoordinateProjection Bᶜ ⁻¹' Φ.target := by
    simpa only [Set.mem_preimage, map_zero] using h0tar
  filter_upwards [hN.mem_nhds h0N] with z hz
  let w := actualBlockCoordinateProjection Bᶜ z
  let u := Φ.invFun w
  have hw : w ∈ Φ.target := hz
  have hΓ : actualNextBlockEquationMap kprev k f u = w := by
    rw [← hΦ]
    exact Φ.right_inv w hw
  have hold : ∀ i ∈ Bprev, u i = 0 := by
    intro i hi
    have hinot : i ∉ C := fun hc => hc.2 hi
    have h := congrArg (fun v : ComplexModel n => v i) hΓ
    rw [actualNextBlockEquationMap_apply, dif_neg hinot] at h
    have hiB : i ∈ B := degree_prefix_block_mono hcut hi
    have hw0 : w i = 0 := by simp [w, actualBlockCoordinateProjection_apply, hiB]
    exact h.trans hw0
  have hPu : actualBlockCoordinateProjection Bprevᶜ u = u := by
    ext i
    by_cases hi : i ∈ Bprev
    · simp [actualBlockCoordinateProjection_apply, hi, hold i hi]
    · simp [actualBlockCoordinateProjection_apply, hi]
  have hψ : actualBlockGraphMap B C D.value w = u := by
    ext i
    rw [actualBlockGraphMap_apply]
    by_cases hi : i ∈ C
    · rw [if_pos hi]
      have hw0 : w i = 0 := by simp [w, actualBlockCoordinateProjection_apply, hCB hi]
      have hval : D.value (actualBlockCoordinateProjection Bᶜ w) i = u i := by
        have hwP : actualBlockCoordinateProjection Bᶜ w = w := block_projection_idempotent Bᶜ z
        change Φ.invFun (actualBlockCoordinateProjection Bᶜ
          (actualBlockCoordinateProjection Bᶜ w)) i = u i
        rw [hwP, hwP]
      rw [hw0, hval, zero_add]
    · rw [if_neg hi, add_zero]
      have h := congrArg (fun v : ComplexModel n => v i) hΓ
      rw [actualNextBlockEquationMap_apply, dif_neg hi] at h
      exact h.symm
  have hj := congrArg (fun v : ComplexModel n => v j.val) hΓ
  rw [actualNextBlockEquationMap_apply, dif_pos j.property, hPu] at hj
  have hwj : w j.val = 0 := by
    have hjB : j.val ∈ B := j.property.1
    simp [w, actualBlockCoordinateProjection_apply, hjB]
  change f j (actualBlockGraphMap B C D.value w) = 0
  rw [hψ]
  exact hj.trans hwj

end

end Hironaka.HironakaActualInheritedNextBlockCentreGraph
