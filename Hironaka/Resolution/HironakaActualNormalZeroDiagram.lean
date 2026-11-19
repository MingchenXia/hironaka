import Hironaka.Resolution.HironakaActualNormalRename
import Hironaka.Resolution.HironakaActualRelativeStandardnessNormalPivotPriority
import Hironaka.Resolution.HironakaActualCanonicalNormalZeroDirectionOrder
import Hironaka.Resolution.HironakaActualRelativeStandardnessPointLeadingDiagram

/-! In the internally adapted first-normal zero chart, genuine source tangent
stability, SAME canonical centre powers and actual whole HS equality produce
the unchanged heads, the whole diagram, and the literal canonical identity of
the inherited family. No target diagram or marked order is assumed. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalZeroDiagram
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalMonomialBlowupReflection HironakaActualFormalStrictGenerators
  HironakaActualCoefficientReducedStrictGenerators HironakaActualHomogeneousInitialHS
  HironakaActualTangentInitialVertices HironakaActualCanonicalVertexDirectionalInvariance
  HironakaActualPointUnitCoordinateChange HironakaActualPointNormalizedExponents
  HironakaActualRelativeStandardnessBlockSupport
  HironakaActualRelativeStandardnessNormalPointBridge HironakaActualCanonicalNormalZeroDirectionOrder
  HironakaActualCanonicalZeroDirectionOrder HironakaActualFormalStandardMonomialHS
  HironakaActualRelativeStandardnessNormalPivotPriority
  HironakaActualRelativeStandardnessPointLeadingDiagram
variable {n : ℕ}

/-- The actual chart at the first coordinate of the selected normal tail. -/
def normalZeroStrict (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q : Fin (n + 1)) :
    Ideal (MvPowerSeries (Fin (n + 1)) ℂ) :=
  actualFormalStrictTransform K (normalPivotVariables q) q (by change q ≤ q; exact le_rfl) (fun _ => 0)

private theorem point_power_of_normal_power
    (q : Fin (n + 1)) (μ : ℕ) (F : MvPowerSeries (Fin (n + 1)) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^ μ) :
    F ∈ actualFormalCoordinateIdeal (n + 1) Set.univ ^ μ := by
  have hI : actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ≤
      actualFormalCoordinateIdeal (n + 1) Set.univ := by
    apply Ideal.span_le.mpr
    rintro G ⟨i, hi, rfl⟩
    exact Ideal.subset_span ⟨i, mem_univ i, rfl⟩
  exact (pow_le_pow_left' hI μ) hF

/-- The true point-normalization exponent dictionary and the genuine whole
tangent-scaling coefficient embedding agree on the transverse head plane. -/
theorem actual_normal_zero_transverse_coefficient
    (q : Fin (n + 1)) (μ : ℕ) (F : MvPowerSeries (Fin (n + 1)) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^ μ)
    (γ : Fin (n + 1) →₀ ℕ) (hdegree : normalExponentDegree γ = μ)
    (hprefix : ∀ i ≤ q, γ i = 0) :
    MvPowerSeries.coeff γ (actualNormalizedFormalMember (normalPivotVariables q) q (by change q ≤ q; exact le_rfl)
      (fun _ => 0) μ F hF) = MvPowerSeries.coeff γ F := by
  let A := normalPivotVariables q
  let N := actualNormalizedFormalMember A q (by change q ≤ q; exact le_rfl) (fun _ => 0) μ F hF
  have hweight : Finsupp.weight (actualCoordinateWeight (Aᶜ \ {q})) γ = 0 := by
    rw [Finsupp.weight_eq_sum]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i ∈ Aᶜ \ {q}
    · have hiq : i ≤ q := le_of_lt (lt_of_not_ge hi.1)
      simp only [actualCoordinateWeight, if_pos hi, hprefix i hiq, zero_smul]
    · simp only [actualCoordinateWeight, if_neg hi, smul_zero]
  have hExp : actualMonomialBlowupExponent Aᶜ q γ = γ := by
    change γ + Finsupp.single q (Finsupp.weight (actualCoordinateWeight (Aᶜ \ {q})) γ) = γ
    rw [hweight, Finsupp.single_zero, add_zero]
  have hscaling := actualFormalBlowup_zero_coefficient Aᶜ q N γ
  rw [hExp] at hscaling
  have hPoint := actualNormalizedPointMember_eq_tangentScaling_normal A q (by change q ≤ q; exact le_rfl)
    (fun _ => 0) μ F hF
  have hz : actualNormalPointDirection A (fun _ => 0) = (fun _ => 0) := by
    funext i
    simp [actualNormalPointDirection]
  rw [hz] at hPoint
  have hPointCoeff := congrArg (MvPowerSeries.coeff γ) hPoint
  have hγq : γ q = 0 := hprefix q le_rfl
  have hPointExp : actualPointNormalizedExponent q μ γ = γ := by
    rw [actualPointNormalizedExponent, hdegree, Nat.sub_self, Finsupp.single_zero, add_zero]
    exact Finsupp.erase_of_notMem_support (Finsupp.notMem_support_iff.mpr hγq)
  have hcoeff := actualNormalizedFormalMember_zero_coefficient q μ F
    (point_power_of_normal_power q μ F hF) γ (by omega)
  rw [hPointExp] at hcoeff
  exact hscaling.symm.trans (hPointCoeff.symm.trans hcoeff)

section Source
variable (K : Ideal (MvPowerSeries (Fin (n + 1)) ℂ)) (q : Fin (n + 1))
variable (hD : ∀ i ∉ normalPivotVariables q, ∀ F ∈ actualHomogeneousInitialIdeal K,
  MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
variable (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
  actualReducedVertexSeries MonomialOrder.degLex K a ∈
    actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^
      Finsupp.weight (actualCoordinateWeight (normalPivotVariables q)) a.val)
variable (hHS : ∀ ℓ, genuineFormalHilbertSamuelValue (n + 1) (normalZeroStrict K q) ℓ =
  genuineFormalHilbertSamuelValue (n + 1) K ℓ)

include hD hV hHS in
private theorem first_normal_initial_stable :
    ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ q F ∈ actualHomogeneousInitialIdeal K := by
  intro F hF
  have hd := actual_homogeneous_initial_normal_directional_stable_of_hs_eq K
    (normalPivotVariables q) q (by change q ≤ q; exact le_rfl) (fun _ => 0) hD hV hHS F hF
  simpa only [actualPointUnitBasePoint_apply, actualNormalPointDirection, ite_self,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hd

include hD hV hHS in
private theorem source_vertex_prefix_zero (a : actualInitialVertices MonomialOrder.degLex K) :
    ∀ i ≤ q, a.val i = 0 := by
  intro i hi
  by_cases hie : i = q
  · subst i
    exact actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) q (first_normal_initial_stable K q hD hV hHS)
      (actualHomogeneousInitialVertex K a)
  · have hiq : i < q := lt_of_le_of_ne hi hie
    exact actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) i (hD i (not_le_of_gt hiq))
      (actualHomogeneousInitialVertex K a)

include hD in
private theorem normalized_reduced_eq_degree_member
    (a : actualInitialVertices MonomialOrder.degLex K)
    (hR : actualReducedVertexSeries MonomialOrder.degLex K a ∈
      actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^ normalExponentDegree a.val) :
    actualNormalizedReducedFormalVertex MonomialOrder.degLex K (normalPivotVariables q) q (by change q ≤ q; exact le_rfl)
      (fun _ => 0) hV a = actualNormalizedFormalMember (normalPivotVariables q) q (by change q ≤ q; exact le_rfl)
        (fun _ => 0) (normalExponentDegree a.val)
          (actualReducedVertexSeries MonomialOrder.degLex K a) hR := by
  let N := actualNormalizedReducedFormalVertex MonomialOrder.degLex K
    (normalPivotVariables q) q (by change q ≤ q; exact le_rfl) (fun _ => 0) hV a
  apply actualNormalizedFormalMember_unique
  have hs := actualNormalizedFormalMember_spec (normalPivotVariables q) q (by change q ≤ q; exact le_rfl) (fun _ => 0)
    _ (actualReducedVertexSeries MonomialOrder.degLex K a) (hV a)
  change (MvPowerSeries.X q) ^ Finsupp.weight (actualCoordinateWeight (normalPivotVariables q)) a.val *
    N = actualFormalBlowup (normalPivotVariables q) q (fun _ => 0)
      (actualReducedVertexSeries MonomialOrder.degLex K a) at hs
  rw [actual_normal_vertex_mark_eq_degree K (normalPivotVariables q) hD a] at hs
  exact hs

include hD hHS in
/-- Genuine marked orders and the transverse coefficient dictionary produce
the original heads. This is restricted to the first NORMAL zero chart. -/
theorem actual_normal_zero_reduced_vertex_monic
    (a : actualInitialVertices MonomialOrder.degLex K) :
    let N := actualNormalizedReducedFormalVertex MonomialOrder.degLex K
      (normalPivotVariables q) q (by change q ≤ q; exact le_rfl) (fun _ => 0) hV a
    MvPowerSeries.coeff a.val N = 1 ∧
      ∀ γ, MonomialOrder.degLex.toSyn γ < MonomialOrder.degLex.toSyn a.val →
        MvPowerSeries.coeff γ N = 0 := by
  let μ := normalExponentDegree a.val
  have hR : actualReducedVertexSeries MonomialOrder.degLex K a ∈
      actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^ μ := by
    simpa only [actual_normal_vertex_mark_eq_degree K (normalPivotVariables q) hD a] using hV a
  let N := actualNormalizedFormalMember (normalPivotVariables q) q (by change q ≤ q; exact le_rfl) (fun _ => 0) μ
    (actualReducedVertexSeries MonomialOrder.degLex K a) hR
  have hNorm := normalized_reduced_eq_degree_member K q hD hV a hR
  dsimp only
  rw [hNorm]
  have hprefix := source_vertex_prefix_zero K q hD hV hHS a
  constructor
  · rw [actual_normal_zero_transverse_coefficient q μ _ hR a.val rfl hprefix]
    exact actualReducedVertexSeries_coefficient MonomialOrder.degLex K a
  · intro γ hγ
    have horder := actualNormalizedReducedFormalVertex_normal_zero_mem_degree_power_of_hs_eq
      K (normalPivotVariables q) q (by change q ≤ q; exact le_rfl) hD hV hHS a
    rw [hNorm] at horder
    have hle : normalExponentDegree γ ≤ μ := actual_degree_le_of_deglex_lt γ a.val hγ
    by_cases hsmall : normalExponentDegree γ < μ
    · exact (mem_genuineFormalVariables_pow_iff_coefficients_zero (n + 1) μ N).mp horder γ hsmall
    · have hdegree : normalExponentDegree γ = μ := by omega
      have hγprefix : ∀ i ≤ q, γ i = 0 := by
        rcases Finsupp.DegLex.lt_iff.mp (MonomialOrder.degLex_lt_iff.mp hγ) with
          hdeg | ⟨_, hlex⟩
        · have hdeg' : normalExponentDegree γ < μ := by
            simpa only [ofDegLex_toDegLex, Finsupp.degree_eq_sum, normalExponentDegree, μ] using hdeg
          omega
        · obtain ⟨j, hj, hjlt⟩ := Finsupp.Lex.lt_iff.mp hlex
          have hqj : q < j := by
            by_contra h
            have hjq : j ≤ q := le_of_not_gt h
            have hzero := hprefix j hjq
            have hjlt' : γ j < a.val j := by
              simpa only [ofLex_toLex, ofDegLex_toDegLex] using hjlt
            omega
          intro i hi
          have hei : γ i = a.val i := by
            simpa only [ofLex_toLex, ofDegLex_toDegLex] using hj i (lt_of_le_of_lt hi hqj)
          exact hei.trans (hprefix i hi)
      rw [actual_normal_zero_transverse_coefficient q μ _ hR γ hdegree hγprefix]
      exact actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex K a γ hγ

include hD hV hHS in
/-- The SAME inherited heads give one diagram inclusion. ALL genuine closed
HS values give the reverse inclusion by actual finite complement dimensions. -/
theorem actualInitialDiagram_normal_zero_eq_of_hs_eq :
    actualInitialDiagram MonomialOrder.degLex (normalZeroStrict K q) =
      actualInitialDiagram MonomialOrder.degLex K := by
  apply actualInitialDiagram_eq_of_subset_of_hs_eq K (normalZeroStrict K q) ?_ hHS
  intro α hα
  obtain ⟨a, ha, hle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K α).mp hα
  let v : actualInitialVertices MonomialOrder.degLex K := ⟨a, ha⟩
  let N := actualNormalizedReducedFormalVertex MonomialOrder.degLex K
    (normalPivotVariables q) q (by change q ≤ q; exact le_rfl) (fun _ => 0) hV v
  have hm := actual_normal_zero_reduced_vertex_monic K q hD hV hHS v
  have hne : N ≠ 0 := by
    intro hz
    have hc := hm.1
    change MvPowerSeries.coeff v.val N = 1 at hc
    rw [hz, map_zero] at hc
    exact zero_ne_one hc
  have hmem : N ∈ normalZeroStrict K q := by
    rw [normalZeroStrict, actualFormalStrictTransform_eq_reduced_vertex_span
      MonomialOrder.degLex K (normalPivotVariables q) q (by change q ≤ q; exact le_rfl) (fun _ => 0) hV]
    exact Ideal.subset_span ⟨v, rfl⟩
  have hhead : actualInitialExponent MonomialOrder.degLex N hne = a :=
    actualInitialExponent_eq_of_coefficients MonomialOrder.degLex N hne a
      (by rw [hm.1]; exact one_ne_zero) hm.2
  exact actualInitialDiagram_upper MonomialOrder.degLex _ a α ⟨N, hmem, hne, hhead⟩ hle

include hD hV hHS in
/-- Actual target minimal exponents have the unchanged source labels, using
the PRODUCED whole diagram equality. -/
def normalZeroVertex (a : actualInitialVertices MonomialOrder.degLex K) :
    actualInitialVertices MonomialOrder.degLex (normalZeroStrict K q) :=
  ⟨a.val, by
    simpa only [actualInitialVertices, actualInitialDiagram_normal_zero_eq_of_hs_eq K q hD hV hHS]
      using a.property⟩

theorem normalZeroVertex_surjective :
    Function.Surjective (normalZeroVertex K q hD hV hHS) := by
  rintro ⟨a, ha⟩
  refine ⟨⟨a, ?_⟩, Subtype.ext rfl⟩
  simpa only [actualInitialVertices, actualInitialDiagram_normal_zero_eq_of_hs_eq K q hD hV hHS]
    using ha

private theorem component_mem_coordinate_power (A : Set (Fin (n + 1))) (μ d : ℕ)
    (F : MvPowerSeries (Fin (n + 1)) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal (n + 1) A ^ μ) :
    MvPowerSeries.homogeneousComponent d F ∈ actualFormalCoordinateIdeal (n + 1) A ^ μ := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff A μ _).mpr
  intro α hα
  rw [MvPowerSeries.coeff_homogeneousComponent]
  split_ifs
  · exact (mem_actualFormalCoordinateIdeal_pow_iff A μ F).mp hF α hα
  · rfl

/-- Full reduction survives in this SPECIFIC adapted chart. The fixed leading
head and the SAME tail's genuine whole forbidden-diagram support supply the
actual coefficient rule; whole canonical uniqueness then identifies the SAME
normalized member, rather than selecting a replacement family. -/
theorem actual_normal_zero_normalized_eq_canonical
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualNormalizedReducedFormalVertex MonomialOrder.degLex K (normalPivotVariables q) q (by change q ≤ q; exact le_rfl)
      (fun _ => 0) hV a = actualReducedVertexSeries MonomialOrder.degLex (normalZeroStrict K q)
        (normalZeroVertex K q hD hV hHS a) := by
  let A := normalPivotVariables q
  let μ := normalExponentDegree a.val
  let R := actualReducedVertexSeries MonomialOrder.degLex K a
  let H := actualCanonicalLeadingHead K a
  have heD := first_normal_initial_stable K q hD hV hHS
  have hR : R ∈ actualFormalCoordinateIdeal (n + 1) A ^ μ := by
    change actualReducedVertexSeries MonomialOrder.degLex K a ∈
      actualFormalCoordinateIdeal (n + 1) (normalPivotVariables q) ^ normalExponentDegree a.val
    simpa only [actual_normal_vertex_mark_eq_degree K (normalPivotVariables q) hD a] using hV a
  have hH : H ∈ actualFormalCoordinateIdeal (n + 1) A ^ μ :=
    component_mem_coordinate_power A μ μ R hR
  have hTail : actualCanonicalHigherTail K a ∈ actualFormalCoordinateIdeal (n + 1) A ^ μ :=
    (actualFormalCoordinateIdeal (n + 1) A ^ μ).sub_mem hR hH
  have hHnorm := actualNormalizedFormalMember_normal_zero_eq_of_homogeneous_independent A q (by change q ≤ q; exact le_rfl)
    μ H (MvPowerSeries.isHomogeneous_homogeneousComponent _ _)
    (pderiv_homogeneousComponent_actualReducedVertexSeries_eq_zero_of_stable K q heD a) hH
  let N := actualNormalizedFormalMember A q (by change q ≤ q; exact le_rfl) (fun _ => 0) μ R hR
  let T := actualNormalizedFormalMember A q (by change q ≤ q; exact le_rfl) (fun _ => 0) μ (actualCanonicalHigherTail K a) hTail
  have hsub : N - H = T := by
    apply actualNormalizedFormalMember_unique
    change (MvPowerSeries.X q) ^ μ * (N - H) = actualFormalBlowup A q (fun _ => 0) (R - H)
    rw [map_sub, mul_sub, actualNormalizedFormalMember_spec]
    have hp := actualNormalizedFormalMember_spec A q (by change q ≤ q; exact le_rfl) (fun _ => 0) μ H hH
    rw [hHnorm] at hp
    rw [hp]
  have hNorm := normalized_reduced_eq_degree_member K q hD hV a hR
  rw [hNorm]
  apply actualReducedVertexSeries_unique MonomialOrder.degLex (normalZeroStrict K q)
    (normalZeroVertex K q hD hV hHS a) N
  · rw [normalZeroStrict, actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
    exact Ideal.subset_span ⟨μ, R, actualReducedVertexSeries_mem MonomialOrder.degLex K a, hR, rfl⟩
  · intro γ hγ
    have hγK : γ ∈ actualInitialDiagram MonomialOrder.degLex K := by
      rwa [actualInitialDiagram_normal_zero_eq_of_hs_eq K q hD hV hHS] at hγ
    have hTzero := actualNormalized_normal_canonical_tail_diagram_coefficients_zero
      K A q (by change q ≤ q; exact le_rfl) hD heD hV a γ hγK
    have hcoeff : MvPowerSeries.coeff γ N = MvPowerSeries.coeff γ H := by
      have hc := congrArg (MvPowerSeries.coeff γ) hsub
      rw [map_sub, hTzero] at hc
      exact sub_eq_zero.mp hc
    rw [hcoeff]
    change MvPowerSeries.coeff γ (MvPowerSeries.homogeneousComponent μ R) =
      if γ = a.val then 1 else 0
    rw [homogeneousComponent_actualReducedVertexSeries_eq_initial]
    exact actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) (actualHomogeneousInitialVertex K a) γ
        (by rwa [actual_homogeneous_initial_ideal_diagram])

end Source
end
end Hironaka.HironakaActualNormalZeroDiagram
