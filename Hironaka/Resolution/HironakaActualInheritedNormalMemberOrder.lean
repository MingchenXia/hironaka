import Hironaka.Resolution.HironakaActualInheritedPrefixShearSupport
import Hironaka.Resolution.HironakaActualNormalAdaptedDiagram
import Hironaka.Resolution.HironakaActualInheritedHSDirections

/-! Actual whole closed-point HS equality preserves the original marks of
SAME inherited members with genuine whole proper-prefix cone support.
The natural endpoints internally produce canonical source data and the
adapted target diagram; no target order/diagram or contact certificate is
an input. These statements do not assert target heads or a whole phase. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedNormalMemberOrder
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualReducedBasisDivision
  HironakaActualCanonicalVertexDirectionalInvariance
  HironakaActualOriginalFormalTaylor HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualFormalStandardMonomialHS
  HironakaActualFormalBlowupAllDirections HironakaActualCoefficientReducedStrictGenerators
  HironakaActualHomogeneousInitialHS HironakaActualTangentInitialVertices
  HironakaActualCanonicalBlockJacobian HironakaActualCanonicalDirectionPivot
  HironakaActualCanonicalTriangularShear HironakaActualPointUnitCoordinateChange
  HironakaActualNormalCentreChartTransition HironakaActualRelativeStandardnessNormalPointBridge
  HironakaActualCanonicalNormalZeroDirectionOrder HironakaActualCanonicalNormalDirectionOrder
  HironakaActualRelativeStandardnessNormalPivotPriority HironakaActualNormalRename
  HironakaActualNormalZeroDiagram HironakaActualNormalAdaptedDiagram
  HironakaActualRelativeStandardnessBlockSupport HironakaActualInheritedPrefixShearSupport
  HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
  HironakaActualCanonicalCentreCompatibility HironakaActualAnalyticBlowupTaylor
variable {n : ℕ}

/-- Explicit lower interface: the natural HS endpoint below supplies the
actual target diagram internally. The member itself need not be canonical. -/
theorem actual_normal_zero_member_order_of_same_diagram
    (K : Ideal (MvPowerSeries (Fin (n+1)) ℂ)) (q : Fin (n+1))
    (hpure : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      ∀ i ∉ normalPivotVariables q, a.val i = 0)
    (hq : ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val q = 0)
    (hdiagram : actualInitialDiagram MonomialOrder.degLex (normalZeroStrict K q) =
      actualInitialDiagram MonomialOrder.degLex K)
    (μ : ℕ) (F : MvPowerSeries (Fin (n+1)) ℂ) (hFK : F ∈ K)
    (hF : F ∈ actualFormalCoordinateIdeal (n+1) (normalPivotVariables q) ^ μ)
    (hprefix : ∀ c : actualInitialVertices MonomialOrder.degLex K,
      normalExponentDegree c.val < μ → ∀ α, c.val ≤ α → MvPowerSeries.coeff α F = 0) :
    actualNormalizedFormalMember (normalPivotVariables q) q (by change q ≤ q; exact le_rfl)
      (fun _ => 0) μ F hF ∈ genuineFormalVariables (n+1) ^ μ := by
  let A := normalPivotVariables q
  let B := actualCanonicalEssentialVariables MonomialOrder.degLex K
  let D (α : Fin (n+1) →₀ ℕ) : Prop :=
    ∃ c : actualInitialVertices MonomialOrder.degLex K,
      normalExponentDegree c.val < μ ∧ c.val ≤ α
  let N := actualNormalizedFormalMember A q (by change q ≤ q; exact le_rfl) (fun _ => 0) μ F hF
  have hB : B ⊆ A := by
    rintro i ⟨a, hai⟩
    by_contra hi
    exact hai (hpure a i hi)
  have hqB : q ∉ B := by
    rintro ⟨a, haq⟩
    exact haq (hq a)
  have hzoutside (c : actualInitialVertices MonomialOrder.degLex K) (i : Fin (n+1))
      (hi : i ∉ B) : c.val i = 0 := by
    by_contra hc
    exact hi ⟨c, hc⟩
  have hD : ∀ α γ : Fin (n+1) →₀ ℕ,
      (∀ i ∈ B, α i = γ i) → (D α ↔ D γ) := by
    intro α γ heq
    constructor
    · rintro ⟨c, hc, hca⟩
      refine ⟨c, hc, fun i => ?_⟩
      by_cases hi : i ∈ B
      · rw [← heq i hi]
        exact hca i
      · rw [hzoutside c i hi]
        exact Nat.zero_le _
    · rintro ⟨c, hc, hcg⟩
      refine ⟨c, hc, fun i => ?_⟩
      by_cases hi : i ∈ B
      · rw [heq i hi]
        exact hcg i
      · rw [hzoutside c i hi]
        exact Nat.zero_le _
  have hzero : ∀ α, D α → MvPowerSeries.coeff α N = 0 := by
    apply actualNormalizedFormalMember_forbidden_block_support A B q
      (by change q ≤ q; exact le_rfl) (fun _ => 0) hB hqB (fun _ _ => rfl) μ F hF D hD
    rintro α ⟨c, hc, hcα⟩
    exact hprefix c hc α hcα
  have hN : N ∈ normalZeroStrict K q := by
    rw [normalZeroStrict, actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
    exact Ideal.subset_span ⟨μ, F, hFK, hF, rfl⟩
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero (n+1) μ N).mpr
  intro β hβ
  by_contra hcoeff
  have hne : N ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hz, map_zero])
  let α := actualInitialExponent MonomialOrder.degLex N hne
  have hαdegree : normalExponentDegree α ≤ normalExponentDegree β := by
    have hle := (actualInitialExponent_spec MonomialOrder.degLex N hne).2 β hcoeff
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact le_of_eq (congrArg normalExponentDegree (MonomialOrder.degLex.toSyn.injective heq))
    · exact actual_degree_le_of_deglex_lt α β hlt
  have hαD : α ∈ actualInitialDiagram MonomialOrder.degLex K := by
    rw [← hdiagram]
    exact ⟨N, hN, hne, rfl⟩
  obtain ⟨c, hc, hcα⟩ :=
    (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K α).mp hαD
  have hcd : normalExponentDegree c ≤ normalExponentDegree α := by
    apply Finset.sum_le_sum
    intro i _
    exact hcα i
  have hz := hzero α ⟨⟨c, hc⟩, lt_of_le_of_lt (hcd.trans hαdegree) hβ, hcα⟩
  exact (actualInitialExponent_spec MonomialOrder.degLex N hne).1 hz

private theorem permute_degree (p : Fin (n+1) ≃ Fin (n+1)) (α : Fin (n+1) →₀ ℕ) :
    normalExponentDegree (Finsupp.domCongr p α) = normalExponentDegree α := by
  simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    normalExponentDegree, ← Finsupp.degree_eq_sum] using Finsupp.degree_mapDomain p α

private theorem normal_mem_iff (q f : Fin (n+1)) (hqf : q ≤ f) (i : Fin (n+1)) :
    normalPivotEquiv q f i ∈ normalPivotVariables q ↔ i ∈ normalPivotVariables q := by
  constructor
  · intro hi
    by_contra h
    have ht := normalPivotEquiv_tangent q f hqf i (lt_of_not_ge h)
    rw [ht] at hi
    exact h hi
  · intro hi
    by_contra h
    have hpi : normalPivotEquiv q f i < q := lt_of_not_ge h
    have hfix := normalPivotEquiv_tangent q f hqf (normalPivotEquiv q f i) hpi
    have heq : normalPivotEquiv q f i = i := (normalPivotEquiv q f).injective hfix
    rw [heq] at hpi
    exact (not_lt_of_ge hi) hpi

private theorem coeff_rename_permuted (p : Fin (n+1) ≃ Fin (n+1))
    (F : MvPowerSeries (Fin (n+1)) ℂ) (α : Fin (n+1) →₀ ℕ) :
    MvPowerSeries.coeff (Finsupp.domCongr p α) (MvPowerSeries.rename p F) = MvPowerSeries.coeff α F := by
  simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding] using
    MvPowerSeries.coeff_embDomain_rename p.toEmbedding F α

private theorem normalized_eq_of_normal_direction
    (A : Set (Fin (n+1))) (e : Fin (n+1)) (he : e ∈ A)
    (b c : Fin (n+1) → ℂ) (hbc : ∀ i ∈ A, i ≠ e → b i = c i)
    (μ : ℕ) (F : MvPowerSeries (Fin (n+1)) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal (n+1) A ^ μ) :
    actualNormalizedFormalMember A e he b μ F hF = actualNormalizedFormalMember A e he c μ F hF := by
  have hcoords : actualFormalBlowupCoordinates A e b = actualFormalBlowupCoordinates A e c := by
    funext i
    by_cases hi : i ∈ A
    · by_cases hie : i = e
      · simp [actualFormalBlowupCoordinates, hie]
      · simp only [actualFormalBlowupCoordinates, if_pos hi, if_neg hie, hbc i hi hie]
    · simp only [actualFormalBlowupCoordinates, if_neg hi]
  have hblowup : actualFormalBlowup A e b = actualFormalBlowup A e c := by
    apply AlgHom.ext
    intro H
    simp only [actualFormalBlowup, MvPowerSeries.substAlgHom_apply]
    exact congrArg (fun d => MvPowerSeries.subst d H) hcoords
  apply actualNormalizedFormalMember_unique
  rw [← hblowup]
  exact actualNormalizedFormalMember_spec A e he b μ F hF

private theorem normalized_zero_congr
    (A : Set (Fin (n+1))) (e e' : Fin (n+1)) (he : e ∈ A) (he' : e' ∈ A)
    (hee' : e = e') (μ : ℕ) (F G : MvPowerSeries (Fin (n+1)) ℂ) (hFG : F = G)
    (hF : F ∈ actualFormalCoordinateIdeal (n+1) A ^ μ)
    (hG : G ∈ actualFormalCoordinateIdeal (n+1) A ^ μ) :
    actualNormalizedFormalMember A e he (fun _ => 0) μ F hF =
      actualNormalizedFormalMember A e' he' (fun _ => 0) μ G hG := by
  subst e'
  subst G
  rfl

/-- Natural specified-member endpoint: actual SOURCE canonical data and true
whole HS equality internally produce the target diagram and every chart map.
The specified member is never replaced by a canonical series. -/
theorem actual_normalized_member_order_of_hs_eq_and_prefix_support
    (K : Ideal (MvPowerSeries (Fin (n+1)) ℂ)) (q e : Fin (n+1))
    (he : e ∈ normalPivotVariables q) (b : Fin (n+1) → ℂ)
    (hD : ∀ i ∉ normalPivotVariables q, ∀ H ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i H ∈ actualHomogeneousInitialIdeal K)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈
        actualFormalCoordinateIdeal (n+1) (normalPivotVariables q) ^
          Finsupp.weight (actualCoordinateWeight (normalPivotVariables q)) a.val)
    (hHS : ∀ ℓ, genuineFormalHilbertSamuelValue (n+1)
      (actualFormalStrictTransform K (normalPivotVariables q) e he b) ℓ =
        genuineFormalHilbertSamuelValue (n+1) K ℓ)
    (μ : ℕ) (F : MvPowerSeries (Fin (n+1)) ℂ) (hFK : F ∈ K)
    (hF : F ∈ actualFormalCoordinateIdeal (n+1) (normalPivotVariables q) ^ μ)
    (hprefix : ∀ c : actualInitialVertices MonomialOrder.degLex K,
      normalExponentDegree c.val < μ → ∀ α, c.val ≤ α → MvPowerSeries.coeff α F = 0) :
    actualNormalizedFormalMember (normalPivotVariables q) e he b μ F hF ∈
      genuineFormalVariables (n+1) ^ μ := by
  let A := normalPivotVariables q
  let v : Fin (n+1) → ℂ := fun i => actualPointUnitBasePoint e (actualNormalPointDirection A b) i
  obtain ⟨f, hqf, w, hvf, hw, hwt, htri, aP, _aJ, haP, _haJ,
    _hDimage, hDsame, haPval, _hcanonP, _haJval, _hcanonJ⟩ :=
    exists_actual_normal_adapted_canonical_chart_of_hs_eq K q e he b hD hV hHS
  let p := normalPivotEquiv q f
  let KS := Ideal.map (actualFormalCenterShear Set.univ f w).toRingHom K
  let Kp := Ideal.map (normalPivotRename q f).toRingHom KS
  have hfA : f ∈ A := hqf
  have hpA (i : Fin (n+1)) : p i ∈ A ↔ i ∈ A := normal_mem_iff q f hqf i
  have hpf : p f = q := normalPivotEquiv_pivot q f hqf
  have hsymmq : p.symm q = f := by rw [← hpf, Equiv.symm_apply_apply]
  have haPp (a : actualInitialVertices MonomialOrder.degLex K) :
      (aP a).val = Finsupp.domCongr p a.val := haPval a
  have hve : v e = 1 := by simp only [v, actualPointUnitBasePoint_apply, if_true]
  have hvb : ∀ i ∈ A, i ≠ e → v i = b i := by
    intro i hi hie
    simp only [v, actualPointUnitBasePoint_apply, if_neg hie,
      actualNormalPointDirection, if_pos hi]
  have hDir := actual_homogeneous_initial_normal_directional_stable_of_hs_eq K A e he b hD hV hHS
  have hmax : ∀ i : Fin (n+1), v i ≠ 0 →
      MonomialOrder.degLex.toSyn (Finsupp.single i 1) ≤
        MonomialOrder.degLex.toSyn (Finsupp.single f 1) := by
    intro i hi
    by_cases hie : i = f
    · subst i
      exact le_rfl
    · apply (htri i hie ?_).le
      rw [hw]
      exact div_ne_zero hi hvf
  have hfzero (a : actualInitialVertices MonomialOrder.degLex K) : a.val f = 0 :=
    actualInitialVertex_maximal_direction_coordinate_eq_zero MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) v hDir f hvf hmax (actualHomogeneousInitialVertex K a)
  have hpure (a : actualInitialVertices MonomialOrder.degLex K) (i : Fin (n+1)) (hi : i ∉ A) :
      a.val i = 0 :=
    actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
      (actualHomogeneousInitialIdeal K) i (hD i hi) (actualHomogeneousInitialVertex K a)
  have hnewpure (a : actualInitialVertices MonomialOrder.degLex Kp)
      (i : Fin (n+1)) (hi : i ∉ A) : a.val i = 0 := by
    obtain ⟨a, rfl⟩ := haP a
    rw [haPp]
    have hpre : p.symm i ∉ A := by
      intro h
      exact hi (by simpa only [Equiv.apply_symm_apply] using (hpA (p.symm i)).mpr h)
    simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.mapDomain_equiv_apply] using hpure a (p.symm i) hpre
  have hnewq (a : actualInitialVertices MonomialOrder.degLex Kp) : a.val q = 0 := by
    obtain ⟨a, rfl⟩ := haP a
    rw [haPp]
    simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.mapDomain_equiv_apply, hsymmq] using hfzero a
  have hwA : ∀ i ∉ A, w i = 0 := by
    intro i hi
    exact hwt i (lt_of_not_ge hi)
  have hShear := actualFormalCenterShear_normal_eq_point A f w hwA
  let FS := actualFormalCenterShear Set.univ f w F
  let FP := normalPivotRename q f FS
  have hFS : FS ∈ actualFormalCoordinateIdeal (n+1) A ^ μ := by
    have h := (mem_coordinate_power_iff_centerShear A f hfA w μ F).mp hF
    rwa [hShear] at h
  have hFP : FP ∈ actualFormalCoordinateIdeal (n+1) A ^ μ :=
    (mem_coordinate_power_iff_rename p A hpA μ FS).mpr hFS
  have hFPK : FP ∈ Kp :=
    Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hFK)
  have hSsupport := actualFormalCenterShear_proper_prefix_support K f w hfzero μ F hprefix
  have hPsupport : ∀ c : actualInitialVertices MonomialOrder.degLex Kp,
      normalExponentDegree c.val < μ → ∀ α, c.val ≤ α → MvPowerSeries.coeff α FP = 0 := by
    intro c hc α hcα
    obtain ⟨c, rfl⟩ := haP c
    obtain ⟨β, rfl⟩ := (Finsupp.domCongr p).surjective α
    have hcdegree : normalExponentDegree c.val < μ := by
      rw [haPval, permute_degree] at hc
      exact hc
    have hcβ : c.val ≤ β := by
      intro i
      have h := hcα (p i)
      rw [haPp] at h
      simpa only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
        Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply] using h
    change MvPowerSeries.coeff (Finsupp.domCongr p β) (MvPowerSeries.rename p FS) = 0
    rw [coeff_rename_permuted]
    exact hSsupport c hcdegree β hcβ
  have horderP := actual_normal_zero_member_order_of_same_diagram Kp q hnewpure hnewq
    hDsame μ FP hFPK hFP hPsupport
  have hrename := rename_actual_normal_normalized_member p A hpA f hfA (fun _ => 0) μ FS hFS
  have horderRename : MvPowerSeries.rename p
      (actualNormalizedFormalMember A f hfA (fun _ => 0) μ FS hFS) ∈
        genuineFormalVariables (n+1) ^ μ := by
    rw [hrename]
    rw [normalized_zero_congr A (p f) q ((hpA f).mpr hfA)
      (by change q ≤ q; exact le_rfl) hpf μ (MvPowerSeries.rename p FS) FP rfl
      ((mem_coordinate_power_iff_rename p A hpA μ FS).mpr hFS) hFP]
    exact horderP
  have hpoint : actualFormalCoordinateIdeal (n+1) Set.univ = genuineFormalVariables (n+1) := by
    simp only [actualFormalCoordinateIdeal, Set.image_univ, genuineFormalVariables]
  have horderS : actualNormalizedFormalMember A f hfA (fun _ => 0) μ FS hFS ∈
      genuineFormalVariables (n+1) ^ μ := by
    rw [← hpoint] at horderRename ⊢
    exact (mem_coordinate_power_iff_rename p Set.univ (fun _ => iff_true_intro (mem_univ _)) μ _).mp horderRename
  have horderW : actualNormalizedFormalMember A f hfA w μ F hF ∈
      genuineFormalVariables (n+1) ^ μ := by
    have hN : actualNormalizedFormalMember A f hfA (fun _ => 0) μ FS hFS =
        actualNormalizedFormalMember A f hfA w μ F hF := by
      apply actualNormalizedFormalMember_unique
      rw [actualNormalizedFormalMember_spec]
      dsimp only [FS]
      rw [← hShear]
      exact (actualFormalBlowup_eq_zero_comp_centerShear A f hfA w F).symm
    rwa [hN] at horderS
  have horderV : actualNormalizedFormalMember A e he v μ F hF ∈
      genuineFormalVariables (n+1) ^ μ := by
    apply (normalized_member_mem_power_iff_normal_chart_transition A e f he hfA v hve hvf μ F hF μ).mpr
    have hwv : actualNormalChartNormalizedDirection f v = w := hw.symm
    have hN := congrArg (fun c => actualNormalizedFormalMember A f hfA c μ F hF) hwv
    rw [hN]
    exact horderW
  rw [normalized_eq_of_normal_direction A e he v b hvb μ F hF] at horderV
  exact horderV

variable {K : Ideal (MvPowerSeries (Fin (n+1)) ℂ)}

private theorem coordinate_weight_le_degree (A : Set (Fin (n+1))) (α : Fin (n+1) →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight A) α ≤ normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum, normalExponentDegree]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ A <;> simp [actualCoordinateWeight, hi]

private theorem source_vertices_pure (G : ActualAnalyticInheritedFamily (n+1) 0 K)
    (A : Set (Fin (n+1)))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal A ^ normalExponentDegree a.val) :
    ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i ∉ A, a.val i = 0 := by
  intro a i hi
  have hp := actualTaylor_mem_coordinateCentre_pow A _ (G.germs a) (hpower a)
  have hw : normalExponentDegree a.val ≤ Finsupp.weight (actualCoordinateWeight A) a.val := by
    by_contra h
    have hz := (mem_actualFormalCoordinateIdeal_pow_iff A _ _).mp hp a.val (lt_of_not_ge h)
    have hc : MvPowerSeries.coeff a.val
        (actualUnshiftedTaylorAlgHom (n+1) (G.germs a)) = 1 := G.monic a
    rw [hc] at hz
    exact one_ne_zero hz
  have he : Finsupp.weight (actualCoordinateWeight A) a.val = normalExponentDegree a.val :=
    le_antisymm (coordinate_weight_le_degree A a.val) hw
  have hsum : Finsupp.weight (actualCoordinateWeight A) a.val +
      Finsupp.weight (actualCoordinateWeight Aᶜ) a.val = normalExponentDegree a.val := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ A <;> simp [actualCoordinateWeight, hj]
  have hle : a.val i ≤ Finsupp.weight (actualCoordinateWeight Aᶜ) a.val := by
    rw [Finsupp.weight_eq_sum]
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (a.val j • actualCoordinateWeight Aᶜ j))
      (Finset.mem_univ i)
    simpa only [actualCoordinateWeight, Set.mem_compl_iff, if_pos hi, smul_eq_mul, mul_one] using h
  omega

/-- Natural CURRENT-family endpoint: genuine membership and marked normal
powers internally produce source canonical compatibility and tangent
stability. No contact or target certificate is required for these orders. -/
theorem actual_normal_hs_equal_inherited_member_orders
    (G : ActualAnalyticInheritedFamily (n+1) 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom (n+1) (G.germs a) ∈ K)
    (q e : Fin (n+1)) (he : e ∈ normalPivotVariables q) (b : Fin (n+1) → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (normalPivotVariables q) ^
      normalExponentDegree a.val)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (hHS : ∀ ℓ, genuineFormalHilbertSamuelValue (n+1)
      (actualFormalStrictTransform K (normalPivotVariables q) e he b) ℓ =
        genuineFormalHilbertSamuelValue (n+1) K ℓ) :
    ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualNormalizedFormalMember (normalPivotVariables q) e he b (normalExponentDegree a.val)
        (actualUnshiftedTaylorAlgHom (n+1) (G.germs a))
        (actualTaylor_mem_coordinateCentre_pow (normalPivotVariables q) _ (G.germs a) (hpower a)) ∈
          genuineFormalVariables (n+1) ^ normalExponentDegree a.val := by
  let A := normalPivotVariables q
  let B : ActualMonicVertexFamily MonomialOrder.degLex K :=
    { series := fun a => actualUnshiftedTaylorAlgHom (n+1) (G.germs a)
      mem := hmem
      monic := G.monic
      lower := G.lower }
  have hB (a : actualInitialVertices MonomialOrder.degLex K) :
      B.series a ∈ actualFormalCoordinateIdeal (n+1) A ^ Finsupp.weight (actualCoordinateWeight A) a.val := by
    exact (Ideal.pow_le_pow_right (coordinate_weight_le_degree A a.val))
      (actualTaylor_mem_coordinateCentre_pow A _ (G.germs a) (hpower a))
  have hV := actualReducedVertexSeries_mem_coordinate_power_of_family MonomialOrder.degLex K B A hB
  have hpure := source_vertices_pure G A hpower
  have hD := actual_tangent_initial_stability_of_pure_vertices_normal_powers K A hpure hV
  intro a
  apply actual_normalized_member_order_of_hs_eq_and_prefix_support K q e he b hD hV hHS
    (normalExponentDegree a.val) (actualUnshiftedTaylorAlgHom (n+1) (G.germs a)) (hmem a)
    (actualTaylor_mem_coordinateCentre_pow A _ (G.germs a) (hpower a))
  intro c hc α hcα
  exact hred (normalExponentDegree c.val) a hc c le_rfl α hcα

end
end Hironaka.HironakaActualInheritedNormalMemberOrder
