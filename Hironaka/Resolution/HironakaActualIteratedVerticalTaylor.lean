import Hironaka.Resolution.HironakaActualProjectionVerticalFunctionOrder

/-! Finite composites of the held actual vertical substitution in ONE fixed
source frame. All coefficients, germs and thresholds include zero/infinity.
This constructs no arbitrary-q geometric history or next cosupport. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualIteratedVerticalTaylor
noncomputable section
open Hironaka.HolomorphicIdealSheaves RelativePrincipalizationSpan
  HironakaRelativeNormalMonomialBasis HironakaActualFormalMonomialBlowupReflection
  HironakaActualPointNormalizedExponents HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalCoordinatePowerDivision HironakaActualAnalyticBlowupTaylor
  HironakaActualTaylorCoordinateNaturality HironakaActualCoefficientPresentationCentrePower
  HironakaRelativeNormalIdeal HolGerm HironakaActualOriginalFormalTaylor
  HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance GermIdealOrder IdealWeightPowers

/-- The fixed original old block and its q-fold LAST insertion. -/
def iteratedVerticalExponent (n q : ℕ) (α : Fin n →₀ ℕ) : Fin (n+1) →₀ ℕ :=
  Finsupp.embDomain (Fin.castAddEmb 1) α + Finsupp.single (Fin.last n) (q*normalExponentDegree α)

/-- Only the genuine previously constructed formal algebra map is iterated. -/
def iteratedVerticalFormal {n : ℕ} : ℕ → MvPowerSeries (Fin n) ℂ → MvPowerSeries (Fin (n+1)) ℂ
  | 0,F => MvPowerSeries.rename (Fin.castAdd 1) F
  | q+1,F => actualFormalBlowup Set.univ (Fin.last n) (fun _ => 0) (iteratedVerticalFormal q F)

private theorem cast_ne_last {n : ℕ} (i : Fin n) : i.castAdd 1 ≠ Fin.last n := by
  intro h
  have hh := congrArg Fin.val h
  change i.val=n at hh
  omega

private theorem last_not_cast {n : ℕ} :
    Fin.last n∉Set.range (Fin.castAddEmb 1 : Fin n ↪ Fin (n+1)) := by
  rintro ⟨i,hi⟩
  exact cast_ne_last i hi

private theorem exponent_old {n : ℕ} (q : ℕ) (α : Fin n →₀ ℕ) (i : Fin n) :
    iteratedVerticalExponent n q α (i.castAdd 1)=α i := by
  change (Finsupp.embDomain (Fin.castAddEmb 1) α) ((Fin.castAddEmb 1) i)+
    Finsupp.single (Fin.last n) (q*normalExponentDegree α) (i.castAdd 1)=α i
  rw [Finsupp.embDomain_apply_self]
  simp [cast_ne_last i]

private theorem exponent_injective (n q : ℕ) : Function.Injective (iteratedVerticalExponent n q) := by
  intro α β h
  ext i
  simpa only [exponent_old] using congrArg (fun δ : Fin (n+1) →₀ ℕ => δ (i.castAdd 1)) h

private theorem embedded_degree {n : ℕ} (α : Fin n →₀ ℕ) :
    normalExponentDegree (Finsupp.embDomain (Fin.castAddEmb 1) α)=normalExponentDegree α := by
  have h := Finsupp.degree_mapDomain (Fin.castAddEmb 1) α
  simpa only [normalExponentDegree,Finsupp.embDomain_eq_mapDomain,Finsupp.degree_eq_sum] using h

private theorem exponent_degree {n : ℕ} (q : ℕ) (α : Fin n →₀ ℕ) :
    normalExponentDegree (iteratedVerticalExponent n q α)=(q+1)*normalExponentDegree α := by
  have h : normalExponentDegree (iteratedVerticalExponent n q α)=
      normalExponentDegree (Finsupp.embDomain (Fin.castAddEmb 1) α)+q*normalExponentDegree α := by
    simp [iteratedVerticalExponent,normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]
  rw [h,embedded_degree]
  ring

private theorem exponent_step {n : ℕ} (q : ℕ) (α : Fin n →₀ ℕ) :
    actualMonomialBlowupExponent Set.univ (Fin.last n) (iteratedVerticalExponent n q α)=
      iteratedVerticalExponent n (q+1) α := by
  let β := Finsupp.embDomain (Fin.castAddEmb 1) α
  have he : β (Fin.last n)=0 := Finsupp.embDomain_of_notMem_range _ _ _ last_not_cast
  have hw : Finsupp.weight (actualCoordinateWeight (Set.univ\{Fin.last n})) β=
      normalExponentDegree α := by
    have hb : Finsupp.weight (actualCoordinateWeight (Set.univ\{Fin.last n})) β=
        normalExponentDegree β := by
      rw [Finsupp.weight_eq_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i=Fin.last n
      · subst i; simp [actualCoordinateWeight,he]
      · simp [actualCoordinateWeight,hi]
    exact hb.trans (embedded_degree α)
  have hq : Finsupp.weight (actualCoordinateWeight (Set.univ\{Fin.last n}))
      (iteratedVerticalExponent n q α)=normalExponentDegree α := by
    change Finsupp.weight _ (β+Finsupp.single (Fin.last n) (q*normalExponentDegree α))=_
    simp [map_add,Finsupp.weight_single,actualCoordinateWeight,hw]
  change iteratedVerticalExponent n q α+Finsupp.single (Fin.last n)
    (Finsupp.weight (actualCoordinateWeight (Set.univ\{Fin.last n})) (iteratedVerticalExponent n q α))=_
  rw [hq]
  ext i
  simp only [iteratedVerticalExponent,Finsupp.add_apply]
  by_cases hi : i=Fin.last n
  · subst i; simp only [Finsupp.single_eq_same]; ring
  · simp [Finsupp.single_eq_of_ne hi]

private theorem formal_coefficient {n : ℕ} (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff (iteratedVerticalExponent n q α) (iteratedVerticalFormal q F)=
      MvPowerSeries.coeff α F := by
  induction q with
  | zero => simpa [iteratedVerticalExponent,iteratedVerticalFormal] using
      MvPowerSeries.coeff_embDomain_rename (Fin.castAddEmb 1) F α
  | succ q ih =>
    rw [iteratedVerticalFormal,←exponent_step,actualFormalBlowup_zero_coefficient,ih]

private theorem formal_preimage {n : ℕ} (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (γ : Fin (n+1) →₀ ℕ) (hγ : MvPowerSeries.coeff γ (iteratedVerticalFormal q F)≠0) :
    ∃α : Fin n →₀ ℕ,iteratedVerticalExponent n q α=γ ∧ MvPowerSeries.coeff α F≠0 := by
  induction q generalizing γ with
  | zero =>
    have hb : γ∈Set.range (Finsupp.embDomain (Fin.castAddEmb 1)) := by
      by_contra h
      apply hγ
      apply MvPowerSeries.coeff_rename_eq_zero
      rintro ⟨α,hα⟩
      refine h ⟨α,?_⟩
      rw [Finsupp.embDomain_eq_mapDomain]
      change Finsupp.mapDomain (Fin.castAdd 1) α=γ
      exact hα
    obtain ⟨α,rfl⟩ := hb
    refine ⟨α,by simp [iteratedVerticalExponent],?_⟩
    change MvPowerSeries.coeff (Finsupp.embDomain (Fin.castAddEmb 1) α)
      (MvPowerSeries.rename (Fin.castAddEmb 1) F)≠0 at hγ
    simpa only [MvPowerSeries.coeff_embDomain_rename] using hγ
  | succ q ih =>
    have hb : γ∈Set.range (actualMonomialBlowupExponent Set.univ (Fin.last n)) := by
      by_contra h
      exact hγ (actualFormalBlowup_zero_coefficient_outside_image Set.univ (Fin.last n) _ γ h)
    obtain ⟨β,hβ⟩ := hb
    have hc : MvPowerSeries.coeff β (iteratedVerticalFormal q F)≠0 := by
      rw [←actualFormalBlowup_zero_coefficient Set.univ (Fin.last n),hβ]
      exact hγ
    obtain ⟨α,hα,hc⟩ := ih β hc
    exact ⟨α,(exponent_step q α).symm.trans (congrArg _ hα |>.trans hβ),hc⟩

/-- Exact coefficient preservation, full image and degree for EVERY series. -/
theorem iterated_vertical_coefficients (n q : ℕ) :
    Function.Injective (iteratedVerticalExponent n q) ∧
      (∀α,normalExponentDegree (iteratedVerticalExponent n q α)=(q+1)*normalExponentDegree α) ∧
      (∀F α,MvPowerSeries.coeff (iteratedVerticalExponent n q α) (iteratedVerticalFormal q F)=
        MvPowerSeries.coeff α F) ∧
      (∀F γ,γ∉Set.range (iteratedVerticalExponent n q) →
        MvPowerSeries.coeff γ (iteratedVerticalFormal q F)=0) := by
  refine ⟨exponent_injective n q,exponent_degree q,formal_coefficient q,?_⟩
  intro F γ hγ
  by_contra h
  obtain ⟨α,hα,_⟩ := formal_preimage q F γ h
  exact hγ ⟨α,hα⟩

/-- Every nonzero output coefficient has its unique actual original exponent. -/
theorem iterated_vertical_nonzero_preimage {n : ℕ} (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (γ : Fin (n+1) →₀ ℕ) (hγ : MvPowerSeries.coeff γ (iteratedVerticalFormal q F)≠0) :
    ∃!α : Fin n →₀ ℕ,iteratedVerticalExponent n q α=γ ∧
      MvPowerSeries.coeff α F=MvPowerSeries.coeff γ (iteratedVerticalFormal q F) := by
  obtain ⟨α,hα,_⟩ := formal_preimage q F γ hγ
  refine ⟨α,⟨hα,?_⟩,fun β hβ => exponent_injective n q (hβ.1.trans hα.symm)⟩
  rw [←hα,formal_coefficient]

/-- Genuine whole germ maps, with only ONE initial projection. -/
def iteratedVerticalGerm {n : ℕ} : ℕ → HolGerm (ComplexModel n) → HolGerm (ComplexModel (n+1))
  | 0,g => tangentPullback n 1 g
  | q+1,g => actualAnalyticBlowupPullback Set.univ (Fin.last n) (fun _ => 0) (iteratedVerticalGerm q g)

/-- The independently defined actual polynomial finite composite. -/
def iteratedVerticalBase (n q : ℕ) : ComplexModel (n+1) → ComplexModel n :=
  tangentProjection n 1 ∘ (actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _ => 0))^[q]

private theorem iterate_coordinates (n q : ℕ) (w : ComplexModel (n+1)) :
    (∀i : Fin n,(actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _ => 0))^[q] w (i.castAdd 1)=
      w (Fin.last n)^q*w (i.castAdd 1)) ∧
    (actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _ => 0))^[q] w (Fin.last n)=w (Fin.last n) := by
  induction q generalizing w with
  | zero => simp
  | succ q ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨ho,he⟩ := ih (actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _ => 0) w)
    constructor
    · intro i
      rw [ho i]
      simp only [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,mem_univ,
        if_pos,cast_ne_last i,if_false,zero_add,pow_succ]
      ring
    · simpa [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate] using he

/-- Full old block and unchanged fibre of the actual polynomial composite. -/
theorem iterated_vertical_base_coordinates (n q : ℕ) (w : ComplexModel (n+1)) :
    (∀i : Fin n,iteratedVerticalBase n q w i=w (Fin.last n)^q*w (i.castAdd 1)) ∧
      (actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _ => 0))^[q] w (Fin.last n)=w (Fin.last n) :=
  iterate_coordinates n q w

/-- The actual composed polynomial fixes the actual source origin. -/
theorem iterated_vertical_base_zero (n q : ℕ) : iteratedVerticalBase n q 0=0 := by
  ext i
  rw [(iterated_vertical_base_coordinates n q 0).1 i]
  simp

/-- Holomorphicity is finite composition of held polynomial maps. -/
theorem differentiable_iteratedVerticalBase (n q : ℕ) : Differentiable ℂ (iteratedVerticalBase n q) := by
  have hi : Differentiable ℂ ((actualAnalyticBlowupMap Set.univ (Fin.last n) (fun _ => 0))^[q]) := by
    induction q with
    | zero => exact differentiable_id
    | succ q ih =>
      rw [Function.iterate_succ]
      exact ih.comp (differentiable_actualAnalyticBlowupMap _ _ _)
  exact (tangentProjection n 1).differentiable.comp hi

private theorem composed_differentiable {n : ℕ} (q : ℕ) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ F z) :
    ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),DifferentiableAt ℂ (F∘iteratedVerticalBase n q) w := by
  have ht : Tendsto (iteratedVerticalBase n q) (𝓝 0) (𝓝 0) := by
    simpa only [iterated_vertical_base_zero] using (differentiable_iteratedVerticalBase n q).continuous.tendsto 0
  filter_upwards [ht.eventually hF] with w hw
  exact hw.comp w (differentiable_iteratedVerticalBase n q).differentiableAt

/-- The actual representative composition is derived for every function. -/
theorem iterated_vertical_germ_mk {n : ℕ} (q : ℕ) (F : ComplexModel n → ℂ)
    (hF : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ F z) :
    iteratedVerticalGerm q (HolGerm.mk F hF)=
      HolGerm.mk (F∘iteratedVerticalBase n q) (composed_differentiable q F hF) := by
  induction q with
  | zero =>
    unfold iteratedVerticalGerm tangentPullback
    rw [compAlgHom_mk]
    rfl
  | succ q ih =>
    rw [iteratedVerticalGerm,ih]
    unfold actualAnalyticBlowupPullback
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => by
      simp only [Function.comp_apply,iteratedVerticalBase,Function.iterate_succ_apply]

/-- The whole original Taylor square follows by the two held squares. -/
theorem iterated_vertical_Taylor (n q : ℕ) (g : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom (n+1) (iteratedVerticalGerm q g)=
      iteratedVerticalFormal q (actualUnshiftedTaylorAlgHom n g) := by
  induction q with
  | zero => exact DFunLike.congr_fun (actualUnshiftedTaylor_tangentPullback n 1) g
  | succ q ih =>
    have h := DFunLike.congr_fun (actualTaylor_analyticBlowupPullback Set.univ (Fin.last n) (fun _ => 0))
      (iteratedVerticalGerm q g)
    simp only [AlgHom.comp_apply] at h
    change actualUnshiftedTaylorAlgHom (n+1)
      (actualAnalyticBlowupPullback _ _ _ (iteratedVerticalGerm q g))=_
    rw [h,ih]
    rfl

/-- All integer coefficient thresholds, without a nonzero premise. -/
theorem iterated_vertical_coefficient_cut {n : ℕ} (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) (t : ℕ) :
    (∀γ : Fin (n+1) →₀ ℕ,normalExponentDegree γ<t →
      MvPowerSeries.coeff γ (iteratedVerticalFormal q F)=0) ↔
      ∀α : Fin n →₀ ℕ,(q+1)*normalExponentDegree α<t → MvPowerSeries.coeff α F=0 := by
  constructor
  · intro h α hα
    rw [←formal_coefficient q F α]
    apply h
    rwa [exponent_degree]
  · intro h γ hγ
    by_contra hc
    obtain ⟨α,hα,hc⟩ := formal_preimage q F γ hc
    rw [←hα,exponent_degree] at hγ
    exact hc (h α hγ)

private theorem formal_zero (n q : ℕ) : iteratedVerticalFormal (n:=n) q 0=0 := by
  induction q with
  | zero => exact map_zero _
  | succ q ih => simp only [iteratedVerticalFormal,ih,map_zero]

/-- Exact ENat scaling includes zero series, infinite order and finite order0. -/
theorem iterated_vertical_order (n q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    (iteratedVerticalFormal q F).order=((q+1 : ℕ) : ℕ∞)*F.order := by
  by_cases hF : F=0
  · subst F
    rw [formal_zero]
    simp
  · let N := F.order.toNat
    have hfin : (N : ℕ∞)=F.order := MvPowerSeries.ne_zero_iff_order_finite.mp hF
    obtain ⟨α,hα,hd⟩ := MvPowerSeries.exists_coeff_ne_zero_and_order hfin
    have hαdeg : normalExponentDegree α=N := by
      have hh : (normalExponentDegree α : ℕ∞)=(N : ℕ∞) := by
        simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hd.trans hfin.symm
      exact_mod_cast hh
    have hout : (iteratedVerticalFormal q F).order=((q+1)*N : ℕ) := by
      apply MvPowerSeries.order_eq_nat.mpr
      constructor
      · refine ⟨iteratedVerticalExponent n q α,?_,?_⟩
        · rwa [formal_coefficient]
        · have hh := exponent_degree q α
          rw [hαdeg] at hh
          simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hh
      · intro γ hγ
        have hcut : ∀β : Fin n →₀ ℕ,(q+1)*normalExponentDegree β<(q+1)*N →
            MvPowerSeries.coeff β F=0 := by
          intro β hβ
          apply MvPowerSeries.coeff_of_lt_order
          rw [←hfin]
          have hβN : normalExponentDegree β<N := Nat.lt_of_mul_lt_mul_left hβ
          exact_mod_cast (by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hβN)
        exact (iterated_vertical_coefficient_cut q F ((q+1)*N)).mpr hcut γ
          (by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hγ)
    simpa only [Nat.cast_mul,hfin] using hout

private theorem actual_maximal_pow_iff {n : ℕ} (t : ℕ) (g : HolGerm (ComplexModel n)) :
    g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^t ↔
      ∀α : Fin n →₀ ℕ,normalExponentDegree α<t →
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n g)=0 := by
  let P (s : ℕ) (f : HolGerm (ComplexModel s)→ₐ[ℂ]MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀h : HolGerm (ComplexModel s),h∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel s))^t ↔
      ∀α : Fin n →₀ ℕ,normalExponentDegree α<t → MvPowerSeries.coeff α (f h)=0
  have hP : P (0+n) (originalTaylorAlgHom n) := fun h =>
    mem_original_maximal_pow_iff_formal_coefficients_zero n t h
  have transport {s : ℕ} (hs : s=n)
      (f : HolGerm (ComplexModel s)→ₐ[ℂ]MvPowerSeries (Fin n) ℂ) (h : P s f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j)→ₐ[ℂ]MvPowerSeries (Fin n) ℂ) hs) f) := by
    subst s
    exact h
  exact transport (Nat.zero_add n) (originalTaylorAlgHom n) hP g

/-- ALL actual maximal-power cuts of the genuine original germ composite. -/
theorem iterated_vertical_maximal_cut (n q t : ℕ) (g : HolGerm (ComplexModel n)) :
    iteratedVerticalGerm q g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^t ↔
      ∀α : Fin n →₀ ℕ,(q+1)*normalExponentDegree α<t →
        MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n g)=0 := by
  rw [actual_maximal_pow_iff,iterated_vertical_Taylor,iterated_vertical_coefficient_cut]

/-- Exact multiple thresholds retain the original maximal power. -/
theorem iterated_vertical_maximal_multiple_cut (n q r : ℕ) (g : HolGerm (ComplexModel n)) :
    iteratedVerticalGerm q g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^((q+1)*r) ↔
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^r := by
  rw [iterated_vertical_maximal_cut,actual_maximal_pow_iff]
  apply forall_congr'
  intro α
  rw [Nat.mul_lt_mul_left (Nat.succ_pos q)]

/-- Every intermediate successor threshold, including the two extreme offsets. -/
theorem iterated_vertical_maximal_successor_cut (n q r s : ℕ) (hs : s≤q)
    (g : HolGerm (ComplexModel n)) :
    iteratedVerticalGerm q g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^((q+1)*r+s+1) ↔
      g∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^(r+1) := by
  rw [iterated_vertical_maximal_cut,actual_maximal_pow_iff]
  apply forall_congr'
  intro α
  have hh : (q+1)*normalExponentDegree α<(q+1)*r+s+1 ↔ normalExponentDegree α<r+1 := by
    constructor
    · intro h
      by_contra hn
      have hl : r+1≤normalExponentDegree α := by omega
      have hp := Nat.mul_le_mul_left (q+1) hl
      nlinarith
    · intro h
      have hl : normalExponentDegree α≤r := by omega
      have hp := Nat.mul_le_mul_left (q+1) hl
      omega
  rw [hh]

/-- ALL original functions and literal point-power thresholds, at the same model. -/
theorem iterated_vertical_point_cuts (n q : ℕ) :
    ∀(F : ComplexModel n → ℂ) (hF : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ F z) (t : ℕ),
      (idealPow (pointIdeal (n+1) (0 : ComplexModel (n+1))) t).mem 0 (F∘iteratedVerticalBase n q) ↔
        ∀α : Fin n →₀ ℕ,(q+1)*normalExponentDegree α<t →
          MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (HolGerm.mk F hF))=0 := by
  intro F hF t
  rw [←mem_maximalIdeal_pow_iff_point_power (composed_differentiable q F hF) t,
    ←iterated_vertical_germ_mk,iterated_vertical_maximal_cut]

end
end Hironaka.HironakaActualIteratedVerticalTaylor
