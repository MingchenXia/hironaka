import Hironaka.Analytic.PullbackNonvanishing
import Hironaka.Blowup.BlowupKahler
import Hironaka.Blowup.BlowupExceptionalCentre
import Hironaka.Blowup.BlowupBigPullback
import Hironaka.Analytic.FactorizedWeightPsh
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.Analytic.FormPullbackFunctorial
import Hironaka.Blowup.ExceptionalLocus

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Exceptional correction of a pulled-back Kähler form

Let `(X, ω)` be a compact Kähler manifold and `π : Y → X` a composition of blowups with smooth
centres.  There is an effective `ℚ`-divisor `E` supported in `Exc π`, with a smooth metric, such
that `π^* ω - Θ_E` is Kähler.

* `ofWeightFactorization`: for a weight `U ≥ 0` with local factorizations `U = |h|² U'` and
  `q ∈ ℚ_{>0}`, the divisor `q · div U` with weight `q log U` and curvature `-q ddᶜ log U`.
* `isKahler_add_smul_of_le`: if `A ≥ 0` and `A + ε Θ` is Kähler, so is `A + q Θ` for `0 < q ≤ ε`.
* `exists_exceptionalMetric`: induction over the sequence.  For one more blowup `g : Z → Y` along
  `C`, with `β = f^* ω - Θ_E` Kähler on `Y`, take the Blanchard weight `U` of the exceptional
  centre `C₂ = g(Exc g)` (`π⁻¹ C₂ = Exc g`), so that `g^* β + ε Θ_U` is Kähler, choose a
  rational `0 < q ≤ ε`, and set `E' = g^* E + q · div (U ∘ g)`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ExceptionalMetricProof

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.NumericalRestrictedVolumeScaffold Hironaka.BlowupSequences
  FactorizedWeightForm FactorizedWeightPsh MeteredDivisorOperations

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **The divisor `q · div U`** of a factorized weight, with weight `q log U` and curvature
`-q ddᶜ log U`. -/
def ofWeightFactorization {U : M → ℝ} (F : WeightFactorization n U) (q : ℚ) (hq : 0 < q) :
    MeteredEffectiveQDivisor n M where
  weight := fun y => ((q : ℝ) : EReal) * logWeight U y
  curvature := (-(q : ℝ)) • F.closedForm
  local_presentation := fun x => by
    refine ⟨F.domain x, F.isOpen_domain x, F.mem_domain x, 1, fun _ => q, fun _ => F.gen x,
      fun y => (q : ℝ) * Real.log (F.smoothPart x y), fun _ => hq.le,
      fun _ y hy => (F.gen_mdifferentiable x y hy).mdifferentiableWithinAt, ?_, ?_, ?_, ?_⟩
    · intro _ W hW hWU hWne
      obtain ⟨y, hyW, hy⟩ := F.nowhereZero W hW hWne
      exact ⟨y, hyW, F.gen_ne_zero_of (hWU hyW) hy⟩
    · intro e
      exact contDiffOn_const.mul ((F.smooth x e).log fun u hu => (F.pos x _ hu.2).ne')
    · intro y hy
      have hU := F.factor x y hy
      have hpos := F.pos x y hy
      simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
      by_cases hg : F.gen x y = 0
      · have hU0 : U y = 0 := by rw [hU, hg]; simp
        have hbot : generatorLog (fun _ : Fin 1 => F.gen x) y = ⊥ := by
          simp [generatorLog_eq_bot_iff, hg]
        have hq' : (0 : EReal) < ((q : ℝ) : EReal) := by exact_mod_cast hq
        rw [hbot, EReal.mul_bot_of_pos hq', EReal.bot_add]
        simp [logWeight, hU0, EReal.mul_bot_of_pos hq']
      · have hns : 0 < Complex.normSq (F.gen x y) := Complex.normSq_pos.mpr hg
        have hUpos : 0 < U y := by rw [hU]; exact mul_pos hns hpos
        rw [logWeight_of_pos hUpos, generatorLog_of_nonzero ⟨0, hg⟩, hU,
          Real.log_mul hns.ne' hpos.ne']
        have hgen : generatorNormSq (fun _ : Fin 1 => F.gen x) y = Complex.normSq (F.gen x y) := by
          simp [generatorNormSq, Complex.sq_norm]
        rw [hgen, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, mul_add]
    · intro e z hz hzU
      have hS : IsOpen (e.val.target ∩ e.val.symm ⁻¹' F.domain x) :=
        e.val.isOpen_inter_preimage_symm (F.isOpen_domain x)
      have hsm := (F.smooth x e).log fun u hu => (F.pos x _ hu.2).ne'
      rw [ClosedRealOneOneForm.coeff_smul, (F.closedForm_coeff_eventuallyEq x e hz hzU).self_of_nhds]
      have h := smoothDDC_smul hS hsm (q : ℝ) ⟨hz, hzU⟩
      simp only [smul_eq_mul] at h
      rw [h]
      ext v
      simp

theorem ofWeightFactorization_support_subset {U : M → ℝ} (F : WeightFactorization n U) (q : ℚ)
    (hq : 0 < q) {S : Set M} (hS : ∀ y ∉ S, 0 < U y) :
    (ofWeightFactorization F q hq).support ⊆ S := by
  intro y hy
  by_contra hyS
  have h : ((q : ℝ) : EReal) * logWeight U y = ⊥ := by exact hy
  rw [logWeight_of_pos (hS y hyS), ← EReal.coe_mul] at h
  exact EReal.coe_ne_bot _ h

theorem isKahler_of_isStrictlyPositive {a : ClosedRealOneOneForm n M}
    (h : ∀ (e : ComplexChart n M) z, z ∈ e.val.target → IsStrictlyPositive (a.val.coeff e z)) :
    a.val.IsKahler :=
  ⟨fun e z hz => ⟨a.property.2 e z hz, h e z hz⟩, a.property.1⟩

/-- If `A ≥ 0` and `A + ε Θ` is Kähler, then so is `A + q Θ` for `0 < q ≤ ε`. -/
theorem isKahler_add_smul_of_le {A Θ : ClosedRealOneOneForm n M} (hA : A.val.IsSemipositive)
    {ε q : ℝ} (hε : 0 < ε) (hq : 0 < q) (hqε : q ≤ ε) (hK : (A + ε • Θ).val.IsKahler) :
    (A + q • Θ).val.IsKahler := by
  refine isKahler_of_isStrictlyPositive fun e z hz v hv => ?_
  have h1 := (hK.1 e z hz).2 v hv
  have h2 := hA e z hz v
  simp only [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul] at h1 ⊢
  set a := A.val.coeff e z ![v, Complex.I • v]
  set b := Θ.val.coeff e z ![v, Complex.I • v]
  have key : a + q * b = (1 - q / ε) * a + (q / ε) * (a + ε * b) := by
    field_simp
    ring
  rw [key]
  have ht1 : 0 ≤ 1 - q / ε := by rw [sub_nonneg, div_le_one hε]; exact hqε
  have ht2 : 0 < q / ε := div_pos hq hε
  nlinarith [mul_nonneg ht1 h2, mul_pos ht2 h1]

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- **Exceptional correction**, with compactness of the blown-up manifold carried along the
induction. -/
theorem exists_exceptionalMetric_aux [CompactSpace X] (omega : KahlerBackground n X)
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {π : Y → X} (hπ : IsBlowupSequence n X Y π) :
    CompactSpace Y ∧ ∃ E : MeteredEffectiveQDivisor n Y, E.support ⊆ exceptionalLocus n π ∧
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature).val.IsKahler := by
  induction hπ with
  | refl =>
    refine ⟨inferInstance, zero n X, by simp [zero_support],
      isKahler_of_isStrictlyPositive fun e z hz => ?_⟩
    have h := SmoothRealForm.pullback_id_geometricallyEq omega.form.val e hz
    rw [BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.pullback_val]
    erw [h]
    simpa [zero] using (omega.isKahler.1 e z hz).2
  | step f C g hf hg ih =>
    obtain ⟨hYc, E, hEsupp, hK⟩ := ih
    have : CompactSpace _ := BlowupCompact.compactSpace_of_isBlowupAlong hg
    let β : KahlerBackground n _ := ⟨_, hK⟩
    obtain ⟨D, -, hflat⟩ := BlowupExceptionalCentre.exists_blanchardData_exceptionalCentre hg
    have hC₂ : ∀ z, g z ∈ BlowupExceptionalCentre.exceptionalCentre n g →
        z ∈ exceptionalLocus n g := fun z hz => by
      rw [← BlowupExceptionalCentre.preimage_exceptionalCentre hg]; exact hz
    obtain ⟨F, ε, hε, hKZ⟩ := BlowupKahler.exists_isKahler_pullback_add_of_flat β hg D hflat
      (BlowupExceptionalCentre.isClosed_exceptionalCentre hg)
      (BlowupExceptionalCentre.exceptionalCentre_subset hg) fun z hz hE => hz (by
        rw [← BlowupExceptionalCentre.preimage_exceptionalCentre hg] at hE; exact hE)
    obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
    have hq : (0 : ℚ) < q := by exact_mod_cast hq0
    have hint : interior (exceptionalLocus n g) = ∅ :=
      subset_empty_iff.mp ((interior_mono fun z hz =>
        BlowupIsomorphismOff.exceptionalLocus_subset_preimage hg hz).trans
          (ExceptionalFibres.interior_preimage_eq_empty hg).subset)
    refine ⟨inferInstance, add (pullback hg.contMDiff hint E) (ofWeightFactorization F q hq), ?_, ?_⟩
    · intro z hz
      rw [exceptionalLocus_comp (hf.contMDiff.mdifferentiable (by simp))
        (hg.contMDiff.mdifferentiable (by simp))]
      rcases add_support_subset _ _ hz with h | h
      · exact Or.inr (hEsupp h)
      · refine Or.inl (hC₂ z ?_)
        exact ofWeightFactorization_support_subset F q hq
          (S := g ⁻¹' BlowupExceptionalCentre.exceptionalCentre n g)
          (fun z hz => D.weight_pos_of_notMem hz) h
    · have hA := ClosedRealOneOneForm.pullback_isSemipositive hg.contMDiff β.isSemipositive
      have hKq := isKahler_add_smul_of_le hA hε hq0 hqε.le hKZ
      refine isKahler_of_isStrictlyPositive fun e z hz => ?_
      have h1 := SmoothRealForm.pullback_comp_geometricallyEq hf.contMDiff hg.contMDiff
        omega.form.val e hz
      have h2 := BlowupBigPullback.pullback_sub_geometricallyEq hg.contMDiff
        (ClosedRealOneOneForm.pullback hf.contMDiff omega.form) E.curvature e hz
      have hcoeff := (hKq.1 e z hz).2
      rw [BlowupBigPullback.coeff_sub] at h2
      set P := ClosedRealOneOneForm.pullback hg.contMDiff
        (ClosedRealOneOneForm.pullback hf.contMDiff omega.form)
      set Q := ClosedRealOneOneForm.pullback hg.contMDiff E.curvature
      have hL : (ClosedRealOneOneForm.pullback hg.contMDiff β.form + (q : ℝ) • F.closedForm).val.coeff
          e z = P.val.coeff e z - Q.val.coeff e z + (q : ℝ) • F.closedForm.val.coeff e z := by
        rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_smul]
        exact congrArg (· + _) h2
      have hR : (ClosedRealOneOneForm.pullback (hf.contMDiff.comp hg.contMDiff) omega.form -
          (Q + (-(q : ℝ)) • F.closedForm)).val.coeff e z =
          P.val.coeff e z - (Q.val.coeff e z + (-(q : ℝ)) • F.closedForm.val.coeff e z) := by
        rw [BlowupBigPullback.coeff_sub, ClosedRealOneOneForm.coeff_add,
          ClosedRealOneOneForm.coeff_smul]
        exact congrArg (· - _) h1
      have heq : (ClosedRealOneOneForm.pullback (hf.contMDiff.comp hg.contMDiff) omega.form -
          (Q + (-(q : ℝ)) • F.closedForm)).val.coeff e z =
          (ClosedRealOneOneForm.pullback hg.contMDiff β.form + (q : ℝ) • F.closedForm).val.coeff
            e z := by
        rw [hR, hL]
        ext v
        simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.add_apply,
          ContinuousAlternatingMap.smul_apply, smul_eq_mul]
        ring
      change IsStrictlyPositive ((ClosedRealOneOneForm.pullback (hf.contMDiff.comp hg.contMDiff)
        omega.form - (Q + (-(q : ℝ)) • F.closedForm)).val.coeff e z)
      rw [heq]
      exact hcoeff

/-- **Exceptional correction of a pulled-back Kähler form** (Copy-4, `lem:exceptional-metric`). -/
theorem exists_exceptionalMetric [CompactSpace X] (omega : KahlerBackground n X)
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (π : Y → X) (hπ : IsBlowupSequence n X Y π) :
    ∃ E : MeteredEffectiveQDivisor n Y,
      E.support ⊆ exceptionalLocus n π ∧
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature).val.IsKahler ∧
      (IsIsomorphismOver n π univ → E.support = ∅) := by
  obtain ⟨-, E, hE, hK⟩ := exists_exceptionalMetric_aux omega hπ
  refine ⟨E, hE, hK, fun hiso => subset_empty_iff.mp (hE.trans fun y hy => ?_)⟩
  exact disjoint_left.mp hiso.2 (mem_univ (π y)) hy

end

end Hironaka.ExceptionalMetricProof
