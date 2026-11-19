import Hironaka.Analytic.HormanderAPriori

set_option autoImplicit false

/-!
# Test functions, weights and the weak `∂̄` pairing

Pointwise and integral identities relating distributional `∂̄` (`WeakDbarEq`) to the weighted
formal adjoint `T* α = -e^{-ψ₀} Σ_j δ^{w₂}_j α_j` on an open set `D` with weights that are only
smooth on `D`:

* products of test functions with functions smooth on `D` are test functions;
* `δ_v` only depends on the weight near the support of its argument;
* `∂̄_v (conj a · e^{-W}) = conj (δ^W_v a) · e^{-W}`.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate ContDiff Topology

namespace Hironaka.Hormander

noncomputable section

open CauchyGreen

variable {n : ℕ} {D : Set (ComplexModel n)}

theorem IsTestFunctionOn.mul_left (hD : IsOpen D) {F h : ComplexModel n → ℂ}
    (hF : ContDiffOn ℝ ∞ F D) (hh : IsTestFunctionOn D h) :
    IsTestFunctionOn D fun x ↦ F x * h x := by
  refine ⟨contDiff_iff_contDiffAt.mpr fun x ↦ ?_, hh.2.1.mul_left, ?_⟩
  · by_cases hx : x ∈ D
    · exact (hF.contDiffAt (hD.mem_nhds hx)).mul hh.1.contDiffAt
    · have hxs : x ∉ tsupport h := fun h' ↦ hx (hh.2.2 h')
      have h0 : (fun x ↦ F x * h x) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
        simp [hy]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  · exact (tsupport_mul_subset_right).trans hh.2.2

theorem IsTestFunctionOn.conj {h : ComplexModel n → ℂ} (hh : IsTestFunctionOn D h) :
    IsTestFunctionOn D fun x ↦ conj (h x) := by
  refine ⟨Complex.conjCLE.contDiff.comp hh.1, hh.2.1.comp_left (map_zero _), ?_⟩
  exact (tsupport_comp_subset (map_zero _) _).trans hh.2.2

theorem deltaDir_congr_weight {O : Set (ComplexModel n)} (hO : IsOpen O) {W w : ComplexModel n → ℝ}
    (heq : EqOn W w O) {a : ComplexModel n → ℂ} (hsub : tsupport a ⊆ O) (v x : ComplexModel n) :
    deltaDir v W a x = deltaDir v w a x := by
  by_cases hx : x ∈ O
  · have hev : (fun y ↦ (W y : ℂ)) =ᶠ[𝓝 x] fun y ↦ (w y : ℂ) := by
      filter_upwards [hO.mem_nhds hx] with y hy
      rw [heq hy]
    simp only [deltaDir, dDir, hev.fderiv_eq]
  · have hxs : x ∉ tsupport a := fun h ↦ hx (hsub h)
    rw [deltaDir_eq_zero_of_notMem_tsupport hxs, deltaDir_eq_zero_of_notMem_tsupport hxs]

theorem dbarDir_conj_mul_cweight {W : ComplexModel n → ℝ} {a : ComplexModel n → ℂ}
    (hW : ContDiff ℝ 1 W) (ha : ContDiff ℝ 1 a) (v x : ComplexModel n) :
    dbarDir v (fun y ↦ conj (a y) * cweight W y) x =
      conj (deltaDir v W a x) * cweight W x := by
  have hcw : ∀ y, conj (cweight W y) = cweight W y := fun y ↦ by
    rw [cweight, Complex.conj_ofReal]
  have hfun : (fun y ↦ conj (a y) * cweight W y) = fun y ↦ conj (a y * cweight W y) := by
    funext y; rw [map_mul, hcw]
  have hd : DifferentiableAt ℝ (fun y ↦ a y * cweight W y) x :=
    (ha.differentiable one_ne_zero x).mul
      (differentiableAt_cweight (hW.differentiable one_ne_zero x))
  rw [hfun, dbarDir_conj hd, ← deltaDir_mul_cweight (hW.differentiable one_ne_zero x)
    (ha.differentiable one_ne_zero x), map_mul, hcw]

theorem continuous_mul_of_continuousOn (hD : IsOpen D) {F c : ComplexModel n → ℂ}
    (hF : ContinuousOn F D) (hc : Continuous c) (hcD : tsupport c ⊆ D) :
    Continuous fun x ↦ F x * c x := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : x ∈ D
  · exact (hF.continuousAt (hD.mem_nhds hx)).mul hc.continuousAt
  · have hxs : x ∉ tsupport c := fun h ↦ hx (hcD h)
    have h0 : (fun x ↦ F x * c x) =ᶠ[𝓝 x] fun _ ↦ (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
      simp [hy]
    exact continuousAt_const.congr h0.symm

theorem integrable_mul_of_memLp_two {μ : Measure (ComplexModel n)} {u v : ComplexModel n → ℂ}
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) : Integrable (fun x ↦ u x * v x) μ :=
  hu.integrable_mul hv

/-- Integrals of `u c` with `c` supported in `D`, as weighted integrals. -/
theorem integral_mul_eq_integral_weightedVolume (hD : IsOpen D) {w : ComplexModel n → ℝ}
    (hw : ContinuousOn w D) {u c : ComplexModel n → ℂ} (hcD : tsupport c ⊆ D) :
    ∫ x, u x * c x = ∫ x, u x * (c x * (Real.exp (w x) : ℂ)) ∂(weightedVolume D w) := by
  rw [integral_weightedVolume hD hw]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D) fun x hx ↦ by
    simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hcD h)]]
  refine setIntegral_congr_fun hD.measurableSet fun x _ ↦ ?_
  simp only [Complex.real_smul]
  have : ((Real.exp (-w x) : ℝ) : ℂ) * (Real.exp (w x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  linear_combination (-(u x * c x)) * this

theorem memLp_mul_exp_of_continuous (hD : IsOpen D) {w w' : ComplexModel n → ℝ}
    (hw : ContinuousOn w D) (hw' : ContinuousOn w' D) {c : ComplexModel n → ℂ}
    (hc : Continuous c) (hcc : HasCompactSupport c) (hcD : tsupport c ⊆ D) (r : ℝ) :
    MemLp (fun x ↦ c x * (Real.exp (r * w x) : ℂ)) 2 (weightedVolume D w') := by
  have hcont : Continuous fun x ↦ (Real.exp (r * w x) : ℂ) * c x :=
    continuous_mul_of_continuousOn hD (by
      have := hw.const_smul r
      exact (Complex.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn this))) hc hcD
  refine (memLp_weightedVolume_of_continuous hD hw' (hcont.congr fun x ↦ mul_comm _ _)
    hcc.mul_right ((tsupport_mul_subset_left).trans hcD) 2)

/-- A weight smooth on `D` agrees on an open neighbourhood `O ⊆ D` of a compact `K ⊆ D` with a
globally smooth weight. -/
theorem exists_global_weight (hD : IsOpen D) {w : ComplexModel n → ℝ} (hw : ContDiffOn ℝ ∞ w D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ (W : ComplexModel n → ℝ) (O : Set (ComplexModel n)), ContDiff ℝ ∞ W ∧ IsOpen O ∧
      K ⊆ O ∧ O ⊆ D ∧ EqOn W w O := by
  obtain ⟨W, hW, hev⟩ := exists_contDiff_eventuallyEq_nhdsSet hD hw hK hKD
  obtain ⟨O, hO, hKO, hOeq⟩ := eventually_nhdsSet_iff_exists.mp hev
  exact ⟨W, O ∩ D, hW, hO.inter hD, subset_inter hKO hKD, inter_subset_right,
    fun x hx ↦ hOeq x hx.1⟩

theorem ae_mem_weightedVolume (hD : IsOpen D) (w : ComplexModel n → ℝ) :
    ∀ᵐ x ∂(weightedVolume D w), x ∈ D := by
  have h : ∀ᵐ x ∂(volume.restrict D), x ∈ D := ae_restrict_mem hD.measurableSet
  exact (withDensity_absolutelyContinuous _ _).ae_le h

/-- `δ^W (F e^W) = e^W ∂ F`. -/
theorem deltaDir_mul_exp {v : ComplexModel n} {W : ComplexModel n → ℝ} {F : ComplexModel n → ℂ}
    {x : ComplexModel n} (hW : DifferentiableAt ℝ W x) (hF : DifferentiableAt ℝ F x) :
    deltaDir v W (fun y ↦ F y * (Real.exp (W y) : ℂ)) x = (Real.exp (W x) : ℂ) * dDir v F x := by
  have hexp : DifferentiableAt ℝ (fun y ↦ (Real.exp (W y) : ℂ)) x :=
    differentiableAt_ofReal_comp hW.exp
  have h := deltaDir_mul_cweight (v := v) (a := fun y ↦ F y * (Real.exp (W y) : ℂ)) hW
    (hF.mul hexp)
  have hcancel : (fun y ↦ F y * (Real.exp (W y) : ℂ) * cweight W y) = F := by
    funext y
    rw [cweight, mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      Complex.ofReal_one, mul_one]
  rw [hcancel] at h
  have hpos : (Real.exp (W x) : ℂ) * cweight W x = 1 := by
    rw [cweight, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      Complex.ofReal_one]
  calc deltaDir v W (fun y ↦ F y * (Real.exp (W y) : ℂ)) x
      = deltaDir v W (fun y ↦ F y * (Real.exp (W y) : ℂ)) x *
          ((Real.exp (W x) : ℂ) * cweight W x) := by rw [hpos, mul_one]
    _ = (Real.exp (W x) : ℂ) * dDir v F x := by rw [← h]; ring

theorem tsupport_subset_of_eq_zero {f g : ComplexModel n → ℂ}
    (h : ∀ x, x ∉ tsupport g → f x = 0) : tsupport f ⊆ tsupport g :=
  closure_minimal (fun x hx ↦ by_contra fun h' ↦ hx (h x h')) (isClosed_tsupport _)

/-- Replacing `e^{-W}` by the weighted volume of a weight agreeing with `W` near the support. -/
theorem integral_mul_cweight_eq (hD : IsOpen D) {w W : ComplexModel n → ℝ} (hw : ContinuousOn w D)
    {O : Set (ComplexModel n)} (hOD : O ⊆ D) (hEq : EqOn W w O) {u c : ComplexModel n → ℂ}
    (hcO : tsupport c ⊆ O) :
    ∫ x, u x * (c x * cweight W x) = ∫ x, u x * c x ∂(weightedVolume D w) := by
  have hsub : tsupport (fun x ↦ c x * cweight W x) ⊆ D :=
    (tsupport_mul_subset_left).trans (hcO.trans hOD)
  rw [integral_mul_eq_integral_weightedVolume hD hw hsub]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_weightedVolume hD w] with x hx
  by_cases hxO : x ∈ tsupport c
  · have hW : W x = w x := hEq (hcO hxO)
    rw [cweight, hW, mul_assoc (c x), ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, Complex.ofReal_one, mul_one]
  · simp [image_eq_zero_of_notMem_tsupport hxO]

theorem continuous_deltaDir_of_eqOn {O : Set (ComplexModel n)} (hO : IsOpen O)
    {W w : ComplexModel n → ℝ} (hW : ContDiff ℝ 1 W) (hEq : EqOn W w O) {a : ComplexModel n → ℂ}
    (ha : ContDiff ℝ 1 a) (haO : tsupport a ⊆ O) (v : ComplexModel n) :
    Continuous (deltaDir v w a) := by
  have h : deltaDir v w a = deltaDir v W a := funext fun x ↦
    (deltaDir_congr_weight hO hEq haO v x).symm
  rw [h]
  exact continuous_deltaDir hW ha

/-- **Weak `∂̄` gives the adjoint pairing.** -/
theorem adjoint_pairing_of_weakDbarEq (hD : IsOpen D) {w₁ w₂ ψ₀ : ComplexModel n → ℝ}
    (hw₁ : ContinuousOn w₁ D) (hw₂ : ContDiffOn ℝ ∞ w₂ D) (hψ : ContinuousOn ψ₀ D)
    (h12 : ∀ x ∈ D, w₂ x = w₁ x + ψ₀ x) {u : ComplexModel n → ℂ}
    (hu : MemLp u 2 (weightedVolume D w₁)) {f : Fin n → ComplexModel n → ℂ}
    (hweak : WeakDbarEq D u f) {α : Fin n → ComplexModel n → ℂ}
    (hα : ∀ j, IsTestFunctionOn D (α j)) :
    ∫ x, conj (tstarForm w₂ ψ₀ α x) * u x ∂(weightedVolume D w₁) =
      ∑ j, ∫ x, conj (α j x) * f j x ∂(weightedVolume D w₂) := by
  have hK : IsCompact (⋃ j, tsupport (α j)) := isCompact_iUnion fun j ↦ (hα j).2.1
  have hKD : (⋃ j, tsupport (α j)) ⊆ D := iUnion_subset fun j ↦ (hα j).2.2
  obtain ⟨W, O, hW, hO, hKO, hOD, hEq⟩ := exists_global_weight hD hw₂ hK hKD
  have hαO : ∀ j, tsupport (α j) ⊆ O := fun j ↦ (subset_iUnion (fun j ↦ tsupport (α j)) j).trans hKO
  have hα1 : ∀ j, ContDiff ℝ 1 (α j) := fun j ↦ (hα j).1.of_le (by norm_cast)
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_cast)
  -- the test functions `conj α_j e^{-W}`
  have htest : ∀ j, IsTestFunctionOn D fun y ↦ conj (α j y) * cweight W y := by
    intro j
    refine ⟨(hα j).conj.1.mul (contDiff_cweight hW), (hα j).conj.2.1.mul_right,
      (tsupport_mul_subset_left).trans (hα j).conj.2.2⟩
  have hδsupp : ∀ j, tsupport (deltaDir (coordVec j) w₂ (α j)) ⊆ tsupport (α j) := fun j ↦
    tsupport_subset_of_eq_zero fun x hx ↦ deltaDir_eq_zero_of_notMem_tsupport hx
  have hδc : ∀ j, Continuous (deltaDir (coordVec j) w₂ (α j)) := fun j ↦
    continuous_deltaDir_of_eqOn hO hW1 hEq (hα1 j) (hαO j) _
  -- the left side, summand by summand
  have hL : ∀ j, ∫ x, u x * dbarDir (coordVec j) (fun y ↦ conj (α j y) * cweight W y) x =
      ∫ x, u x * (conj (deltaDir (coordVec j) w₂ (α j) x) * (Real.exp (-ψ₀ x) : ℂ))
        ∂(weightedVolume D w₁) := by
    intro j
    have e1 : ∀ x, dbarDir (coordVec j) (fun y ↦ conj (α j y) * cweight W y) x =
        conj (deltaDir (coordVec j) w₂ (α j) x) * cweight W x := fun x ↦ by
      rw [dbarDir_conj_mul_cweight hW1 (hα1 j), deltaDir_congr_weight hO hEq (hαO j)]
    simp_rw [e1]
    have hsub : tsupport (fun x ↦ conj (deltaDir (coordVec j) w₂ (α j) x) * cweight W x) ⊆ D :=
      (tsupport_subset_of_eq_zero fun x hx ↦ by
        rw [deltaDir_eq_zero_of_notMem_tsupport hx]; simp).trans (hα j).2.2
    rw [integral_mul_eq_integral_weightedVolume hD hw₁ hsub]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_weightedVolume hD w₁] with x hx
    by_cases hxs : x ∈ tsupport (α j)
    · have hWx : W x = w₁ x + ψ₀ x := (hEq (hαO j hxs)).trans (h12 x hx)
      congr 1
      rw [cweight, hWx, mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3; ring
    · simp [deltaDir_eq_zero_of_notMem_tsupport hxs]
  have hR : ∀ j, ∫ x, f j x * (conj (α j x) * cweight W x) =
      ∫ x, conj (α j x) * f j x ∂(weightedVolume D w₂) := by
    intro j
    rw [integral_mul_cweight_eq (c := fun x ↦ conj (α j x)) hD hw₂.continuousOn hOD hEq
      ((tsupport_subset_of_eq_zero fun x hx ↦ by
        rw [image_eq_zero_of_notMem_tsupport hx, map_zero]).trans (hαO j))]
    simp_rw [mul_comm]
  -- sum the weak equations
  have hsum : ∑ j, ∫ x, u x * dbarDir (coordVec j) (fun y ↦ conj (α j y) * cweight W y) x =
      - ∑ j, ∫ x, f j x * (conj (α j x) * cweight W x) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ hweak _ (htest j) j
  simp_rw [hL, hR] at hsum
  have hmem : ∀ j, MemLp (fun x ↦ conj (deltaDir (coordVec j) w₂ (α j) x) *
      (Real.exp (-ψ₀ x) : ℂ)) 2 (weightedVolume D w₁) := by
    intro j
    have hcont : Continuous fun x ↦ (Real.exp (-ψ₀ x) : ℂ) *
        conj (deltaDir (coordVec j) w₂ (α j) x) :=
      continuous_mul_of_continuousOn hD
        (Complex.continuous_ofReal.comp_continuousOn
          (Real.continuous_exp.comp_continuousOn hψ.neg))
        (continuous_conj.comp (hδc j))
        ((tsupport_subset_of_eq_zero (f := fun x ↦ conj (deltaDir (coordVec j) w₂ (α j) x))
          fun x hx ↦ by rw [deltaDir_eq_zero_of_notMem_tsupport hx, map_zero]).trans (hα j).2.2)
    have hsub : tsupport (fun x ↦ conj (deltaDir (coordVec j) w₂ (α j) x) *
        (Real.exp (-ψ₀ x) : ℂ)) ⊆ tsupport (α j) :=
      tsupport_subset_of_eq_zero fun x hx ↦ by
        rw [deltaDir_eq_zero_of_notMem_tsupport hx]; simp
    exact memLp_weightedVolume_of_continuous hD hw₁ (hcont.congr fun x ↦ mul_comm _ _)
      ((hα j).2.1.of_isClosed_subset (isClosed_tsupport _) hsub) (hsub.trans (hα j).2.2) 2
  rw [← integral_finsetSum _ fun j _ ↦ integrable_mul_of_memLp_two hu (hmem j)] at hsum
  have htstar : ∀ x, conj (tstarForm w₂ ψ₀ α x) * u x =
      -∑ j, u x * (conj (deltaDir (coordVec j) w₂ (α j) x) * (Real.exp (-ψ₀ x) : ℂ)) := by
    intro x
    simp only [tstarForm, map_mul, map_neg, map_sum, Complex.conj_ofReal, Finset.mul_sum,
      Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun j _ ↦ ?_)
    ring
  simp_rw [htstar]
  rw [integral_neg, hsum, neg_neg]

/-- **The adjoint pairing gives weak `∂̄`.** -/
theorem weakDbarEq_of_adjoint_pairing (hD : IsOpen D) {w₁ w₂ ψ₀ : ComplexModel n → ℝ}
    (hw₁ : ContinuousOn w₁ D) (hw₂ : ContDiffOn ℝ ∞ w₂ D)
    (h12 : ∀ x ∈ D, w₂ x = w₁ x + ψ₀ x) {u : ComplexModel n → ℂ}
    {f : Fin n → ComplexModel n → ℂ}
    (hpair : ∀ α : Fin n → ComplexModel n → ℂ, (∀ j, IsTestFunctionOn D (α j)) →
      ∫ x, conj (tstarForm w₂ ψ₀ α x) * u x ∂(weightedVolume D w₁) =
        ∑ j, ∫ x, conj (α j x) * f j x ∂(weightedVolume D w₂)) :
    WeakDbarEq D u f := by
  classical
  intro h hh j
  obtain ⟨W, O, hW, hO, hKO, hOD, hEq⟩ := exists_global_weight hD hw₂ hh.2.1 hh.2.2
  have hexpW : ContDiff ℝ ∞ fun y ↦ (Real.exp (W y) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp hW.exp
  set F : ComplexModel n → ℂ := fun y ↦ conj (h y) * (Real.exp (W y) : ℂ) with hFdef
  have hFsupp : tsupport F ⊆ tsupport h := tsupport_subset_of_eq_zero fun x hx ↦ by
    simp [hFdef, image_eq_zero_of_notMem_tsupport hx]
  have hFtest : IsTestFunctionOn D F :=
    ⟨hh.conj.1.mul hexpW, hh.2.1.of_isClosed_subset (isClosed_tsupport _) hFsupp,
      hFsupp.trans hh.2.2⟩
  set α : Fin n → ComplexModel n → ℂ := Pi.single j F with hαdef
  have hαtest : ∀ k, IsTestFunctionOn D (α k) := by
    intro k
    by_cases hk : k = j
    · subst hk; simpa [hαdef] using hFtest
    · simp only [hαdef, Pi.single_eq_of_ne hk]
      exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  have hp := hpair α hαtest
  -- right side
  have hR : ∑ k, ∫ x, conj (α k x) * f k x ∂(weightedVolume D w₂) = ∫ x, f j x * h x := by
    rw [Finset.sum_eq_single j (fun k _ hk ↦ by simp [hαdef, Pi.single_eq_of_ne hk])
      (by simp)]
    rw [integral_mul_eq_integral_weightedVolume (u := f j) hD hw₂.continuousOn hh.2.2]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_weightedVolume hD w₂] with x hx
    simp only [hαdef, Pi.single_eq_same, hFdef, map_mul, conj_conj, Complex.conj_ofReal]
    by_cases hxs : x ∈ tsupport h
    · rw [hEq (hKO hxs)]; ring
    · simp [image_eq_zero_of_notMem_tsupport hxs]
  -- left side
  have hT : ∀ x, conj (tstarForm w₂ ψ₀ α x) =
      -((Real.exp (-ψ₀ x) : ℝ) : ℂ) * ((Real.exp (W x) : ℝ) : ℂ) * dbarDir (coordVec j) h x := by
    intro x
    have hsum : ∑ k, deltaDir (coordVec k) w₂ (α k) x = deltaDir (coordVec j) w₂ F x := by
      rw [Finset.sum_eq_single j (fun k _ hk ↦ by
        simp [hαdef, Pi.single_eq_of_ne hk, deltaDir, dDir]) (by simp)]
      simp [hαdef]
    have hδ : deltaDir (coordVec j) w₂ F x = (Real.exp (W x) : ℂ) *
        conj (dbarDir (coordVec j) h x) := by
      rw [← deltaDir_congr_weight hO hEq (hFsupp.trans hKO),
        deltaDir_mul_exp (hW.differentiable (by norm_num) x)
          (hh.conj.1.differentiable (by norm_num) x),
        dDir_conj (hh.1.differentiable (by norm_num) x)]
    simp only [tstarForm, hsum, hδ, map_mul, map_neg, Complex.conj_ofReal, conj_conj]
    ring
  have hL : ∫ x, conj (tstarForm w₂ ψ₀ α x) * u x ∂(weightedVolume D w₁) =
      -∫ x, u x * dbarDir (coordVec j) h x := by
    have hsupp : tsupport (dbarDir (coordVec j) h) ⊆ D :=
      (tsupport_subset_of_eq_zero fun x hx ↦ dbarDir_eq_zero_of_notMem_tsupport hx).trans hh.2.2
    rw [integral_mul_eq_integral_weightedVolume hD hw₁ hsupp, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_weightedVolume hD w₁] with x hx
    rw [hT]
    by_cases hxs : x ∈ tsupport h
    · have hWx : W x = w₁ x + ψ₀ x := (hEq (hKO hxs)).trans (h12 x hx)
      rw [hWx]
      have : ((Real.exp (-ψ₀ x) : ℝ) : ℂ) * ((Real.exp (w₁ x + ψ₀ x) : ℝ) : ℂ) =
          ((Real.exp (w₁ x) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
      linear_combination (-(dbarDir (coordVec j) h x * u x)) * this
    · simp [dbarDir_eq_zero_of_notMem_tsupport hxs]
  rw [hL, hR] at hp
  linear_combination -hp

end

end Hironaka.Hormander
