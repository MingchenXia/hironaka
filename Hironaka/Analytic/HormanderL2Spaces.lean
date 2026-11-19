import Hironaka.Analytic.HormanderTestPairing
import Hironaka.Analytic.HormanderAbstract

set_option autoImplicit false

/-!
# The Hilbert spaces of Hörmander's method

On an open set `D ⊆ ℂⁿ` with weights `w₂ = w₃ - ψ₀`, `w₁ = w₃ - 2ψ₀` smooth on `D`:

* `testForms D`: the complex vector space of smooth compactly supported `(0,1)`-forms in `D`;
* `formToL2`: `α ↦ α ∈ L²_{(0,1)}(e^{-w₂})`;
* `tstarToL2`: `α ↦ T* α ∈ L²(e^{-w₁})`;
* inner products of these with arbitrary `L²` elements are weighted integrals.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate ContDiff Topology InnerProductSpace

namespace Hironaka.Hormander

noncomputable section

open CauchyGreen

variable {n : ℕ} {D : Set (ComplexModel n)}

theorem IsTestFunctionOn.add {h₁ h₂ : ComplexModel n → ℂ} (h₁t : IsTestFunctionOn D h₁)
    (h₂t : IsTestFunctionOn D h₂) : IsTestFunctionOn D (h₁ + h₂) :=
  ⟨h₁t.1.add h₂t.1, h₁t.2.1.add h₂t.2.1,
    (tsupport_add h₁ h₂).trans (union_subset h₁t.2.2 h₂t.2.2)⟩

theorem IsTestFunctionOn.const_mul {h : ComplexModel n → ℂ} (ht : IsTestFunctionOn D h)
    (c : ℂ) : IsTestFunctionOn D fun x ↦ c * h x :=
  ⟨contDiff_const.mul ht.1, ht.2.1.mul_left, (tsupport_mul_subset_right).trans ht.2.2⟩

theorem isTestFunctionOn_zero : IsTestFunctionOn D (0 : ComplexModel n → ℂ) :=
  ⟨contDiff_const, HasCompactSupport.zero, by simp⟩

/-- Smooth compactly supported `(0,1)`-forms in `D`. -/
def testForms (D : Set (ComplexModel n)) : Submodule ℂ (Fin n → ComplexModel n → ℂ) where
  carrier := {α | ∀ j, IsTestFunctionOn D (α j)}
  add_mem' ha hb j := (ha j).add (hb j)
  zero_mem' _ := isTestFunctionOn_zero
  smul_mem' c _ ha j := (ha j).const_mul c

/-- The vector of coefficients of a `(0,1)`-form. -/
def formVec (α : Fin n → ComplexModel n → ℂ) (x : ComplexModel n) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j ↦ α j x

@[simp] theorem formVec_apply (α : Fin n → ComplexModel n → ℂ) (x : ComplexModel n) (j : Fin n) :
    formVec α x j = α j x := rfl

theorem inner_formVec (α β : Fin n → ComplexModel n → ℂ) (x : ComplexModel n) :
    ⟪formVec α x, formVec β x⟫_ℂ = ∑ j, conj (α j x) * β j x := by
  simp [formVec, PiLp.inner_apply, mul_comm]

theorem norm_sq_formVec (α : Fin n → ComplexModel n → ℂ) (x : ComplexModel n) :
    ‖formVec α x‖ ^ 2 = ∑ j, ‖α j x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; rfl

theorem memLp_formVec (hD : IsOpen D) {w : ComplexModel n → ℝ} (hw : ContinuousOn w D)
    {α : Fin n → ComplexModel n → ℂ} (hα : α ∈ testForms D) :
    MemLp (formVec α) 2 (weightedVolume D w) := by
  have hK : IsCompact (⋃ j, tsupport (α j)) := isCompact_iUnion fun j ↦ (hα j).2.1
  have hsub : tsupport (formVec α) ⊆ ⋃ j, tsupport (α j) := by
    refine closure_minimal (fun x hx ↦ ?_) hK.isClosed
    by_contra h
    apply hx
    ext j
    simp only [formVec_apply, PiLp.zero_apply]
    exact image_eq_zero_of_notMem_tsupport fun h' ↦ h (mem_iUnion.mpr ⟨j, h'⟩)
  have hcont : Continuous (formVec α) := by
    have : ∀ j, Continuous (α j) := fun j ↦ (hα j).1.continuous
    unfold formVec
    fun_prop
  exact memLp_weightedVolume_of_continuous hD hw hcont
    (hK.of_isClosed_subset (isClosed_tsupport _) hsub)
    (hsub.trans (iUnion_subset fun j ↦ (hα j).2.2)) 2

theorem deltaDir_add {v : ComplexModel n} {w : ComplexModel n → ℝ} {a b : ComplexModel n → ℂ}
    {x : ComplexModel n} (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x) :
    deltaDir v w (a + b) x = deltaDir v w a x + deltaDir v w b x := by
  have h : dDir v (a + b) x = dDir v a x + dDir v b x := by
    simp only [dDir, fderiv_add ha hb, add_apply]; ring
  simp only [deltaDir, h, Pi.add_apply]; ring

theorem deltaDir_const_mul {v : ComplexModel n} {w : ComplexModel n → ℝ} {a : ComplexModel n → ℂ}
    {x : ComplexModel n} (ha : DifferentiableAt ℝ a x) (c : ℂ) :
    deltaDir v w (fun y ↦ c * a y) x = c * deltaDir v w a x := by
  have h : dDir v (fun y ↦ c * a y) x = c * dDir v a x := by
    simp only [dDir, fderiv_const_mul ha c, smul_apply, smul_eq_mul]; ring
  simp only [deltaDir, h]; ring

section Weights

variable {w₁ w₂ ψ₀ : ComplexModel n → ℝ}

theorem continuous_tstarForm (hD : IsOpen D) (hw₂ : ContDiffOn ℝ ∞ w₂ D)
    (hψ : ContinuousOn ψ₀ D) {α : Fin n → ComplexModel n → ℂ} (hα : α ∈ testForms D) :
    Continuous (tstarForm w₂ ψ₀ α) := by
  have hK : IsCompact (⋃ j, tsupport (α j)) := isCompact_iUnion fun j ↦ (hα j).2.1
  have hKD : (⋃ j, tsupport (α j)) ⊆ D := iUnion_subset fun j ↦ (hα j).2.2
  obtain ⟨W, O, hW, hO, hKO, hOD, hEq⟩ := exists_global_weight hD hw₂ hK hKD
  have hαO : ∀ j, tsupport (α j) ⊆ O := fun j ↦
    (subset_iUnion (fun j ↦ tsupport (α j)) j).trans hKO
  have hsum : Continuous fun x ↦ ∑ j, deltaDir (coordVec j) w₂ (α j) x := by
    have := fun j ↦ continuous_deltaDir_of_eqOn hO (hW.of_le (by norm_cast)) hEq
      ((hα j).1.of_le (by norm_cast)) (hαO j) (coordVec j)
    fun_prop
  have hsupp : tsupport (fun x ↦ ∑ j, deltaDir (coordVec j) w₂ (α j) x) ⊆ D := by
    refine (closure_minimal (fun x hx ↦ ?_) hK.isClosed).trans hKD
    by_contra h
    apply hx
    exact Finset.sum_eq_zero fun j _ ↦
      deltaDir_eq_zero_of_notMem_tsupport fun h' ↦ h (mem_iUnion.mpr ⟨j, h'⟩)
  have h := continuous_mul_of_continuousOn hD
    (F := fun x ↦ -((Real.exp (-ψ₀ x) : ℝ) : ℂ))
    ((Complex.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn hψ.neg)).neg) hsum hsupp
  exact h

theorem tsupport_tstarForm_subset {α : Fin n → ComplexModel n → ℂ} :
    tsupport (tstarForm w₂ ψ₀ α) ⊆ ⋃ j, tsupport (α j) := by
  have hc : IsClosed (⋃ j, tsupport (α j)) := isClosed_iUnion_of_finite fun j ↦ isClosed_tsupport _
  refine closure_minimal (fun x hx ↦ ?_) hc
  by_contra h
  apply hx
  simp only [tstarForm]
  rw [Finset.sum_eq_zero fun j _ ↦
    deltaDir_eq_zero_of_notMem_tsupport fun h' ↦ h (mem_iUnion.mpr ⟨j, h'⟩), mul_zero]

theorem memLp_tstarForm (hD : IsOpen D) (hw₁ : ContinuousOn w₁ D) (hw₂ : ContDiffOn ℝ ∞ w₂ D)
    (hψ : ContinuousOn ψ₀ D) {α : Fin n → ComplexModel n → ℂ} (hα : α ∈ testForms D) :
    MemLp (tstarForm w₂ ψ₀ α) 2 (weightedVolume D w₁) := by
  have hK : IsCompact (⋃ j, tsupport (α j)) := isCompact_iUnion fun j ↦ (hα j).2.1
  have hKD : (⋃ j, tsupport (α j)) ⊆ D := iUnion_subset fun j ↦ (hα j).2.2
  exact memLp_weightedVolume_of_continuous hD hw₁ (continuous_tstarForm hD hw₂ hψ hα)
    (hK.of_isClosed_subset (isClosed_tsupport _) tsupport_tstarForm_subset)
    (tsupport_tstarForm_subset.trans hKD) 2

theorem tstarForm_add {α β : Fin n → ComplexModel n → ℂ} (hα : α ∈ testForms D)
    (hβ : β ∈ testForms D) (x : ComplexModel n) :
    tstarForm w₂ ψ₀ (α + β) x = tstarForm w₂ ψ₀ α x + tstarForm w₂ ψ₀ β x := by
  simp only [tstarForm, Pi.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact deltaDir_add ((hα j).1.differentiable (by norm_cast) x)
    ((hβ j).1.differentiable (by norm_cast) x)

theorem tstarForm_smul {α : Fin n → ComplexModel n → ℂ} (hα : α ∈ testForms D) (c : ℂ)
    (x : ComplexModel n) :
    tstarForm w₂ ψ₀ (c • α) x = c * tstarForm w₂ ψ₀ α x := by
  simp only [tstarForm, Pi.smul_apply]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have h : deltaDir (coordVec j) w₂ (c • α j) x = c * deltaDir (coordVec j) w₂ (α j) x :=
    deltaDir_const_mul ((hα j).1.differentiable (by norm_cast) x) c
  rw [h]; ring

end Weights

section Maps

variable {w₁ w₂ ψ₀ : ComplexModel n → ℝ}

/-- `α ↦ α ∈ L²_{(0,1)}(D, e^{-w₂})`. -/
def formToL2 (hD : IsOpen D) (hw₂ : ContinuousOn w₂ D) :
    testForms D →ₗ[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (weightedVolume D w₂) where
  toFun α := (memLp_formVec hD hw₂ α.2).toLp _
  map_add' α β := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ by ext j; rfl)
  map_smul' c α := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ by ext j; rfl)

/-- `α ↦ T* α ∈ L²(D, e^{-w₁})`. -/
def tstarToL2 (hD : IsOpen D) (hw₁ : ContinuousOn w₁ D) (hw₂ : ContDiffOn ℝ ∞ w₂ D)
    (hψ : ContinuousOn ψ₀ D) : testForms D →ₗ[ℂ] Lp ℂ 2 (weightedVolume D w₁) where
  toFun α := (memLp_tstarForm hD hw₁ hw₂ hψ α.2).toLp _
  map_add' α β := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ tstarForm_add α.2 β.2 x)
  map_smul' c α := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x ↦ tstarForm_smul α.2 c x)

theorem inner_toLp_eq_integral {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {μ : Measure (ComplexModel n)} {f : ComplexModel n → V} (hf : MemLp f 2 μ)
    (G : Lp V 2 μ) : ⟪hf.toLp f, G⟫_ℂ = ∫ x, ⟪f x, G x⟫_ℂ ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem inner_formToL2 (hD : IsOpen D) (hw₂ : ContinuousOn w₂ D) (α : testForms D)
    (G : Lp (EuclideanSpace ℂ (Fin n)) 2 (weightedVolume D w₂)) :
    ⟪formToL2 hD hw₂ α, G⟫_ℂ =
      ∑ j, ∫ x, conj ((α : Fin n → ComplexModel n → ℂ) j x) * G x j ∂(weightedVolume D w₂) := by
  change ⟪(memLp_formVec hD hw₂ α.2).toLp _, G⟫_ℂ = _
  rw [inner_toLp_eq_integral]
  simp_rw [PiLp.inner_apply, formVec_apply, RCLike.inner_apply, mul_comm (G _ _)]
  refine integral_finsetSum _ fun j _ ↦ ?_
  have hG : MemLp (fun x ↦ G x j) 2 (weightedVolume D w₂) :=
    (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).comp_memLp' (Lp.memLp G)
  have hαj : MemLp (fun x ↦ conj ((α : Fin n → ComplexModel n → ℂ) j x)) 2
      (weightedVolume D w₂) := by
    have h := (memLp_formVec hD hw₂ α.2)
    have := (EuclideanSpace.proj j : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).comp_memLp' h
    exact (Complex.conjCLE.toContinuousLinearMap).comp_memLp' this
  exact integrable_mul_of_memLp_two hαj hG

theorem inner_tstarToL2 (hD : IsOpen D) (hw₁ : ContinuousOn w₁ D) (hw₂ : ContDiffOn ℝ ∞ w₂ D)
    (hψ : ContinuousOn ψ₀ D) (α : testForms D) (G : Lp ℂ 2 (weightedVolume D w₁)) :
    ⟪tstarToL2 hD hw₁ hw₂ hψ α, G⟫_ℂ =
      ∫ x, conj (tstarForm w₂ ψ₀ α x) * G x ∂(weightedVolume D w₁) := by
  change ⟪(memLp_tstarForm hD hw₁ hw₂ hψ α.2).toLp _, G⟫_ℂ = _
  rw [inner_toLp_eq_integral]
  simp_rw [RCLike.inner_apply, mul_comm (G _)]

end Maps

section Closed

variable {w₂ : ComplexModel n → ℝ}

/-- Functions supported in `D` which are integrable after multiplication by `e^{w}` for the
weighted volume are integrable. -/
theorem integrable_volume_of_weightedVolume (hD : IsOpen D) {w : ComplexModel n → ℝ}
    (hw : ContinuousOn w D) {F : ComplexModel n → ℂ} (hFm : AEStronglyMeasurable F volume)
    (hF0 : ∀ x ∉ D, F x = 0)
    (hint : Integrable (fun x ↦ F x * (Real.exp (w x) : ℂ)) (weightedVolume D w)) :
    Integrable F volume := by
  refine ⟨hFm, ?_⟩
  have h1 : ∫⁻ x, ‖F x‖ₑ = ∫⁻ x in D, ‖F x‖ₑ := by
    rw [setLIntegral_eq_of_support_subset]
    intro x hx
    by_contra h
    exact hx (by simp [hF0 x h])
  have h2 : ∫⁻ x, ‖F x * (Real.exp (w x) : ℂ)‖ₑ ∂(weightedVolume D w) = ∫⁻ x in D, ‖F x‖ₑ := by
    rw [lintegral_weightedVolume hD hw]
    refine setLIntegral_congr_fun hD.measurableSet fun x _ ↦ ?_
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have : Real.exp (-w x) * Real.exp (w x) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    linear_combination ‖F x‖ * this
  rw [HasFiniteIntegral, h1, ← h2]
  exact hint.2

theorem integral_eq_integral_weightedVolume_mul_exp (hD : IsOpen D) {w : ComplexModel n → ℝ}
    (hw : ContinuousOn w D) {F : ComplexModel n → ℂ} (hF0 : ∀ x ∉ D, F x = 0) :
    ∫ x, F x = ∫ x, F x * (Real.exp (w x) : ℂ) ∂(weightedVolume D w) := by
  rw [integral_weightedVolume hD hw,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D) fun x hx ↦ hF0 x hx]
  refine setIntegral_congr_fun hD.measurableSet fun x _ ↦ ?_
  simp only [Complex.real_smul]
  have : ((Real.exp (-w x) : ℝ) : ℂ) * (Real.exp (w x) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  linear_combination (-F x) * this

theorem IsTestFunctionOn.dbarDir {h : ComplexModel n → ℂ} (hh : IsTestFunctionOn D h)
    (v : ComplexModel n) : IsTestFunctionOn D (CauchyGreen.dbarDir v h) := by
  refine ⟨?_, hasCompactSupport_dbarDir hh.2.1, ?_⟩
  · have h1 : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ h x) := hh.1.fderiv_right (by simp)
    unfold CauchyGreen.dbarDir
    fun_prop
  · exact (tsupport_subset_of_eq_zero fun x hx ↦ dbarDir_eq_zero_of_notMem_tsupport hx).trans
      hh.2.2

variable {w₂ : ComplexModel n → ℝ}

/-- The test form whose pairing with `G` is `∫ (G_k ∂̄_j h - G_j ∂̄_k h)`. -/
def closedWitness (w₂ : ComplexModel n → ℝ) (h : ComplexModel n → ℂ) (j k : Fin n) :
    Fin n → ComplexModel n → ℂ :=
  fun i x ↦ (Real.exp (w₂ x) : ℂ) * ((if i = k then conj (dbarDir (coordVec j) h x) else 0) -
    (if i = j then conj (dbarDir (coordVec k) h x) else 0))

theorem closedWitness_mem (hD : IsOpen D) (hw₂ : ContDiffOn ℝ ∞ w₂ D)
    {h : ComplexModel n → ℂ} (hh : IsTestFunctionOn D h) (j k : Fin n) :
    closedWitness w₂ h j k ∈ testForms D := by
  intro i
  have hexp : ContDiffOn ℝ ∞ (fun x ↦ (Real.exp (w₂ x) : ℂ)) D :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hw₂.exp
  have hite : ∀ (p : Prop) [Decidable p] (v : ComplexModel n),
      IsTestFunctionOn D fun x ↦ if p then conj (CauchyGreen.dbarDir v h x) else 0 := by
    intro p _ v
    by_cases hp : p
    · simpa [hp] using (hh.dbarDir v).conj
    · simp only [hp, if_false]; exact isTestFunctionOn_zero (D := D)
  have hsub := (hite (i = k) (coordVec j)).add ((hite (i = j) (coordVec k)).const_mul (-1))
  have heq : ((fun x ↦ if i = k then conj (CauchyGreen.dbarDir (coordVec j) h x) else 0) +
      fun x ↦ -1 * if i = j then conj (CauchyGreen.dbarDir (coordVec k) h x) else 0) =
      fun x ↦ (if i = k then conj (CauchyGreen.dbarDir (coordVec j) h x) else 0) -
        (if i = j then conj (CauchyGreen.dbarDir (coordVec k) h x) else 0) := by
    funext x; simp only [Pi.add_apply]; ring
  rw [heq] at hsub
  exact IsTestFunctionOn.mul_left hD hexp hsub

theorem inner_closedWitness (hD : IsOpen D) (hw₂ : ContDiffOn ℝ ∞ w₂ D)
    {h : ComplexModel n → ℂ} (hh : IsTestFunctionOn D h) (j k : Fin n)
    (G : Lp (EuclideanSpace ℂ (Fin n)) 2 (weightedVolume D w₂)) :
    ⟪formToL2 hD hw₂.continuousOn ⟨_, closedWitness_mem hD hw₂ hh j k⟩, G⟫_ℂ =
      ∫ x, (G x k * dbarDir (coordVec j) h x - G x j * dbarDir (coordVec k) h x) := by
  change ⟪(memLp_formVec hD hw₂.continuousOn (closedWitness_mem hD hw₂ hh j k)).toLp _, G⟫_ℂ = _
  rw [inner_toLp_eq_integral, integral_eq_integral_weightedVolume_mul_exp hD hw₂.continuousOn]
  · refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [PiLp.inner_apply, formVec_apply, RCLike.inner_apply, closedWitness, map_mul,
      map_sub, Complex.conj_ofReal]
    simp only [apply_ite conj, conj_conj, map_zero, mul_sub, sub_mul, Finset.sum_sub_distrib]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  · intro x hx
    have hxs : x ∉ tsupport h := fun h' ↦ hx (hh.2.2 h')
    simp [dbarDir_eq_zero_of_notMem_tsupport hxs]

end Closed

section ClosedForms

variable {w₂ : ComplexModel n → ℝ}

/-- The witnesses of weak `∂̄`-closedness. -/
def closedWitnessSet (hD : IsOpen D) (hw₂ : ContDiffOn ℝ ∞ w₂ D) :
    Set (Lp (EuclideanSpace ℂ (Fin n)) 2 (weightedVolume D w₂)) :=
  {c | ∃ (h : ComplexModel n → ℂ) (hh : IsTestFunctionOn D h) (j k : Fin n),
    c = formToL2 hD hw₂.continuousOn ⟨_, closedWitness_mem hD hw₂ hh j k⟩}

/-- The closed subspace of weakly `∂̄`-closed forms in `L²_{(0,1)}(D, e^{-w₂})`. -/
def closedForms (hD : IsOpen D) (hw₂ : ContDiffOn ℝ ∞ w₂ D) :
    Submodule ℂ (Lp (EuclideanSpace ℂ (Fin n)) 2 (weightedVolume D w₂)) :=
  (Submodule.span ℂ (closedWitnessSet hD hw₂))ᗮ

theorem mem_closedForms_iff (hD : IsOpen D) (hw₂ : ContDiffOn ℝ ∞ w₂ D)
    (G : Lp (EuclideanSpace ℂ (Fin n)) 2 (weightedVolume D w₂)) :
    G ∈ closedForms hD hw₂ ↔ ∀ h, IsTestFunctionOn D h → ∀ j k,
      ∫ x, (G x k * dbarDir (coordVec j) h x - G x j * dbarDir (coordVec k) h x) = 0 := by
  constructor
  · intro hG h hh j k
    rw [← inner_closedWitness hD hw₂ hh j k G]
    exact Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (s := closedWitnessSet hD hw₂) ⟨h, hh, j, k, rfl⟩) hG
  · intro hG
    rw [closedForms, Submodule.mem_orthogonal]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨h, hh, j, k, rfl⟩ := hc
      rw [inner_closedWitness hD hw₂ hh j k G]
      exact hG h hh j k
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

end ClosedForms

end

end Hironaka.Hormander
