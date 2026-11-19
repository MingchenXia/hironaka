import Hironaka.Analytic.HormanderL2Core
import Hironaka.Analytic.HormanderPairingBound
import Hironaka.Analytic.HormanderCutoffWeights

set_option autoImplicit false

/-!
# Hörmander's `L²` estimate on convex domains

Assembly of `HormanderL2Estimate` from:

* the cutoff weights on a convex subdomain (`exists_hormanderCutoffData`);
* the pairing bound (`norm_sq_pairing_le`: Cauchy--Schwarz and the a priori estimate);
* density of test forms in `dom T* ∩ ker S` (Hörmander's Lemma 4.1.3), stated here as
  `HormanderDensityStatement` and proved in `Hironaka.HormanderDensity`;
* the Hilbert-space argument (`hormander_of_pairing_bound`).
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate ContDiff Topology InnerProductSpace

namespace Hironaka.Hormander

noncomputable section

open CauchyGreen

/-- Density of test forms in `dom T* ∩ dom S` for Hörmander's three weights
(Hörmander, Lemma 4.1.3). -/
def HormanderDensityStatement (n : ℕ) : Prop :=
  ∀ (D : Set (ComplexModel n)), IsOpen D →
  ∀ (w₃ ψ₀ : ComplexModel n → ℝ), ContDiffOn ℝ ∞ w₃ D → ContDiffOn ℝ ∞ ψ₀ D → (∀ x, 0 ≤ ψ₀ x) →
  ∀ (η : ℕ → ComplexModel n → ℝ),
    (∀ k, ContDiff ℝ ∞ (η k) ∧ HasCompactSupport (η k) ∧ tsupport (η k) ⊆ D ∧
      ∀ x, 0 ≤ η k x ∧ η k x ≤ 1) →
    (∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1) →
    (∀ k, ∀ x ∈ D, ‖fderiv ℝ (η k) x‖ ^ 2 ≤ Real.exp (ψ₀ x)) →
  ∀ (β : Fin n → ComplexModel n → ℂ) (γ : ComplexModel n → ℂ)
    (σ : Fin n × Fin n → ComplexModel n → ℂ),
    (∀ j, MemLp (β j) 2 (weightedVolume D fun x ↦ w₃ x - ψ₀ x)) →
    MemLp γ 2 (weightedVolume D fun x ↦ w₃ x - 2 * ψ₀ x) →
    (∀ p, MemLp (σ p) 2 (weightedVolume D w₃)) →
    (∀ g, IsTestFunctionOn D g →
      ∑ j, ∫ x in D, conj (dbarDir (coordVec j) g x) * β j x * Real.exp (-(w₃ x - ψ₀ x)) =
        ∫ x in D, conj (g x) * γ x * Real.exp (-(w₃ x - 2 * ψ₀ x))) →
    (∀ h, IsTestFunctionOn D h → ∀ j k,
      ∫ x, (β k x * dbarDir (coordVec j) h x - β j x * dbarDir (coordVec k) h x) =
        - ∫ x, σ (j, k) x * h x) →
  ∃ βs : ℕ → Fin n → ComplexModel n → ℂ, (∀ m j, IsTestFunctionOn D (βs m j)) ∧
    (∀ j, Tendsto (fun m ↦ eLpNorm (fun x ↦ βs m j x - β j x) 2
      (weightedVolume D fun x ↦ w₃ x - ψ₀ x)) atTop (𝓝 0)) ∧
    Tendsto (fun m ↦ eLpNorm (fun x ↦ tstarForm (fun x ↦ w₃ x - ψ₀ x) ψ₀ (βs m) x - γ x) 2
      (weightedVolume D fun x ↦ w₃ x - 2 * ψ₀ x)) atTop (𝓝 0) ∧
    ∀ p, Tendsto (fun m ↦ eLpNorm (fun x ↦ dbarForm (βs m) p x - σ p x) 2
      (weightedVolume D w₃)) atTop (𝓝 0)

section Convergence

variable {n : ℕ} {D : Set (ComplexModel n)}

theorem norm_euclidean_le_sum (v : EuclideanSpace ℂ (Fin n)) : ‖v‖ ≤ ∑ j, ‖v j‖ := by
  have h : v = ∑ j, EuclideanSpace.single j (v j) := by
    ext i; simp [Finset.sum_apply]
  calc ‖v‖ = ‖∑ j, EuclideanSpace.single j (v j)‖ := by rw [← h]
    _ ≤ ∑ j, ‖EuclideanSpace.single j (v j)‖ := norm_sum_le _ _
    _ = ∑ j, ‖v j‖ := by simp

theorem eLpNorm_euclidean_le_sum {μ : Measure (ComplexModel n)}
    {F : ComplexModel n → EuclideanSpace ℂ (Fin n)} (hF : AEStronglyMeasurable F μ) :
    eLpNorm F 2 μ ≤ ∑ j, eLpNorm (fun x ↦ F x j) 2 μ := by
  have hc : ∀ j, AEStronglyMeasurable (fun x ↦ F x j) μ := fun j ↦
    ((continuous_apply j).comp (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable hF
  have h2 : eLpNorm (fun x ↦ ∑ j, ‖F x j‖) 2 μ ≤ ∑ j, eLpNorm (fun x ↦ ‖F x j‖) 2 μ := by
    have h := eLpNorm_sum_le (μ := μ) (p := 2) (f := fun j x ↦ ‖F x j‖) (s := Finset.univ)
      (fun j _ ↦ (hc j).norm) one_le_two
    have e : (∑ j, fun x ↦ ‖F x j‖) = fun x ↦ ∑ j, ‖F x j‖ := by
      funext x; simp [Finset.sum_apply]
    rwa [e] at h
  have h1 : eLpNorm F 2 μ ≤ eLpNorm (fun x ↦ ∑ j, ‖F x j‖) 2 μ :=
    eLpNorm_mono_real (f := F) (g := fun x ↦ ∑ j, ‖F x j‖) fun x ↦ norm_euclidean_le_sum (F x)
  have h3 : ∀ j, eLpNorm (fun x ↦ ‖F x j‖) 2 μ = eLpNorm (fun x ↦ F x j) 2 μ :=
    fun j ↦ eLpNorm_norm (f := fun x ↦ F x j)
  calc eLpNorm F 2 μ ≤ ∑ j, eLpNorm (fun x ↦ ‖F x j‖) 2 μ := h1.trans h2
    _ = ∑ j, eLpNorm (fun x ↦ F x j) 2 μ := Finset.sum_congr rfl fun j _ ↦ h3 j

theorem tendsto_formToL2 (hD : IsOpen D) {w₂ : ComplexModel n → ℝ} (hw₂ : ContinuousOn w₂ D)
    {βs : ℕ → testForms D} {β : Lp (EuclideanSpace ℂ (Fin n)) 2 (weightedVolume D w₂)}
    (h : ∀ j, Tendsto (fun m ↦ eLpNorm (fun x ↦ (βs m : Fin n → ComplexModel n → ℂ) j x - β x j)
      2 (weightedVolume D w₂)) atTop (𝓝 0)) :
    Tendsto (fun m ↦ formToL2 hD hw₂ (βs m)) atTop (𝓝 β) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin n)) fun j _ ↦ h j
  rw [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
    fun m ↦ ?_
  refine (eLpNorm_euclidean_le_sum ((Lp.aestronglyMeasurable _).sub
    (Lp.aestronglyMeasurable _))).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ ↦ eLpNorm_congr_ae ?_
  filter_upwards [(memLp_formVec hD hw₂ (βs m).2).coeFn_toLp] with x hx
  change (formToL2 hD hw₂ (βs m) x - β x) j = _
  rw [PiLp.sub_apply]
  change ((memLp_formVec hD hw₂ (βs m).2).toLp _) x j - β x j = _
  rw [hx, formVec_apply]

theorem tendsto_tstarToL2 (hD : IsOpen D) {w₁ w₂ ψ₀ : ComplexModel n → ℝ}
    (hw₁ : ContinuousOn w₁ D) (hw₂ : ContDiffOn ℝ ∞ w₂ D) (hψ : ContinuousOn ψ₀ D)
    {βs : ℕ → testForms D} {α : testForms D}
    (h : Tendsto (fun m ↦ eLpNorm (fun x ↦ tstarForm w₂ ψ₀ (βs m) x - tstarForm w₂ ψ₀ α x) 2
      (weightedVolume D w₁)) atTop (𝓝 0)) :
    Tendsto (fun m ↦ tstarToL2 hD hw₁ hw₂ hψ (βs m)) atTop (𝓝 (tstarToL2 hD hw₁ hw₂ hψ α)) :=
  (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun m ↦ tstarForm w₂ ψ₀ (βs m))
    (fun m ↦ memLp_tstarForm hD hw₁ hw₂ hψ (βs m).2) (tstarForm w₂ ψ₀ α)
    (memLp_tstarForm hD hw₁ hw₂ hψ α.2)).mpr h

theorem continuous_dbarForm {α : Fin n → ComplexModel n → ℂ} (hα : α ∈ testForms D)
    (p : Fin n × Fin n) : Continuous (dbarForm α p) := by
  have h1 := continuous_dbarDir (v := (coordVec p.1 : ComplexModel n))
    ((hα p.2).1.of_le (by norm_cast))
  have h2 := continuous_dbarDir (v := (coordVec p.2 : ComplexModel n))
    ((hα p.1).1.of_le (by norm_cast))
  exact h1.sub h2

theorem tsupport_dbarForm_subset {α : Fin n → ComplexModel n → ℂ} (p : Fin n × Fin n) :
    tsupport (dbarForm α p) ⊆ tsupport (α p.1) ∪ tsupport (α p.2) := by
  refine closure_minimal (fun x hx ↦ ?_) ((isClosed_tsupport _).union (isClosed_tsupport _))
  by_contra h
  simp only [mem_union, not_or] at h
  apply hx
  simp [dbarForm, dbarDir_eq_zero_of_notMem_tsupport h.1, dbarDir_eq_zero_of_notMem_tsupport h.2]

theorem memLp_dbarForm (hD : IsOpen D) {w : ComplexModel n → ℝ} (hw : ContinuousOn w D)
    {α : Fin n → ComplexModel n → ℂ} (hα : α ∈ testForms D) (p : Fin n × Fin n) :
    MemLp (dbarForm α p) 2 (weightedVolume D w) :=
  memLp_weightedVolume_of_continuous hD hw (continuous_dbarForm hα p)
    (((hα p.1).2.1.union (hα p.2).2.1).of_isClosed_subset (isClosed_tsupport _)
      (tsupport_dbarForm_subset p))
    ((tsupport_dbarForm_subset p).trans (union_subset (hα p.1).2.2 (hα p.2).2.2)) 2

theorem integral_norm_sq_eq_eLpNorm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {μ : Measure (ComplexModel n)} {f : ComplexModel n → V} (hf : MemLp f 2 μ) :
    ∫ x, ‖f x‖ ^ 2 ∂μ = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [← norm_sq_toLp_eq_integral hf, Lp.norm_toLp]

theorem tendsto_dbarEnergy (hD : IsOpen D) {w₃ : ComplexModel n → ℝ} (hw₃ : ContinuousOn w₃ D)
    {βs : ℕ → testForms D}
    (h : ∀ p, Tendsto (fun m ↦ eLpNorm (fun x ↦ dbarForm (βs m : Fin n → ComplexModel n → ℂ) p x -
      (0 : Fin n × Fin n → ComplexModel n → ℂ) p x) 2 (weightedVolume D w₃)) atTop (𝓝 0)) :
    Tendsto (fun m ↦ ∫ x, (∑ p, ‖dbarForm (βs m : Fin n → ComplexModel n → ℂ) p x‖ ^ 2) *
      Real.exp (-w₃ x)) atTop (𝓝 0) := by
  have heq : ∀ m, ∫ x, (∑ p, ‖dbarForm (βs m : Fin n → ComplexModel n → ℂ) p x‖ ^ 2) *
      Real.exp (-w₃ x) = ∑ p, (eLpNorm (dbarForm (βs m : Fin n → ComplexModel n → ℂ) p) 2
        (weightedVolume D w₃)).toReal ^ 2 := by
    intro m
    have hzero : ∀ x ∉ D, (∑ p, ‖dbarForm (βs m : Fin n → ComplexModel n → ℂ) p x‖ ^ 2) *
        Real.exp (-w₃ x) = 0 := by
      intro x hx
      rw [Finset.sum_eq_zero fun p _ ↦ by
        rw [image_eq_zero_of_notMem_tsupport fun h' ↦ hx
          ((tsupport_dbarForm_subset p).trans (union_subset ((βs m).2 p.1).2.2
            ((βs m).2 p.2).2.2) h'), norm_zero]; norm_num, zero_mul]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have hw := integral_weightedVolume (V := ℝ) hD hw₃
      (fun x ↦ ∑ p, ‖dbarForm (βs m : Fin n → ComplexModel n → ℂ) p x‖ ^ 2)
    simp only [smul_eq_mul] at hw
    simp_rw [mul_comm _ (Real.exp _)]
    rw [← hw, integral_finsetSum _ fun p _ ↦
      (memLp_two_iff_integrable_sq_norm (memLp_dbarForm hD hw₃ (βs m).2 p).1).mp
        (memLp_dbarForm hD hw₃ (βs m).2 p)]
    exact Finset.sum_congr rfl fun p _ ↦
      integral_norm_sq_eq_eLpNorm_sq (memLp_dbarForm hD hw₃ (βs m).2 p)
  simp_rw [heq]
  have hp : ∀ p, Tendsto (fun m ↦ (eLpNorm (dbarForm (βs m : Fin n → ComplexModel n → ℂ) p) 2
      (weightedVolume D w₃)).toReal ^ 2) atTop (𝓝 0) := by
    intro p
    have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (h p)
    simp only [Pi.zero_apply, sub_zero, Function.comp_def, ENNReal.toReal_zero] at h0
    simpa using h0.pow 2
  simpa using tendsto_finsetSum Finset.univ fun p _ ↦ hp p

end Convergence

section Approx

variable {n : ℕ} {D : Set (ComplexModel n)}

theorem integral_congr_of_ae_weightedVolume (hD : IsOpen D) {w : ComplexModel n → ℝ}
    (hw : ContinuousOn w D) {H₁ H₂ : ComplexModel n → ℂ} (h1 : ∀ x ∉ D, H₁ x = 0)
    (h2 : ∀ x ∉ D, H₂ x = 0) (hae : ∀ᵐ x ∂(weightedVolume D w), H₁ x = H₂ x) :
    ∫ x, H₁ x = ∫ x, H₂ x := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h1,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero h2]
  exact integral_congr_ae (ae_restrict_of_ae_weightedVolume hD hw hae)

theorem memLp_test (hD : IsOpen D) {w : ComplexModel n → ℝ} (hw : ContinuousOn w D)
    {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) : MemLp g 2 (weightedVolume D w) :=
  memLp_weightedVolume_of_continuous hD hw hg.1.continuous hg.2.1 hg.2.2 2

/-- The `(0,1)`-form `∂̄ g` of a test function. -/
def dbarTest {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) : testForms D :=
  ⟨fun j ↦ dbarDir (coordVec j) g, fun _ ↦ hg.dbarDir _⟩

theorem weakDbarEq_dbarTest {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) :
    WeakDbarEq D g (dbarTest hg : Fin n → ComplexModel n → ℂ) := by
  intro h hh j
  exact integral_mul_dbarDir_eq_neg (μ := volume) (hg.1.of_le (by norm_cast))
    (hh.1.of_le (by norm_cast)) (Or.inl hg.2.1) _

theorem integral_dbar_dbar_comm {g h : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g)
    (hh : IsTestFunctionOn D h) (j k : Fin n) :
    ∫ x, (dbarDir (coordVec k) g x * dbarDir (coordVec j) h x -
      dbarDir (coordVec j) g x * dbarDir (coordVec k) h x) = 0 := by
  have hg2 : ContDiff ℝ 2 g := hg.1.of_le (by norm_cast)
  have hh2 : ContDiff ℝ 2 h := hh.1.of_le (by norm_cast)
  have i1 : Integrable fun x ↦ dbarDir (coordVec k) g x * dbarDir (coordVec j) h x :=
    ((continuous_dbarDir (hg2.of_le (by norm_num))).mul
      (continuous_dbarDir (hh2.of_le (by norm_num)))).integrable_of_hasCompactSupport
      (hasCompactSupport_dbarDir hg.2.1).mul_right
  have i2 : Integrable fun x ↦ dbarDir (coordVec j) g x * dbarDir (coordVec k) h x :=
    ((continuous_dbarDir (hg2.of_le (by norm_num))).mul
      (continuous_dbarDir (hh2.of_le (by norm_num)))).integrable_of_hasCompactSupport
      (hasCompactSupport_dbarDir hg.2.1).mul_right
  rw [integral_sub i1 i2]
  have e1 : ∫ x, dbarDir (coordVec k) g x * dbarDir (coordVec j) h x =
      - ∫ x, dbarDir (coordVec k) (dbarDir (coordVec j) h) x * g x := by
    rw [← integral_mul_dbarDir_eq_neg (μ := volume) (contDiff_dbarDir (k := 1) hh2)
      (hg2.of_le (by norm_num)) (Or.inr hg.2.1) (coordVec k)]
    congr 1; funext x; ring
  have e2 : ∫ x, dbarDir (coordVec j) g x * dbarDir (coordVec k) h x =
      - ∫ x, dbarDir (coordVec j) (dbarDir (coordVec k) h) x * g x := by
    rw [← integral_mul_dbarDir_eq_neg (μ := volume) (contDiff_dbarDir (k := 1) hh2)
      (hg2.of_le (by norm_num)) (Or.inr hg.2.1) (coordVec j)]
    congr 1; funext x; ring
  have hcomm : (fun x ↦ dbarDir (coordVec k) (dbarDir (coordVec j) h) x * g x) =
      fun x ↦ dbarDir (coordVec j) (dbarDir (coordVec k) h) x * g x := by
    funext x; rw [dbarDir_dbarDir_comm hh2.contDiffAt]
  rw [e1, e2, hcomm, sub_self]

/-- `a (∂̄ g)` is weakly `∂̄`-closed. -/
theorem formToL2_dbarTest_mem_closedForms (hD : IsOpen D) {w₂ : ComplexModel n → ℝ}
    (hw₂ : ContDiffOn ℝ ∞ w₂ D) {g : ComplexModel n → ℂ} (hg : IsTestFunctionOn D g) :
    formToL2 hD hw₂.continuousOn (dbarTest hg) ∈ closedForms hD hw₂ := by
  rw [mem_closedForms_iff]
  intro h hh j k
  rw [← integral_dbar_dbar_comm hg hh j k]
  refine integral_congr_of_ae_weightedVolume hD hw₂.continuousOn (fun x hx ↦ ?_) (fun x hx ↦ ?_)
    ?_
  · have hxs : x ∉ tsupport h := fun h' ↦ hx (hh.2.2 h')
    simp [dbarDir_eq_zero_of_notMem_tsupport hxs]
  · have hxs : x ∉ tsupport h := fun h' ↦ hx (hh.2.2 h')
    simp [dbarDir_eq_zero_of_notMem_tsupport hxs]
  · filter_upwards [(memLp_formVec hD hw₂.continuousOn (dbarTest hg).2).coeFn_toLp] with x hx
    change (memLp_formVec hD hw₂.continuousOn (dbarTest hg).2).toLp _ x k * _ -
      (memLp_formVec hD hw₂.continuousOn (dbarTest hg).2).toLp _ x j * _ = _
    rw [hx]
    rfl

theorem memLp_component {μ : Measure (ComplexModel n)}
    (β : Lp (EuclideanSpace ℂ (Fin n)) 2 μ) (j : Fin n) : MemLp (fun x ↦ β x j) 2 μ := by
  have h := (EuclideanSpace.proj (𝕜 := ℂ) j).comp_memLp' (Lp.memLp β)
  exact h

/-- **Approximation of the projection of a test form onto the weakly closed forms.** -/
theorem exists_approx_of_density (hdens : HormanderDensityStatement n) (hD : IsOpen D)
    {w₃ ψ₀ : ComplexModel n → ℝ} (hw₃ : ContDiffOn ℝ ∞ w₃ D) (hψ : ContDiffOn ℝ ∞ ψ₀ D)
    (hψ0 : ∀ x, 0 ≤ ψ₀ x) {η : ℕ → ComplexModel n → ℝ}
    (hη1 : ∀ k, ContDiff ℝ ∞ (η k) ∧ HasCompactSupport (η k) ∧ tsupport (η k) ⊆ D ∧
      ∀ x, 0 ≤ η k x ∧ η k x ≤ 1)
    (hη2 : ∀ x ∈ D, ∀ᶠ k in atTop, η k =ᶠ[𝓝 x] fun _ ↦ 1)
    (hη3 : ∀ k, ∀ x ∈ D, ‖fderiv ℝ (η k) x‖ ^ 2 ≤ Real.exp (ψ₀ x))
    (hw₂ : ContDiffOn ℝ ∞ (fun x ↦ w₃ x - ψ₀ x) D)
    (hw₁ : ContinuousOn (fun x ↦ w₃ x - 2 * ψ₀ x) D)
    [(closedForms hD hw₂).HasOrthogonalProjection] (α : testForms D) :
    ∃ βs : ℕ → testForms D,
      Tendsto (fun m ↦ formToL2 hD hw₂.continuousOn (βs m)) atTop
        (𝓝 ((closedForms hD hw₂).starProjection (formToL2 hD hw₂.continuousOn α))) ∧
      Tendsto (fun m ↦ tstarToL2 hD hw₁ hw₂ hψ.continuousOn (βs m)) atTop
        (𝓝 (tstarToL2 hD hw₁ hw₂ hψ.continuousOn α)) ∧
      Tendsto (fun m ↦ ∫ x, (∑ p, ‖dbarForm (βs m : Fin n → ComplexModel n → ℂ) p x‖ ^ 2) *
        Real.exp (-w₃ x)) atTop (𝓝 0) := by
  have h12 : ∀ x ∈ D, w₃ x - ψ₀ x = (w₃ x - 2 * ψ₀ x) + ψ₀ x := fun x _ ↦ by ring
  set W := closedForms hD hw₂ with hWdef
  set β := W.starProjection (formToL2 hD hw₂.continuousOn α) with hβdef
  have hβW : β ∈ W := W.starProjection_apply_mem _
  have horth : formToL2 hD hw₂.continuousOn α - β ∈ Wᗮ := W.sub_starProjection_mem_orthogonal _
  have hT : ∀ g, IsTestFunctionOn D g →
      ∑ j, ∫ x in D, conj (dbarDir (coordVec j) g x) * β x j * Real.exp (-(w₃ x - ψ₀ x)) =
        ∫ x in D, conj (g x) * tstarForm (fun x ↦ w₃ x - ψ₀ x) ψ₀ α x *
          Real.exp (-(w₃ x - 2 * ψ₀ x)) := by
    intro g hg
    have hfd : ∀ j, MemLp (dbarDir (coordVec j) g) 2 (weightedVolume D fun x ↦ w₃ x - ψ₀ x) :=
      fun j ↦ memLp_test hD hw₂.continuousOn (hg.dbarDir _)
    have h1 : ⟪formToL2 hD hw₂.continuousOn (dbarTest hg), β⟫_ℂ =
        ⟪formToL2 hD hw₂.continuousOn (dbarTest hg), formToL2 hD hw₂.continuousOn α⟫_ℂ := by
      have := Submodule.inner_right_of_mem_orthogonal
        (formToL2_dbarTest_mem_closedForms hD hw₂ hg) horth
      rw [inner_sub_right, sub_eq_zero] at this
      exact this.symm
    have h2 := (weakDbarEq_iff_inner hD hw₁ hw₂ hψ.continuousOn h12
      (memLp_test hD hw₁ hg) hfd).mp (weakDbarEq_dbarTest hg) α
    have h3 : ⟪formToL2 hD hw₂.continuousOn (dbarTest hg), β⟫_ℂ =
        ⟪(memLp_test hD hw₁ hg).toLp g, tstarToL2 hD hw₁ hw₂ hψ.continuousOn α⟫_ℂ := by
      rw [h1, ← inner_conj_symm, ← inner_conj_symm ((memLp_test hD hw₁ hg).toLp g)]
      congr 1
      exact h2.symm
    rw [inner_formToL2, inner_toLp_eq_integral] at h3
    have hL : ∀ j, ∫ x, conj ((dbarTest hg : Fin n → ComplexModel n → ℂ) j x) * β x j
        ∂(weightedVolume D fun x ↦ w₃ x - ψ₀ x) =
        ∫ x in D, conj (dbarDir (coordVec j) g x) * β x j * Real.exp (-(w₃ x - ψ₀ x)) := by
      intro j
      rw [integral_weightedVolume hD hw₂.continuousOn]
      refine setIntegral_congr_fun hD.measurableSet fun x _ ↦ ?_
      simp only [Complex.real_smul, dbarTest]
      ring
    have hA : ((tstarToL2 hD hw₁ hw₂ hψ.continuousOn) α :
        Lp ℂ 2 (weightedVolume D fun x ↦ w₃ x - 2 * ψ₀ x)) =
        (memLp_tstarForm hD hw₁ hw₂ hψ.continuousOn α.2).toLp _ := rfl
    have hR : ∫ x, ⟪g x, ((tstarToL2 hD hw₁ hw₂ hψ.continuousOn) α :
        Lp ℂ 2 (weightedVolume D fun x ↦ w₃ x - 2 * ψ₀ x)) x⟫_ℂ
        ∂(weightedVolume D fun x ↦ w₃ x - 2 * ψ₀ x) =
        ∫ x in D, conj (g x) * tstarForm (fun x ↦ w₃ x - ψ₀ x) ψ₀ α x *
          Real.exp (-(w₃ x - 2 * ψ₀ x)) := by
      rw [hA]
      have e : ∫ x, ⟪g x, (memLp_tstarForm hD hw₁ hw₂ hψ.continuousOn α.2).toLp _ x⟫_ℂ
          ∂(weightedVolume D fun x ↦ w₃ x - 2 * ψ₀ x) =
          ∫ x, conj (g x) * tstarForm (fun x ↦ w₃ x - ψ₀ x) ψ₀ α x
          ∂(weightedVolume D fun x ↦ w₃ x - 2 * ψ₀ x) := by
        refine integral_congr_ae ?_
        filter_upwards [(memLp_tstarForm hD hw₁ hw₂ hψ.continuousOn α.2).coeFn_toLp] with x hx
        rw [hx, RCLike.inner_apply, mul_comm]
      rw [e, integral_weightedVolume hD hw₁]
      refine setIntegral_congr_fun hD.measurableSet fun x _ ↦ ?_
      simp only [Complex.real_smul]
      ring
    rw [← hR, ← h3]
    exact Finset.sum_congr rfl fun j _ ↦ (hL j).symm
  have hS : ∀ h, IsTestFunctionOn D h → ∀ j k,
      ∫ x, (β x k * dbarDir (coordVec j) h x - β x j * dbarDir (coordVec k) h x) =
        - ∫ x, (0 : Fin n × Fin n → ComplexModel n → ℂ) (j, k) x * h x := by
    intro h hh j k
    rw [(mem_closedForms_iff hD hw₂ β).mp hβW h hh j k]
    simp
  obtain ⟨βs, hβs, c1, c2, c3⟩ := hdens D hD w₃ ψ₀ hw₃ hψ hψ0 η hη1 hη2 hη3
    (fun j x ↦ β x j) (tstarForm (fun x ↦ w₃ x - ψ₀ x) ψ₀ α) 0
    (fun j ↦ memLp_component β j) (memLp_tstarForm hD hw₁ hw₂ hψ.continuousOn α.2)
    (fun p ↦ by simp) hT hS
  refine ⟨fun m ↦ ⟨βs m, hβs m⟩, tendsto_formToL2 hD hw₂.continuousOn c1,
    tendsto_tstarToL2 hD hw₁ hw₂ hψ.continuousOn c2,
    tendsto_dbarEnergy hD hw₃.continuousOn c3⟩

end Approx

/-- **Hörmander's `L²` estimate on convex domains**, from the density statement. -/
theorem hormanderL2Estimate_of_density {n : ℕ} (hdens : HormanderDensityStatement n) :
    HormanderL2Estimate n := by
  intro D hDo hDc hDb K hK hKD t ht
  obtain ⟨L', U₀, η, ψ₀, χ, hL'o, hL'c, hL'D, hU₀o, hKU₀, hU₀L', hη, hηev, hψs, hχs, hηgrad,
    hψ0, hU₀z, h2ψ, hLevi, -⟩ := exists_hormanderCutoffData hDo hDc hDb hK hKD ((1 + 1 / t) * n)
  refine ⟨L', U₀, fun x ↦ χ x - 2 * ψ₀ x, fun x ↦ χ x - ψ₀ x, hL'o, hL'c, hL'D, hU₀o, hKU₀,
    hU₀L', hχs.continuousOn.sub (continuousOn_const.mul hψs.continuousOn),
    hχs.continuousOn.sub hψs.continuousOn,
    fun x hx ↦ ⟨by linarith [h2ψ x hx], by linarith [hψ0 x]⟩,
    fun x hx ↦ by simp [(hU₀z x hx).1, (hU₀z x hx).2], ?_⟩
  intro Φ hΦ hpsh f hf hfc g hg0 hfg hgi
  simp only [← add_sub_assoc] at hf hgi ⊢
  have hΦ' : ContDiffOn ℝ ∞ Φ L' := hΦ.mono (subset_closure.trans hL'D)
  have hpsh' : ∀ x ∈ L', ∀ ξ, 0 ≤ leviForm Φ x ξ := fun x hx ↦ hpsh x (hL'D (subset_closure hx))
  have hw₃ : ContDiffOn ℝ ∞ (fun x ↦ Φ x + χ x) L' := hΦ'.add hχs
  have hw₂ : ContDiffOn ℝ ∞ (fun x ↦ (fun x ↦ Φ x + χ x) x - ψ₀ x) L' := hw₃.sub hψs
  have hw₁ : ContinuousOn (fun x ↦ (fun x ↦ Φ x + χ x) x - 2 * ψ₀ x) L' :=
    hw₃.continuousOn.sub (continuousOn_const.mul hψs.continuousOn)
  have h12 : ∀ x ∈ L', (fun x ↦ (fun x ↦ Φ x + χ x) x - ψ₀ x) x =
      (fun x ↦ (fun x ↦ Φ x + χ x) x - 2 * ψ₀ x) x + ψ₀ x := fun x _ ↦ by simp only; ring
  have : CompleteSpace (closedForms hL'o hw₂) :=
    (Submodule.isClosed_orthogonal _).completeSpace_coe
  set a := formToL2 hL'o hw₂.continuousOn
  set A := tstarToL2 hL'o hw₁ hw₂ hψs.continuousOn
  set F := (memLp_formVec_of_components hf).toLp (formVec f)
  set G := ∫ x in L', g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) with hGdef
  have hG0 : 0 ≤ G := setIntegral_nonneg hL'o.measurableSet fun x hx ↦
    mul_nonneg (hg0 x hx) (Real.exp_pos _).le
  have hM : 0 ≤ (1 + t) * G := mul_nonneg (by linarith) hG0
  have hFW : F ∈ closedForms hL'o hw₂ := by
    rw [mem_closedForms_iff]
    intro h hh j k
    rw [← hfc h hh j k]
    refine integral_congr_of_ae_weightedVolume hL'o hw₂.continuousOn (fun x hx ↦ ?_)
      (fun x hx ↦ ?_) ?_
    · have hxs : x ∉ tsupport h := fun h' ↦ hx (hh.2.2 h')
      simp [dbarDir_eq_zero_of_notMem_tsupport hxs]
    · have hxs : x ∉ tsupport h := fun h' ↦ hx (hh.2.2 h')
      simp [dbarDir_eq_zero_of_notMem_tsupport hxs]
    · filter_upwards [(memLp_formVec_of_components hf).coeFn_toLp] with x hx
      simp only [F]
      rw [hx, formVec_apply, formVec_apply]
  set Q : testForms L' → ℝ := fun α ↦
    ∫ x, (∑ p, ‖dbarForm (α : Fin n → ComplexModel n → ℂ) p x‖ ^ 2) * Real.exp (-(Φ x + χ x))
  have hest : ∀ α : testForms L', ‖⟪a α, F⟫_ℂ‖ ^ 2 ≤ (1 + t) * G * (‖A α‖ ^ 2 + Q α) := by
    intro α
    have hpair := norm_sq_pairing_le hL'o hΦ' hχs hψs hpsh' ht hLevi hf hg0 hfg hgi α.2
    have hinner : ⟪a α, F⟫_ℂ = ∑ j, ∫ x, conj ((α : Fin n → ComplexModel n → ℂ) j x) * f j x
        ∂(weightedVolume L' fun x ↦ Φ x + χ x - ψ₀ x) := by
      simp only [a, F]
      rw [inner_formToL2]
      refine Finset.sum_congr rfl fun j _ ↦ integral_congr_ae ?_
      filter_upwards [(memLp_formVec_of_components hf).coeFn_toLp] with x hx
      rw [hx, formVec_apply]
    have hnorm : ‖A α‖ ^ 2 = ∫ x, ‖tstarForm (fun x ↦ Φ x + χ x - ψ₀ x) ψ₀ α x‖ ^ 2
        ∂(weightedVolume L' fun x ↦ Φ x + χ x - 2 * ψ₀ x) :=
      norm_sq_toLp_eq_integral (memLp_tstarForm hL'o hw₁ hw₂ hψs.continuousOn α.2)
    rw [hinner, hnorm]
    exact hpair
  have happrox := fun α ↦ exists_approx_of_density hdens hL'o hw₃ hψs hψ0 hη hηev hηgrad hw₂ hw₁ α
  have hbound := norm_inner_le_of_approx' a A Q (closedForms hL'o hw₂) hFW hM hest happrox
  exact hormander_of_pairing_bound hL'o hw₁ hw₂ hψs.continuousOn h12 hf hM hbound

end

end Hironaka.Hormander
