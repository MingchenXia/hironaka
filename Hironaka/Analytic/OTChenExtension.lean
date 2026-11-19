import Hironaka.Analytic.OTChenWeights
import Hironaka.Analytic.OTWeakDbar
import Hironaka.Analytic.OTSliceVanishing
import Hironaka.Analytic.WeakDbarWeyl
import Hironaka.Manifold.HolomorphicContDiff

set_option autoImplicit false

/-!
# Chen's extension step

The cutoff extension `chenA ε f z = χ(|z_n|²/ε²) f(z')` of data `f` on the hyperplane and its
`∂̄`, `chenV ε f`, supported in `{|z_n| ≤ ε}`.
-/

open Set Filter MeasureTheory Complex Metric
open scoped Topology ContDiff ComplexConjugate ENNReal

namespace Hironaka.OTChen

noncomputable section

open CauchyGreen Hormander

variable {m : ℕ}

/-! ### The cutoff extension -/

/-- `χ(|z_n|²/ε²) f(z')`. -/
def chenA (ε : ℝ) (f : ComplexModel m → ℂ) (z : ComplexModel (m + 1)) : ℂ :=
  ((chenCutoff (coordSq (Fin.last m) z / ε ^ 2) : ℝ) : ℂ) * f (initCoords z)

/-- The `z_n`-component of `∂̄ (chenA ε f)`. -/
def chenV (ε : ℝ) (f : ComplexModel m → ℂ) (z : ComplexModel (m + 1)) : ℂ :=
  ((deriv chenCutoff (coordSq (Fin.last m) z / ε ^ 2) / ε ^ 2 : ℝ) : ℂ) * z (Fin.last m) *
    f (initCoords z)

/-- The first `m` coordinates as a complex continuous linear map. -/
def initCLM (m : ℕ) : ComplexModel (m + 1) →L[ℂ] ComplexModel m :=
  (ContinuousLinearMap.fst ℂ _ _).comp (splitCLE m).toContinuousLinearMap

@[simp] theorem initCLM_apply (z : ComplexModel (m + 1)) : initCLM m z = initCoords z := rfl

@[simp] theorem initCoords_hyperplaneEmbedding (w : ComplexModel m) :
    initCoords (hyperplaneEmbedding m w) = w := by
  ext i; simp

theorem coordSq_hyperplaneEmbedding (w : ComplexModel m) :
    coordSq (Fin.last m) (hyperplaneEmbedding m w) = 0 := by
  simp [coordSq]

theorem chenA_hyperplaneEmbedding (ε : ℝ) (f : ComplexModel m → ℂ) (w : ComplexModel m) :
    chenA ε f (hyperplaneEmbedding m w) = f w := by
  simp [chenA, coordSq_hyperplaneEmbedding, chenCutoff_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem contDiff_cutoff_comp (ε : ℝ) :
    ContDiff ℝ ∞ (fun z : ComplexModel (m + 1) ↦
      ((chenCutoff (coordSq (Fin.last m) z / ε ^ 2) : ℝ) : ℂ)) :=
  ofRealCLM.contDiff.comp (contDiff_chenCutoff.comp ((contDiff_coordSq _).div_const _))

theorem contDiffAt_comp_initCoords {f : ComplexModel m → ℂ} {W : Set (ComplexModel m)}
    (hW : IsOpen W) (hf : DifferentiableOn ℂ f W) {z : ComplexModel (m + 1)}
    (hz : initCoords z ∈ W) : ContDiffAt ℝ ∞ (fun y ↦ f (initCoords y)) z := by
  have h2 : ContDiffAt ℝ ∞ f (initCoords z) :=
    contDiffAt_real_of_differentiableOn_complex hf hW hz
  exact h2.comp z ((initCLM m).restrictScalars ℝ).contDiff.contDiffAt

theorem eventually_chenA_eq_zero {ε : ℝ} {f : ComplexModel m → ℂ} {z : ComplexModel (m + 1)}
    (hz : ε ^ 2 < coordSq (Fin.last m) z) (hε : 0 < ε) : chenA ε f =ᶠ[𝓝 z] fun _ ↦ 0 := by
  have hc : ContinuousAt (coordSq (Fin.last m)) z := (contDiff_coordSq _).continuous.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hz)] with y hy
  have : 1 ≤ coordSq (Fin.last m) y / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; linarith
  simp [chenA, chenCutoff_of_ge this]

/-- `chenA ε f` is smooth at points where either `f` is holomorphic near the projection or
`|z_n| > ε`. -/
theorem contDiffAt_chenA {ε : ℝ} (hε : 0 < ε) {f : ComplexModel m → ℂ}
    {W : Set (ComplexModel m)} (hW : IsOpen W) (hf : DifferentiableOn ℂ f W)
    {z : ComplexModel (m + 1)} (hz : coordSq (Fin.last m) z ≤ ε ^ 2 → initCoords z ∈ W) :
    ContDiffAt ℝ ∞ (chenA ε f) z := by
  by_cases hq : coordSq (Fin.last m) z ≤ ε ^ 2
  · exact (contDiff_cutoff_comp ε).contDiffAt.mul (contDiffAt_comp_initCoords hW hf (hz hq))
  · exact contDiffAt_const.congr_of_eventuallyEq (eventually_chenA_eq_zero (not_le.mp hq) hε)

theorem hasDerivAt_cutoff_div {ε s : ℝ} :
    HasDerivAt (fun t : ℝ ↦ chenCutoff (t / ε ^ 2))
      (deriv chenCutoff (s / ε ^ 2) / ε ^ 2) s := by
  have h1 := (contDiff_chenCutoff (k := 1)).differentiable one_ne_zero (s / ε ^ 2)
  have hd : HasDerivAt (fun t : ℝ ↦ t / ε ^ 2) (1 / ε ^ 2) s := (hasDerivAt_id s).div_const _
  have h2 := HasDerivAt.comp (h₂ := chenCutoff) (h := fun t : ℝ ↦ t / ε ^ 2) s h1.hasDerivAt hd
  exact h2.congr_deriv (by simp [div_eq_mul_inv])

/-- **`∂̄` of the cutoff extension.** -/
theorem dbarDir_chenA {ε : ℝ} (hε : 0 < ε) {f : ComplexModel m → ℂ}
    {W : Set (ComplexModel m)} (hW : IsOpen W) (hf : DifferentiableOn ℂ f W)
    {z : ComplexModel (m + 1)} (hz : coordSq (Fin.last m) z ≤ ε ^ 2 → initCoords z ∈ W)
    (j : Fin (m + 1)) :
    dbarDir (coordVec j) (chenA ε f) z = if j = Fin.last m then chenV ε f z else 0 := by
  by_cases hq : coordSq (Fin.last m) z ≤ ε ^ 2
  · have hfd : DifferentiableAt ℂ (fun y ↦ f (initCoords y)) z :=
      ((hf.differentiableAt (hW.mem_nhds (hz hq))).comp z (initCLM m).differentiableAt)
    have hχ : DifferentiableAt ℝ (fun y ↦ chenCutoff (coordSq (Fin.last m) y / ε ^ 2)) z :=
      ((contDiff_chenCutoff (k := ⊤)).comp ((contDiff_coordSq _).div_const _)).differentiable
        (by simp) z
    have h := dbarDir_ofReal_mul (v := coordVec j) hχ (hfd.restrictScalars ℝ)
    change dbarDir (coordVec j) (fun y ↦ ((chenCutoff (coordSq (Fin.last m) y / ε ^ 2) : ℝ) : ℂ) *
      f (initCoords y)) z = _
    rw [h, dbarDir_eq_zero_of_differentiableAt hfd, mul_zero, add_zero]
    have hG := dbarDir_comp_coordSq (G := fun t ↦ chenCutoff (t / ε ^ 2)) (x := z) (Fin.last m) j
      hasDerivAt_cutoff_div.differentiableAt
    rw [hG, hasDerivAt_cutoff_div.deriv]
    split_ifs <;> simp [chenV]
  · have hq' : ε ^ 2 < coordSq (Fin.last m) z := not_le.mp hq
    rw [dbarDir_congr (eventually_chenA_eq_zero hq' hε), dbarDir_const]
    have hd : deriv chenCutoff (coordSq (Fin.last m) z / ε ^ 2) = 0 := by
      apply deriv_chenCutoff_of_lt
      rw [lt_div_iff₀ (by positivity)]; linarith
    split_ifs <;> simp [chenV, hd]

theorem coordSq_le_of_chenV_ne_zero {ε : ℝ} (hε : 0 < ε) {f : ComplexModel m → ℂ}
    {z : ComplexModel (m + 1)} (h : chenV ε f z ≠ 0) : coordSq (Fin.last m) z ≤ ε ^ 2 := by
  by_contra hq
  apply h
  have hd : deriv chenCutoff (coordSq (Fin.last m) z / ε ^ 2) = 0 := by
    apply deriv_chenCutoff_of_lt
    rw [lt_div_iff₀ (by positivity)]; linarith [not_le.mp hq]
  simp [chenV, hd]

theorem norm_chenV_sq_eq (ε : ℝ) (f : ComplexModel m → ℂ) (z : ComplexModel (m + 1)) :
    ‖chenV ε f z‖ ^ 2 = (deriv chenCutoff (coordSq (Fin.last m) z / ε ^ 2) / ε ^ 2) ^ 2 *
      coordSq (Fin.last m) z * ‖f (initCoords z)‖ ^ 2 := by
  simp only [chenV, norm_mul, Complex.norm_real, Real.norm_eq_abs, coordSq]
  rw [mul_pow, mul_pow, sq_abs]

theorem norm_chenA_le (ε : ℝ) (f : ComplexModel m → ℂ) (z : ComplexModel (m + 1)) :
    ‖chenA ε f z‖ ≤ ‖f (initCoords z)‖ := by
  simp only [chenA, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (chenCutoff_nonneg _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (chenCutoff_le_one _)

theorem chenA_eq_zero_of_lt {ε : ℝ} (hε : 0 < ε) {f : ComplexModel m → ℂ}
    {z : ComplexModel (m + 1)} (hz : ε ^ 2 < coordSq (Fin.last m) z) : chenA ε f z = 0 :=
  (eventually_chenA_eq_zero (f := f) hz hε).self_of_nhds

/-! ### Helpers -/

theorem integrable_restrict_of_continuousOn_bound {n : ℕ} {D : Set (ComplexModel n)}
    (hDo : IsOpen D) (hDb : Bornology.IsBounded D) {F : ComplexModel n → ℝ}
    (hF : ContinuousOn F D) {M : ℝ} (hM : ∀ z ∈ D, ‖F z‖ ≤ M) :
    Integrable F (volume.restrict D) := by
  have : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hDb.measure_lt_top.ne
  exact Integrable.of_bound (hF.aestronglyMeasurable hDo.measurableSet) M
    ((ae_restrict_iff' hDo.measurableSet).mpr (Eventually.of_forall hM))

theorem sum_smul_coordVec_apply {n : ℕ} (ξ : Fin n → ℂ) (i : Fin n) :
    (∑ j, ξ j • coordVec j : ComplexModel n) i = ξ i := by
  simp [coordVec, Pi.single_apply]

theorem sum_conj_mul_ite {n : ℕ} (ξ : Fin n → ℂ) (i : Fin n) (c : ℂ) :
    ∑ j, conj (ξ j) * (if j = i then c else 0) = conj (ξ i) * c := by
  simp

/-- The weight `Φ_δ = ϕ + log (|z_n|² + δ²)`. -/
def chenPhi (ϕ : ComplexModel (m + 1) → ℝ) (δ : ℝ) (z : ComplexModel (m + 1)) : ℝ :=
  ϕ z + Real.log (coordSq (Fin.last m) z + δ ^ 2)

theorem exp_neg_chenPhi_add {ϕ : ComplexModel (m + 1) → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (z : ComplexModel (m + 1)) (l : ℝ) :
    Real.exp (-(chenPhi ϕ δ z + l)) =
      Real.exp (-ϕ z) * Real.exp (-l) / (coordSq (Fin.last m) z + δ ^ 2) := by
  have hq : 0 ≤ coordSq (Fin.last m) z := by unfold coordSq; positivity
  have hP : 0 < coordSq (Fin.last m) z + δ ^ 2 := by positivity
  rw [chenPhi, show -(ϕ z + Real.log (coordSq (Fin.last m) z + δ ^ 2) + l) =
    -ϕ z + -l - Real.log (coordSq (Fin.last m) z + δ ^ 2) by ring, Real.exp_sub,
    Real.exp_add, Real.exp_log hP]

theorem coordSq_nonneg (z : ComplexModel (m + 1)) : 0 ≤ coordSq (Fin.last m) z := by
  unfold coordSq; positivity

theorem coordSq_le_norm_sq (z : ComplexModel (m + 1)) : coordSq (Fin.last m) z ≤ ‖z‖ ^ 2 := by
  unfold coordSq
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le z _) 2

theorem exists_coordSq_le_of_isBounded {D : Set (ComplexModel (m + 1))}
    (hD : Bornology.IsBounded D) : ∃ r : ℝ, 0 ≤ r ∧ ∀ z ∈ D, coordSq (Fin.last m) z ≤ r := by
  obtain ⟨r, hr⟩ := hD.subset_closedBall 0
  refine ⟨r ^ 2, by positivity, fun z hz ↦ (coordSq_le_norm_sq z).trans ?_⟩
  have := hr hz
  rw [mem_closedBall, dist_zero_right] at this
  exact pow_le_pow_left₀ (norm_nonneg _) this 2

theorem contDiffOn_chenPhi {D : Set (ComplexModel (m + 1))} {ϕ : ComplexModel (m + 1) → ℝ}
    (hϕ : ContDiffOn ℝ ∞ ϕ D) {δ : ℝ} (hδ : 0 < δ) : ContDiffOn ℝ ∞ (chenPhi ϕ δ) D := by
  refine hϕ.add ?_
  refine ((contDiff_coordSq _).add contDiff_const).contDiffOn.log fun z _ ↦ ?_
  have := coordSq_nonneg z
  positivity

theorem leviForm_log_coordSq (δ : ℝ) (hδ : 0 < δ) (x ξ : ComplexModel (m + 1)) :
    leviForm (fun z ↦ Real.log (coordSq (Fin.last m) z + δ ^ 2)) x ξ =
      δ ^ 2 / (coordSq (Fin.last m) x + δ ^ 2) ^ 2 * ‖ξ (Fin.last m)‖ ^ 2 := by
  have hP : 0 < coordSq (Fin.last m) x + δ ^ 2 := by have := coordSq_nonneg x; positivity
  rw [leviForm_comp_coordSq (G := fun t ↦ Real.log (t + δ ^ 2)) _ (contDiffAt_log_add_sq hP),
    levi_log_add_sq hP]

theorem leviForm_chenPhi {D : Set (ComplexModel (m + 1))} (hDo : IsOpen D)
    {ϕ : ComplexModel (m + 1) → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D) {δ : ℝ} (hδ : 0 < δ)
    {x : ComplexModel (m + 1)} (hx : x ∈ D) (ξ : ComplexModel (m + 1)) :
    leviForm (chenPhi ϕ δ) x ξ = leviForm ϕ x ξ +
      δ ^ 2 / (coordSq (Fin.last m) x + δ ^ 2) ^ 2 * ‖ξ (Fin.last m)‖ ^ 2 := by
  have h1 : ContDiffAt ℝ 2 ϕ x :=
    ((hϕ x hx).contDiffAt (hDo.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hP : 0 < coordSq (Fin.last m) x + δ ^ 2 := by have := coordSq_nonneg x; positivity
  have h2 : ContDiffAt ℝ 2 (fun z ↦ Real.log (coordSq (Fin.last m) z + δ ^ 2)) x :=
    (contDiffAt_log_add_sq hP).comp x ((contDiff_coordSq _).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top))
  have := leviForm_add h1 h2 ξ
  rw [← leviForm_log_coordSq δ hδ x ξ, ← this]
  rfl

/-- The Hörmander clause for fixed data `D', lam₁, lam₂, t`. -/
def HormanderClause {n : ℕ} (D D' : Set (ComplexModel n)) (lam₁ lam₂ : ComplexModel n → ℝ)
    (t : ℝ) : Prop :=
  ∀ Φ : ComplexModel n → ℝ, ContDiffOn ℝ ∞ Φ D → (∀ x ∈ D, ∀ ξ, 0 ≤ leviForm Φ x ξ) →
    ∀ f : Fin n → ComplexModel n → ℂ,
      (∀ j, MemLp (f j) 2 (weightedVolume D' fun x ↦ Φ x + lam₂ x)) → WeakDbarClosed D' f →
    ∀ g : ComplexModel n → ℝ, (∀ x ∈ D', 0 ≤ g x) →
      (∀ x ∈ D', ∀ ξ : Fin n → ℂ,
        ‖∑ j, conj (ξ j) * f j x‖ ^ 2 ≤ g x * leviForm Φ x (∑ j, ξ j • coordVec j)) →
      Integrable (fun x ↦ g x * Real.exp (-(Φ x + lam₁ x))) (volume.restrict D') →
    (∃ u : ComplexModel n → ℂ, MemLp u 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) ∧
        WeakDbarEq D' u f ∧
        ∀ h : ComplexModel n → ℂ, MemLp h 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) →
          WeakDbarEq D' h 0 →
          ∫ x in D', conj (h x) * u x * Real.exp (-(Φ x + lam₁ x)) = 0) ∧
    ∀ u : ComplexModel n → ℂ, MemLp u 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) →
      WeakDbarEq D' u f →
      (∀ h : ComplexModel n → ℂ, MemLp h 2 (weightedVolume D' fun x ↦ Φ x + lam₁ x) →
          WeakDbarEq D' h 0 →
          ∫ x in D', conj (h x) * u x * Real.exp (-(Φ x + lam₁ x)) = 0) →
      ∫ x in D', ‖u x‖ ^ 2 * Real.exp (-(Φ x + lam₁ x)) ≤
        (1 + t) * ∫ x in D', g x * Real.exp (-(Φ x + lam₁ x))

/-! ### Step one: the minimal solution for the weight `Φ_δ` -/

/-- **Step one.**  Hörmander's minimal solution of `∂̄ u = ∂̄ (chenA ε f)` for the weight
`Φ_δ + lam₁`, corrected by Weyl's lemma to `chenA ε f - G` with `G` holomorphic. -/
theorem exists_holomorphic_minimal_solution {D D' : Set (ComplexModel (m + 1))}
    (hDo : IsOpen D) (hD'o : IsOpen D') (hD'D : D' ⊆ D) (hD'b : Bornology.IsBounded D')
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {ϕ : ComplexModel (m + 1) → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ x ∈ D, ∀ ξ, 0 ≤ leviForm ϕ x ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    {f : ComplexModel m → ℂ} {W : Set (ComplexModel m)} (hW : IsOpen W)
    (hf : DifferentiableOn ℂ f W)
    (hDW : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → initCoords z ∈ W)
    {Mf : ℝ} (hMf : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → ‖f (initCoords z)‖ ≤ Mf)
    {Mχ : ℝ} (hMχ : ∀ x, |deriv chenCutoff x| ≤ Mχ)
    {lam₁ lam₂ : ComplexModel (m + 1) → ℝ} (hl₁ : ContinuousOn lam₁ D')
    (hl₂ : ContinuousOn lam₂ D') (hl : ∀ x ∈ D', 0 ≤ lam₁ x ∧ lam₁ x ≤ lam₂ x) {t : ℝ}
    (hest : HormanderClause D D' lam₁ lam₂ t) :
    ∃ G : ComplexModel (m + 1) → ℂ, DifferentiableOn ℂ G D' ∧
      MemLp (fun z ↦ chenA ε f z - G z) 2
        (weightedVolume D' fun x ↦ chenPhi ϕ δ x + lam₁ x) ∧
      ∀ h : ComplexModel (m + 1) → ℂ,
        MemLp h 2 (weightedVolume D' fun x ↦ chenPhi ϕ δ x + lam₁ x) → WeakDbarEq D' h 0 →
        ∫ x in D', conj (h x) * (chenA ε f x - G x) *
          Real.exp (-(chenPhi ϕ δ x + lam₁ x)) = 0 := by
  set q := coordSq (Fin.last m) with hq
  set a := chenA ε f with ha
  set V := chenV ε f with hV
  set v : Fin (m + 1) → ComplexModel (m + 1) → ℂ := fun j ↦ dbarDir (coordVec j) a with hv
  have hD'm : MeasurableSet D' := hD'o.measurableSet
  have hD'sub : ∀ z ∈ D', z ∈ D := fun z hz ↦ hD'D hz
  have haD : ContDiffOn ℝ ∞ a D := fun z hz ↦
    (contDiffAt_chenA hε hW hf (hDW z hz)).contDiffWithinAt
  have haD' : ContDiffOn ℝ 1 a D' :=
    (haD.mono hD'D).of_le (WithTop.coe_le_coe.mpr le_top)
  have hvD : ∀ z ∈ D, ∀ j, v j z = if j = Fin.last m then V z else 0 := fun z hz j ↦
    dbarDir_chenA hε hW hf (hDW z hz) j
  have hΦc : ContinuousOn (chenPhi ϕ δ) D := (contDiffOn_chenPhi hϕ hδ).continuousOn
  have hVsq : ∀ z ∈ D, ‖V z‖ ^ 2 ≤ Mχ ^ 2 * Mf ^ 2 / ε ^ 2 := by
    intro z hz
    by_cases hV0 : V z = 0
    · rw [hV0, norm_zero, zero_pow two_ne_zero]
      have : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0)
      positivity
    · have hqz := coordSq_le_of_chenV_ne_zero hε hV0
      have hf' := hMf z hz hqz
      rw [hV, norm_chenV_sq_eq]
      have h1 : (deriv chenCutoff (q z / ε ^ 2) / ε ^ 2) ^ 2 ≤ Mχ ^ 2 / ε ^ 4 := by
        have h0 : deriv chenCutoff (q z / ε ^ 2) ^ 2 ≤ Mχ ^ 2 :=
          sq_le_sq' (abs_le.mp (hMχ _)).1 (abs_le.mp (hMχ _)).2
        rw [div_pow, ← pow_mul]
        exact div_le_div_of_nonneg_right h0 (by positivity)
      have h2 : ‖f (initCoords z)‖ ^ 2 ≤ Mf ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hf' 2
      have hq0 : 0 ≤ q z := coordSq_nonneg z
      calc (deriv chenCutoff (q z / ε ^ 2) / ε ^ 2) ^ 2 * q z * ‖f (initCoords z)‖ ^ 2
          ≤ Mχ ^ 2 / ε ^ 4 * ε ^ 2 * Mf ^ 2 := by gcongr
        _ = Mχ ^ 2 * Mf ^ 2 / ε ^ 2 := by field_simp
  have hwt : ∀ z ∈ D', ∀ l, 0 ≤ l → Real.exp (-(chenPhi ϕ δ z + l)) ≤ Real.exp Bϕ / δ ^ 2 := by
    intro z hz l hl0
    rw [exp_neg_chenPhi_add hδ]
    have hq0 : 0 ≤ q z := coordSq_nonneg z
    have e1 : Real.exp (-ϕ z) ≤ Real.exp Bϕ := Real.exp_le_exp.mpr (by linarith [hBϕ z (hD'D hz)])
    have e2 : Real.exp (-l) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : Real.exp (-ϕ z) * Real.exp (-l) ≤ Real.exp Bϕ := by
      nlinarith [Real.exp_pos (-ϕ z), Real.exp_pos (-l)]
    nlinarith [Real.exp_pos Bϕ]
  -- The data of the first application.
  have hΦL : ∀ x ∈ D, ∀ ξ, 0 ≤ leviForm (chenPhi ϕ δ) x ξ := by
    intro x hx ξ
    rw [leviForm_chenPhi hDo hϕ hδ hx]
    have := hϕL x hx ξ
    have hq0 := coordSq_nonneg x
    positivity
  have hvcont : ∀ j, ContinuousOn (v j) D' := fun j ↦
    continuousOn_dbarDir_of_contDiffOn hD'o haD' _
  have hvmem : ∀ j, MemLp (v j) 2 (weightedVolume D' fun x ↦ chenPhi ϕ δ x + lam₂ x) := by
    intro j
    rw [memLp_weightedVolume_iff (w := fun x ↦ chenPhi ϕ δ x + lam₂ x)
      (((hΦc.mono hD'D).add hl₂).aemeasurable hD'm) ((hvcont j).aestronglyMeasurable hD'm)]
    refine integrable_restrict_of_continuousOn_bound hD'o hD'b
      (((hvcont j).norm.pow 2).mul ((hΦc.mono hD'D).add hl₂).neg.rexp)
      (M := Mχ ^ 2 * Mf ^ 2 / ε ^ 2 * (Real.exp Bϕ / δ ^ 2)) fun z hz ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hvz : ‖v j z‖ ^ 2 ≤ Mχ ^ 2 * Mf ^ 2 / ε ^ 2 := by
      rw [hvD z (hD'D hz) j]
      split_ifs
      · exact hVsq z (hD'D hz)
      · rw [norm_zero, zero_pow two_ne_zero]
        have : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0)
        positivity
    exact mul_le_mul hvz (hwt z hz (lam₂ z) ((hl z hz).1.trans (hl z hz).2)) (by positivity)
      (by positivity)
  have hvclosed : WeakDbarClosed D' v := weakDbarClosed_of_contDiffOn hD'o haD'
  set g₁ : ComplexModel (m + 1) → ℝ := fun z ↦ ‖V z‖ ^ 2 * (q z + δ ^ 2) ^ 2 / δ ^ 2 with hg₁
  have hg₁0 : ∀ x ∈ D', 0 ≤ g₁ x := fun x _ ↦ by positivity
  have hg₁levi : ∀ x ∈ D', ∀ ξ : Fin (m + 1) → ℂ, ‖∑ j, conj (ξ j) * v j x‖ ^ 2 ≤
      g₁ x * leviForm (chenPhi ϕ δ) x (∑ j, ξ j • coordVec j) := by
    intro x hx ξ
    have hsum : ∑ j, conj (ξ j) * v j x =
        ∑ j, conj (ξ j) * (if j = Fin.last m then V x else 0) :=
      Finset.sum_congr rfl fun j _ ↦ by rw [hvD x (hD'D hx) j]
    rw [hsum, sum_conj_mul_ite, leviForm_chenPhi hDo hϕ hδ (hD'D hx), sum_smul_coordVec_apply]
    have hL := hϕL x (hD'D hx) (∑ j, ξ j • coordVec j)
    have hq0 := coordSq_nonneg x
    have hP : 0 < q x + δ ^ 2 := by positivity
    rw [norm_mul, Complex.norm_conj, mul_pow, hg₁]
    simp only
    have e : ‖V x‖ ^ 2 * (q x + δ ^ 2) ^ 2 / δ ^ 2 *
        (δ ^ 2 / (q x + δ ^ 2) ^ 2 * ‖ξ (Fin.last m)‖ ^ 2) =
        ‖ξ (Fin.last m)‖ ^ 2 * ‖V x‖ ^ 2 := by
      field_simp
    have hnn : 0 ≤ ‖V x‖ ^ 2 * (q x + δ ^ 2) ^ 2 / δ ^ 2 * leviForm ϕ x (∑ j, ξ j • coordVec j) :=
      mul_nonneg (by positivity) hL
    rw [mul_add, e]
    linarith
  obtain ⟨r₀, hr₀, hr₀D'⟩ := exists_coordSq_le_of_isBounded hD'b
  have hg₁int : Integrable (fun x ↦ g₁ x * Real.exp (-(chenPhi ϕ δ x + lam₁ x)))
      (volume.restrict D') := by
    have hgc : ContinuousOn g₁ D' := by
      have hVc : ContinuousOn V D' := by
        intro z hz
        have hv := hvcont (Fin.last m) z hz
        refine hv.congr (fun y hy ↦ ?_) ?_
        · rw [hvD y (hD'D hy)]; simp
        · rw [hvD z (hD'D hz)]; simp
      exact ((hVc.norm.pow 2).mul (((contDiff_coordSq _).continuous.continuousOn.add
        continuousOn_const).pow 2)).div_const _
    refine integrable_restrict_of_continuousOn_bound hD'o hD'b
      (hgc.mul ((hΦc.mono hD'D).add hl₁).neg.rexp)
      (M := Mχ ^ 2 * Mf ^ 2 / ε ^ 2 * (r₀ + δ ^ 2) ^ 2 / δ ^ 2 * (Real.exp Bϕ / δ ^ 2))
      fun z hz ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hq0 := coordSq_nonneg z
    have h1 : g₁ z ≤ Mχ ^ 2 * Mf ^ 2 / ε ^ 2 * (r₀ + δ ^ 2) ^ 2 / δ ^ 2 := by
      simp only [hg₁]
      gcongr
      · exact hVsq z (hD'D hz)
      · exact hr₀D' z hz
    exact mul_le_mul h1 (hwt z hz (lam₁ z) (hl z hz).1) (by positivity) (by positivity)
  obtain ⟨⟨u₀, hu₀mem, hu₀eq, hu₀orth⟩, -⟩ := hest (chenPhi ϕ δ) (contDiffOn_chenPhi hϕ hδ) hΦL
    v hvmem hvclosed g₁ hg₁0 hg₁levi hg₁int
  -- Weyl's lemma.
  have hwc : ContinuousOn (fun x ↦ chenPhi ϕ δ x + lam₁ x) D' := (hΦc.mono hD'D).add hl₁
  have hu₀loc : LocallyIntegrableOn u₀ D' :=
    locallyIntegrableOn_of_memLp_weightedVolume hD'o hwc hu₀mem
  have haloc : LocallyIntegrableOn a D' := haD'.continuousOn.locallyIntegrableOn hD'm
  have hFloc : LocallyIntegrableOn (fun z ↦ a z - u₀ z) D' := haloc.sub hu₀loc
  have hcoord : ∀ h, IsTestFunctionOn D' h → ∀ j,
      ∫ x, (a x - u₀ x) * dbarDir (coordVec j) h x = 0 := by
    intro h hh j
    have hdc : Continuous (dbarDir (coordVec j) h) :=
      continuous_dbarDir' (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
    have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
    have hdts := (tsupport_dbarDir_subset (coordVec j) h).trans hh.2.2
    have i1 := integrable_mul_of_locallyIntegrableOn haloc hdc hdcs hdts
    have i2 := integrable_mul_of_locallyIntegrableOn hu₀loc hdc hdcs hdts
    simp only [sub_mul]
    rw [integral_sub i1 i2, weakDbarEq_of_contDiffOn hD'o haD' h hh j, hu₀eq h hh j]
    ring
  obtain ⟨G, hG, hGae⟩ := exists_differentiableOn_ae_eq_of_weak_dbar hD'o hFloc
    (integral_mul_dbarDir_eq_zero_of_coord hFloc hcoord)
  have hae : (fun z ↦ a z - G z) =ᵐ[volume.restrict D'] u₀ := by
    filter_upwards [hGae] with x hx
    rw [← hx]; ring
  refine ⟨G, hG, ?_, ?_⟩
  · exact hu₀mem.ae_eq ((withDensity_absolutelyContinuous _ _).ae_eq hae.symm)
  · intro h hh hw
    rw [← hu₀orth h hh hw]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hx]

/-! ### Step two: the twisted estimate -/

theorem norm_chenV_sq_le {ε : ℝ} (hε : 0 < ε) {f : ComplexModel m → ℂ}
    {Mχ : ℝ} (hMχ : ∀ x, |deriv chenCutoff x| ≤ Mχ) {Mf : ℝ} {z : ComplexModel (m + 1)}
    (hMf : coordSq (Fin.last m) z ≤ ε ^ 2 → ‖f (initCoords z)‖ ≤ Mf) :
    ‖chenV ε f z‖ ^ 2 ≤ Mχ ^ 2 * Mf ^ 2 / ε ^ 2 := by
  have hMχ0 : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0)
  by_cases hV0 : chenV ε f z = 0
  · rw [hV0, norm_zero, zero_pow two_ne_zero]
    positivity
  · have hqz := coordSq_le_of_chenV_ne_zero hε hV0
    have hf' := hMf hqz
    rw [norm_chenV_sq_eq]
    have h1 : (deriv chenCutoff (coordSq (Fin.last m) z / ε ^ 2) / ε ^ 2) ^ 2 ≤ Mχ ^ 2 / ε ^ 4 := by
      have h0 : deriv chenCutoff (coordSq (Fin.last m) z / ε ^ 2) ^ 2 ≤ Mχ ^ 2 :=
        sq_le_sq' (abs_le.mp (hMχ _)).1 (abs_le.mp (hMχ _)).2
      rw [div_pow, ← pow_mul]
      exact div_le_div_of_nonneg_right h0 (by positivity)
    have h2 : ‖f (initCoords z)‖ ^ 2 ≤ Mf ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hf' 2
    have hq0 : 0 ≤ coordSq (Fin.last m) z := coordSq_nonneg z
    calc (deriv chenCutoff (coordSq (Fin.last m) z / ε ^ 2) / ε ^ 2) ^ 2 *
          coordSq (Fin.last m) z * ‖f (initCoords z)‖ ^ 2
        ≤ Mχ ^ 2 / ε ^ 4 * ε ^ 2 * Mf ^ 2 := by gcongr
      _ = Mχ ^ 2 * Mf ^ 2 / ε ^ 2 := by field_simp

theorem exp_neg_chenPhi_add_le {ϕ : ComplexModel (m + 1) → ℝ} {δ : ℝ} (hδ : 0 < δ)
    {Bϕ : ℝ} {z : ComplexModel (m + 1)} (hBϕ : -Bϕ ≤ ϕ z) {l : ℝ} (hl : 0 ≤ l) :
    Real.exp (-(chenPhi ϕ δ z + l)) ≤ Real.exp Bϕ / δ ^ 2 := by
  rw [exp_neg_chenPhi_add hδ]
  have hq0 : 0 ≤ coordSq (Fin.last m) z := coordSq_nonneg z
  have e1 : Real.exp (-ϕ z) ≤ Real.exp Bϕ := Real.exp_le_exp.mpr (by linarith)
  have e2 : Real.exp (-l) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : Real.exp (-ϕ z) * Real.exp (-l) ≤ Real.exp Bϕ := by
    nlinarith [Real.exp_pos (-ϕ z), Real.exp_pos (-l)]
  nlinarith [Real.exp_pos Bϕ]

theorem hasDerivAt_exp_chenPsi (R ε : ℝ) {s : ℝ} (hP : 0 < s + ε ^ 2) (hL : 0 < chenL R ε s)
    (hη : 0 < chenEta R ε s) :
    HasDerivAt (fun t ↦ Real.exp (chenPsi R ε t))
      (Real.exp (chenPsi R ε s) * chenPsiD R ε s) s :=
  (hasDerivAt_chenPsi R ε hP hL hη).exp

theorem leviForm_chenPsi_comp {R ε : ℝ} (hε : 0 < ε) {x : ComplexModel (m + 1)}
    (hsR : coordSq (Fin.last m) x + ε ^ 2 ≤ 2 * R ^ 2) (ξ : ComplexModel (m + 1)) :
    leviForm (fun z ↦ chenPsi R ε (coordSq (Fin.last m) z)) x ξ =
      chenLevi R ε (coordSq (Fin.last m) x) * ‖ξ (Fin.last m)‖ ^ 2 := by
  obtain ⟨hP, hL, hη⟩ := chen_good hε (coordSq_nonneg x) hsR
  rw [leviForm_comp_coordSq _ (contDiffAt_chenPsi R ε hP hL hη), deriv_chenPsi R ε hP hL hη,
    deriv_deriv_chenPsi R ε hP hL hη]
  rfl

set_option maxHeartbeats 1600000 in
/-- **Step two: the twisted estimate.**  For the minimal solution `u = chenA ε f - G` of step
one, the twist by `e^{ψ}` gives
`∫ |u|² e^{-Φ_δ-lam₁} / (24 L η) ≤ 2 ∫ 25 |v|² (|z_n|²+ε²)² ε⁻² e^{-Φ_δ-lam₁}`. -/
theorem chen_twisted_estimate {D D' : Set (ComplexModel (m + 1))}
    (hDo : IsOpen D) (hD'o : IsOpen D') (hD'D : D' ⊆ D) (hD'b : Bornology.IsBounded D')
    {R ε δ : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) (hδ : 0 < δ)
    (hDR : ∀ z ∈ D, ‖z (Fin.last m)‖ < R)
    {ϕ : ComplexModel (m + 1) → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ x ∈ D, ∀ ξ, 0 ≤ leviForm ϕ x ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    {f : ComplexModel m → ℂ} {W : Set (ComplexModel m)} (hW : IsOpen W)
    (hf : DifferentiableOn ℂ f W)
    (hDW : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → initCoords z ∈ W)
    {Mf : ℝ} (hMf : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → ‖f (initCoords z)‖ ≤ Mf)
    {Mχ : ℝ} (hMχ : ∀ x, |deriv chenCutoff x| ≤ Mχ)
    {lam₁ lam₂ : ComplexModel (m + 1) → ℝ} (hl₁ : ContinuousOn lam₁ D')
    (hl₂ : ContinuousOn lam₂ D') (hl : ∀ x ∈ D', 0 ≤ lam₁ x ∧ lam₁ x ≤ lam₂ x) {t : ℝ}
    (ht0 : 0 ≤ t) (ht : t ≤ 1 / (24 * chenL R ε 0))
    (hest : HormanderClause D D' lam₁ lam₂ t)
    {G : ComplexModel (m + 1) → ℂ} (hG : DifferentiableOn ℂ G D')
    (hmem : MemLp (fun z ↦ chenA ε f z - G z) 2
        (weightedVolume D' fun x ↦ chenPhi ϕ δ x + lam₁ x))
    (horth : ∀ h : ComplexModel (m + 1) → ℂ,
        MemLp h 2 (weightedVolume D' fun x ↦ chenPhi ϕ δ x + lam₁ x) → WeakDbarEq D' h 0 →
        ∫ x in D', conj (h x) * (chenA ε f x - G x) *
          Real.exp (-(chenPhi ϕ δ x + lam₁ x)) = 0) :
    Integrable (fun x ↦ ‖chenA ε f x - G x‖ ^ 2 * Real.exp (-(chenPhi ϕ δ x + lam₁ x)) /
        (24 * chenL R ε (coordSq (Fin.last m) x) * chenEta R ε (coordSq (Fin.last m) x)))
        (volume.restrict D') ∧
    ∫ x in D', ‖chenA ε f x - G x‖ ^ 2 * Real.exp (-(chenPhi ϕ δ x + lam₁ x)) /
        (24 * chenL R ε (coordSq (Fin.last m) x) * chenEta R ε (coordSq (Fin.last m) x)) ≤
      2 * ∫ x in D', 25 * ‖chenV ε f x‖ ^ 2 * (coordSq (Fin.last m) x + ε ^ 2) ^ 2 / ε ^ 2 *
        Real.exp (-(chenPhi ϕ δ x + lam₁ x)) := by
  set q := coordSq (Fin.last m) with hq
  set a := chenA ε f with ha
  set V := chenV ε f with hV
  set u : ComplexModel (m + 1) → ℂ := fun z ↦ a z - G z with hu
  have hD'm : MeasurableSet D' := hD'o.measurableSet
  have hsR : ∀ z ∈ D, q z + ε ^ 2 ≤ 2 * R ^ 2 := by
    intro z hz
    have h1 : q z ≤ R ^ 2 := by
      simp only [hq, coordSq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hDR z hz).le 2
    have h2 : ε ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hε.le hεR 2
    linarith
  have hgood : ∀ z ∈ D, 0 < q z + ε ^ 2 ∧ 0 < chenL R ε (q z) ∧ 0 < chenEta R ε (q z) :=
    fun z hz ↦ chen_good hε (coordSq_nonneg z) (hsR z hz)
  set ψq : ComplexModel (m + 1) → ℝ := fun z ↦ chenPsi R ε (q z) with hψq
  set E : ComplexModel (m + 1) → ℝ := fun z ↦ Real.exp (ψq z) with hE
  set Φ₂ : ComplexModel (m + 1) → ℝ := fun z ↦ chenPhi ϕ δ z + ψq z with hΦ₂
  have hψs : ContDiffOn ℝ ∞ ψq D := fun z hz ↦ by
    obtain ⟨hP, hL, hη⟩ := hgood z hz
    exact ((contDiffAt_chenPsi R ε hP hL hη).comp z
      (contDiff_coordSq (Fin.last m)).contDiffAt).contDiffWithinAt
  have hΦ₁s : ContDiffOn ℝ ∞ (chenPhi ϕ δ) D := contDiffOn_chenPhi hϕ hδ
  have hΦ₂s : ContDiffOn ℝ ∞ Φ₂ D := hΦ₁s.add hψs
  have hlevi₁ : ∀ x ∈ D, ∀ ξ, 0 ≤ leviForm (chenPhi ϕ δ) x ξ := by
    intro x hx ξ
    rw [leviForm_chenPhi hDo hϕ hδ hx]
    have := hϕL x hx ξ
    have hq0 := coordSq_nonneg x
    positivity
  have hlevi₂ : ∀ x ∈ D, ∀ ξ, leviForm Φ₂ x ξ =
      leviForm (chenPhi ϕ δ) x ξ + chenLevi R ε (q x) * ‖ξ (Fin.last m)‖ ^ 2 := by
    intro x hx ξ
    have h1 : ContDiffAt ℝ 2 (chenPhi ϕ δ) x :=
      ((hΦ₁s x hx).contDiffAt (hDo.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top)
    have h2 : ContDiffAt ℝ 2 ψq x :=
      ((hψs x hx).contDiffAt (hDo.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top)
    rw [← leviForm_chenPsi_comp hε (hsR x hx) ξ, ← leviForm_add h1 h2]
    rfl
  have hΦ₂L : ∀ x ∈ D, ∀ ξ, 0 ≤ leviForm Φ₂ x ξ := by
    intro x hx ξ
    rw [hlevi₂ x hx]
    have := hlevi₁ x hx ξ
    have := (chenLevi_pos hε (coordSq_nonneg x) (hsR x hx)).le
    positivity
  have haD : ContDiffOn ℝ ∞ a D := fun z hz ↦
    (contDiffAt_chenA hε hW hf (hDW z hz)).contDiffWithinAt
  have huD' : ContDiffOn ℝ ∞ u D' :=
    (haD.mono hD'D).sub (contDiffOn_real_of_differentiableOn_complex hG hD'o)
  set u' : ComplexModel (m + 1) → ℂ := fun z ↦ ((E z : ℝ) : ℂ) * u z with hu'
  have hEs : ContDiffOn ℝ ∞ (fun z ↦ ((E z : ℝ) : ℂ)) D :=
    ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn hψs)
  have hu'D' : ContDiffOn ℝ ∞ u' D' := (hEs.mono hD'D).mul huD'
  have hu'1 : ContDiffOn ℝ 1 u' D' := hu'D'.of_le (WithTop.coe_le_coe.mpr le_top)
  set f' : Fin (m + 1) → ComplexModel (m + 1) → ℂ := fun j ↦ dbarDir (coordVec j) u' with hf'
  have hf'D' : ∀ z ∈ D', ∀ j, f' j z = if j = Fin.last m then
      ((E z : ℝ) : ℂ) * (V z + u z * (chenPsiD R ε (q z) : ℂ) * z (Fin.last m)) else 0 := by
    intro z hz j
    obtain ⟨hP, hL, hη⟩ := hgood z (hD'D hz)
    have hEd : DifferentiableAt ℝ E z :=
      ((hasDerivAt_exp_chenPsi R ε hP hL hη).differentiableAt).comp z
        ((contDiff_coordSq (Fin.last m)).differentiable (by simp) z)
    have hGd : DifferentiableAt ℂ G z := hG.differentiableAt (hD'o.mem_nhds hz)
    have had : DifferentiableAt ℝ a z :=
      (haD.differentiableOn (by simp) z (hD'D hz)).differentiableAt
        (hDo.mem_nhds (hD'D hz))
    have hud : DifferentiableAt ℝ u z := had.sub (hGd.restrictScalars ℝ)
    change dbarDir (coordVec j) (fun y ↦ ((E y : ℝ) : ℂ) * u y) z = _
    rw [dbarDir_ofReal_mul hEd hud]
    have h1 := dbarDir_comp_coordSq (G := fun s ↦ Real.exp (chenPsi R ε s)) (x := z)
      (Fin.last m) j (hasDerivAt_exp_chenPsi R ε hP hL hη).differentiableAt
    have h2 : dbarDir (coordVec j) u z = dbarDir (coordVec j) a z := by
      rw [show u = fun y ↦ a y - G y from rfl, dbarDir_sub had (hGd.restrictScalars ℝ),
        dbarDir_eq_zero_of_differentiableAt hGd, sub_zero]
    change dbarDir (coordVec j) (fun y ↦ ((Real.exp (chenPsi R ε (q y)) : ℝ) : ℂ)) z * u z +
      _ * _ = _
    rw [h1, h2, dbarDir_chenA hε hW hf (hDW z (hD'D hz)) j,
      (hasDerivAt_exp_chenPsi R ε hP hL hη).deriv]
    split_ifs
    · simp only [hE, hψq]
      push_cast
      ring
    · simp
  -- Pointwise identities.
  have hEpos : ∀ z, 0 < E z := fun z ↦ Real.exp_pos _
  have hEle : ∀ z ∈ D, E z ≤ 1 := fun z hz ↦
    Real.exp_le_one_iff.mpr (chenPsi_nonpos hε (coordSq_nonneg z) (hsR z hz))
  have hEη : ∀ z ∈ D, E z * chenEta R ε (q z) = 1 := by
    intro z hz
    simp only [hE, hψq]
    rw [exp_chenPsi hε (coordSq_nonneg z) (hsR z hz)]
    exact inv_mul_cancel₀ (hgood z hz).2.2.ne'
  have hexpΦ₂ : ∀ z l, Real.exp (-(Φ₂ z + l)) =
      Real.exp (-(chenPhi ϕ δ z + l)) * (E z)⁻¹ := by
    intro z l
    simp only [hΦ₂, hE]
    rw [← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  have hI4 : ∀ z l, ‖u' z‖ ^ 2 * Real.exp (-(Φ₂ z + l)) =
      E z * (‖u z‖ ^ 2 * Real.exp (-(chenPhi ϕ δ z + l))) := by
    intro z l
    rw [hexpΦ₂]
    simp only [hu']
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hEpos z)]
    field_simp [(hEpos z).ne']
  set U : ComplexModel (m + 1) → ℝ := fun z ↦ ‖u z‖ ^ 2 * Real.exp (-(chenPhi ϕ δ z + lam₁ z))
    with hU
  have hΦ₁c' : ContinuousOn (chenPhi ϕ δ) D' := hΦ₁s.continuousOn.mono hD'D
  have hψc' : ContinuousOn ψq D' := hψs.continuousOn.mono hD'D
  have hΦ₂c' : ContinuousOn Φ₂ D' := hΦ₂s.continuousOn.mono hD'D
  have hEc' : ContinuousOn E D' := hψc'.rexp
  have hucont : ContinuousOn u D' := huD'.continuousOn
  have hUc : ContinuousOn U D' := (hucont.norm.pow 2).mul (hΦ₁c'.add hl₁).neg.rexp
  have hw₁m : AEMeasurable (fun x ↦ chenPhi ϕ δ x + lam₁ x) (volume.restrict D') :=
    (hΦ₁c'.add hl₁).aemeasurable hD'm
  have hUint : Integrable U (volume.restrict D') := integrable_of_memLp_weightedVolume hw₁m hmem
  have hU0 : ∀ z, 0 ≤ U z := fun z ↦ by positivity
  obtain ⟨r₀, hr₀, hr₀D'⟩ := exists_coordSq_le_of_isBounded hD'b
  have hMχ0 : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0)
  have hVsq : ∀ z ∈ D, ‖V z‖ ^ 2 ≤ Mχ ^ 2 * Mf ^ 2 / ε ^ 2 := fun z hz ↦
    norm_chenV_sq_le hε hMχ (hMf z hz)
  have hVc : ContinuousOn V D' := by
    have hv := continuousOn_dbarDir_of_contDiffOn hD'o
      ((haD.mono hD'D).of_le (WithTop.coe_le_coe.mpr le_top)) (coordVec (Fin.last m))
    refine hv.congr fun y hy ↦ ?_
    rw [dbarDir_chenA hε hW hf (hDW y (hD'D hy))]
    simp [hV]
  have hqc : Continuous q := (contDiff_coordSq (Fin.last m)).continuous
  have hLc : ContinuousOn (fun x ↦ chenL R ε (q x)) D := fun x hx ↦
    ((hasDerivAt_chenL R ε (hgood x hx).1).continuousAt.comp hqc.continuousAt).continuousWithinAt
  have hηc : ContinuousOn (fun x ↦ chenEta R ε (q x)) D := fun x hx ↦
    ((hasDerivAt_chenEta R ε (hgood x hx).1 (hgood x hx).2.1).continuousAt.comp
      hqc.continuousAt).continuousWithinAt
  have hIsFin : IsFiniteMeasure (volume.restrict D') :=
    isFiniteMeasure_restrict.mpr hD'b.measure_lt_top.ne
  -- `u'` is in `L²`.
  have hu'mem : MemLp u' 2 (weightedVolume D' fun x ↦ Φ₂ x + lam₁ x) := by
    rw [memLp_weightedVolume_iff (w := fun x ↦ Φ₂ x + lam₁ x) ((hΦ₂c'.add hl₁).aemeasurable hD'm)
      (hu'D'.continuousOn.aestronglyMeasurable hD'm)]
    refine hUint.mono' (((hu'D'.continuousOn.norm.pow 2).mul
      (hΦ₂c'.add hl₁).neg.rexp).aestronglyMeasurable hD'm) ?_
    refine (ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun z hz ↦ ?_)
    rw [hI4, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (hU0 z) (hEle z (hD'D hz))
  -- `f'` is in `L²`.
  have hψD : ∀ z ∈ D, q z * chenPsiD R ε (q z) ^ 2 ≤ 2 * R ^ 2 * (2 / ε ^ 2) ^ 2 := by
    intro z hz
    have h1 := chenPsiD_le hε (coordSq_nonneg z) (hsR z hz)
    have h0 := chenPsiD_nonneg hε (coordSq_nonneg z) (hsR z hz)
    have hq0 := coordSq_nonneg z
    have hq2 : q z ≤ 2 * R ^ 2 := by linarith [hsR z hz, sq_nonneg ε]
    exact mul_le_mul hq2 (pow_le_pow_left₀ h0 h1 2) (by positivity) (by positivity)
  have hnormb : ∀ z, ‖u z * (chenPsiD R ε (q z) : ℂ) * z (Fin.last m)‖ ^ 2 =
      ‖u z‖ ^ 2 * (q z * chenPsiD R ε (q z) ^ 2) := by
    intro z
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs]
    simp only [hq, coordSq]
    ring
  have hf'mem : ∀ j, MemLp (f' j) 2 (weightedVolume D' fun x ↦ Φ₂ x + lam₂ x) := by
    intro j
    have hf'c : ContinuousOn (f' j) D' := continuousOn_dbarDir_of_contDiffOn hD'o hu'1 _
    rw [memLp_weightedVolume_iff (w := fun x ↦ Φ₂ x + lam₂ x) ((hΦ₂c'.add hl₂).aemeasurable hD'm)
      (hf'c.aestronglyMeasurable hD'm)]
    set K₁ := 2 * (Mχ ^ 2 * Mf ^ 2 / ε ^ 2) * (Real.exp Bϕ / δ ^ 2) with hK₁
    set K₂ := 2 * (2 * R ^ 2 * (2 / ε ^ 2) ^ 2) with hK₂
    refine ((integrable_const K₁).add (hUint.const_mul K₂)).mono'
      (((hf'c.norm.pow 2).mul (hΦ₂c'.add hl₂).neg.rexp).aestronglyMeasurable hD'm) ?_
    refine (ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun z hz ↦ ?_)
    have hK₁0 : 0 ≤ K₁ := by positivity
    have hK₂0 : 0 ≤ K₂ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hf'D' z hz j]
    split_ifs
    · rw [hexpΦ₂, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hEpos z)]
      set N := ‖V z + u z * (chenPsiD R ε (q z) : ℂ) * z (Fin.last m)‖ with hN
      set X₂ := Real.exp (-(chenPhi ϕ δ z + lam₂ z)) with hX₂
      have hb : N ^ 2 ≤ 2 * ‖V z‖ ^ 2 + 2 * (‖u z‖ ^ 2 * (q z * chenPsiD R ε (q z) ^ 2)) := by
        rw [← hnormb]
        have := norm_add_le (V z) (u z * (chenPsiD R ε (q z) : ℂ) * z (Fin.last m))
        have h0 := norm_nonneg (V z + u z * (chenPsiD R ε (q z) : ℂ) * z (Fin.last m))
        nlinarith [sq_nonneg (‖V z‖ - ‖u z * (chenPsiD R ε (q z) : ℂ) * z (Fin.last m)‖),
          norm_nonneg (V z), norm_nonneg (u z * (chenPsiD R ε (q z) : ℂ) * z (Fin.last m))]
      have hexp1 : X₂ ≤ Real.exp Bϕ / δ ^ 2 :=
        exp_neg_chenPhi_add_le hδ (hBϕ z (hD'D hz)) ((hl z hz).1.trans (hl z hz).2)
      have hexp2 : X₂ ≤ Real.exp (-(chenPhi ϕ δ z + lam₁ z)) :=
        Real.exp_le_exp.mpr (by linarith [(hl z hz).2])
      have hX₂0 : 0 ≤ X₂ := (Real.exp_pos _).le
      have hq0 := coordSq_nonneg z
      calc (E z * N) ^ 2 * (X₂ * (E z)⁻¹) = E z * (N ^ 2 * X₂) := by
            field_simp [(hEpos z).ne']
        _ ≤ N ^ 2 * X₂ := mul_le_of_le_one_left (by positivity) (hEle z (hD'D hz))
        _ ≤ (2 * ‖V z‖ ^ 2 + 2 * (‖u z‖ ^ 2 * (q z * chenPsiD R ε (q z) ^ 2))) * X₂ :=
            mul_le_mul_of_nonneg_right hb hX₂0
        _ = 2 * ‖V z‖ ^ 2 * X₂ + 2 * (q z * chenPsiD R ε (q z) ^ 2) * (‖u z‖ ^ 2 * X₂) := by
            ring
        _ ≤ K₁ + K₂ * U z := by
            have t1 : 2 * ‖V z‖ ^ 2 * X₂ ≤ K₁ :=
              mul_le_mul (by linarith [hVsq z (hD'D hz)]) hexp1 hX₂0 (by positivity)
            have t2 : 2 * (q z * chenPsiD R ε (q z) ^ 2) * (‖u z‖ ^ 2 * X₂) ≤ K₂ * U z :=
              mul_le_mul (by linarith [hψD z (hD'D hz)])
                (mul_le_mul_of_nonneg_left hexp2 (by positivity)) (by positivity) hK₂0
            linarith
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact add_nonneg hK₁0 (mul_nonneg hK₂0 (hU0 z))
  have hf'closed : WeakDbarClosed D' f' := weakDbarClosed_of_contDiffOn hD'o hu'1
  have hu'eq : WeakDbarEq D' u' f' := weakDbarEq_of_contDiffOn hD'o hu'1
  -- The Levi bound.
  set c : ComplexModel (m + 1) → ℝ := fun x ↦ 1 - 1 / (12 * chenL R ε (q x)) with hc
  have hc01 : ∀ x ∈ D, 0 ≤ c x ∧ c x ≤ 1 := by
    intro x hx
    have hL := one_le_chenL hε (coordSq_nonneg x) (hsR x hx)
    have h1 : 0 < 1 / (12 * chenL R ε (q x)) := by positivity
    have h2 : 1 / (12 * chenL R ε (q x)) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    exact ⟨by simp only [hc]; linarith, by simp only [hc]; linarith⟩
  set g' : ComplexModel (m + 1) → ℝ := fun z ↦ E z ^ 2 *
      (25 * ‖V z‖ ^ 2 * (q z + ε ^ 2) ^ 2 * chenEta R ε (q z) / ε ^ 2 + c z * ‖u z‖ ^ 2)
    with hg'
  have hg'0 : ∀ x ∈ D', 0 ≤ g' x := by
    intro x hx
    have := (hgood x (hD'D hx)).2.2
    have := (hc01 x (hD'D hx)).1
    positivity
  have hg'levi : ∀ x ∈ D', ∀ ξ : Fin (m + 1) → ℂ, ‖∑ j, conj (ξ j) * f' j x‖ ^ 2 ≤
      g' x * leviForm Φ₂ x (∑ j, ξ j • coordVec j) := by
    intro x hx ξ
    have hsum : ∑ j, conj (ξ j) * f' j x = ∑ j, conj (ξ j) * (if j = Fin.last m then
        ((E x : ℝ) : ℂ) * (V x + u x * (chenPsiD R ε (q x) : ℂ) * x (Fin.last m)) else 0) :=
      Finset.sum_congr rfl fun j _ ↦ by rw [hf'D' x hx j]
    rw [hsum, sum_conj_mul_ite, hlevi₂ x (hD'D hx), sum_smul_coordVec_apply]
    obtain ⟨hP, hL, hη⟩ := hgood x (hD'D hx)
    have hx0 := coordSq_nonneg x
    have hkey := chen_norm_sq_le (s := q x) (e := ε ^ 2) (L := chenL R ε (q x))
      (η := chenEta R ε (q x)) (V := V x) (U := u x) (Z := x (Fin.last m))
      (ψ' := chenPsiD R ε (q x)) (a := chenLevi R ε (q x)) (P := q x + ε ^ 2) rfl
      (one_le_chenL hε hx0 (hsR x (hD'D hx))) hP hη (by positivity)
      (sq_chenPsiD_le hε hx0 (hsR x (hD'D hx)))
      (fun hV0 ↦ sq_chenPsiD_le_of_le hε hx0 (hsR x (hD'D hx))
        (coordSq_le_of_chenV_ne_zero hε hV0))
      (le_chenLevi hε hx0 (hsR x (hD'D hx)))
    have hL1 := hlevi₁ x (hD'D hx) (∑ j, ξ j • coordVec j)
    have hg'x0 := hg'0 x hx
    rw [norm_mul, Complex.norm_conj, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hEpos x)]
    have ha0 := (chenLevi_pos hε hx0 (hsR x (hD'D hx))).le
    calc (‖ξ (Fin.last m)‖ * (E x *
          ‖V x + u x * (chenPsiD R ε (q x) : ℂ) * x (Fin.last m)‖)) ^ 2
        = ‖ξ (Fin.last m)‖ ^ 2 * E x ^ 2 *
          ‖V x + u x * (chenPsiD R ε (q x) : ℂ) * x (Fin.last m)‖ ^ 2 := by ring
      _ ≤ ‖ξ (Fin.last m)‖ ^ 2 * E x ^ 2 *
          ((25 * ‖V x‖ ^ 2 * (q x + ε ^ 2) ^ 2 * chenEta R ε (q x) / ε ^ 2 +
            (1 - 1 / (12 * chenL R ε (q x))) * ‖u x‖ ^ 2) * chenLevi R ε (q x)) := by
          gcongr
      _ = g' x * (chenLevi R ε (q x) * ‖ξ (Fin.last m)‖ ^ 2) := by
          simp only [hg', hc]; ring
      _ ≤ g' x * (leviForm (chenPhi ϕ δ) x (∑ j, ξ j • coordVec j) +
          chenLevi R ε (q x) * ‖ξ (Fin.last m)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hg'x0
  -- The right-hand side.
  set A : ComplexModel (m + 1) → ℝ := fun x ↦ 25 * ‖V x‖ ^ 2 * (q x + ε ^ 2) ^ 2 / ε ^ 2 *
      Real.exp (-(chenPhi ϕ δ x + lam₁ x)) with hA
  have hA0 : ∀ x, 0 ≤ A x := fun x ↦ by positivity
  have hI5 : ∀ x ∈ D', g' x * Real.exp (-(Φ₂ x + lam₁ x)) = A x + c x * (E x * U x) := by
    intro x hx
    rw [hexpΦ₂]
    have h1 := hEη x (hD'D hx)
    have hE0 := (hEpos x).ne'
    calc g' x * (Real.exp (-(chenPhi ϕ δ x + lam₁ x)) * (E x)⁻¹)
        = E x * (25 * ‖V x‖ ^ 2 * (q x + ε ^ 2) ^ 2 * chenEta R ε (q x) / ε ^ 2 +
            c x * ‖u x‖ ^ 2) * Real.exp (-(chenPhi ϕ δ x + lam₁ x)) := by
          simp only [hg']; field_simp
      _ = 25 * ‖V x‖ ^ 2 * (q x + ε ^ 2) ^ 2 / ε ^ 2 * (E x * chenEta R ε (q x)) *
            Real.exp (-(chenPhi ϕ δ x + lam₁ x)) + c x * (E x * U x) := by
          simp only [hU]; ring
      _ = A x + c x * (E x * U x) := by rw [h1]; simp only [hA]; ring
  have hAc : ContinuousOn A D' :=
    ((((hVc.norm.pow 2).const_smul (25 : ℝ)).mul
      ((hqc.continuousOn.add continuousOn_const).pow 2)).div_const _).mul
      (hΦ₁c'.add hl₁).neg.rexp
  have hAint : Integrable A (volume.restrict D') := by
    refine integrable_restrict_of_continuousOn_bound hD'o hD'b hAc
      (M := 25 * (Mχ ^ 2 * Mf ^ 2 / ε ^ 2) * (r₀ + ε ^ 2) ^ 2 / ε ^ 2 * (Real.exp Bϕ / δ ^ 2))
      fun z hz ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hA0 z)]
    have hq0 := coordSq_nonneg z
    have h1 : 25 * ‖V z‖ ^ 2 * (q z + ε ^ 2) ^ 2 / ε ^ 2 ≤
        25 * (Mχ ^ 2 * Mf ^ 2 / ε ^ 2) * (r₀ + ε ^ 2) ^ 2 / ε ^ 2 := by
      gcongr
      · exact hVsq z (hD'D hz)
      · exact hr₀D' z hz
    exact mul_le_mul h1 (exp_neg_chenPhi_add_le hδ (hBϕ z (hD'D hz)) (hl z hz).1)
      (Real.exp_pos _).le (by positivity)
  have hEUint : Integrable (fun x ↦ E x * U x) (volume.restrict D') :=
    hUint.mono' ((hEc'.mul hUc).aestronglyMeasurable hD'm)
      ((ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun z hz ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hEpos z).le (hU0 z))]
        exact mul_le_of_le_one_left (hU0 z) (hEle z (hD'D hz))))
  have hcc : ContinuousOn c D' := by
    refine (continuousOn_const.sub (continuousOn_const.div (continuousOn_const.mul
      (hLc.mono hD'D)) fun x hx ↦ ?_))
    have := (hgood x (hD'D hx)).2.1
    positivity
  have hcEUint : Integrable (fun x ↦ c x * (E x * U x)) (volume.restrict D') :=
    hEUint.mono' ((hcc.mul (hEc'.mul hUc)).aestronglyMeasurable hD'm)
      ((ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun z hz ↦ by
        have h01 := hc01 z (hD'D hz)
        have hEU0 := mul_nonneg (hEpos z).le (hU0 z)
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h01.1 hEU0)]
        exact mul_le_of_le_one_left hEU0 h01.2))
  have hg'int : Integrable (fun x ↦ g' x * Real.exp (-(Φ₂ x + lam₁ x)))
      (volume.restrict D') :=
    (hAint.add hcEUint).congr ((ae_restrict_iff' hD'm).mpr
      (Eventually.of_forall fun x hx ↦ (hI5 x hx).symm))
  -- Orthogonality of the twisted solution.
  have hmono : weightedVolume D' (fun x ↦ chenPhi ϕ δ x + lam₁ x) ≤
      weightedVolume D' (fun x ↦ Φ₂ x + lam₁ x) := by
    refine withDensity_mono ((ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun x hx ↦ ?_))
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have := chenPsi_nonpos hε (coordSq_nonneg x) (hsR x (hD'D hx))
    simp only [hΦ₂, hψq]
    linarith
  have hu'orth : ∀ h : ComplexModel (m + 1) → ℂ,
      MemLp h 2 (weightedVolume D' fun x ↦ Φ₂ x + lam₁ x) → WeakDbarEq D' h 0 →
      ∫ x in D', conj (h x) * u' x * Real.exp (-(Φ₂ x + lam₁ x)) = 0 := by
    intro h hh hw
    rw [← horth h (hh.mono_measure hmono) hw]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [hu', hexpΦ₂]
    have hE0 : ((E x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hEpos x).ne'
    push_cast
    field_simp
    rfl
  -- The main estimate.
  have hmain := (hest Φ₂ hΦ₂s hΦ₂L f' hf'mem hf'closed g' hg'0 hg'levi hg'int).2 u' hu'mem
    hu'eq hu'orth
  rw [setIntegral_congr_fun hD'm (fun x _ ↦ hI4 x (lam₁ x)), setIntegral_congr_fun hD'm hI5,
    integral_add hAint hcEUint] at hmain
  have hLηint : Integrable (fun x ↦ U x / (24 * chenL R ε (q x) * chenEta R ε (q x)))
      (volume.restrict D') := by
    refine hUint.mono' ((hUc.div ((continuousOn_const.mul (hLc.mono hD'D)).mul (hηc.mono hD'D))
      fun x hx ↦ ?_).aestronglyMeasurable hD'm) ?_
    · exact (mul_pos (mul_pos (by norm_num) (hgood x (hD'D hx)).2.1)
        (hgood x (hD'D hx)).2.2).ne'
    · refine (ae_restrict_iff' hD'm).mpr (Eventually.of_forall fun z hz ↦ ?_)
      have hL1 := one_le_chenL hε (coordSq_nonneg z) (hsR z (hD'D hz))
      have hη1 := chenL_le_chenEta hε (coordSq_nonneg z) (hsR z (hD'D hz))
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hU0 z)
        (mul_pos (mul_pos (by norm_num) (by linarith)) (by linarith)).le)]
      exact div_le_self (hU0 z) (by nlinarith)
  have hlow : ∫ x in D', U x / (24 * chenL R ε (q x) * chenEta R ε (q x)) ≤
      ∫ x in D', (E x * U x - (1 + t) * (c x * (E x * U x))) := by
    refine setIntegral_mono_on hLηint (hEUint.sub (hcEUint.const_mul _)) hD'm fun x hx ↦ ?_
    have hEη' := hEη x (hD'D hx)
    have hx0 := coordSq_nonneg x
    have hLq := one_le_chenL hε hx0 (hsR x (hD'D hx))
    have hLle := chenL_le_chenL_zero (R := R) hε hx0
    have ht' : t ≤ 1 / (24 * chenL R ε (q x)) :=
      ht.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
    have hcoef := chen_coeff_ge hLq ht0 ht'
    have hEU0 := mul_nonneg (hEpos x).le (hU0 x)
    have hEeq : E x = (chenEta R ε (q x))⁻¹ := eq_inv_of_mul_eq_one_left hEη'
    have e1 : U x / (24 * chenL R ε (q x) * chenEta R ε (q x)) =
        1 / (24 * chenL R ε (q x)) * (E x * U x) := by
      rw [hEeq]; field_simp
    rw [e1]
    have := mul_le_mul_of_nonneg_right hcoef hEU0
    simp only [hc]
    nlinarith
  rw [integral_sub hEUint (hcEUint.const_mul _), integral_const_mul] at hlow
  have hA0' : 0 ≤ ∫ x in D', A x := setIntegral_nonneg hD'm fun x _ ↦ hA0 x
  have hL0 : 1 ≤ chenL R ε 0 := one_le_chenL hε le_rfl (by
    have := pow_le_pow_left₀ hε.le hεR 2; nlinarith)
  have ht1 : t ≤ 1 := ht.trans (by rw [div_le_one (by positivity)]; linarith)
  exact ⟨hLηint, by nlinarith [mul_le_mul_of_nonneg_right ht1 hA0']⟩

end

end Hironaka.OTChen
