import Hironaka.Analytic.BergmanSupWeight
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false

/-!
# The Bergman kernel on the diagonal is `C^∞`

Let `B ⊆ ℂᵈ` be open and `w : ℂᵈ → [0, ∞]` a weight which is a.e.-measurable on `B` and
locally bounded below by positive constants on `B` (in the application `w = e^{-mΨ}` with `Ψ`
plurisubharmonic, hence locally bounded above).  The Bergman kernel on the diagonal

  `K(z) = bergmanSup B w z = sup {|f(z)|² | f holomorphic on B, ∫_B |f|² w ≤ 1}`

is finite and `C^∞` on `B` (`contDiffOn_toReal_bergmanSup`).  This is step B3 of programme
`TN.3.3.DEMPROVE` (Demailly, *Analytic methods in algebraic geometry*, proof of Theorem 13.21:
the Bergman kernel `∑ |σ_ℓ|²` is real analytic).

## The argument

* `bergmanSubspace B w`: the holomorphic classes in `L²(B, w · vol)`.  It is closed
  (`isClosed_bergmanSubspace`): by the sub-mean-value inequality an `L²`-Cauchy sequence of
  holomorphic functions is locally uniformly Cauchy (`norm_rep_le`), its locally uniform limit is
  holomorphic (Weierstrass, `Hironaka.differentiableAt_of_tendstoUniformlyOn_ball`), and an
  a.e.-convergent subsequence identifies the limit class.  So it is a Hilbert space.
* `evalCLM z`: evaluation at `z` of the holomorphic representative, a continuous linear form;
  `‖evalCLM z‖² = K(z)` (`bergmanSup_eq_ofReal_norm_evalCLM_sq`, from the extremal property).
* `hasFDerivAt_evalCLM`: `z ↦ evalCLM z` is complex differentiable into the dual, with
  derivative `u ↦ (F ↦ D f_F(z) u)`, by the Cauchy and second-order Taylor estimates
  (`Hironaka.norm_fderiv_le_of_forall_norm_le`, `Hironaka.norm_sub_sub_fderiv_le`), uniform
  over the unit ball.  Hence it is `C^∞` (`Hironaka.contDiffOn_real_of_differentiableOn_complex`).
* The dual norm squared is `C^∞`: by Riesz (`InnerProductSpace.toDual`) the dual is isometric,
  hence (Mazur--Ulam) real-linearly isometric, to the Hilbert space itself.
-/

open Set Filter MeasureTheory Metric
open scoped ENNReal Topology ContDiff

namespace Hironaka.BergmanKernelSmooth

noncomputable section

open Hironaka BergmanSupWeight

variable {d : ℕ}

/-! ### The weight hypotheses -/

/-- The hypotheses on the domain and the weight: `B` open, `w` a.e.-measurable on `B`, and `w`
bounded below by a positive constant on a closed ball around every point of `B`. -/
structure BergmanWeight (B : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞) : Prop where
  isOpen : IsOpen B
  aemeasurable : AEMeasurable w (volume.restrict B)
  exists_lower : ∀ z ∈ B, ∃ δ : ℝ, 0 < δ ∧ ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ B ∧
    ∀ x ∈ closedBall z s, ENNReal.ofReal δ ≤ w x

variable {B : Set (ComplexModel d)} {w : ComplexModel d → ℝ≥0∞}

theorem BergmanWeight.ne_zero (hBw : BergmanWeight B w) {x : ComplexModel d} (hx : x ∈ B) :
    w x ≠ 0 := by
  obtain ⟨δ, hδ, s, hs, -, hlow⟩ := hBw.exists_lower x hx
  exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hδ) (hlow x (mem_closedBall_self hs.le))).ne'

/-! ### The sub-mean-value bound -/

/-- **Pointwise bound by the weighted `L²` norm.**  If `w ≥ δ` on `closedBall y s ⊆ B`, then on
`ball y (s/2)` a holomorphic `f` satisfies `δ · vol(ball 0 (s/2)) · |f(z)|² ≤ ∫_B |f|² w`. -/
theorem ofReal_mul_normSq_le (hB : IsOpen B) {f : ComplexModel d → ℂ}
    (hf : DifferentiableOn ℂ f B) {y : ComplexModel d} {δ s : ℝ} (hs : 0 < s)
    (hsub : closedBall y s ⊆ B) (hlow : ∀ x ∈ closedBall y s, ENNReal.ofReal δ ≤ w x)
    {z : ComplexModel d} (hz : z ∈ ball y (s / 2)) :
    ENNReal.ofReal δ * volume (ball (0 : ComplexModel d) (s / 2)) *
        ENNReal.ofReal (‖f z‖ ^ 2) ≤ ∫⁻ x in B, ENNReal.ofReal (‖f x‖ ^ 2) * w x := by
  have hzs : closedBall z (s / 2) ⊆ closedBall y s := by
    intro u hu
    rw [mem_closedBall] at hu ⊢
    rw [mem_ball] at hz
    linarith [dist_triangle u z y]
  have hmv := lintegral_ball_normSq_ge hB hf (by positivity : 0 < s / 2) (hzs.trans hsub)
  rw [Measure.addHaar_ball_center] at hmv
  calc ENNReal.ofReal δ * volume (ball (0 : ComplexModel d) (s / 2)) * ENNReal.ofReal (‖f z‖ ^ 2)
      = ENNReal.ofReal δ * (volume (ball (0 : ComplexModel d) (s / 2)) *
          ENNReal.ofReal (‖f z‖ ^ 2)) := by rw [mul_assoc]
    _ ≤ ENNReal.ofReal δ * ∫⁻ x in ball z (s / 2), ENNReal.ofReal (‖f x‖ ^ 2) := by gcongr
    _ = ∫⁻ x in ball z (s / 2), ENNReal.ofReal δ * ENNReal.ofReal (‖f x‖ ^ 2) :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ ∫⁻ x in ball z (s / 2), ENNReal.ofReal (‖f x‖ ^ 2) * w x := by
        refine setLIntegral_mono' measurableSet_ball fun x hx => ?_
        rw [mul_comm]
        gcongr
        exact hlow x (hzs (ball_subset_closedBall hx))
    _ ≤ ∫⁻ x in B, ENNReal.ofReal (‖f x‖ ^ 2) * w x :=
        lintegral_mono_set ((ball_subset_closedBall.trans hzs).trans hsub)

/-! ### The weighted `L²` space -/

/-- The measure `w · vol` on `B`. -/
def bergmanMeasure (B : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞) :
    Measure (ComplexModel d) :=
  (volume.restrict B).withDensity w

/-- The squared `L²` norm, as a lower integral. -/
theorem ofReal_norm_sq_eq_lintegral {μ : Measure (ComplexModel d)} (F : Lp ℂ 2 μ) :
    ENNReal.ofReal (‖F‖ ^ 2) = ∫⁻ x, ‖(F : ComplexModel d → ℂ) x‖ₑ ^ 2 ∂μ := by
  have hlt := Lp.eLpNorm_lt_top F
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at hlt
  rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hlt ⊢
  set I : ℝ≥0∞ := ∫⁻ x, ‖(F : ComplexModel d → ℂ) x‖ₑ ^ 2 ∂μ with hI
  have hItop : I ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_rpow_of_pos (by norm_num)] at hlt
    exact lt_irrefl _ hlt
  rw [← ENNReal.toReal_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  exact hItop

/-- `∫ |g|² d(w · vol) = ∫_B |f|² w` when `g = f` a.e. -/
theorem lintegral_enorm_sq_eq (hw : AEMeasurable w (volume.restrict B))
    {g f : ComplexModel d → ℂ} (hg : AEStronglyMeasurable g (bergmanMeasure B w))
    (hgf : g =ᵐ[bergmanMeasure B w] f) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂bergmanMeasure B w = ∫⁻ x in B, ENNReal.ofReal (‖f x‖ ^ 2) * w x := by
  have hmeas : AEMeasurable (fun x => ‖g x‖ₑ ^ 2) (bergmanMeasure B w) :=
    hg.enorm.pow_const 2
  erw [lintegral_withDensity_eq_lintegral_mul₀' hw hmeas]
  refine lintegral_congr_ae ?_
  have h := (ae_withDensity_iff' hw).mp hgf
  filter_upwards [h] with x hx
  simp only [Pi.mul_apply]
  by_cases hw0 : w x = 0
  · rw [hw0, zero_mul, mul_zero]
  · rw [hx hw0, mul_comm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- `‖F‖² = ∫_B |f|² w` for a representative `f`. -/
theorem ofReal_norm_sq_eq (hw : AEMeasurable w (volume.restrict B))
    {F : Lp ℂ 2 (bergmanMeasure B w)} {f : ComplexModel d → ℂ}
    (hFf : (F : ComplexModel d → ℂ) =ᵐ[bergmanMeasure B w] f) :
    ENNReal.ofReal (‖F‖ ^ 2) = ∫⁻ x in B, ENNReal.ofReal (‖f x‖ ^ 2) * w x := by
  rw [ofReal_norm_sq_eq_lintegral, lintegral_enorm_sq_eq hw (Lp.aestronglyMeasurable F) hFf]

/-- Two functions holomorphic on `B` which agree `w · vol`-a.e. agree on `B`. -/
theorem eqOn_of_ae_eq (hBw : BergmanWeight B w) {f g : ComplexModel d → ℂ}
    (hf : DifferentiableOn ℂ f B) (hg : DifferentiableOn ℂ g B)
    (hfg : f =ᵐ[bergmanMeasure B w] g) : EqOn f g B := by
  have h := (ae_withDensity_iff' hBw.aemeasurable).mp hfg
  have h' : f =ᵐ[volume.restrict B] g := by
    filter_upwards [h, ae_restrict_mem hBw.isOpen.measurableSet] with x hx hxB
    exact hx (hBw.ne_zero hxB)
  exact Measure.eqOn_open_of_ae_eq h' hBw.isOpen hf.continuousOn hg.continuousOn

/-! ### The Bergman space -/

/-- **The weighted Bergman space**: the classes in `L²(B, w · vol)` with a representative
holomorphic on `B`. -/
def bergmanSubspace (B : Set (ComplexModel d)) (w : ComplexModel d → ℝ≥0∞) :
    Submodule ℂ (Lp ℂ 2 (bergmanMeasure B w)) where
  carrier := {F | ∃ f : ComplexModel d → ℂ, DifferentiableOn ℂ f B ∧
    (F : ComplexModel d → ℂ) =ᵐ[bergmanMeasure B w] f}
  add_mem' := by
    rintro F G ⟨f, hf, hFf⟩ ⟨g, hg, hGg⟩
    exact ⟨f + g, hf.add hg, (Lp.coeFn_add F G).trans (hFf.add hGg)⟩
  zero_mem' := ⟨0, differentiableOn_const 0, Lp.coeFn_zero _ _ _⟩
  smul_mem' := by
    rintro c F ⟨f, hf, hFf⟩
    refine ⟨c • f, hf.const_smul c, (Lp.coeFn_smul c F).trans ?_⟩
    filter_upwards [hFf] with x hx
    simp only [Pi.smul_apply, hx]

/-- The holomorphic representative of a class, normalized to vanish off `B`. -/
def rep (F : bergmanSubspace B w) : ComplexModel d → ℂ :=
  B.indicator (Classical.choose F.2)

theorem differentiableOn_rep (F : bergmanSubspace B w) : DifferentiableOn ℂ (rep F) B := by
  have h := (Classical.choose_spec F.2).1
  refine h.congr fun x hx => ?_
  simp only [rep, indicator_of_mem hx]

theorem ae_eq_rep (hBw : BergmanWeight B w) (F : bergmanSubspace B w) :
    ((F : Lp ℂ 2 (bergmanMeasure B w)) : ComplexModel d → ℂ) =ᵐ[bergmanMeasure B w] rep F := by
  refine (Classical.choose_spec F.2).2.trans ?_
  have hB : ∀ᵐ x ∂bergmanMeasure B w, x ∈ B :=
    (withDensity_absolutelyContinuous _ w).ae_le (ae_restrict_mem hBw.isOpen.measurableSet)
  filter_upwards [hB] with x hx
  simp only [rep, indicator_of_mem hx]

theorem rep_of_not_mem (F : bergmanSubspace B w) {x : ComplexModel d} (hx : x ∉ B) :
    rep F x = 0 := by
  simp only [rep, indicator_of_notMem hx]

/-- The representative is the given holomorphic function on `B`. -/
theorem rep_eqOn (hBw : BergmanWeight B w) (F : bergmanSubspace B w) {f : ComplexModel d → ℂ}
    (hf : DifferentiableOn ℂ f B)
    (hFf : ((F : Lp ℂ 2 (bergmanMeasure B w)) : ComplexModel d → ℂ) =ᵐ[bergmanMeasure B w] f) :
    EqOn (rep F) f B :=
  eqOn_of_ae_eq hBw (differentiableOn_rep F) hf ((ae_eq_rep hBw F).symm.trans hFf)

/-- Two functions vanishing off `B` and agreeing on `B` are equal. -/
theorem eq_of_eqOn_of_not_mem {f g : ComplexModel d → ℂ} (h : EqOn f g B)
    (hf : ∀ x ∉ B, f x = 0) (hg : ∀ x ∉ B, g x = 0) : f = g := by
  funext x
  by_cases hx : x ∈ B
  · exact h hx
  · rw [hf x hx, hg x hx]

theorem rep_add (hBw : BergmanWeight B w) (F G : bergmanSubspace B w) :
    rep (F + G) = rep F + rep G := by
  refine eq_of_eqOn_of_not_mem (rep_eqOn hBw (F + G)
    ((differentiableOn_rep F).add (differentiableOn_rep G)) ?_) (fun x hx => rep_of_not_mem _ hx)
    (fun x hx => by simp [rep_of_not_mem _ hx])
  exact (Lp.coeFn_add (F : Lp ℂ 2 (bergmanMeasure B w)) G).trans
    ((ae_eq_rep hBw F).add (ae_eq_rep hBw G))

theorem rep_smul (hBw : BergmanWeight B w) (c : ℂ) (F : bergmanSubspace B w) :
    rep (c • F) = c • rep F := by
  refine eq_of_eqOn_of_not_mem (rep_eqOn hBw (c • F) ((differentiableOn_rep F).const_smul c) ?_)
    (fun x hx => rep_of_not_mem _ hx) (fun x hx => by simp [rep_of_not_mem _ hx])
  refine (Lp.coeFn_smul c (F : Lp ℂ 2 (bergmanMeasure B w))).trans ?_
  filter_upwards [ae_eq_rep hBw F] with x hx
  simp only [Pi.smul_apply, hx]

theorem rep_sub (hBw : BergmanWeight B w) (F G : bergmanSubspace B w) :
    rep (F - G) = rep F - rep G := by
  refine eq_of_eqOn_of_not_mem (rep_eqOn hBw (F - G)
    ((differentiableOn_rep F).sub (differentiableOn_rep G)) ?_) (fun x hx => rep_of_not_mem _ hx)
    (fun x hx => by simp [rep_of_not_mem _ hx])
  exact (Lp.coeFn_sub (F : Lp ℂ 2 (bergmanMeasure B w)) G).trans
    ((ae_eq_rep hBw F).sub (ae_eq_rep hBw G))

/-! ### Local uniform bounds and closedness -/

/-- **Local uniform bound**: near every point of `B` the representatives are bounded by one
constant times the norm. -/
theorem exists_norm_rep_le (hBw : BergmanWeight B w) {z₀ : ComplexModel d} (hz₀ : z₀ ∈ B) :
    ∃ r : ℝ, 0 < r ∧ ball z₀ r ⊆ B ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (F : bergmanSubspace B w), ∀ z ∈ ball z₀ r, ‖rep F z‖ ≤ C * ‖F‖ := by
  obtain ⟨δ, hδ, s, hs, hsub, hlow⟩ := hBw.exists_lower z₀ hz₀
  set V : ℝ≥0∞ := volume (ball (0 : ComplexModel d) (s / 2)) with hVdef
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ (by positivity)).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  set c : ℝ := δ * V.toReal with hcdef
  have hc : 0 < c := mul_pos hδ (ENNReal.toReal_pos hV0 hVtop)
  refine ⟨s / 2, by positivity, ball_subset_closedBall.trans
    ((closedBall_subset_closedBall (by linarith)).trans hsub), Real.sqrt c⁻¹,
    Real.sqrt_nonneg _, fun F z hz => ?_⟩
  have h1 := ofReal_mul_normSq_le hBw.isOpen (differentiableOn_rep F) hs hsub hlow hz
  rw [← ofReal_norm_sq_eq hBw.aemeasurable (ae_eq_rep hBw F)] at h1
  have h2 : c * ‖rep F z‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [← hVdef, ← ENNReal.ofReal_toReal hVtop, ← ENNReal.ofReal_mul hδ.le,
      ← ENNReal.ofReal_mul (by positivity)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  rw [← Real.sqrt_sq (norm_nonneg (rep F z)), ← Real.sqrt_sq (norm_nonneg F),
    ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  rw [inv_mul_eq_div, le_div_iff₀ hc]
  linarith

/-- **The Bergman space is closed in `L²`**, hence a Hilbert space. -/
theorem isClosed_bergmanSubspace (hBw : BergmanWeight B w) :
    IsClosed (bergmanSubspace B w : Set (Lp ℂ 2 (bergmanMeasure B w))) := by
  refine isClosed_of_closure_subset fun F hF => ?_
  obtain ⟨G, hGS, hGF⟩ := mem_closure_iff_seq_limit.mp hF
  let G' : ℕ → bergmanSubspace B w := fun n => ⟨G n, hGS n⟩
  set g : ℕ → ComplexModel d → ℂ := fun n => rep (G' n) with hgdef
  have hcauchy : CauchySeq G := hGF.cauchySeq
  have hloc : ∀ z₀ ∈ B, ∃ r : ℝ, 0 < r ∧ ball z₀ r ⊆ B ∧
      UniformCauchySeqOn g atTop (ball z₀ r) := by
    intro z₀ hz₀
    obtain ⟨r, hr, hrB, C, hC, hbd⟩ := exists_norm_rep_le hBw hz₀
    refine ⟨r, hr, hrB, ?_⟩
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hcauchy (ε / (C + 1)) (by positivity)
    refine ⟨N, fun m hm n hn z hz => ?_⟩
    have hmn := hN m hm n hn
    have hb := hbd (G' m - G' n) z hz
    rw [rep_sub hBw] at hb
    rw [dist_eq_norm]
    have hnorm : ‖G' m - G' n‖ = dist (G m) (G n) := by
      rw [dist_eq_norm]
      rfl
    calc ‖g m z - g n z‖ = ‖(rep (G' m) - rep (G' n)) z‖ := rfl
      _ ≤ C * ‖G' m - G' n‖ := hb
      _ ≤ C * (ε / (C + 1)) := by rw [hnorm]; gcongr
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  -- the pointwise limit
  set f : ComplexModel d → ℂ := fun z => limUnder atTop fun n => g n z with hfdef
  have hlim : ∀ z ∈ B, Tendsto (fun n => g n z) atTop (𝓝 (f z)) := by
    intro z hz
    obtain ⟨r, hr, -, hU⟩ := hloc z hz
    exact (hU.cauchySeq (mem_ball_self hr)).tendsto_limUnder
  have hfd : DifferentiableOn ℂ f B := by
    intro z₀ hz₀
    obtain ⟨r, hr, hrB, hU⟩ := hloc z₀ hz₀
    have hTU : TendstoUniformlyOn g f atTop (ball z₀ r) :=
      hU.tendstoUniformlyOn_of_tendsto fun z hz => hlim z (hrB hz)
    exact (Hironaka.differentiableAt_of_tendstoUniformlyOn_ball hr
      (Eventually.of_forall fun n => (differentiableOn_rep (G' n)).mono hrB)
      hTU).differentiableWithinAt
  refine ⟨f, hfd, ?_⟩
  -- identify the class through an a.e.-convergent subsequence
  have hL2 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' G F).mp hGF
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (f := fun n => (G n : ComplexModel d → ℂ))
    two_ne_zero (fun n => Lp.aestronglyMeasurable (G n)) (Lp.aestronglyMeasurable F) hL2
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂bergmanMeasure B w, ∀ n, (G n : ComplexModel d → ℂ) x = g n x :=
    ae_all_iff.mpr fun n => ae_eq_rep hBw (G' n)
  have hB : ∀ᵐ x ∂bergmanMeasure B w, x ∈ B :=
    (withDensity_absolutelyContinuous _ w).ae_le (ae_restrict_mem hBw.isOpen.measurableSet)
  filter_upwards [hae, hrep, hB] with x hx hxr hxB
  refine tendsto_nhds_unique hx ?_
  have := (hlim x hxB).comp hns.tendsto_atTop
  refine this.congr fun i => ?_
  simp only [Function.comp, hxr]

/-! ### Evaluation -/

/-- Evaluation of the holomorphic representative at `z`, as a linear form. -/
def evalLM (hBw : BergmanWeight B w) (z : ComplexModel d) : bergmanSubspace B w →ₗ[ℂ] ℂ where
  toFun F := rep F z
  map_add' F G := by rw [rep_add hBw]; rfl
  map_smul' c F := by rw [rep_smul hBw]; rfl

theorem exists_bound_evalLM (hBw : BergmanWeight B w) (z : ComplexModel d) :
    ∃ C : ℝ, ∀ F, ‖evalLM hBw z F‖ ≤ C * ‖F‖ := by
  by_cases hz : z ∈ B
  · obtain ⟨r, hr, -, C, -, hbd⟩ := exists_norm_rep_le hBw hz
    exact ⟨C, fun F => hbd F z (mem_ball_self hr)⟩
  · refine ⟨0, fun F => ?_⟩
    simp only [evalLM, LinearMap.coe_mk, AddHom.coe_mk, rep_of_not_mem F hz, norm_zero, zero_mul,
      le_refl]

/-- **The evaluation form** `F ↦ f_F(z)` of the weighted Bergman space. -/
def evalCLM (hBw : BergmanWeight B w) (z : ComplexModel d) : bergmanSubspace B w →L[ℂ] ℂ :=
  (evalLM hBw z).mkContinuousOfExistsBound (exists_bound_evalLM hBw z)

@[simp] theorem evalCLM_apply (hBw : BergmanWeight B w) (z : ComplexModel d)
    (F : bergmanSubspace B w) : evalCLM hBw z F = rep F z := rfl

/-- An element of the Bergman unit ball defines an element of the Bergman space of norm `≤ 1`. -/
theorem exists_of_mem_bergmanBall (hBw : BergmanWeight B w) {f : ComplexModel d → ℂ}
    (hf : f ∈ bergmanBall B w) :
    ∃ F : bergmanSubspace B w, ‖F‖ ≤ 1 ∧ EqOn (rep F) f B := by
  have hmeas : AEStronglyMeasurable f (bergmanMeasure B w) :=
    (hf.1.continuousOn.aestronglyMeasurable hBw.isOpen.measurableSet).mono_ac
      (withDensity_absolutelyContinuous _ _)
  have hint := lintegral_enorm_sq_eq hBw.aemeasurable hmeas (EventuallyEq.refl _ f)
  have hmem : MemLp f 2 (bergmanMeasure B w) := by
    refine ⟨hmeas, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [hint]
    exact lt_of_le_of_lt hf.2 ENNReal.one_lt_top
  let F : bergmanSubspace B w := ⟨hmem.toLp f, f, hf.1, hmem.coeFn_toLp⟩
  refine ⟨F, ?_, rep_eqOn hBw F hf.1 hmem.coeFn_toLp⟩
  have hF := ofReal_norm_sq_eq hBw.aemeasurable (F := hmem.toLp f) hmem.coeFn_toLp
  have h1 : ENNReal.ofReal (‖F‖ ^ 2) ≤ 1 := by
    change ENNReal.ofReal (‖hmem.toLp f‖ ^ 2) ≤ 1
    rw [hF]
    exact hf.2
  have h2 : ‖F‖ ^ 2 ≤ 1 := by
    rw [← ENNReal.ofReal_one] at h1
    exact (ENNReal.ofReal_le_ofReal_iff zero_le_one).mp h1
  nlinarith [norm_nonneg F]

/-- **The Bergman kernel is the squared norm of the evaluation form.** -/
theorem bergmanSup_eq_ofReal_norm_evalCLM_sq (hBw : BergmanWeight B w) {z : ComplexModel d}
    (hz : z ∈ B) : bergmanSup B w z = ENNReal.ofReal (‖evalCLM hBw z‖ ^ 2) := by
  have h1 : bergmanSup B w z ≤ ENNReal.ofReal (‖evalCLM hBw z‖ ^ 2) := by
    refine bergmanSup_le fun f hf => ?_
    obtain ⟨F, hF1, hFf⟩ := exists_of_mem_bergmanBall hBw hf
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    calc ‖f z‖ = ‖evalCLM hBw z F‖ := by rw [evalCLM_apply, hFf hz]
      _ ≤ ‖evalCLM hBw z‖ * ‖F‖ := (evalCLM hBw z).le_opNorm F
      _ ≤ ‖evalCLM hBw z‖ * 1 := by gcongr
      _ = ‖evalCLM hBw z‖ := mul_one _
  have htop : bergmanSup B w z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  refine le_antisymm h1 ?_
  set K : ℝ := (bergmanSup B w z).toReal with hKdef
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hbound : ‖evalCLM hBw z‖ ≤ Real.sqrt K := by
    refine (evalCLM hBw z).opNorm_le_bound (Real.sqrt_nonneg _) fun F => ?_
    rw [evalCLM_apply]
    by_cases hF0 : F = 0
    · rw [hF0, show rep (0 : bergmanSubspace B w) z = evalCLM hBw z 0 from rfl, map_zero,
        norm_zero, norm_zero, mul_zero]
    have hFpos : 0 < ‖F‖ := norm_pos_iff.mpr hF0
    have hA0 : ENNReal.ofReal (‖F‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hext := bergmanSup_extremal (differentiableOn_rep F) hA0 ENNReal.ofReal_ne_top
      (ofReal_norm_sq_eq hBw.aemeasurable (ae_eq_rep hBw F)).symm.le z
    rw [← ENNReal.ofReal_toReal htop, ← hKdef, ← ENNReal.ofReal_mul (by positivity)] at hext
    have h3 : ‖rep F z‖ ^ 2 ≤ ‖F‖ ^ 2 * K :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hext
    have h4 : ‖rep F z‖ ^ 2 ≤ (Real.sqrt K * ‖F‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK0]
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h4
  rw [← ENNReal.ofReal_toReal htop, ← hKdef]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖evalCLM hBw z‖ ^ 2 ≤ Real.sqrt K ^ 2 := by gcongr
    _ = K := Real.sq_sqrt hK0

/-! ### The evaluation form depends holomorphically on the point -/

/-- **Complex differentiability of the evaluation form**, from the Cauchy estimate and the
second-order Taylor estimate, uniform over the unit ball of the Bergman space. -/
theorem differentiableAt_evalCLM (hBw : BergmanWeight B w) {z₀ : ComplexModel d}
    (hz₀ : z₀ ∈ B) : DifferentiableAt ℂ (evalCLM hBw) z₀ := by
  obtain ⟨r, hr, hrB, C, hC, hbd⟩ := exists_norm_rep_le hBw hz₀
  have hdiff : ∀ F : bergmanSubspace B w, DifferentiableAt ℂ (rep F) z₀ := fun F =>
    (differentiableOn_rep F).differentiableAt (hBw.isOpen.mem_nhds hz₀)
  -- the derivative of the representatives at `z₀`, as a bounded operator
  let D₀ : bergmanSubspace B w →ₗ[ℂ] (ComplexModel d →L[ℂ] ℂ) :=
    { toFun := fun F => fderiv ℂ (rep F) z₀
      map_add' := fun F G => by rw [rep_add hBw]; exact fderiv_add (hdiff F) (hdiff G)
      map_smul' := fun c F => by rw [rep_smul hBw]; exact fderiv_const_smul (hdiff F) c }
  have hcauchy : ∀ F : bergmanSubspace B w, ∀ v ∈ ball z₀ (r / 2),
      ‖fderiv ℂ (rep F) v‖ ≤ C * ‖F‖ / (r / 4) := by
    intro F v hv
    have hsub : ball v (r / 2) ⊆ ball z₀ r := by
      intro u hu
      rw [mem_ball] at hu hv ⊢
      linarith [dist_triangle u v z₀]
    exact _root_.Hironaka.norm_fderiv_le_of_forall_norm_le ((differentiableOn_rep F).mono
      (hsub.trans hrB)) (fun u hu => hbd F u (hsub hu)) (by positivity) (by linarith)
  have hD₀ : ∃ K : ℝ, ∀ F, ‖D₀ F‖ ≤ K * ‖F‖ :=
    ⟨C / (r / 4), fun F => by
      have := hcauchy F z₀ (mem_ball_self (by positivity))
      calc ‖D₀ F‖ ≤ C * ‖F‖ / (r / 4) := this
        _ = C / (r / 4) * ‖F‖ := by ring⟩
  let D : bergmanSubspace B w →L[ℂ] (ComplexModel d →L[ℂ] ℂ) := D₀.mkContinuousOfExistsBound hD₀
  refine ⟨D.flip, (hasFDerivAt_iff_isLittleO_nhds_zero (𝕜 := ℂ) (E := ComplexModel d)
    (F := bergmanSubspace B w →L[ℂ] ℂ) (f := evalCLM hBw) (f' := D.flip) (x := z₀)).mpr ?_⟩
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun u : ComplexModel d => ‖u‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (C / (r / 4) / (r / 2 / 4)) ?_
  filter_upwards [ball_mem_nhds (0 : ComplexModel d) (by positivity : 0 < r / 2 / 8)] with u hu
  rw [mem_ball_zero_iff] at hu
  rw [Real.norm_of_nonneg (by positivity)]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun F => ?_
  have htaylor := Hironaka.norm_sub_sub_fderiv_le (f := rep F) (z₀ := z₀) (δ := r / 2)
    (L := C * ‖F‖ / (r / 4)) (by positivity)
    ((differentiableOn_rep F).mono ((ball_subset_ball (by linarith)).trans hrB))
    (hcauchy F) (z := z₀) (u := u) (mem_ball_self (by positivity)) hu
  have heq : ((evalCLM hBw (z₀ + u) - evalCLM hBw z₀ - D.flip u) F) =
      rep F (z₀ + u) - rep F z₀ - fderiv ℂ (rep F) z₀ u := rfl
  rw [heq]
  calc ‖rep F (z₀ + u) - rep F z₀ - fderiv ℂ (rep F) z₀ u‖
      ≤ C * ‖F‖ / (r / 4) / (r / 2 / 4) * ‖u‖ * ‖u‖ := htaylor
    _ = C / (r / 4) / (r / 2 / 4) * ‖u‖ ^ 2 * ‖F‖ := by ring

theorem differentiableOn_evalCLM (hBw : BergmanWeight B w) :
    DifferentiableOn ℂ (evalCLM hBw) B := fun _ hz =>
  (differentiableAt_evalCLM hBw hz).differentiableWithinAt

/-! ### Smoothness of the kernel -/

/-- **B3: the Bergman kernel on the diagonal is `C^∞` on `B`.**  The evaluation form is
holomorphic, hence `C^∞`, and the squared dual norm is `C^∞`: by Riesz the dual is isometric,
hence (Mazur--Ulam) real-linearly isometric, to the Hilbert space itself. -/
theorem contDiffOn_toReal_bergmanSup (hBw : BergmanWeight B w) :
    ContDiffOn ℝ ∞ (fun z => (bergmanSup B w z).toReal) B := by
  have hev := Hironaka.contDiffOn_real_of_differentiableOn_complex (E := ComplexModel d)
    (F := bergmanSubspace B w →L[ℂ] ℂ) (differentiableOn_evalCLM hBw) hBw.isOpen
  have : CompleteSpace (bergmanSubspace B w) :=
    completeSpace_coe_iff_isComplete.mpr (isClosed_bergmanSubspace hBw).isComplete
  let T := (InnerProductSpace.toDual ℂ (bergmanSubspace B w)).symm
  let T' := @IsometryEquiv.toRealLinearIsometryEquivOfMapZero
    (StrongDual ℂ (bergmanSubspace B w)) (bergmanSubspace B w) _ NormedSpace.complexToReal
    _ _ T.toIsometryEquiv T.map_zero
  have h := (contDiff_norm_sq ℂ).comp_contDiffOn (T'.contDiff.comp_contDiffOn hev)
  refine h.congr fun z hz => ?_
  simp only [Function.comp, T', LinearIsometryEquiv.norm_map, T,
    bergmanSup_eq_ofReal_norm_evalCLM_sq hBw hz, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- The Bergman kernel is finite on `B`. -/
theorem bergmanSup_ne_top (hBw : BergmanWeight B w) {z : ComplexModel d} (hz : z ∈ B) :
    bergmanSup B w z ≠ ⊤ := by
  rw [bergmanSup_eq_ofReal_norm_evalCLM_sq hBw hz]
  exact ENNReal.ofReal_ne_top

end

end Hironaka.BergmanKernelSmooth
