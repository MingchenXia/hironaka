import Hironaka.Resolution.HironakaG10FlatPolydiscAlgebra
import Hironaka.Resolution.HironakaG10FlatDiscWeierstrassDivision
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Fibres of `B(K' × D̄(0,ρ))` and continuity of the boundary Cauchy operators

Two preparatory steps for the privilege of the polydisc `K = K' × D̄(0,ρ)` with respect to a
Weierstrass polynomial (REPORT-r1, splits 1 and 2):

* `interior_prod_closedBall`: `interior (K' × D̄(0,ρ)) = interior K' × D(0,ρ)`;
* `differentiableOn_fibre`: if `K' ⊆ closure (interior K')` (true for polydiscs), every fibre
  `f(z,·)`, `z ∈ K'`, of `f ∈ B(K)` is holomorphic on `D(0,ρ)` (uniform limit of the fibres over
  interior points; without the hypothesis this FAILS, e.g. for `K'` a point);
  `continuousOn_fibre`: the fibres are continuous on `D̄(0,ρ)`;
* `continuousOn_circleIntegral_param`: `p ↦ ∮_{|ζ|=ρ} Ψ(p,ζ)` is continuous on `S` whenever `Ψ`
  is continuous on `S × {|ζ| = ρ}` (no openness, any topological parameter space);
* `continuousOn_remCoeff_extendZero`: for `f ∈ B(K)` and `W ≠ 0` on `K' × {|ζ|=ρ}`, the boundary
  remainder coefficients `z ↦ remCoeff b A f ρ i z` are continuous on `K'`.
BP: hironaka-g10-flat-polydisc-fibre.tex. -/
set_option autoImplicit false
open Set Filter Metric Complex
open scoped Topology Real
namespace Hironaka.HironakaG10FlatPolydiscFibre
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatDiscWeierstrassDivision

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

omit [NormedSpace ℂ P] in
theorem interior_prod_closedBall (K' : Set P) {ρ : ℝ} (hρ : 0 < ρ) :
    interior (K' ×ˢ closedBall (0 : ℂ) ρ) = interior K' ×ˢ ball (0 : ℂ) ρ := by
  rw [interior_prod_eq, interior_closedBall _ hρ.ne']

/-- **Fibre holomorphy.** -/
theorem differentiableOn_fibre {K' : Set P} (hK' : K' ⊆ closure (interior K')) {ρ : ℝ}
    (hρ : 0 < ρ) [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)]
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) {z : P} (hz : z ∈ K') :
    DifferentiableOn ℂ (fun w : ℂ => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ)
      (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) (z, w)) (ball 0 ρ) := by
  have hf : DifferentiableOn ℂ (extendZero (K' ×ˢ closedBall (0 : ℂ) ρ)
      (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ))) (interior K' ×ˢ ball (0 : ℂ) ρ) := by
    have h0 := mem_holSubalgebra.mp f.2
    rwa [interior_prod_closedBall K' hρ] at h0
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (hK' hz)
  have hunif : UniformContinuous (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) :=
    CompactSpace.uniformContinuous_of_continuous (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)).continuous
  intro w₀ hw₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_ball w₀ hw₀
  refine DifferentiableAt.differentiableWithinAt ?_
  refine Hironaka.differentiableAt_of_tendstoUniformlyOn_ball
    (g := fun n w => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ)
      (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) (u n, w)) hr
    (Eventually.of_forall fun n => (hf.comp ((differentiableOn_const (u n)).prodMk
      differentiableOn_id) fun w hw => ⟨hu n, hball hw⟩).mono subset_rfl) ?_
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp hunif ε hε
  filter_upwards [Metric.tendsto_nhds.mp hlim δ hδ] with n hn
  intro w hw
  have hwc : w ∈ closedBall (0 : ℂ) ρ := ball_subset_closedBall (hball hw)
  have h₁ : (z, w) ∈ K' ×ˢ closedBall (0 : ℂ) ρ := ⟨hz, hwc⟩
  have h₂ : (u n, w) ∈ K' ×ˢ closedBall (0 : ℂ) ρ := ⟨interior_subset (hu n), hwc⟩
  rw [extendZero_of_mem _ _ h₁, extendZero_of_mem _ _ h₂]
  refine hδf ?_
  change dist (z, w) (u n, w) < δ
  rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg, dist_comm]
  exact hn

omit [NormedSpace ℂ P] in
/-- The fibres are continuous on the closed disc. -/
theorem continuousOn_fibre {K' : Set P} {ρ : ℝ} (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ))
    {z : P} (hz : z ∈ K') :
    ContinuousOn (fun w : ℂ => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) f (z, w)) (closedBall 0 ρ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (closedBall (0 : ℂ) ρ).domRestrict
      (fun w => extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) f (z, w)) =
      fun w : closedBall (0 : ℂ) ρ => f ⟨(z, w.1), hz, w.2⟩ := by
    funext w
    exact extendZero_of_mem _ _ _
  rw [this]
  exact f.continuous.comp (Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val) _)

/-- **Continuity of circle integrals in a parameter**, on any subset of any topological
parameter space. -/
theorem continuousOn_circleIntegral_param {Q : Type*} [TopologicalSpace Q] {S : Set Q}
    {Ψ : Q × ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hΨ : ContinuousOn Ψ (S ×ˢ sphere (0 : ℂ) ρ)) :
    ContinuousOn (fun p => ∮ ζ in C(0, ρ), Ψ (p, ζ)) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun x : S × ℝ => deriv (circleMap 0 ρ) x.2 • Ψ (x.1.1, circleMap 0 ρ x.2)) := by
    simp only [deriv_circleMap, smul_eq_mul]
    exact (((continuous_circleMap 0 ρ).comp continuous_snd).mul continuous_const).mul
      (hΨ.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_circleMap 0 ρ).comp continuous_snd)) fun x =>
          ⟨x.1.2, circleMap_mem_sphere 0 hρ x.2⟩)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : S) (θ : ℝ) => deriv (circleMap 0 ρ) θ • Ψ (x.1, circleMap 0 ρ θ)) hc 0 (2 * π)

omit [NormedSpace ℂ P] in
/-- The boundary remainder coefficients of an element of `B(K' × D̄(0,ρ))` are continuous on
`K'`. -/
theorem continuousOn_remCoeff_extendZero {K' : Set P} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) {b : ℕ} {A : ℕ → P → ℂ}
    (hA : ∀ k, ContinuousOn (A k) K') (hW : ∀ z ∈ K', ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0)
    (i : ℕ) : ContinuousOn (remCoeff b A (extendZero _ f) ρ i) K' := by
  have hfK : ContinuousOn (extendZero _ f) (K' ×ˢ closedBall (0 : ℂ) ρ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : (K' ×ˢ closedBall (0 : ℂ) ρ).domRestrict (extendZero _ f) = f := by
      funext x
      exact extendZero_of_mem _ _ x.2
    rw [this]
    exact f.continuous
  have hsub : K' ×ˢ sphere (0 : ℂ) ρ ⊆ K' ×ˢ closedBall (0 : ℂ) ρ :=
    prod_mono subset_rfl sphere_subset_closedBall
  have hWc : ContinuousOn (fun x : P × ℂ => polyEval b A x.1 x.2) (K' ×ˢ sphere (0 : ℂ) ρ) :=
    continuousOn_finsetSum _ fun k _ =>
      ((hA k).comp continuousOn_fst fun x hx => hx.1).mul (continuousOn_snd.pow k)
  have hcc : ContinuousOn (fun x : P × ℂ => diffCoeff b A i x.1 x.2) (K' ×ˢ sphere (0 : ℂ) ρ) :=
    continuousOn_finsetSum _ fun k _ => by
      split_ifs
      · exact ((hA k).comp continuousOn_fst fun x hx => hx.1).mul (continuousOn_snd.pow _)
      · exact continuousOn_const
  have hΨ : ContinuousOn (fun x : P × ℂ => extendZero _ f x * diffCoeff b A i x.1 x.2 /
      polyEval b A x.1 x.2) (K' ×ˢ sphere (0 : ℂ) ρ) :=
    ((hfK.mono hsub).mul hcc).div hWc fun x hx => hW x.1 hx.1 x.2 hx.2
  exact (continuousOn_circleIntegral_param hρ hΨ).const_smul ((2 * π * I)⁻¹) |>.congr
    fun z _ => by simp [remCoeff, smul_eq_mul]

end
end Hironaka.HironakaG10FlatPolydiscFibre
