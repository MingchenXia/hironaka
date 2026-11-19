import Hironaka.Analytic.GAGA.CoreCousin

/-!
# Cousin I across a real hyperplane with a constant uniform in the cutoffs

Infrastructure of lane SERRE-CORE2 (Serre's GAGA, towards source `lma:GAGA`), step M2.3 of the
plan in `blueprint/src/claude-serre-core.tex` (see `blueprint/src/claude-serre-core2.tex`).

`Hironaka.Analytic.GAGA.Core.Cousin.exists_cousin_split` splits a function holomorphic near a slab
`S = {z_k ∈ tsupport ψ_k, |Re(θ z_i) - t| ≤ δ}` as `f' - f''` with sup-norm bounds `C M`, where
`C` depends on the cutoffs `ψ_k`. The iteration of Cartan's matrix lemma (`CoreBCartan`) applies
the splitting on a decreasing sequence of domains, so it needs a constant that does not depend
on the cutoffs. This file proves that form (`exists_cousin_split_uniform`): for cutoffs with
`|ψ_k| ≤ 1` and supports in a fixed ball, the constant depends only on `(i, θ, t, δ)` and the
radius of the ball. The hypothesis on `f` is also weakened to the half-open slab
`{z_k ∈ tsupport ψ_k, |Re(θ z_i) - t| < δ}`, so that the output domains
`{z_k ∈ O_k, Re(θ z_i) < t + δ}`, `{z_k ∈ O_k, t - δ < Re(θ z_i)}` of one step contain the input
slab of the next step for the same `δ`.

The proof is that of `exists_cousin_split` (one-variable Cauchy--Green operator of
`Hironaka` applied to `ψ · ∂̄_i χ · f`), with the constant
`1 + π⁻¹ · sup |∂̄_i χ| · ∫_{|w| < 2R + 1} |w|⁻¹` chosen before the cutoffs.
`exists_cutoff_between` provides cutoffs with values in `[0, 1]` between two thickenings.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff Real Manifold
open Hironaka Hironaka.CauchyGreen
  Hironaka

namespace Hironaka.Analytic.GAGA.Core.Cousin

noncomputable section

variable {n : ℕ}

/-- A smooth cutoff on `ℂ` with values in `[0, 1]`, equal to `1` on the open `r`-neighbourhood
of a compact set and supported in its closed `ρ`-neighbourhood (`r < ρ`). -/
theorem exists_cutoff_between {K : Set ℂ} (hK : IsCompact K) {r ρ : ℝ} (hr : 0 ≤ r)
    (hrρ : r < ρ) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ w, |ψ w| ≤ 1) ∧
      (∀ w ∈ thickening r K, ψ w = 1) ∧ tsupport ψ ⊆ cthickening ρ K := by
  have hρ : 0 < ρ := lt_of_le_of_lt hr hrρ
  have hd : Disjoint (thickening ρ K)ᶜ (cthickening r K) := by
    rw [disjoint_compl_left_iff_subset]
    exact cthickening_subset_thickening' hρ hrρ K
  obtain ⟨f, hf0, hf1, hf01⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := ⊤) 𝓘(ℝ, ℂ)
    isOpen_thickening.isClosed_compl isClosed_cthickening hd
  have hsupp : tsupport f ⊆ cthickening ρ K := by
    refine (closure_mono fun w hw => ?_).trans (closure_thickening_subset_cthickening ρ K)
    by_contra hw'
    exact hw (hf0 hw')
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, ?_, fun w => ?_, fun w hw =>
    hf1 (thickening_subset_cthickening _ _ hw), hsupp⟩
  · exact IsCompact.of_isClosed_subset (hK.cthickening) (isClosed_tsupport _) hsupp
  · have h := hf01 w
    rw [abs_le]
    exact ⟨by linarith [h.1], h.2⟩

/-- **Cousin I across the hyperplane `Re(θ z_i) = t`, with a bound uniform in the cutoffs.**
The constant depends only on `(i, θ, t, δ)` and on the radius `R` of a ball containing the
supports of the cutoffs. -/
theorem exists_cousin_split_uniform (i : Fin n) (θ : ℂ) (t δ : ℝ) (hδ : 0 < δ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : Fin n → ℂ → ℝ), (∀ k, ContDiff ℝ ∞ (ψ k)) →
      (∀ k, HasCompactSupport (ψ k)) → (∀ k w, |ψ k w| ≤ 1) →
      (∀ k, tsupport (ψ k) ⊆ closedBall (0 : ℂ) R) →
      ∀ (O : Fin n → Set ℂ), (∀ k, IsOpen (O k)) → (∀ k, ∀ w ∈ O k, ψ k w = 1) →
      ∀ (U : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ)
      (M : ℝ), IsOpen U → DifferentiableOn ℂ f U →
      {z | (∀ k, z k ∈ tsupport (ψ k)) ∧ |(θ * z i).re - t| < δ} ⊆ U →
      (∀ z, (∀ k, z k ∈ tsupport (ψ k)) → |(θ * z i).re - t| < δ → ‖f z‖ ≤ M) → 0 ≤ M →
      ∃ f' f'' : EuclideanSpace ℂ (Fin n) → ℂ,
        DifferentiableOn ℂ f' {z | (∀ k, z k ∈ O k) ∧ (θ * z i).re < t + δ} ∧
        DifferentiableOn ℂ f'' {z | (∀ k, z k ∈ O k) ∧ t - δ < (θ * z i).re} ∧
        (∀ z, f z = f' z - f'' z) ∧
        (∀ z, (∀ k, z k ∈ O k) → (θ * z i).re < t + δ → ‖f' z‖ ≤ C * M) ∧
        (∀ z, (∀ k, z k ∈ O k) → t - δ < (θ * z i).re → ‖f'' z‖ ≤ C * M) := by
  classical
  -- the linear form and the transition function
  set L : EuclideanSpace ℂ (Fin n) → ℝ := fun z => (θ * z i).re with hLdef
  have hLc : ContDiff ℝ ∞ L :=
    reCLM.contDiff.comp (contDiff_const.mul (contDiff_coord i))
  have hLcont : Continuous L := hLc.continuous
  let χ₀ : ℝ → ℝ := fun s => Real.smoothTransition ((δ / 2 - s) / δ)
  have hχ₀ : ContDiff ℝ ∞ χ₀ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const δ)
  have hχ₀1 : ∀ s, s ≤ -(δ / 2) → χ₀ s = 1 := fun s hs =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδ]; linarith)
  have hχ₀0 : ∀ s, δ / 2 ≤ s → χ₀ s = 0 := fun s hs =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  let χ : EuclideanSpace ℂ (Fin n) → ℝ := fun z => χ₀ (L z - t)
  have hχ : ContDiff ℝ ∞ χ := hχ₀.comp (hLc.sub contDiff_const)
  let χc : EuclideanSpace ℂ (Fin n) → ℂ := fun z => (χ z : ℂ)
  have hχc : ContDiff ℝ ∞ χc := ofRealCLM.contDiff.comp hχ
  have hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1 := fun z =>
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  -- local constancy of `χ` off the slab
  have hχone : ∀ z, L z - t < -(δ / 2) → ∀ᶠ y in 𝓝 z, χ y = 1 := by
    intro z hz
    have hopen : IsOpen {y | L y - t < -(δ / 2)} :=
      isOpen_lt (hLcont.sub continuous_const) continuous_const
    exact eventually_of_mem (hopen.mem_nhds hz) fun y hy => hχ₀1 _ (le_of_lt hy)
  have hχzero : ∀ z, δ / 2 < L z - t → ∀ᶠ y in 𝓝 z, χ y = 0 := by
    intro z hz
    have hopen : IsOpen {y | δ / 2 < L y - t} :=
      isOpen_lt continuous_const (hLcont.sub continuous_const)
    exact eventually_of_mem (hopen.mem_nhds hz) fun y hy => hχ₀0 _ (le_of_lt hy)
  -- the derivative `∂̄_i χ`
  let dχ : EuclideanSpace ℂ (Fin n) → ℂ := dbarDir (basisVec i) χc
  have hdχ : ContDiff ℝ ∞ dχ := by
    have hD := hχc.fderiv_right (m := ∞) (by simp)
    show ContDiff ℝ ∞ (fun x => (fderiv ℝ χc x (basisVec i) +
      I * fderiv ℝ χc x (I • basisVec i)) / 2)
    exact ((hD.clm_apply contDiff_const).add
      (contDiff_const.mul (hD.clm_apply contDiff_const))).div_const _
  have hdχ0 : ∀ z, δ / 2 < |L z - t| → dχ z = 0 := by
    intro z hz
    rcases lt_abs.1 hz with h | h
    · have hev : χc =ᶠ[𝓝 z] fun _ => (0 : ℂ) :=
        (hχzero z h).mono fun y hy => by simp [χc, hy]
      exact (dbarDir_congr hev).trans (dbarDir_const _ _)
    · have hev : χc =ᶠ[𝓝 z] fun _ => (1 : ℂ) :=
        (hχone z (by linarith)).mono fun y hy => by simp [χc, hy]
      exact (dbarDir_congr hev).trans (dbarDir_const _ _)
  have hdχ0ev : ∀ z, δ / 2 < |L z - t| → dχ =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    have hopen : IsOpen {y | δ / 2 < |L y - t|} :=
      isOpen_lt continuous_const (continuous_abs.comp (hLcont.sub continuous_const))
    exact eventually_of_mem (hopen.mem_nhds hz) fun y hy => hdχ0 y hy
  -- `χ` depends only on `z_i`
  have hχinv : ∀ k, k ≠ i → ∀ (c : ℂ) (z : EuclideanSpace ℂ (Fin n)) (s : ℝ),
      χc (z + s • (c • basisVec k)) = χc z := by
    intro k hk c z s
    simp only [χc, χ, L, basisVec, coord_add_smul_single hk.symm]
  have hdχc_k : ∀ k, k ≠ i → ∀ y, dbarDir (basisVec k) χc y = 0 := by
    intro k hk y
    refine dbarDir_eq_zero_of_invariant (fun z s => ?_) (fun z s => ?_) y
    · simpa using hχinv k hk 1 z s
    · exact hχinv k hk I z s
  have hdχ_k : ∀ k, k ≠ i → ∀ y, dbarDir (basisVec k) dχ y = 0 := by
    intro k hk y
    rw [show dχ = dbarDir (basisVec i) χc from rfl,
      dbarDir_dbarDir_comm (hχc.contDiffAt.of_le (by norm_cast))]
    have : dbarDir (basisVec k) χc = fun _ => 0 := funext (hdχc_k k hk)
    rw [this, dbarDir_const]
  -- the constant: a bound for `∂̄_i χ` on the polydisc of radius `R`
  have hPRc : IsCompact {z : EuclideanSpace ℂ (Fin n) | ∀ k, z k ∈ closedBall (0 : ℂ) R} :=
    isCompact_coord_pi fun _ => isCompact_closedBall _ _
  obtain ⟨B₀, hB₀⟩ := hPRc.exists_bound_of_continuousOn hdχ.continuous.continuousOn
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  set D : ℝ := 2 * |R| + 1 with hDdef
  set ID : ℝ := ∫ w : ℂ, (ball (0 : ℂ) D).indicator (fun w => ‖w‖⁻¹) w with hIDdef
  have hID0 : 0 ≤ ID := integral_nonneg fun w => by
    by_cases hw : w ∈ ball (0 : ℂ) D <;> simp [hw]
  refine ⟨1 + π⁻¹ * B * ID, by positivity, ?_⟩
  intro ψ hψ hψc hψ1 hψR O hO hψO U f M hU hf hSU hfM hM0
  -- the product cutoff
  let ψp : EuclideanSpace ℂ (Fin n) → ℝ := fun z => ∏ k, ψ k (z k)
  have hψp : ContDiff ℝ ∞ ψp :=
    contDiff_prod fun k _ => (hψ k).comp (contDiff_coord k)
  set P : Set (EuclideanSpace ℂ (Fin n)) := {z | ∀ k, z k ∈ tsupport (ψ k)} with hPdef
  have hPc : IsCompact P := isCompact_coord_pi fun k => hψc k
  have hψp0 : ∀ z, z ∉ P → ψp =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    simp only [hPdef, mem_ofPred_eq, not_forall] at hz
    obtain ⟨k, hk⟩ := hz
    have hopen : IsOpen {y : EuclideanSpace ℂ (Fin n) | y k ∉ tsupport (ψ k)} :=
      (isClosed_tsupport (ψ k)).isOpen_compl.preimage (continuous_coord k)
    refine eventually_of_mem (hopen.mem_nhds hk) fun y hy => ?_
    exact Finset.prod_eq_zero (Finset.mem_univ k) (image_eq_zero_of_notMem_tsupport hy)
  have hOsub : ∀ k, O k ⊆ tsupport (ψ k) := fun k w hw =>
    subset_tsupport _ (by rw [Function.mem_support, hψO k w hw]; exact one_ne_zero)
  have hψp1 : ∀ z, (∀ k, z k ∈ O k) → ψp z = 1 := fun z hz =>
    Finset.prod_eq_one fun k _ => hψO k _ (hz k)
  -- `∂̄_k ψ = 0` where `z_k ∈ O_k`
  have hψp_k : ∀ k, ∀ y : EuclideanSpace ℂ (Fin n), y k ∈ O k →
      dbarDir (basisVec k) (fun z => (ψp z : ℂ)) y = 0 := by
    intro k y hy
    let ψk : EuclideanSpace ℂ (Fin n) → ℂ := fun z => ((∏ l ∈ Finset.univ.erase k, ψ l (z l) : ℝ) : ℂ)
    have hopen : IsOpen {z : EuclideanSpace ℂ (Fin n) | z k ∈ O k} :=
      (hO k).preimage (continuous_coord k)
    have hev : (fun z => (ψp z : ℂ)) =ᶠ[𝓝 y] ψk := by
      refine eventually_of_mem (hopen.mem_nhds hy) fun z hz => ?_
      simp only [ψk, ψp, ← Finset.mul_prod_erase Finset.univ (fun l => ψ l (z l))
        (Finset.mem_univ k), hψO k _ hz, one_mul]
    rw [dbarDir_congr hev]
    have hinv : ∀ (c : ℂ) (z : EuclideanSpace ℂ (Fin n)) (s : ℝ),
        ψk (z + s • (c • basisVec k)) = ψk z := by
      intro c z s
      simp only [ψk]
      congr 1
      exact Finset.prod_congr rfl fun l hl => by
        rw [coord_add_smul_single (Finset.ne_of_mem_erase hl)]
    refine dbarDir_eq_zero_of_invariant (fun z s => ?_) (fun z s => hinv I z s) y
    simpa using hinv 1 z s
  -- the bound for `ψ ∂̄_i χ`
  have hB : ∀ z, ‖(ψp z : ℂ) * dχ z‖ ≤ B := by
    intro z
    by_cases hz : z ∈ P
    · have h1 : ‖(ψp z : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]
        exact Finset.prod_le_one (fun k _ => abs_nonneg _) fun k _ => hψ1 k _
      have h2 : ‖dχ z‖ ≤ B := (hB₀ z fun k => hψR k (hz k)).trans (le_max_left _ _)
      calc ‖(ψp z : ℂ) * dχ z‖ = ‖(ψp z : ℂ)‖ * ‖dχ z‖ := norm_mul _ _
        _ ≤ 1 * B := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = B := one_mul B
    · simp [(hψp0 z hz).self_of_nhds, hB0]
  -- the radius for the Cauchy--Green integral
  have hA : tsupport (ψ i) ⊆ closedBall (0 : ℂ) R := hψR i
  set S : Set (EuclideanSpace ℂ (Fin n)) :=
    {z | (∀ k, z k ∈ tsupport (ψ k)) ∧ |(θ * z i).re - t| < δ} with hSdef
  have hfC : ∀ z ∈ U, ContDiffAt ℝ ∞ f z := fun z hz =>
    contDiffAt_real_of_differentiableOn_complex hf hU hz
  -- the right-hand side `g = ψ ∂̄_i χ f`
  let g : EuclideanSpace ℂ (Fin n) → ℂ := fun z => (ψp z : ℂ) * (dχ z * f z)
  have hg0ev : ∀ z, z ∉ U → g =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    have hzS : z ∉ S := fun h => hz (hSU h)
    simp only [hSdef, mem_ofPred_eq, not_and_or, not_lt] at hzS
    rcases hzS with h | h
    · exact (hψp0 z h).mono fun y hy => by simp [g, hy]
    · exact (hdχ0ev z (by linarith)).mono fun y hy => by simp [g, hy]
  have hg : ContDiff ℝ ∞ g := by
    refine contDiff_iff_contDiffAt.2 fun z => ?_
    by_cases hz : z ∈ U
    · exact (ofRealCLM.contDiff.comp hψp).contDiffAt.mul (hdχ.contDiffAt.mul (hfC z hz))
    · exact contDiffAt_const.congr_of_eventuallyEq (hg0ev z hz)
  have hgc : HasCompactSupport g := by
    refine HasCompactSupport.intro hPc fun z hz => ?_
    simp [g, (hψp0 z hz).self_of_nhds]
  have hgbound : ∀ y, ‖g y‖ ≤ B * M := by
    intro y
    by_cases h0 : (ψp y : ℂ) * dχ y = 0
    · have : g y = 0 := by simp only [g, ← mul_assoc, h0, zero_mul]
      rw [this, norm_zero]
      positivity
    · have hyP : y ∈ P := by
        by_contra hy
        exact h0 (by simp [(hψp0 y hy).self_of_nhds])
      have hyslab : |L y - t| < δ := by
        by_contra hy
        exact h0 (by rw [hdχ0 y (by linarith [not_lt.1 hy]), mul_zero])
      calc ‖g y‖ = ‖(ψp y : ℂ) * dχ y‖ * ‖f y‖ := by simp only [g, ← mul_assoc, norm_mul]
        _ ≤ B * M := mul_le_mul (hB y) (hfM y hyP hyslab) (norm_nonneg _) hB0
  -- the Cauchy--Green solution
  have hei : (basisVec i : EuclideanSpace ℂ (Fin n)) ≠ 0 := by simp [basisVec]
  let u : EuclideanSpace ℂ (Fin n) → ℂ := cauchyGreen (basisVec i) g
  have hu : ContDiff ℝ ∞ u := contDiff_cauchyGreen hg hgc hei
  have hu_i : ∀ z, (∀ k, z k ∈ O k) → dbarDir (basisVec i) u z = dχ z * f z := by
    intro z hz
    rw [dbarDir_cauchyGreen (hg.of_le (by simp)) hgc hei z]
    simp [g, hψp1 z hz]
  have hg_k : ∀ k, k ≠ i → ∀ y : EuclideanSpace ℂ (Fin n), y k ∈ O k →
      dbarDir (basisVec k) g y = 0 := by
    intro k hk y hy
    by_cases hyU : y ∈ U
    · have hfy : DifferentiableAt ℂ f y := hf.differentiableAt (hU.mem_nhds hyU)
      have h1 : dbarDir (basisVec k) g y =
          dbarDir (basisVec k) (fun z => (ψp z : ℂ)) y * (dχ y * f y) +
            ψp y * dbarDir (basisVec k) (fun z => dχ z * f z) y :=
        dbarDir_ofReal_mul (hψp.differentiable (by simp) y)
          ((hdχ.differentiable (by simp) y).mul (hfy.restrictScalars ℝ))
      rw [h1, hψp_k k y hy, dbarDir_mul (hdχ.differentiable (by simp) y)
        (hfy.restrictScalars ℝ), hdχ_k k hk y, dbarDir_eq_zero_of_differentiableAt hfy]
      ring
    · exact (dbarDir_congr (hg0ev y hyU)).trans (dbarDir_const _ _)
  have hu_k : ∀ k, k ≠ i → ∀ z : EuclideanSpace ℂ (Fin n), z k ∈ O k →
      dbarDir (basisVec k) u z = 0 := by
    intro k hk z hz
    rw [dbarDir_cauchyGreen_comm (hg.of_le (by simp)) hgc hei]
    have hzero : ∀ w : ℂ, dbarDir (basisVec k) g (z - w • basisVec i) = 0 := by
      intro w
      refine hg_k k hk _ ?_
      have : (z - w • basisVec i) k = z k := by
        simp [basisVec, hk]
      rw [this]
      exact hz
    simp [cauchyGreen, hzero]
  -- the bound for `u`
  have hu_bound : ∀ z : EuclideanSpace ℂ (Fin n), z i ∈ O i → ‖u z‖ ≤ π⁻¹ * B * ID * M := by
    intro z hz
    have hzA : ‖z i‖ ≤ |R| := by
      have := hA (hOsub i hz)
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self R)
    have hpt : ∀ w : ℂ, ‖w⁻¹ • g (z - w • basisVec i)‖ ≤
        (ball (0 : ℂ) D).indicator (fun w => (B * M) * ‖w‖⁻¹) w := by
      intro w
      by_cases hw : w ∈ ball (0 : ℂ) D
      · rw [indicator_of_mem hw, norm_smul, norm_inv, mul_comm]
        exact mul_le_mul_of_nonneg_right (hgbound _) (inv_nonneg.2 (norm_nonneg _))
      · rw [indicator_of_notMem hw]
        have hgz : g (z - w • basisVec i) = 0 := by
          have hnot : z - w • basisVec i ∉ P := by
            intro hmem
            have h1 := hA (hmem i)
            rw [mem_closedBall, dist_zero_right] at h1
            have h2 : (z - w • basisVec i) i = z i - w := by
              simp [basisVec]
            rw [h2] at h1
            have h3 : ‖w‖ ≤ ‖z i‖ + ‖z i - w‖ := by
              calc ‖w‖ = ‖z i - (z i - w)‖ := by ring_nf
                _ ≤ ‖z i‖ + ‖z i - w‖ := norm_sub_le _ _
            rw [mem_ball, dist_zero_right, not_lt] at hw
            have : R ≤ |R| := le_abs_self R
            linarith
          simp [g, (hψp0 _ hnot).self_of_nhds]
        rw [hgz, smul_zero, norm_zero]
    have hint := integrable_indicator_inv_norm (B * M) D
    have hle := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    have hcomp : (∫ w : ℂ, (ball (0 : ℂ) D).indicator (fun w => (B * M) * ‖w‖⁻¹) w) =
        (B * M) * ID := by
      rw [hIDdef, ← integral_const_mul]
      congr 1
      funext w
      by_cases hw : w ∈ ball (0 : ℂ) D <;> simp [hw]
    rw [hcomp] at hle
    show ‖(π : ℂ)⁻¹ * ∫ w : ℂ, w⁻¹ • g (z - w • basisVec i)‖ ≤ π⁻¹ * B * ID * M
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
    calc π⁻¹ * ‖∫ w : ℂ, w⁻¹ • g (z - w • basisVec i)‖ ≤ π⁻¹ * ((B * M) * ID) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.2 Real.pi_pos.le)
      _ = π⁻¹ * B * ID * M := by ring
  -- the two halves
  let F' : EuclideanSpace ℂ (Fin n) → ℂ := fun z => ((1 - χ z : ℝ) : ℂ) * f z
  let F'' : EuclideanSpace ℂ (Fin n) → ℂ := fun z => -((χ z : ℂ) * f z)
  have hmemS : ∀ z, (∀ k, z k ∈ O k) → |L z - t| < δ → z ∈ U := fun z hz hzt =>
    hSU ⟨fun k => hOsub k (hz k), hzt⟩
  -- `F'` near points of the left half
  have hF'loc : ∀ z, (∀ k, z k ∈ O k) → L z < t + δ →
      ContDiffAt ℝ ∞ F' z ∧ dbarDir (basisVec i) F' z = -(dχ z * f z) ∧
        ∀ k, k ≠ i → dbarDir (basisVec k) F' z = 0 := by
    intro z hz hzt
    by_cases hcase : L z - t < -(δ / 2)
    · have hev : F' =ᶠ[𝓝 z] fun _ => 0 :=
        (hχone z hcase).mono fun y hy => by simp [F', hy]
      have hdz : dχ z = 0 := hdχ0 z (by rw [abs_of_neg (by linarith)]; linarith)
      refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, ?_, fun k _ => ?_⟩
      · rw [dbarDir_congr hev, dbarDir_const, hdz, zero_mul, neg_zero]
      · rw [dbarDir_congr hev, dbarDir_const]
    · have hzU : z ∈ U := hmemS z hz (by rw [abs_lt]; constructor <;> linarith)
      have hfy : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hzU)
      have h1c : ContDiff ℝ ∞ fun y => ((1 - χ y : ℝ) : ℂ) :=
        ofRealCLM.contDiff.comp (contDiff_const.sub hχ)
      refine ⟨h1c.contDiffAt.mul (hfC z hzU), ?_, fun k hk => ?_⟩
      · have h := dbarDir_ofReal_mul (v := basisVec i) (χ := fun y => 1 - χ y) (a := f) (x := z)
          ((contDiff_const.sub hχ).differentiable (by simp) z) (hfy.restrictScalars ℝ)
        rw [show F' = fun y => ((1 - χ y : ℝ) : ℂ) * f y from rfl, h,
          dbarDir_eq_zero_of_differentiableAt hfy]
        have hsub : dbarDir (basisVec i) (fun y => (((1 : ℝ) - χ y : ℝ) : ℂ)) z = -dχ z := by
          have h2 : (fun y => (((1 : ℝ) - χ y : ℝ) : ℂ)) = fun y => (1 : ℂ) - χc y := by
            funext y; push_cast; rfl
          rw [h2, dbarDir_sub (differentiableAt_const _) (hχc.differentiable (by simp) z),
            dbarDir_const]
          simp [dχ]
        rw [hsub]
        ring
      · have h := dbarDir_ofReal_mul (v := basisVec k) (χ := fun y => 1 - χ y) (a := f) (x := z)
          ((contDiff_const.sub hχ).differentiable (by simp) z) (hfy.restrictScalars ℝ)
        rw [show F' = fun y => ((1 - χ y : ℝ) : ℂ) * f y from rfl, h,
          dbarDir_eq_zero_of_differentiableAt hfy]
        have h2 : (fun y => (((1 : ℝ) - χ y : ℝ) : ℂ)) = fun y => (1 : ℂ) - χc y := by
          funext y; push_cast; rfl
        rw [h2, dbarDir_sub (differentiableAt_const _) (hχc.differentiable (by simp) z),
          dbarDir_const, hdχc_k k hk z]
        ring
  have hF''loc : ∀ z, (∀ k, z k ∈ O k) → t - δ < L z →
      ContDiffAt ℝ ∞ F'' z ∧ dbarDir (basisVec i) F'' z = -(dχ z * f z) ∧
        ∀ k, k ≠ i → dbarDir (basisVec k) F'' z = 0 := by
    intro z hz hzt
    by_cases hcase : δ / 2 < L z - t
    · have hev : F'' =ᶠ[𝓝 z] fun _ => 0 :=
        (hχzero z hcase).mono fun y hy => by simp [F'', hy]
      have hdz : dχ z = 0 := hdχ0 z (by rw [abs_of_pos (by linarith)]; exact hcase)
      refine ⟨contDiffAt_const.congr_of_eventuallyEq hev, ?_, fun k _ => ?_⟩
      · rw [dbarDir_congr hev, dbarDir_const, hdz, zero_mul, neg_zero]
      · rw [dbarDir_congr hev, dbarDir_const]
    · have hzU : z ∈ U := hmemS z hz (by rw [abs_lt]; constructor <;> linarith)
      have hfy : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hzU)
      have hprod : ∀ v, dbarDir v (fun y => (χ y : ℂ) * f y) z =
          dbarDir v χc z * f z + χ z * dbarDir v f z := fun v =>
        dbarDir_ofReal_mul (hχ.differentiable (by simp) z) (hfy.restrictScalars ℝ)
      have hneg : ∀ v, dbarDir v F'' z = -dbarDir v (fun y => (χ y : ℂ) * f y) z := by
        intro v
        have := dbarDir_sub (v := v) (differentiableAt_const (0 : ℂ))
          ((hχc.differentiable (by simp) z).mul (hfy.restrictScalars ℝ))
        simp only [zero_sub, dbarDir_const] at this
        exact this
      refine ⟨((contDiffAt_const (c := (-1 : ℂ))).mul
          (hχc.contDiffAt.mul (hfC z hzU))).congr_of_eventuallyEq
          (Eventually.of_forall fun y => by simp only [F'', χc]; ring), ?_, fun k hk => ?_⟩
      · rw [hneg, hprod, dbarDir_eq_zero_of_differentiableAt hfy]
        simp [dχ]
      · rw [hneg, hprod, dbarDir_eq_zero_of_differentiableAt hfy, hdχc_k k hk z]
        ring
  -- assembling
  have hOopen : IsOpen {z : EuclideanSpace ℂ (Fin n) | ∀ k, z k ∈ O k} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun k => (hO k).preimage (continuous_coord k)
  refine ⟨fun z => F' z + u z, fun z => F'' z + u z, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨hcd, hdi, hdk⟩ := hF'loc z hz.1 hz.2
    have hRd : DifferentiableAt ℝ (fun z => F' z + u z) z :=
      (hcd.differentiableAt (by simp)).add (hu.differentiable (by simp) z)
    refine (differentiableAt_of_dbarDir_basisVec hRd fun k => ?_).differentiableWithinAt
    rw [dbarDir_add (hcd.differentiableAt (by simp)) (hu.differentiable (by simp) z)]
    by_cases hk : k = i
    · subst hk
      rw [hdi, hu_i z hz.1]
      ring
    · rw [hdk k hk, hu_k k hk z (hz.1 k), add_zero]
  · intro z hz
    obtain ⟨hcd, hdi, hdk⟩ := hF''loc z hz.1 hz.2
    have hRd : DifferentiableAt ℝ (fun z => F'' z + u z) z :=
      (hcd.differentiableAt (by simp)).add (hu.differentiable (by simp) z)
    refine (differentiableAt_of_dbarDir_basisVec hRd fun k => ?_).differentiableWithinAt
    rw [dbarDir_add (hcd.differentiableAt (by simp)) (hu.differentiable (by simp) z)]
    by_cases hk : k = i
    · subst hk
      rw [hdi, hu_i z hz.1]
      ring
    · rw [hdk k hk, hu_k k hk z (hz.1 k), add_zero]
  · intro z
    simp only [F', F'']
    push_cast
    ring
  · intro z hz hzt
    have hF'b : ‖F' z‖ ≤ M := by
      by_cases hcase : L z - t < -(δ / 2)
      · have : χ z = 1 := (hχone z hcase).self_of_nhds
        simp [F', this, hM0]
      · have hzS : |L z - t| < δ := by rw [abs_lt]; constructor <;> linarith
        have hfz := hfM z (fun k => hOsub k (hz k)) hzS
        have h01 := hχ01 z
        calc ‖F' z‖ = |1 - χ z| * ‖f z‖ := by
              rw [show F' z = ((1 - χ z : ℝ) : ℂ) * f z from rfl, norm_mul, Complex.norm_real,
                Real.norm_eq_abs]
          _ ≤ 1 * M := mul_le_mul (by rw [abs_le]; constructor <;> linarith) hfz
              (norm_nonneg _) zero_le_one
          _ = M := one_mul M
    calc ‖F' z + u z‖ ≤ ‖F' z‖ + ‖u z‖ := norm_add_le _ _
      _ ≤ M + π⁻¹ * B * ID * M := add_le_add hF'b (hu_bound z (hz i))
      _ = (1 + π⁻¹ * B * ID) * M := by ring
  · intro z hz hzt
    have hF''b : ‖F'' z‖ ≤ M := by
      by_cases hcase : δ / 2 < L z - t
      · have : χ z = 0 := (hχzero z hcase).self_of_nhds
        simp [F'', this, hM0]
      · have hzS : |L z - t| < δ := by rw [abs_lt]; constructor <;> linarith
        have hfz := hfM z (fun k => hOsub k (hz k)) hzS
        have h01 := hχ01 z
        calc ‖F'' z‖ = |χ z| * ‖f z‖ := by
              rw [show F'' z = -((χ z : ℂ) * f z) from rfl, norm_neg, norm_mul, Complex.norm_real,
                Real.norm_eq_abs]
          _ ≤ 1 * M := mul_le_mul (by rw [abs_le]; constructor <;> linarith) hfz
              (norm_nonneg _) zero_le_one
          _ = M := one_mul M
    calc ‖F'' z + u z‖ ≤ ‖F'' z‖ + ‖u z‖ := norm_add_le _ _
      _ ≤ M + π⁻¹ * B * ID * M := add_le_add hF''b (hu_bound z (hz i))
      _ = (1 + π⁻¹ * B * ID) * M := by ring


end

end Hironaka.Analytic.GAGA.Core.Cousin
