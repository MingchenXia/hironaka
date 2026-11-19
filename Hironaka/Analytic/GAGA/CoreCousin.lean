import Hironaka.Analytic.DolbeaultLemma
import Hironaka.Analytic.WeakDbarWeyl
import Hironaka.Manifold.HolomorphicContDiff
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Cousin I across a real hyperplane, with parameters and bounds

Infrastructure of lane SERRE-CORE (Serre's GAGA, towards source `lma:GAGA`), step M2.1 of the
plan in `blueprint/src/claude-serre-core.tex`. Source for the mathematics: the additive Cousin
problem for adjacent compact product sets (Gunning--Rossi, *Analytic functions of several
complex variables*, I.D and VI.D; Grauert--Remmert, *Theory of Stein spaces*, III §1),
solved here with the one-variable Cauchy--Green operator of `Hironaka`.

Let `ψ_k : ℂ → ℝ` be smooth compactly supported cutoffs, equal to `1` on open sets `O_k`, and
let `L(z) = Re(θ z_i)`. A function `f` holomorphic near
`S = {z : z_k ∈ tsupport ψ_k ∀ k, |L z - t| ≤ δ}` and bounded by `M` there splits as
`f = f' - f''` with `f'` holomorphic on `{z_k ∈ O_k ∀ k, L z < t + δ}` and `f''` holomorphic on
`{z_k ∈ O_k ∀ k, L z > t - δ}`, both bounded by `C M`, where `C` depends only on the cutoffs
and on `(i, θ, t, δ)` (`exists_cousin_split`). The germ form for compact product sets
`Q = {z : z_k ∈ C_k}` (`exists_cousin_split_compact`): a function holomorphic near the slice
`Q ∩ {Re(θ z_i) = t}` is `f' - f''` near the slice, with `f'` holomorphic near
`Q ∩ {Re(θ z_i) ≤ t}` and `f''` holomorphic near `Q ∩ {Re(θ z_i) ≥ t}`; smooth cutoffs come
from the smooth Urysohn lemma (`exists_cutoff`).

Construction: `χ = χ₀(L - t)` passes from `1` to `0` across the slab `|L - t| ≤ δ/2`. Put
`g = ψ · ∂̄_i χ · f`, a smooth compactly supported function (the factor `∂̄_i χ` vanishes off
the slab and `ψ = ∏ ψ_k(z_k)` off `∏ tsupport ψ_k`), and `u = T_i g` (Cauchy--Green operator in
the variable `z_i`). Then `f' = (1 - χ) f + u` and `f'' = -χ f + u`: on `{z_k ∈ O_k}` we have
`∂̄_i u = g = ∂̄_i χ · f`, and `∂̄_k u = T_i (∂̄_k g) = 0` for `k ≠ i`, because along the line
`z - w e_i` the cutoff `ψ` does not depend on `z_k` and `f` is holomorphic.
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

/-! ### Wirtinger derivatives -/

section Wirtinger

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Holomorphic functions have vanishing `∂̄`. -/
theorem dbarDir_eq_zero_of_differentiableAt {f : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x)
    (v : E) : dbarDir v f x = 0 := by
  have h : fderiv ℝ f x = (fderiv ℂ f x).restrictScalars ℝ := hf.fderiv_restrictScalars ℝ
  simp only [dbarDir, h, ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  rw [← mul_assoc, I_mul_I]
  ring

/-- The product rule for `∂̄`. -/
theorem dbarDir_mul {v : E} {a b : E → ℂ} {x : E} (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    dbarDir v (fun y => a y * b y) x = dbarDir v a x * b x + a x * dbarDir v b x := by
  simp only [dbarDir, fderiv_fun_mul ha hb, add_apply,
    smul_apply, smul_eq_mul]
  ring

/-- A function invariant under real translations in the directions `v` and `I v` has
vanishing `∂̄_v`. -/
theorem dbarDir_eq_zero_of_invariant {F : E → ℂ} {v : E}
    (h₁ : ∀ z (s : ℝ), F (z + s • v) = F z) (h₂ : ∀ z (s : ℝ), F (z + s • (I • v)) = F z)
    (x : E) : dbarDir v F x = 0 := by
  simp only [dbarDir, fderiv_apply_eq_zero_of_invariant h₁ x,
    fderiv_apply_eq_zero_of_invariant h₂ x, mul_zero, add_zero, zero_div]

theorem dbarDir_smul_dir (c : ℂ) (u : E) (f : E → ℂ) (x : E) :
    dbarDir (c • u) f x = (starRingEnd ℂ) c * dbarDir u f x := by
  have hc : c • u = (c.re : ℝ) • u + (c.im : ℝ) • (I • u) := by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
  rw [hc, dbarDir_add_dir, dbarDir_real_smul_dir, dbarDir_real_smul_dir, dbarDir_I_smul_dir,
    show (starRingEnd ℂ) c = c.re - c.im * I from by apply Complex.ext <;> simp]
  ring

end Wirtinger

/-- **Holomorphy from the coordinate `∂̄`-equations.** -/
theorem differentiableAt_of_dbarDir_basisVec {f : EuclideanSpace ℂ (Fin n) → ℂ}
    {x : EuclideanSpace ℂ (Fin n)} (hf : DifferentiableAt ℝ f x)
    (h : ∀ k, dbarDir (basisVec k) f x = 0) : DifferentiableAt ℂ f x := by
  classical
  refine differentiableAt_complex_of_dbarDir_eq_zero hf fun v => ?_
  have hv := (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr v
  simp only [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] at hv
  have hsum : ∀ s : Finset (Fin n),
      dbarDir (∑ k ∈ s, v k • EuclideanSpace.single k (1 : ℂ)) f x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [dbarDir]
    | insert k s hk ih =>
        rw [Finset.sum_insert hk, dbarDir_add_dir, ih, dbarDir_smul_dir]
        have := h k
        simp only [basisVec] at this
        rw [this]
        ring
  rw [← hv]
  exact hsum Finset.univ

/-! ### Coordinates -/

theorem coord_add_smul_single {z : EuclideanSpace ℂ (Fin n)} {s : ℝ} {c : ℂ} {k l : Fin n}
    (h : l ≠ k) : (z + s • (c • EuclideanSpace.single k (1 : ℂ))) l = z l := by
  simp [h]

theorem continuous_coord (k : Fin n) :
    Continuous fun z : EuclideanSpace ℂ (Fin n) => z k :=
  (EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).continuous

theorem contDiff_coord (k : Fin n) :
    ContDiff ℝ ∞ fun z : EuclideanSpace ℂ (Fin n) => z k :=
  ((EuclideanSpace.proj k : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).restrictScalars ℝ).contDiff

/-- The compact product of the supports. -/
theorem isCompact_coord_pi {K : Fin n → Set ℂ} (hK : ∀ k, IsCompact (K k)) :
    IsCompact {z : EuclideanSpace ℂ (Fin n) | ∀ k, z k ∈ K k} := by
  have h : IsCompact ((EuclideanSpace.equiv (Fin n) ℂ).toHomeomorph ⁻¹' (Set.univ.pi K)) :=
    (EuclideanSpace.equiv (Fin n) ℂ).toHomeomorph.isCompact_preimage.2 (isCompact_univ_pi hK)
  convert h using 1
  ext z
  simp

/-! ### The splitting -/

/-- **Cousin I across the hyperplane `Re(θ z_i) = t`, with bounds.** -/
theorem exists_cousin_split (i : Fin n) (θ : ℂ) (t δ : ℝ) (hδ : 0 < δ)
    (ψ : Fin n → ℂ → ℝ) (hψ : ∀ k, ContDiff ℝ ∞ (ψ k)) (hψc : ∀ k, HasCompactSupport (ψ k))
    (O : Fin n → Set ℂ) (hO : ∀ k, IsOpen (O k)) (hψO : ∀ k, ∀ w ∈ O k, ψ k w = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Set (EuclideanSpace ℂ (Fin n))) (f : EuclideanSpace ℂ (Fin n) → ℂ)
      (M : ℝ), IsOpen U → DifferentiableOn ℂ f U →
      {z | (∀ k, z k ∈ tsupport (ψ k)) ∧ |(θ * z i).re - t| ≤ δ} ⊆ U →
      (∀ z, (∀ k, z k ∈ tsupport (ψ k)) → |(θ * z i).re - t| ≤ δ → ‖f z‖ ≤ M) → 0 ≤ M →
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
  have hΘc : Continuous fun z => (ψp z : ℂ) * dχ z :=
    (continuous_ofReal.comp hψp.continuous).mul hdχ.continuous
  have hΘs : HasCompactSupport fun z => (ψp z : ℂ) * dχ z := by
    refine HasCompactSupport.intro hPc fun z hz => ?_
    simp [(hψp0 z hz).self_of_nhds]
  obtain ⟨B₀, hB₀⟩ := hΘs.exists_bound_of_continuous hΘc
  set B : ℝ := max B₀ 0 with hBdef
  have hB : ∀ z, ‖(ψp z : ℂ) * dχ z‖ ≤ B := fun z => (hB₀ z).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  -- the radius for the Cauchy--Green integral
  obtain ⟨A, hA⟩ := (hψc i).isCompact.isBounded.subset_closedBall 0
  set D : ℝ := 2 * |A| + 1 with hDdef
  set ID : ℝ := ∫ w : ℂ, (ball (0 : ℂ) D).indicator (fun w => ‖w‖⁻¹) w with hIDdef
  have hID0 : 0 ≤ ID := integral_nonneg fun w => by
    by_cases hw : w ∈ ball (0 : ℂ) D <;> simp [hw]
  refine ⟨1 + π⁻¹ * B * ID, by positivity, ?_⟩
  intro U f M hU hf hSU hfM hM0
  set S : Set (EuclideanSpace ℂ (Fin n)) :=
    {z | (∀ k, z k ∈ tsupport (ψ k)) ∧ |(θ * z i).re - t| ≤ δ} with hSdef
  have hfC : ∀ z ∈ U, ContDiffAt ℝ ∞ f z := fun z hz =>
    contDiffAt_real_of_differentiableOn_complex hf hU hz
  -- the right-hand side `g = ψ ∂̄_i χ f`
  let g : EuclideanSpace ℂ (Fin n) → ℂ := fun z => (ψp z : ℂ) * (dχ z * f z)
  have hg0ev : ∀ z, z ∉ U → g =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    have hzS : z ∉ S := fun h => hz (hSU h)
    simp only [hSdef, mem_ofPred_eq, not_and_or, not_le] at hzS
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
      have hyslab : |L y - t| ≤ δ := by
        by_contra hy
        exact h0 (by rw [hdχ0 y (by linarith [not_le.1 hy]), mul_zero])
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
    have hzA : ‖z i‖ ≤ |A| := by
      have := hA (hOsub i hz)
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self A)
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
            have : A ≤ |A| := le_abs_self A
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
    hSU ⟨fun k => hOsub k (hz k), hzt.le⟩
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
      · have hzS : |L z - t| ≤ δ := by rw [abs_le]; constructor <;> linarith
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
      · have hzS : |L z - t| ≤ δ := by rw [abs_le]; constructor <;> linarith
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

/-! ### Smooth cutoffs and the germ form of the splitting -/

/-- A smooth cutoff on `ℂ` equal to `1` on the `ε/2`-neighbourhood of a compact set and
supported in its closed `ε`-neighbourhood. -/
theorem exists_cutoff {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ w ∈ thickening (ε / 2) K, ψ w = 1) ∧ tsupport ψ ⊆ cthickening ε K := by
  have hd : Disjoint (thickening ε K)ᶜ (cthickening (ε / 2) K) := by
    rw [disjoint_compl_left_iff_subset]
    exact cthickening_subset_thickening' hε (by linarith) K
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed (n := ⊤) 𝓘(ℝ, ℂ)
    isOpen_thickening.isClosed_compl isClosed_cthickening hd
  have hsupp : tsupport f ⊆ cthickening ε K := by
    refine (closure_mono fun w hw => ?_).trans (closure_thickening_subset_cthickening ε K)
    by_contra hw'
    exact hw (hf0 hw')
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, ?_, fun w hw =>
    hf1 (thickening_subset_cthickening _ _ hw), hsupp⟩
  exact IsCompact.of_isClosed_subset (hK.cthickening) (isClosed_tsupport _) hsupp

/-- **Cousin I for compact product sets (germ form).** Let `C_k ⊆ ℂ` be compact and
`Q = {z : z_k ∈ C_k ∀ k}`. A function holomorphic near the slice `Q ∩ {Re(θ z_i) = t}` is the
difference of a function holomorphic near `Q ∩ {Re(θ z_i) ≤ t}` and one holomorphic near
`Q ∩ {Re(θ z_i) ≥ t}`. -/
theorem exists_cousin_split_compact (i : Fin n) (θ : ℂ) (t : ℝ) {C : Fin n → Set ℂ}
    (hC : ∀ k, IsCompact (C k)) {W : Set (EuclideanSpace ℂ (Fin n))} (hW : IsOpen W)
    {f : EuclideanSpace ℂ (Fin n) → ℂ} (hf : DifferentiableOn ℂ f W)
    (hFW : {z : EuclideanSpace ℂ (Fin n) | (∀ k, z k ∈ C k) ∧ (θ * z i).re = t} ⊆ W) :
    ∃ W' W'' : Set (EuclideanSpace ℂ (Fin n)), IsOpen W' ∧ IsOpen W'' ∧
      {z | (∀ k, z k ∈ C k) ∧ (θ * z i).re ≤ t} ⊆ W' ∧
      {z | (∀ k, z k ∈ C k) ∧ t ≤ (θ * z i).re} ⊆ W'' ∧
      ∃ f' f'' : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ f' W' ∧
        DifferentiableOn ℂ f'' W'' ∧ ∀ z ∈ W' ∩ W'', f z = f' z - f'' z := by
  classical
  -- a product neighbourhood of the slice inside `W`
  let V : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun m =>
    {z | (∀ k, z k ∈ cthickening (1 / ((m : ℝ) + 1)) (C k)) ∧
      |(θ * z i).re - t| ≤ 1 / ((m : ℝ) + 1)}
  have hLc : Continuous fun z : EuclideanSpace ℂ (Fin n) => (θ * z i).re :=
    continuous_re.comp (continuous_const.mul (continuous_coord i))
  have hVc : ∀ m, IsCompact (V m) := by
    intro m
    refine (isCompact_coord_pi fun k => (hC k).cthickening).of_isClosed_subset ?_
      fun z hz => hz.1
    have h1 : IsClosed {z : EuclideanSpace ℂ (Fin n) |
        ∀ k, z k ∈ cthickening (1 / ((m : ℝ) + 1)) (C k)} := by
      simp only [ofPred_forall]
      exact isClosed_iInter fun k => isClosed_cthickening.preimage (continuous_coord k)
    exact h1.inter (isClosed_le (continuous_abs.comp (hLc.sub continuous_const))
      continuous_const)
  have hVd : Directed (· ⊇ ·) V := by
    refine directed_of_isDirected_le fun m m' hmm' => ?_
    have hle : 1 / ((m' : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmm' 1)
    intro z hz
    exact ⟨fun k => cthickening_mono hle _ (hz.1 k), hz.2.trans hle⟩
  have hVW : ∀ x ∈ ⋂ m, V m, W ∈ 𝓝 x := by
    intro x hx
    rw [mem_iInter] at hx
    refine hW.mem_nhds (hFW ⟨fun k => ?_, ?_⟩)
    · rw [← (hC k).isClosed.closure_eq, closure_eq_iInter_cthickening]
      simp only [mem_iInter]
      intro δ hδ
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      exact cthickening_mono hm.le _ ((hx m).1 k)
    · by_contra hne
      have hpos : 0 < |(θ * x i).re - t| := abs_pos.2 (sub_ne_zero.2 hne)
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
      exact absurd (hx m).2 (not_le.2 hm)
  obtain ⟨m, hmW⟩ := exists_subset_nhds_of_isCompact hVd hVc hVW
  set ε : ℝ := 1 / ((m : ℝ) + 1) with hεdef
  have hε : 0 < ε := by positivity
  -- cutoffs
  choose ψ hψ hψc hψ1 hψs using fun k => exists_cutoff (hC k) hε
  obtain ⟨Cst, -, hsplit⟩ := exists_cousin_split i θ t ε hε ψ hψ hψc
    (fun k => thickening (ε / 2) (C k)) (fun _ => isOpen_thickening) hψ1
  have hSV : {z : EuclideanSpace ℂ (Fin n) | (∀ k, z k ∈ tsupport (ψ k)) ∧
      |(θ * z i).re - t| ≤ ε} ⊆ W :=
    fun z hz => hmW ⟨fun k => hψs k (hz.1 k), hz.2⟩
  obtain ⟨M, hM⟩ := (hVc m).exists_bound_of_continuousOn
    (hf.continuousOn.mono fun z hz => hmW hz)
  obtain ⟨f', f'', hf', hf'', heq, -, -⟩ := hsplit W f (max M 0) hW hf hSV
    (fun z hz1 hz2 => (hM z ⟨fun k => hψs k (hz1 k), hz2⟩).trans (le_max_left _ _))
    (le_max_right _ _)
  have hOopen : IsOpen {z : EuclideanSpace ℂ (Fin n) | ∀ k, z k ∈ thickening (ε / 2) (C k)} := by
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun k => isOpen_thickening.preimage (continuous_coord k)
  refine ⟨_, _, hOopen.inter (isOpen_lt hLc continuous_const),
    hOopen.inter (isOpen_lt continuous_const hLc), fun z hz => ⟨?_, ?_⟩, fun z hz => ⟨?_, ?_⟩,
    f', f'', hf', hf'', fun z _ => heq z⟩
  · exact fun k => self_subset_thickening (by positivity) _ (hz.1 k)
  · show (θ * z i).re < t + ε
    linarith [hz.2]
  · exact fun k => self_subset_thickening (by positivity) _ (hz.1 k)
  · show t - ε < (θ * z i).re
    linarith [hz.2]

end

end Hironaka.Analytic.GAGA.Core.Cousin
