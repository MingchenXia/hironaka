/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.LastVariableTaylorDivision
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Division by coordinates of holomorphic functions vanishing on a coordinate plane

* `exists_eq_coord_mul`: a function holomorphic near `q`, with `q i = 0`, vanishing near `q`
  on the hyperplane `{u i = 0}`, is `u i * H u` near `q` with `H` holomorphic.  This is
  `lastQuot` (Taylor division by `t`) in the variable `u i`.
* `exists_eq_sum_coord_mul`: (Hadamard) a function holomorphic near `q ∈ ℂᵏ × 0`, vanishing
  near `q` on `ℂᵏ × 0`, is `∑_{i ≥ k} u i * Hᵢ u` near `q` with `Hᵢ` holomorphic.
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka.CoordinatePlaneDivision

noncomputable section

variable {n : ℕ}

/-- `v` with its `i`-th coordinate replaced by `t`. -/
def setCoord (v : ComplexModel n) (i : Fin n) (t : ℂ) : ComplexModel n :=
  v + (t - v i) • EuclideanSpace.single i (1 : ℂ)

@[simp] theorem setCoord_apply (v : ComplexModel n) (i j : Fin n) (t : ℂ) :
    setCoord v i t j = if j = i then t else v j := by
  by_cases h : j = i
  · subst h; simp [setCoord]
  · simp [setCoord, h]

theorem setCoord_self (v : ComplexModel n) (i : Fin n) : setCoord v i (v i) = v := by
  simp [setCoord]

theorem norm_setCoord_sub_le (v : ComplexModel n) (i : Fin n) (t : ℂ) :
    ‖setCoord v i t - v‖ ≤ ‖t - v i‖ := by
  simp [setCoord, norm_smul]

theorem differentiable_setCoord (i : Fin n) :
    Differentiable ℂ (fun x : ComplexModel n × ℂ => setCoord x.1 i x.2) := by
  have hp : Differentiable ℂ (fun x : ComplexModel n × ℂ => x.1 i) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiable.comp differentiable_fst
  unfold setCoord
  exact differentiable_fst.add ((differentiable_snd.sub hp).smul_const _)

theorem norm_apply_le (v : ComplexModel n) (i : Fin n) : ‖v i‖ ≤ ‖v‖ :=
  PiLp.norm_apply_le v i

/-- Division by one coordinate. -/
theorem exists_eq_coord_mul {G : ComplexModel n → ℂ} {q : ComplexModel n} {i : Fin n}
    (hG : ∀ᶠ u in 𝓝 q, DifferentiableAt ℂ G u) (hq : q i = 0)
    (hvan : ∀ᶠ u in 𝓝 q, u i = 0 → G u = 0) :
    ∃ H : ComplexModel n → ℂ, (∀ᶠ u in 𝓝 q, DifferentiableAt ℂ H u) ∧
      ∀ᶠ u in 𝓝 q, G u = u i * H u := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hG.and hvan)
  set h : ComplexModel n × ℂ → ℂ := fun x => G (setCoord (q + x.1) i x.2) with h_def
  set D : Set (ComplexModel n × ℂ) := ball (0 : ComplexModel n) (ε / 4) ×ˢ ball (0 : ℂ) (ε / 4)
  have hDopen : IsOpen D := isOpen_ball.prod isOpen_ball
  have hmem : ∀ x ∈ D, setCoord (q + x.1) i x.2 ∈ ball q ε := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    rw [mem_ball_zero_iff] at hx ht
    rw [mem_ball, dist_eq_norm]
    have h1 := norm_setCoord_sub_le (q + x) i t
    have h2 : ‖(q + x) i‖ ≤ ‖x‖ := by
      simpa [hq] using norm_apply_le x i
    calc ‖setCoord (q + x) i t - q‖
        = ‖(setCoord (q + x) i t - (q + x)) + x‖ := by congr 1; abel
      _ ≤ ‖setCoord (q + x) i t - (q + x)‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ‖t - (q + x) i‖ + ‖x‖ := by gcongr
      _ ≤ (‖t‖ + ‖(q + x) i‖) + ‖x‖ := by gcongr; exact norm_sub_le _ _
      _ < ε := by linarith
  have hh : DifferentiableOn ℂ h D := fun x hx =>
    ((hball _ (hmem x hx)).1.comp x ((differentiable_setCoord i).comp
      ((differentiable_const q).add differentiable_fst |>.prodMk differentiable_snd) x)
      |>.differentiableWithinAt)
  have hρ : (0 : ℝ) < ε / 8 := by positivity
  have hρR : ε / 8 < ε / 4 := by linarith
  have hsplit := eq_lastQuot_mul_add hρ hρR hh 1
  have hcoeff : ∀ z ∈ ball (0 : ComplexModel n) (ε / 4), lastCoeff h (ε / 8) 0 z = 0 := by
    intro z hz
    have hz0 : (z, (0 : ℂ)) ∈ D := ⟨hz, mem_ball_self (by positivity)⟩
    have := hsplit (z, 0) hz0
    have hzero : h (z, 0) = 0 := by
      refine (hball _ (hmem _ hz0)).2 ?_
      simp
    simpa [hzero] using this.symm
  refine ⟨fun u => lastQuot h (ε / 8) 1 (u - q, u i), ?_, ?_⟩
  · have hmap : ∀ u ∈ ball q (ε / 4), (u - q, u i) ∈ D := by
      intro u hu
      rw [mem_ball, dist_eq_norm] at hu
      refine ⟨mem_ball_zero_iff.mpr hu, mem_ball_zero_iff.mpr ?_⟩
      have := norm_apply_le (u - q) i
      simp only [PiLp.sub_apply, hq, sub_zero] at this
      linarith
    filter_upwards [ball_mem_nhds q (by positivity : (0 : ℝ) < ε / 4)] with u hu
    have hdiff : DifferentiableAt ℂ (fun u : ComplexModel n => (u - q, u i)) u :=
      (differentiableAt_id.sub_const q).prodMk
        (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
    exact ((differentiableOn_lastQuot hρ hρR hh 1).differentiableAt
      (hDopen.mem_nhds (hmap u hu))).comp u hdiff
  · filter_upwards [ball_mem_nhds q (by positivity : (0 : ℝ) < ε / 4)] with u hu
    rw [mem_ball, dist_eq_norm] at hu
    have hui : ‖u i‖ < ε / 4 := by
      have := norm_apply_le (u - q) i
      simp only [PiLp.sub_apply, hq, sub_zero] at this
      linarith
    have hx : (u - q, u i) ∈ D := ⟨mem_ball_zero_iff.mpr hu, mem_ball_zero_iff.mpr hui⟩
    have := hsplit _ hx
    simp only [Finset.sum_range_one, pow_zero, mul_one, pow_one,
      hcoeff _ (mem_ball_zero_iff.mpr hu), add_zero] at this
    simp only [h_def, add_sub_cancel, setCoord_self] at this
    rw [this, mul_comm]

theorem norm_setCoord_zero_sub_le {v q : ComplexModel n} {i : Fin n} (hq : q i = 0) :
    ‖setCoord v i 0 - q‖ ≤ ‖v - q‖ := by
  have h1 : setCoord v i 0 - q = setCoord (v - q) i 0 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [hq]
    · simp [hj]
  rw [h1]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun l _ => ?_)
  by_cases hl : l = i
  · subst hl; simp
  · simp [hl]

/-- **Hadamard's lemma for a coordinate plane.**  A function holomorphic near a point `q` of
`ℂʲ × 0` and vanishing near `q` on `ℂʲ × 0` is a holomorphic combination of the coordinates
`u i`, `i ≥ j`. -/
theorem exists_eq_sum_coord_mul (d : ℕ) :
    ∀ (j : ℕ), n - j = d → ∀ {F : ComplexModel n → ℂ} {q : ComplexModel n},
      q ∈ complexCoordinatePlane n j →
      (∀ᶠ u in 𝓝 q, DifferentiableAt ℂ F u) →
      (∀ᶠ u in 𝓝 q, u ∈ complexCoordinatePlane n j → F u = 0) →
      ∃ H : Fin n → ComplexModel n → ℂ, (∀ i : Fin n, i.1 < j → H i = 0) ∧
        (∀ i, ∀ᶠ u in 𝓝 q, DifferentiableAt ℂ (H i) u) ∧
        ∀ᶠ u in 𝓝 q, F u = ∑ i, u i * H i u := by
  induction d with
  | zero =>
    intro j hj F q _ _ hvan
    refine ⟨fun _ _ => 0, fun _ _ => rfl, fun _ => Eventually.of_forall fun _ =>
      differentiableAt_const _, ?_⟩
    filter_upwards [hvan] with u hu
    have : u ∈ complexCoordinatePlane n j := fun i hi => absurd i.2 (by omega)
    simp [hu this]
  | succ d ih =>
    intro j hj F q hq hF hvan
    have hjn : j < n := by omega
    set k : Fin n := ⟨j, hjn⟩
    have hqk : q k = 0 := hq k le_rfl
    set F' : ComplexModel n → ℂ := fun u => F (setCoord u k 0)
    have hnear : Tendsto (fun u => setCoord u k 0) (𝓝 q) (𝓝 q) := by
      rw [Metric.tendsto_nhds_nhds]
      exact fun ε hε => ⟨ε, hε, fun {u} hu => by
        rw [dist_eq_norm] at hu ⊢; exact (norm_setCoord_zero_sub_le hqk).trans_lt hu⟩
    have hdiffset : Differentiable ℂ (fun u : ComplexModel n => setCoord u k 0) :=
      (differentiable_setCoord k).comp (differentiable_id.prodMk (differentiable_const 0))
    have hF' : ∀ᶠ u in 𝓝 q, DifferentiableAt ℂ F' u := by
      filter_upwards [hnear.eventually hF] with u hu
      exact hu.comp u (hdiffset u)
    -- `F - F'` vanishes on `u k = 0`
    obtain ⟨Hk, hHk, hHkeq⟩ := exists_eq_coord_mul (G := fun u => F u - F' u) (i := k)
      (hF.and hF' |>.mono fun u hu => hu.1.sub hu.2) hqk
      (Eventually.of_forall fun u hu => by
        simp only [F', sub_eq_zero]
        rw [← hu, setCoord_self])
    -- `F'` vanishes on the smaller plane
    have hq' : q ∈ complexCoordinatePlane n (j + 1) := fun i hi => hq i (by omega)
    obtain ⟨H', hH'0, hH'd, hH'eq⟩ := ih (j + 1) (by omega) hq' hF' (by
      filter_upwards [hnear.eventually hvan] with u hu hmem
      refine hu fun i hi => ?_
      by_cases hik : i = k
      · subst hik; simp
      · simp only [setCoord_apply, hik, if_false]
        exact hmem i (by
          have : i.1 ≠ j := fun h => hik (Fin.ext h)
          omega))
    refine ⟨Function.update H' k Hk, fun i hi => ?_, fun i => ?_, ?_⟩
    · have hik : i ≠ k := fun h => by subst h; simp [k] at hi
      rw [Function.update_of_ne hik]
      exact hH'0 i (by omega)
    · by_cases hik : i = k
      · subst hik; simpa using hHk
      · simpa [Function.update_of_ne hik] using hH'd i
    · filter_upwards [hHkeq, hH'eq] with u h1 h2
      have hsum : ∑ i, u i * Function.update H' k Hk i u =
          u k * Hk u + ∑ i, u i * H' i u := by
        rw [← Finset.add_sum_erase (a := k) _ _ (Finset.mem_univ k),
          ← Finset.add_sum_erase (a := k) _ (fun i => u i * H' i u) (Finset.mem_univ k)]
        simp only [Function.update_self]
        rw [hH'0 k (by simp [k]), Pi.zero_apply, mul_zero, zero_add]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
      rw [hsum, ← h1, ← h2]
      ring

end

end Hironaka.CoordinatePlaneDivision
