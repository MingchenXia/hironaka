import Hironaka.Analytic.SingularLocus

set_option autoImplicit false

/-!
# A positive Lelong number forces a pole

Source: Demailly, *Complex analytic and differential geometry*, III.5–III.6
(a plurisubharmonic function bounded above by `γ log|z - x| + O(1)` on a
punctured neighbourhood of `x` has the value `-∞` at `x` for `γ > 0`);
Copy-4, `sec:nK`.

`lelongNumber u x` is the supremum of the `γ ≥ 0` for which `u` is bounded above
by `γ log‖z - x‖ + C` on some punctured neighbourhood of `x`, computed in the
preferred holomorphic chart at `x`.  The only consequence needed here is

* `eq_bot_of_lelongNumber_pos`: for a theta-plurisubharmonic potential `u` on a
  complex manifold of positive dimension, `0 < lelongNumber u x` implies
  `u x = ⊥`.

The proof is the classical circle-mean argument, run against the workspace's
extended-real disc criterion `DiscPshOn`: the local psh representative
`v = u + ρ` satisfies the submean inequality on a complex line through `x`, the
circle of radius `r` lies in the punctured neighbourhood where the logarithmic
bound holds, so the angular deficit of `v` is at least
`2π (C₁ - γ log r - C - B)`, which is unbounded as `r ↓ 0`.  The submean
inequality bounds it by `2π (C₁ - v(x))`, so `v(x) = ⊥`.

Positive dimension is genuinely needed: for `n = 0` the punctured neighbourhood
filter is `⊥`, so every `γ` is admissible and `lelongNumber u x = ⊤` for every
`u`.

The consumers are `Hironaka.LocusProperties.nonKahlerLocus_ne_univ` (a Kähler
current has a point with a finite potential value, which therefore has Lelong
number zero) and, through it, the properness of `E_nK(α)`.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace Hironaka

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- The logarithmic bound witnessing a positive Lelong number, with a positive
real coefficient. -/
theorem exists_log_bound_of_lelongNumber_pos {u : M → EReal} {x : M}
    (h : 0 < lelongNumber (n := n) u x) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
      u y ≤ ((γ * Real.log
        ‖(complexChartAt (n := n) x).val y -
          (complexChartAt (n := n) x).val x‖ + C : ℝ) : EReal) := by
  rw [lelongNumber, lt_iSup_iff] at h
  obtain ⟨γ, hγ⟩ := h
  rw [lt_iSup_iff] at hγ
  obtain ⟨⟨C, hC⟩, hpos⟩ := hγ
  refine ⟨(γ : ℝ), ?_, C, hC⟩
  exact_mod_cast (ENNReal.coe_pos.mp hpos)

/-- **A positive Lelong number forces a pole.** -/
theorem eq_bot_of_lelongNumber_pos (hn : 0 < n) {θ : SmoothRealForm n M 2}
    {u : M → EReal} (hu : ThetaPlurisubharmonic θ u) {x : M}
    (hx : 0 < lelongNumber (n := n) u x) : u x = ⊥ := by
  classical
  obtain ⟨γ, hγ, C, hev⟩ := exists_log_bound_of_lelongNumber_pos hx
  set e := complexChartAt (n := n) x with he
  have hxsrc : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ := e.val x with hz₀def
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source hxsrc
  obtain ⟨W, ρ, hz₀W, hρ, hpsh⟩ := hu e z₀ hz₀
  set v : ComplexModel n → EReal := fun z => chartFunction u e z + (ρ z : EReal) with hv
  obtain ⟨U, hUopen, hz₀U, hdisc⟩ := hpsh z₀ hz₀W
  -- Transfer the logarithmic bound into the chart.
  obtain ⟨V, hVopen, hxV, hV⟩ : ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, y ≠ x → u y ≤ ((γ * Real.log ‖e.val y - z₀‖ + C : ℝ) : EReal) := by
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨V, hVsub, hVopen, hxV⟩ := eventually_nhds_iff.mp hev
    exact ⟨V, hVopen, hxV, fun y hy hyx => hVsub y hy hyx⟩
  set O : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' V with hO
  have hOopen : IsOpen O := e.val.isOpen_inter_preimage_symm hVopen
  have hz₀O : z₀ ∈ O := ⟨hz₀, by
    simp only [mem_preimage, hz₀def, e.val.left_inv hxsrc]
    exact hxV⟩
  have hObound : ∀ z ∈ O, z ≠ z₀ →
      chartFunction u e z ≤ ((γ * Real.log ‖z - z₀‖ + C : ℝ) : EReal) := by
    intro z hz hzz₀
    have hsymm : e.val.symm z ≠ x := by
      intro hcontra
      apply hzz₀
      rw [← e.val.right_inv hz.1, hcontra, hz₀def]
    have := hV (e.val.symm z) hz.2 hsymm
    rwa [e.val.right_inv hz.1] at this
  -- A compact coordinate ball inside all the relevant open sets.
  set G : Set (ComplexModel n) := U ∩ W ∩ O with hG
  have hGopen : IsOpen G := (hUopen.inter hρ.1).inter hOopen
  have hz₀G : z₀ ∈ G := ⟨⟨hz₀U, hz₀W⟩, hz₀O⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hGopen z₀ hz₀G
  set r₀ := δ / 2 with hr₀def
  have hr₀ : 0 < r₀ := half_pos hδ
  have hclosed : closedBall z₀ r₀ ⊆ G := fun z hz =>
    hball (by
      refine lt_of_le_of_lt (Metric.mem_closedBall.mp hz) ?_
      rw [hr₀def]
      linarith)
  -- A unit direction; this is where `0 < n` is used.
  set w : ComplexModel n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℂ) with hw
  have hwnorm : ‖w‖ = 1 := by
    rw [hw, PiLp.norm_single]
    simp
  have hdiscsub : ∀ r : ℝ, 0 ≤ r → r ≤ r₀ → affineClosedDisc z₀ w r ⊆ closedBall z₀ r₀ := by
    intro r hr hrr₀ y hy
    obtain ⟨ζ, hζ, rfl⟩ := hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    have : z₀ + ζ • w - z₀ = ζ • w := by abel
    rw [this, norm_smul, hwnorm, mul_one]
    exact le_trans (by simpa using Metric.mem_closedBall.mp hζ) hrr₀
  have hdiscG : ∀ r : ℝ, 0 ≤ r → r ≤ r₀ → affineClosedDisc z₀ w r ⊆ G :=
    fun r hr hrr₀ => (hdiscsub r hr hrr₀).trans hclosed
  -- A finite upper bound for `v` on the largest disc, and for `ρ` on the ball.
  obtain ⟨C₁, hC₁⟩ := hdisc.exists_disc_upper_bound z₀ w hr₀.le
    ((hdiscG r₀ hr₀.le le_rfl).trans (fun z hz => hz.1.1))
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ z ∈ closedBall z₀ r₀, ρ z ≤ B := by
    obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall z₀ r₀).exists_isMaxOn
      ⟨z₀, Metric.mem_closedBall_self hr₀.le⟩
      ((hρ.2.2.1.continuousOn).mono (fun z hz => (hclosed hz).1.2))
    exact ⟨ρ p, fun z hz => hmax hz⟩
  -- `v z₀` is at most `C₁`, since the center lies in the disc.
  have hbC₁ : v z₀ ≤ (C₁ : EReal) :=
    hC₁ z₀ (center_mem_affineClosedDisc z₀ w hr₀.le)
  have hvtop : v z₀ ≠ ⊤ := hdisc.ne_top z₀ hz₀U
  -- Conclude that `v z₀ = ⊥`.
  have hvbot : v z₀ = ⊥ := by
    by_contra hne
    set b := (v z₀).toReal with hb
    have hvz : v z₀ = (b : EReal) := (EReal.coe_toReal hvtop hne).symm
    have hble : b ≤ C₁ := by
      rw [hvz] at hbC₁
      exact EReal.coe_le_coe_iff.mp hbC₁
    have htwopi : (0 : ℝ) < 2 * Real.pi := by positivity
    -- The circle estimate at radius `r`.
    have hkey : ∀ r : ℝ, 0 < r → r ≤ r₀ →
        0 ≤ C₁ - (γ * Real.log r + C + B) →
        C₁ - (γ * Real.log r + C + B) ≤ C₁ - b := by
      intro r hr hrr₀ hnonneg
      have hsub := hdiscG r hr.le hrr₀
      have hsubU : affineClosedDisc z₀ w r ⊆ U := hsub.trans (fun z hz => hz.1.1)
      have hsubbig : affineClosedDisc z₀ w r ⊆ affineClosedDisc z₀ w r₀ := by
        rintro y ⟨ζ, hζ, rfl⟩
        exact ⟨ζ, Metric.closedBall_subset_closedBall hrr₀ hζ, rfl⟩
      -- the pointwise bound on the circle
      have hpt : ∀ t : ℝ, v (z₀ + circleMap 0 r t • w) ≤
          ((γ * Real.log r + C + B : ℝ) : EReal) := by
        intro t
        set p := z₀ + circleMap 0 r t • w with hp
        have hpmem : p ∈ affineClosedDisc z₀ w r :=
          circle_mem_affineClosedDisc z₀ w hr.le t
        have hpnorm : ‖p - z₀‖ = r := by
          have hpz : p - z₀ = circleMap 0 r t • w := by rw [hp]; abel
          rw [hpz, norm_smul, hwnorm, mul_one, norm_circleMap_zero, abs_of_pos hr]
        have hpne : p ≠ z₀ := by
          intro hcontra
          rw [hcontra, sub_self, norm_zero] at hpnorm
          exact hr.ne hpnorm
        have hlog := hObound p (hsub hpmem).2 hpne
        rw [hpnorm] at hlog
        have hρp : ρ p ≤ B := hB p (hdiscsub r hr.le hrr₀ hpmem)
        calc v p = chartFunction u e p + (ρ p : EReal) := rfl
          _ ≤ ((γ * Real.log r + C : ℝ) : EReal) + ((B : ℝ) : EReal) :=
              add_le_add hlog (EReal.coe_le_coe_iff.mpr hρp)
          _ = ((γ * Real.log r + C + B : ℝ) : EReal) := by rw [← EReal.coe_add]
      -- lower bound for the angular deficit
      have hlow : ENNReal.ofReal (C₁ - (γ * Real.log r + C + B)) *
          ENNReal.ofReal (2 * Real.pi) ≤ circleDeficit v z₀ w r C₁ := by
        have hmono : ∀ t : ℝ, ENNReal.ofReal (C₁ - (γ * Real.log r + C + B)) ≤
            ((C₁ : EReal) - v (z₀ + circleMap 0 r t • w)).toENNReal := by
          intro t
          have hle : ((C₁ - (γ * Real.log r + C + B) : ℝ) : EReal) ≤
              (C₁ : EReal) - v (z₀ + circleMap 0 r t • w) := by
            rw [EReal.coe_sub]
            exact EReal.sub_le_sub le_rfl (hpt t)
          calc ENNReal.ofReal (C₁ - (γ * Real.log r + C + B))
              = ((C₁ - (γ * Real.log r + C + B) : ℝ) : EReal).toENNReal :=
                (EReal.real_coe_toENNReal _).symm
            _ ≤ _ := EReal.toENNReal_le_toENNReal hle
        calc ENNReal.ofReal (C₁ - (γ * Real.log r + C + B)) * ENNReal.ofReal (2 * Real.pi)
            = ∫⁻ _ in Ioc (0 : ℝ) (2 * Real.pi),
                ENNReal.ofReal (C₁ - (γ * Real.log r + C + B)) := by
              rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero]
          _ ≤ circleDeficit v z₀ w r C₁ := lintegral_mono fun t => hmono t
      -- the submean inequality
      have hsubmean := hdisc.submean z₀ w r hr hsubU C₁
        (fun y hy => hC₁ y (hsubbig hy))
      rw [hvz, ← EReal.coe_sub, EReal.real_coe_toENNReal] at hsubmean
      have hcomb := hlow.trans hsubmean
      rw [← ENNReal.ofReal_mul hnonneg, mul_comm (ENNReal.ofReal (2 * Real.pi)),
        ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ C₁ - b)] at hcomb
      have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcomb
      nlinarith [htwopi]
    -- choose a radius with `γ log r + C + B < b`
    set K := (b - C - B) / γ with hK
    set r := min r₀ (Real.exp (K - 1)) with hrdef
    have hrpos : 0 < r := lt_min hr₀ (Real.exp_pos _)
    have hlogr : Real.log r ≤ K - 1 :=
      calc Real.log r ≤ Real.log (Real.exp (K - 1)) :=
            Real.log_le_log hrpos (min_le_right _ _)
        _ = K - 1 := Real.log_exp _
    have hgammaK : γ * K = b - C - B := by
      rw [hK]; field_simp
    have hstrict : γ * Real.log r + C + B < b := by
      nlinarith [mul_le_mul_of_nonneg_left hlogr hγ.le, hγ]
    have := hkey r hrpos (min_le_left _ _) (by linarith)
    linarith
  -- Transfer back to `u x`.
  have hchart : chartFunction u e z₀ = ⊥ := by
    have h := hvbot
    rw [hv] at h
    simpa [EReal.add_eq_bot_iff] using h
  rwa [chartFunction, hz₀def, e.val.left_inv hxsrc] at hchart

end

end Hironaka
