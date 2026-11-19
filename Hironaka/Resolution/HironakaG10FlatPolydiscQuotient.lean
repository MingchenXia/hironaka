import Hironaka.Resolution.HironakaG10FlatPolydiscRemainder

/-! # Weierstrass division in `B(K' × D̄(0,ρ))`: the quotient

Split 4a of the privilege plan (REPORT-r1). Hypotheses (`WeierstrassHyp`): `K' ⊆ closure
(interior K')` compact, `0 < ρ`, `W(z,w) = w^b + ∑_{k<b} A_k(z) w^k` with coefficients
holomorphic on an open `U ⊇ K'` and all roots of `W(z,·)` in `D(0,ρ)` for `z ∈ U`.
For `f ∈ B(K)`, `K = K' × D̄(0,ρ)`, with `h` its extension by zero, put
`R = divRem b A h ρ` (boundary remainder) and
`Q(z,w) = divQuot b A h ρ (z,w)` for `|w| < ρ`, `Q(z,w) = (h - R)/W` for `|w| ≥ ρ`.
* `division_on_K`: `h = W·Q + R` on `K`;
* `continuousOn_quotient`: `Q` is continuous on `K`;
* `differentiableOn_quotient`: `Q` is holomorphic on `interior K` (local contour shrinking);
* `quotientElem`: `Q|_K ∈ B(K)`.
BP: hironaka-g10-flat-polydisc-quotient.tex. -/
set_option autoImplicit false
open Set Filter Metric Complex
open scoped Topology Real
namespace Hironaka.HironakaG10FlatPolydiscQuotient
noncomputable section
open Classical HironakaG10FlatPolydiscAlgebra HironakaG10FlatDiscWeierstrassDivision
  HironakaG10FlatDiscDivisionBoundary HironakaG10FlatPolydiscFibre HironakaG10FlatPolydiscRemainder

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- The standing hypotheses of Weierstrass division on `K' × D̄(0,ρ)`. -/
structure WeierstrassHyp (K' : Set P) (ρ : ℝ) (b : ℕ) (A : ℕ → P → ℂ) (U : Set P) : Prop where
  regular : K' ⊆ closure (interior K')
  pos : 0 < ρ
  isOpen : IsOpen U
  sub : K' ⊆ U
  holo : ∀ k, DifferentiableOn ℂ (A k) U
  monic : ∀ z ∈ U, A b z = 1
  roots : ∀ z ∈ U, ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ

variable {K' : Set P} {ρ : ℝ} {b : ℕ} {A : ℕ → P → ℂ} {U : Set P}

namespace WeierstrassHyp
variable (H : WeierstrassHyp K' ρ b A U)
include H

theorem polyEval_ne {z : P} (hz : z ∈ U) {w : ℂ} (hw : ρ ≤ ‖w‖) : polyEval b A z w ≠ 0 :=
  fun h0 => absurd hw (not_le.mpr (mem_ball_zero_iff.mp (H.roots z hz w h0)))

theorem continuousOn_polyEval :
    ContinuousOn (fun x : P × ℂ => polyEval b A x.1 x.2) (U ×ˢ univ) :=
  (differentiableOn_polyEval b H.holo).continuousOn

end WeierstrassHyp

/-- The extension by zero of an element of `B(K' × D̄(0,ρ))`. -/
abbrev ext0 (K' : Set P) (ρ : ℝ) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) : P × ℂ → ℂ :=
  extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ))

/-- The quotient of the division of `h` by `W` on `K' × D̄(0,ρ)`. -/
def quotient (b : ℕ) (A : ℕ → P → ℂ) (h : P × ℂ → ℂ) (ρ : ℝ) (x : P × ℂ) : ℂ :=
  if ‖x.2‖ < ρ then divQuot b A h ρ x else (h x - divRem b A h ρ x) / polyEval b A x.1 x.2

section
variable (H : WeierstrassHyp K' ρ b A U) [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)]
  (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
include H


omit H [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
theorem continuousOn_ext0 : ContinuousOn (ext0 K' ρ f) (K' ×ˢ closedBall (0 : ℂ) ρ) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (K' ×ˢ closedBall (0 : ℂ) ρ).domRestrict (ext0 K' ρ f) =
      ⇑(f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) := by
    funext x
    exact extendZero_of_mem _ _ x.2
  rw [this]
  exact (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)).continuous

/-- **The division identity on `K`.** -/
theorem division_on_K {x : P × ℂ} (hx : x ∈ K' ×ˢ closedBall (0 : ℂ) ρ) :
    (ext0 K' ρ f) x = polyEval b A x.1 x.2 * quotient b A (ext0 K' ρ f) ρ x + divRem b A (ext0 K' ρ f) ρ x := by
  obtain ⟨z, w⟩ := x
  obtain ⟨hz, hw⟩ := hx
  have hWρ : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0 := fun ζ hζ =>
    H.polyEval_ne (H.sub hz) (mem_sphere_zero_iff_norm.mp hζ).ge
  by_cases hlt : ‖w‖ < ρ
  · rw [quotient, if_pos hlt]
    exact division_eq_of_continuousOn H.pos z (continuousOn_fibre _ hz)
      (differentiableOn_fibre H.regular H.pos f hz) hWρ (mem_ball_zero_iff.mpr hlt)
  · rw [quotient, if_neg hlt]
    have hW0 : polyEval b A z w ≠ 0 := H.polyEval_ne (H.sub hz) (not_lt.mp hlt)
    field_simp
    ring

omit [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
/-- The remainder is continuous on `K' × ℂ`. -/
theorem continuousOn_divRem_K : ContinuousOn (divRem b A (ext0 K' ρ f) ρ) (K' ×ˢ univ) := by
  have hW : ∀ z ∈ K', ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0 := fun z hz ζ hζ =>
    H.polyEval_ne (H.sub hz) (mem_sphere_zero_iff_norm.mp hζ).ge
  refine continuousOn_finsetSum _ fun i _ => ?_
  exact ((continuousOn_remCoeff_extendZero H.pos.le _
    (fun k => (H.holo k).continuousOn.mono H.sub) hW i).comp continuousOn_fst
      fun x hx => hx.1).mul (continuousOn_snd.pow i)

omit [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] in
/-- The Cauchy quotient is continuous on `K' × D(0,ρ)`. -/
theorem continuousOn_divQuot_K : ContinuousOn (divQuot b A (ext0 K' ρ f) ρ) (K' ×ˢ ball (0 : ℂ) ρ) := by
  have hfK : ContinuousOn (ext0 K' ρ f) (K' ×ˢ closedBall (0 : ℂ) ρ) := continuousOn_ext0 f
  have hΨ : ContinuousOn (fun q : (P × ℂ) × ℂ => (ext0 K' ρ f) (q.1.1, q.2) /
      (polyEval b A q.1.1 q.2 * (q.2 - q.1.2))) ((K' ×ˢ ball (0 : ℂ) ρ) ×ˢ sphere (0 : ℂ) ρ) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact hfK.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd).continuousOn
        fun q hq => ⟨hq.1.1, sphere_subset_closedBall hq.2⟩
    · refine ContinuousOn.mul ?_ (continuous_snd.sub (continuous_snd.comp continuous_fst)).continuousOn
      exact H.continuousOn_polyEval.comp ((continuous_fst.comp continuous_fst).prodMk
        continuous_snd).continuousOn fun q hq => ⟨H.sub hq.1.1, mem_univ _⟩
    · intro q hq
      refine mul_ne_zero (H.polyEval_ne (H.sub hq.1.1) (mem_sphere_zero_iff_norm.mp hq.2).ge) ?_
      intro h0
      rw [sub_eq_zero] at h0
      have h1 := mem_ball_zero_iff.mp hq.1.2
      rw [← h0, mem_sphere_zero_iff_norm.mp hq.2] at h1
      exact lt_irrefl _ h1
  exact ((continuousOn_circleIntegral_param H.pos.le hΨ).const_smul ((2 * π * I)⁻¹)).congr
    fun x _ => by simp [divQuot, smul_eq_mul]

/-- **Continuity of the quotient on `K`.** -/
theorem continuousOn_quotient : ContinuousOn (quotient b A (ext0 K' ρ f) ρ) (K' ×ˢ closedBall (0 : ℂ) ρ) := by
  have hfK : ContinuousOn (ext0 K' ρ f) (K' ×ˢ closedBall (0 : ℂ) ρ) := continuousOn_ext0 f
  intro x hx
  by_cases hlt : ‖x.2‖ < ρ
  · -- inside: the quotient is the Cauchy quotient on the relatively open set `|w| < ρ`
    have hS : K' ×ˢ ball (0 : ℂ) ρ ∈ 𝓝[K' ×ˢ closedBall (0 : ℂ) ρ] x := by
      refine mem_nhdsWithin.mpr ⟨univ ×ˢ ball (0 : ℂ) ρ, isOpen_univ.prod isOpen_ball,
        ⟨mem_univ _, mem_ball_zero_iff.mpr hlt⟩, fun y hy => ⟨hy.2.1, hy.1.2⟩⟩
    have hc := ((continuousOn_divQuot_K H f) x ⟨hx.1, mem_ball_zero_iff.mpr hlt⟩).mono_of_mem_nhdsWithin hS
    refine hc.congr_of_eventuallyEq ?_ (by rw [quotient, if_pos hlt])
    filter_upwards [hS] with y hy
    rw [quotient, if_pos (mem_ball_zero_iff.mp hy.2)]
  · -- on the circle: near `x`, the quotient is `(h - R)/W`
    have hxU : x.1 ∈ U := H.sub hx.1
    have hW0 : polyEval b A x.1 x.2 ≠ 0 := H.polyEval_ne hxU (not_lt.mp hlt)
    have hWc : ContinuousAt (fun y : P × ℂ => polyEval b A y.1 y.2) x :=
      H.continuousOn_polyEval.continuousAt ((H.isOpen.prod isOpen_univ).mem_nhds ⟨hxU, mem_univ _⟩)
    have hN : {y : P × ℂ | y.1 ∈ U ∧ polyEval b A y.1 y.2 ≠ 0} ∈ 𝓝 x :=
      Filter.inter_mem (continuous_fst.continuousAt.preimage_mem_nhds (H.isOpen.mem_nhds hxU))
        (hWc.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hW0))
    have hg : ContinuousWithinAt (fun y => ((ext0 K' ρ f) y - divRem b A (ext0 K' ρ f) ρ y) / polyEval b A y.1 y.2)
        (K' ×ˢ closedBall (0 : ℂ) ρ) x := by
      refine ContinuousWithinAt.div ?_ hWc.continuousWithinAt hW0
      exact (hfK x hx).sub (((continuousOn_divRem_K H f) x ⟨hx.1, mem_univ _⟩).mono
        fun y hy => ⟨hy.1, mem_univ _⟩)
    refine hg.congr_of_eventuallyEq ?_ (by rw [quotient, if_neg hlt])
    filter_upwards [nhdsWithin_le_nhds hN, self_mem_nhdsWithin] with y hy hyK
    have hdiv := division_on_K H f hyK
    rw [eq_div_iff hy.2]
    linear_combination (-1 : ℂ) * hdiv

variable [FiniteDimensional ℂ P]

/-- **Holomorphy of the quotient on `interior K`.** -/
theorem differentiableOn_quotient :
    DifferentiableOn ℂ (quotient b A (ext0 K' ρ f) ρ) (interior K' ×ˢ ball (0 : ℂ) ρ) := by
  have hfint : DifferentiableOn ℂ (ext0 K' ρ f) (interior K' ×ˢ ball (0 : ℂ) ρ) := by
    have h0 := mem_holSubalgebra.mp f.2
    rwa [interior_prod_closedBall K' H.pos] at h0
  rintro ⟨z₀, w₀⟩ ⟨hz₀, hw₀⟩
  have hz₀U : z₀ ∈ U := H.sub (interior_subset hz₀)
  obtain ⟨ρ'', hρ''pos, hρ''lt, V, hV, hz₀V, hVU, hVroots⟩ :=
    exists_root_radius H.isOpen (fun k => (H.holo k).continuousOn) H.monic H.pos H.roots hz₀U
  have hw₀ρ := mem_ball_zero_iff.mp hw₀
  set ρ' := max ρ'' ((‖w₀‖ + ρ) / 2) with hρ'def
  have hρ'pos : 0 < ρ' := lt_max_of_lt_left hρ''pos
  have hρ'lt : ρ' < ρ := max_lt hρ''lt (by linarith)
  have hw₀ρ' : w₀ ∈ ball (0 : ℂ) ρ' := by
    rw [mem_ball_zero_iff]
    exact lt_max_of_lt_right (by linarith)
  set V' := V ∩ interior K' with hV'
  have hV'o : IsOpen V' := hV.inter isOpen_interior
  have hroots' : ∀ z ∈ V', ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ' := fun z hz α hα =>
    ball_subset_ball (le_max_left _ _) (hVroots z hz.1 α hα)
  have hW' : ∀ z ∈ V', ∀ ζ ∈ sphere (0 : ℂ) ρ', polyEval b A z ζ ≠ 0 := by
    intro z hz ζ hζ h0
    have := hroots' z hz ζ h0
    rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ] at this
    exact lt_irrefl _ this
  have hsmall : DifferentiableOn ℂ (divQuot b A (ext0 K' ρ f) ρ') (V' ×ˢ ball (0 : ℂ) ρ') :=
    differentiableOn_divQuot hV'o (fun k => (H.holo k).mono (inter_subset_left.trans hVU))
      hρ'pos hρ'lt (hfint.mono (prod_mono inter_subset_right subset_rfl)) hW'
  have hagree : ∀ y ∈ V' ×ˢ ball (0 : ℂ) ρ', quotient b A (ext0 K' ρ f) ρ y = divQuot b A (ext0 K' ρ f) ρ' y := by
    rintro ⟨z, w⟩ ⟨hz, hw⟩
    have hzK : z ∈ K' := interior_subset hz.2
    have hfib := differentiableOn_fibre H.regular H.pos f hzK
    have hfibc := continuousOn_fibre (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) hzK
    have hWρ : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0 := fun ζ hζ =>
      H.polyEval_ne (H.sub hzK) (mem_sphere_zero_iff_norm.mp hζ).ge
    have hq : ContinuousOn (fun w => divQuot b A (ext0 K' ρ f) ρ (z, w)) (ball 0 ρ') :=
      ((differentiableOn_divQuot_slice_of_continuousOn H.pos z
        (hfibc.mono sphere_subset_closedBall) hWρ).mono (ball_subset_ball hρ'lt.le)).continuousOn
    have hdiv : ∀ w ∈ ball (0 : ℂ) ρ', (ext0 K' ρ f) (z, w) = polyEval b A z w * divQuot b A (ext0 K' ρ f) ρ (z, w) +
        ∑ j ∈ Finset.range b, remCoeff b A (ext0 K' ρ f) ρ j z * w ^ j := fun w hw =>
      division_eq_of_continuousOn H.pos z hfibc hfib hWρ (ball_subset_ball hρ'lt.le hw)
    have hEq := (eq_divQuot_remCoeff hρ'pos hρ'lt z hfib (H.monic z (H.sub hzK))
      (hroots' z hz) _ hq _ hdiv).2 hw
    rw [quotient, if_pos (lt_trans (mem_ball_zero_iff.mp hw) hρ'lt)]
    exact hEq
  have hnhds : V' ×ˢ ball (0 : ℂ) ρ' ∈ 𝓝 (z₀, w₀) :=
    (hV'o.prod isOpen_ball).mem_nhds ⟨⟨hz₀V, hz₀⟩, hw₀ρ'⟩
  have hev : divQuot b A (ext0 K' ρ f) ρ' =ᶠ[𝓝 (z₀, w₀)] quotient b A (ext0 K' ρ f) ρ :=
    Filter.eventually_of_mem hnhds fun y hy => (hagree y hy).symm
  exact ((hsmall.differentiableAt hnhds).congr_of_eventuallyEq hev.symm).differentiableWithinAt

/-- **The quotient is an element of `B(K)`.** -/
def quotientElem : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ) :=
  ⟨⟨fun x => quotient b A (ext0 K' ρ f) ρ x,
      continuousOn_iff_continuous_domRestrict.mp (continuousOn_quotient H f)⟩, by
    refine ((differentiableOn_quotient H f).congr fun x hx => ?_).mono
      (interior_prod_closedBall K' H.pos).le
    · rw [extendZero_of_mem _ _ (interior_subset ((interior_prod_closedBall K' H.pos).symm ▸ hx))]
      rfl⟩

theorem quotientElem_apply (x : K' ×ˢ closedBall (0 : ℂ) ρ) :
    ((quotientElem H f : holSubalgebra _) : C(_, ℂ)) x = quotient b A (ext0 K' ρ f) ρ x := rfl

end

end
end Hironaka.HironakaG10FlatPolydiscQuotient
