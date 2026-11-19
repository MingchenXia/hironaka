import Hironaka.Resolution.HironakaG10FlatPolydiscQuotient
import Hironaka.Resolution.HironakaG10FlatDiscDivisionClosedBound

/-! # Privilege of `K' × D̄(0,ρ)` for a Weierstrass polynomial

Split 4b of the privilege plan (REPORT-r1), under `WeierstrassHyp` (`K' ⊆ closure (interior K')`,
`W = w^b + ∑_{k<b} A_k w^k` with coefficients holomorphic on an open `U ⊇ K'`, all roots of
`W(z,·)` in `D(0,ρ)`): for every `f ∈ B(K)`, `K = K' × D̄(0,ρ)`, there are UNIQUE `q ∈ B(K)` and
`r₀,…,r_{b-1} ∈ B(K')` with `f = W q + ∑_{i<b} rᵢ wⁱ` on `K` (`exists_division`,
`division_unique_B`), and the division is bounded for the sup norms with constants depending only
on `ρ`, `inf |W|` and bounds of the difference-quotient coefficients on `K' × {|ζ| = ρ}`
(`norm_division_le`). In the language of Douady (1966, §7) and Frisch (1968): `B(K)` is the
topological direct sum of `W·B(K)` and the free `B(K')`-module `⊕_{i<b} B(K') wⁱ`; the polydisc
`K` is privileged for `O/(W)`.
BP: hironaka-g10-flat-polydisc-privilege.tex. -/
set_option autoImplicit false
open Set Filter Metric Complex
open scoped Topology Real
namespace Hironaka.HironakaG10FlatPolydiscPrivilege
noncomputable section
open Classical HironakaG10FlatPolydiscAlgebra HironakaG10FlatDiscWeierstrassDivision
  HironakaG10FlatDiscDivisionBoundary HironakaG10FlatPolydiscFibre HironakaG10FlatPolydiscRemainder
  HironakaG10FlatPolydiscQuotient

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
  {K' : Set P} {ρ : ℝ} {b : ℕ} {A : ℕ → P → ℂ} {U : Set P}
  [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K']

omit [FiniteDimensional ℂ P] [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)] [CompactSpace K'] in
theorem ext0_apply (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) {x : P × ℂ}
    (hx : x ∈ K' ×ˢ closedBall (0 : ℂ) ρ) :
    ext0 K' ρ f x = (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) ⟨x, hx⟩ :=
  extendZero_of_mem _ _ hx

/-- The remainder coefficients as elements of `B(K')` (zero for `i ≥ b`). -/
def remElem (H : WeierstrassHyp K' ρ b A U) (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    (i : ℕ) : holSubalgebra K' :=
  if hi : i < b then
    Classical.choose (remCoeff_mem_holSubalgebra H.regular H.pos f H.isOpen H.sub H.holo H.monic
      H.roots hi)
  else 0

omit [CompactSpace K'] in
theorem remElem_apply (H : WeierstrassHyp K' ρ b A U)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) {i : ℕ} (hi : i < b) (z : K') :
    ((remElem H f i : holSubalgebra K') : C(K', ℂ)) z = remCoeff b A (ext0 K' ρ f) ρ i z := by
  rw [remElem, dif_pos hi]
  exact Classical.choose_spec (remCoeff_mem_holSubalgebra H.regular H.pos f H.isOpen H.sub H.holo
    H.monic H.roots hi) z

omit [CompactSpace K'] in
/-- **Existence of the Weierstrass division in `B(K)`.** -/
theorem exists_division (H : WeierstrassHyp K' ρ b A U)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (x : K' ×ˢ closedBall (0 : ℂ) ρ) :
    ((f : holSubalgebra _) : C(_, ℂ)) x = polyEval b A x.1.1 x.1.2 *
      ((quotientElem H f : holSubalgebra _) : C(_, ℂ)) x +
        ∑ i ∈ Finset.range b, ((remElem H f i : holSubalgebra K') : C(K', ℂ)) ⟨x.1.1, x.2.1⟩ *
          x.1.2 ^ i := by
  have h := division_on_K H f x.2
  rw [ext0_apply f x.2] at h
  rw [quotientElem_apply, h, divRem]
  congr 1
  exact Finset.sum_congr rfl fun i hi => by
    rw [remElem_apply H f (Finset.mem_range.mp hi)]

omit [CompactSpace K'] in
/-- **Uniqueness of the Weierstrass division in `B(K)`.** -/
theorem division_unique_B (H : WeierstrassHyp K' ρ b A U)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) (q : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ))
    (r : ℕ → holSubalgebra K')
    (hdiv : ∀ x : K' ×ˢ closedBall (0 : ℂ) ρ, ((f : holSubalgebra _) : C(_, ℂ)) x =
      polyEval b A x.1.1 x.1.2 * ((q : holSubalgebra _) : C(_, ℂ)) x +
        ∑ i ∈ Finset.range b, ((r i : holSubalgebra K') : C(K', ℂ)) ⟨x.1.1, x.2.1⟩ * x.1.2 ^ i) :
    q = quotientElem H f ∧ ∀ i < b, r i = remElem H f i := by
  -- fibrewise uniqueness on the open disc
  have key : ∀ z (hz : z ∈ K'), (∀ i < b, ((r i : holSubalgebra K') : C(K', ℂ)) ⟨z, hz⟩ =
      remCoeff b A (ext0 K' ρ f) ρ i z) ∧ ∀ w (hw : w ∈ ball (0 : ℂ) ρ),
        ((q : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ))
          ⟨(z, w), hz, ball_subset_closedBall hw⟩ = divQuot b A (ext0 K' ρ f) ρ (z, w) := by
    intro z hz
    set qz : ℂ → ℂ := fun w => ext0 K' ρ q (z, w)
    have hqz : ContinuousOn qz (ball 0 ρ) :=
      (continuousOn_fibre (q : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) hz).mono ball_subset_closedBall
    have hd : ∀ w ∈ ball (0 : ℂ) ρ, ext0 K' ρ f (z, w) = polyEval b A z w * qz w +
        ∑ i ∈ Finset.range b, ((r i : holSubalgebra K') : C(K', ℂ)) ⟨z, hz⟩ * w ^ i := by
      intro w hw
      have hx : (z, w) ∈ K' ×ˢ closedBall (0 : ℂ) ρ := ⟨hz, ball_subset_closedBall hw⟩
      have := hdiv ⟨(z, w), hx⟩
      simp only [qz]
      rw [ext0_apply f hx, ext0_apply q hx]
      exact this
    obtain ⟨h1, h2⟩ := eq_divQuot_remCoeff_of_continuousOn H.pos z
      (continuousOn_fibre (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) hz)
      (differentiableOn_fibre H.regular H.pos f hz) (H.monic z (H.sub hz))
      (H.roots z (H.sub hz)) qz hqz (fun i => ((r i : holSubalgebra K') : C(K', ℂ)) ⟨z, hz⟩) hd
    refine ⟨h1, fun w hw => ?_⟩
    have := h2 hw
    simp only [qz] at this
    rw [ext0_apply q (⟨hz, ball_subset_closedBall hw⟩ : (z, w) ∈ K' ×ˢ closedBall (0 : ℂ) ρ)] at this
    exact this
  have hr : ∀ i < b, r i = remElem H f i := by
    intro i hi
    apply Subtype.ext
    ext z
    rw [remElem_apply H f hi]
    exact (key z.1 z.2).1 i hi
  refine ⟨?_, hr⟩
  apply Subtype.ext
  ext x
  rw [quotientElem_apply]
  obtain ⟨⟨z, w⟩, hz, hw⟩ := x
  by_cases hlt : ‖w‖ < ρ
  · rw [quotient, if_pos hlt]
    exact (key z hz).2 w (mem_ball_zero_iff.mpr hlt)
  · rw [quotient, if_neg hlt]
    have hW0 : polyEval b A z w ≠ 0 := H.polyEval_ne (H.sub hz) (not_lt.mp hlt)
    rw [eq_div_iff hW0]
    have h1 := hdiv ⟨(z, w), hz, hw⟩
    have h2 : divRem b A (ext0 K' ρ f) ρ (z, w) =
        ∑ i ∈ Finset.range b, ((r i : holSubalgebra K') : C(K', ℂ)) ⟨z, hz⟩ * w ^ i := by
      rw [divRem]
      exact Finset.sum_congr rfl fun i hi => by
        rw [(key z hz).1 i (Finset.mem_range.mp hi)]
    rw [h2, ext0_apply f (⟨hz, hw⟩ : (z, w) ∈ K' ×ˢ closedBall (0 : ℂ) ρ), h1]
    ring

/-- **Bounds: the division is a bounded operator for the sup norms.** -/
theorem norm_division_le (H : WeierstrassHyp K' ρ b A U)
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) {m : ℝ} (B : ℕ → ℝ) (hm : 0 < m)
    (hmW : ∀ z ∈ K', ∀ ζ ∈ sphere (0 : ℂ) ρ, m ≤ ‖polyEval b A z ζ‖)
    (hB : ∀ i, ∀ z ∈ K', ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖diffCoeff b A i z ζ‖ ≤ B i)
    (hB0 : ∀ i, 0 ≤ B i) :
    (∀ i < b, ‖remElem H f i‖ ≤ ρ * (‖f‖ * B i / m)) ∧
      ‖quotientElem H f‖ ≤ (‖f‖ + ∑ i ∈ Finset.range b, ρ * (‖f‖ * B i / m) * ρ ^ i) / m := by
  have hfx : ∀ z ∈ K', ∀ ζ ∈ closedBall (0 : ℂ) ρ, ‖ext0 K' ρ f (z, ζ)‖ ≤ ‖f‖ := by
    intro z hz ζ hζ
    rw [ext0_apply f (⟨hz, hζ⟩ : (z, ζ) ∈ K' ×ˢ closedBall (0 : ℂ) ρ)]
    exact (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)).norm_coe_le_norm _
  have hrem : ∀ i < b, ∀ z ∈ K', ‖remCoeff b A (ext0 K' ρ f) ρ i z‖ ≤ ρ * (‖f‖ * B i / m) :=
    fun i _ z hz => norm_remCoeff_le H.pos i z hm (fun ζ hζ => hfx z hz ζ (sphere_subset_closedBall hζ))
      (fun ζ hζ => hB i z hz ζ hζ) (fun ζ hζ => hmW z hz ζ hζ)
  have hC0 : 0 ≤ (‖f‖ + ∑ i ∈ Finset.range b, ρ * (‖f‖ * B i / m) * ρ ^ i) / m := by
    have := H.pos
    have := hm
    refine div_nonneg (add_nonneg (norm_nonneg _) (Finset.sum_nonneg fun i _ => ?_)) hm.le
    have := hB0 i
    positivity
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [norm_holSubalgebra, ContinuousMap.norm_le _ (by have := H.pos; have := hB0 i; positivity)]
    intro z
    rw [remElem_apply H f hi]
    exact hrem i hi z.1 z.2
  · rw [norm_holSubalgebra, ContinuousMap.norm_le _ hC0]
    rintro ⟨⟨z, w⟩, hz, hw⟩
    rw [quotientElem_apply]
    -- bound on the circle
    have hcircle : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖quotient b A (ext0 K' ρ f) ρ (z, ζ)‖ ≤
        (‖f‖ + ∑ i ∈ Finset.range b, ρ * (‖f‖ * B i / m) * ρ ^ i) / m := by
      intro ζ hζ
      have hζn : ‖ζ‖ = ρ := mem_sphere_zero_iff_norm.mp hζ
      rw [quotient, if_neg (by rw [hζn]; exact lt_irrefl _), norm_div]
      have hWm := hmW z hz ζ hζ
      have hRb : ‖divRem b A (ext0 K' ρ f) ρ (z, ζ)‖ ≤
          ∑ i ∈ Finset.range b, ρ * (‖f‖ * B i / m) * ρ ^ i := by
        rw [divRem]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
        rw [norm_mul, norm_pow, hζn]
        exact mul_le_mul_of_nonneg_right (hrem i (Finset.mem_range.mp hi) z hz)
          (pow_nonneg H.pos.le _)
      have hnum := (norm_sub_le _ _).trans (add_le_add (hfx z hz ζ (sphere_subset_closedBall hζ)) hRb)
      calc ‖ext0 K' ρ f (z, ζ) - divRem b A (ext0 K' ρ f) ρ (z, ζ)‖ / ‖polyEval b A z ζ‖
          ≤ (‖f‖ + ∑ i ∈ Finset.range b, ρ * (‖f‖ * B i / m) * ρ ^ i) / ‖polyEval b A z ζ‖ := by
            gcongr
        _ ≤ (‖f‖ + ∑ i ∈ Finset.range b, ρ * (‖f‖ * B i / m) * ρ ^ i) / m := by
            gcongr
            exact (norm_nonneg _).trans hnum
    -- maximum modulus on the closed disc
    have hWρ : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0 := fun ζ hζ =>
      H.polyEval_ne (H.sub hz) (mem_sphere_zero_iff_norm.mp hζ).ge
    have hdiff : DifferentiableOn ℂ (fun w => quotient b A (ext0 K' ρ f) ρ (z, w)) (ball 0 ρ) :=
      (differentiableOn_divQuot_slice_of_continuousOn H.pos z
        ((continuousOn_fibre (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) hz).mono
          sphere_subset_closedBall) hWρ).congr fun w hw => by
        rw [quotient, if_pos (mem_ball_zero_iff.mp hw)]
    have hcont : ContinuousOn (fun w => quotient b A (ext0 K' ρ f) ρ (z, w)) (closedBall 0 ρ) :=
      (continuousOn_quotient H f).comp (continuous_const.prodMk continuous_id).continuousOn
        fun w hw => ⟨hz, hw⟩
    have hcl : DiffContOnCl ℂ (fun w => quotient b A (ext0 K' ρ f) ρ (z, w)) (ball 0 ρ) :=
      ⟨hdiff, by rw [closure_ball (0 : ℂ) H.pos.ne']; exact hcont⟩
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hcl (fun ζ hζ => ?_)
      (by rw [closure_ball (0 : ℂ) H.pos.ne']; exact hw)
    rw [frontier_ball (0 : ℂ) H.pos.ne'] at hζ
    exact hcircle ζ hζ

end
end Hironaka.HironakaG10FlatPolydiscPrivilege
