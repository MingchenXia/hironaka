import Hironaka.Resolution.HironakaG10FlatPolydiscFibre
import Hironaka.Resolution.HironakaG10FlatDiscDivisionBoundary
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-! # The boundary remainder of an element of `B(K' × D̄(0,ρ))` lies in `B(K')`

Split 3 of the privilege plan (REPORT-r1). Let `W(z,w) = w^b + ∑_{k<b} A_k(z) w^k` have
coefficients holomorphic on an open `U ⊇ K'` and all roots of `W(z,·)` in `D(0,ρ)` for `z ∈ U`.
* `exists_root_radius`: around every `z₀ ∈ U` there are `ρ' < ρ` and an open `V ∋ z₀` such that
  all roots of `W(z,·)` lie in `D(0,ρ')` for `z ∈ V` (finite root set, tube lemma on the compact
  annulus `ρ' ≤ |ζ| ≤ ρ`);
* `differentiableOn_remCoeff_extendZero`: if `K' ⊆ closure (interior K')`, the boundary
  remainder coefficients `rᵢ = remCoeff b A f ρ i` (`i < b`) of `f ∈ B(K' × D̄(0,ρ))` are
  holomorphic on `interior K'` (near `z₀` they equal the remainder for the smaller contour `ρ'`,
  by uniqueness of the division, and that one is holomorphic);
* `remCoeff_mem_holSubalgebra`: hence `rᵢ|_{K'} ∈ B(K')` (continuity on `K'` is
  `continuousOn_remCoeff_extendZero`).
BP: hironaka-g10-flat-polydisc-remainder.tex. -/
set_option autoImplicit false
open Set Filter Metric Complex
open scoped Topology Real
namespace Hironaka.HironakaG10FlatPolydiscRemainder
noncomputable section
open HironakaG10FlatPolydiscAlgebra HironakaG10FlatDiscWeierstrassDivision
  HironakaG10FlatDiscDivisionBoundary HironakaG10FlatPolydiscFibre

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {b : ℕ} {A : ℕ → P → ℂ}

omit [NormedSpace ℂ P] in
/-- **Uniform root control near a point.** -/
theorem exists_root_radius {U : Set P} (hU : IsOpen U) (hA : ∀ k, ContinuousOn (A k) U)
    (hmon : ∀ z ∈ U, A b z = 1) {ρ : ℝ} (hρ : 0 < ρ)
    (hroots : ∀ z ∈ U, ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ) {z₀ : P} (hz₀ : z₀ ∈ U) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < ρ ∧ ∃ V : Set P, IsOpen V ∧ z₀ ∈ V ∧ V ⊆ U ∧
      ∀ z ∈ V, ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ' := by
  -- the root set at `z₀` is finite, hence inside a smaller ball
  have hfin : {α : ℂ | polyEval b A z₀ α = 0}.Finite := by
    have h := Polynomial.finite_setOfPred_isRoot (toPoly_monic b A z₀).ne_zero
    refine h.subset fun α hα => ?_
    change Polynomial.IsRoot (toPoly b A z₀) α
    rw [Polynomial.IsRoot.def, eval_toPoly (hmon z₀ hz₀)]
    exact hα
  obtain ⟨ρ₁, hρ₁, hsub⟩ := exists_lt_subset_ball hfin.isClosed
    (fun α hα => hroots z₀ hz₀ α hα)
  set ρ' := max ρ₁ (ρ / 2) with hρ'
  have hρ'pos : 0 < ρ' := lt_max_of_lt_right (half_pos hρ)
  have hρ'lt : ρ' < ρ := max_lt hρ₁ (half_lt_self hρ)
  -- the closed annulus `ρ' ≤ |ζ| ≤ ρ`
  let Ann : Set ℂ := closedBall 0 ρ \ ball 0 ρ'
  have hAnn : IsCompact Ann := (isCompact_closedBall 0 ρ).diff isOpen_ball
  -- `W ≠ 0` on an open set containing `{z₀} × Ann`
  let n : Set (P × ℂ) := (U ×ˢ univ) ∩ (fun x : P × ℂ => polyEval b A x.1 x.2) ⁻¹' {0}ᶜ
  have hWc : ContinuousOn (fun x : P × ℂ => polyEval b A x.1 x.2) (U ×ˢ univ) :=
    continuousOn_finsetSum _ fun k _ =>
      ((hA k).comp continuousOn_fst fun x hx => hx.1).mul (continuousOn_snd.pow k)
  have hn : IsOpen n := hWc.isOpen_inter_preimage (hU.prod isOpen_univ) isOpen_compl_singleton
  have hsub₀ : ({z₀} : Set P) ×ˢ Ann ⊆ n := by
    rintro ⟨z, ζ⟩ ⟨hz, hζ⟩
    rw [mem_singleton_iff] at hz
    subst hz
    refine ⟨⟨hz₀, mem_univ _⟩, fun h0 => ?_⟩
    have h1 := hsub h0
    have h2 : ζ ∈ ball (0 : ℂ) ρ' := ball_subset_ball (le_max_left _ _) h1
    exact hζ.2 h2
  obtain ⟨u, v, hu, -, hz₀u, hAv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hAnn hn hsub₀
  refine ⟨ρ', hρ'pos, hρ'lt, u ∩ U, hu.inter hU, ⟨hz₀u rfl, hz₀⟩, inter_subset_right,
    fun z hz α hα => ?_⟩
  have hαρ := hroots z hz.2 α hα
  by_contra hα'
  have hαA : α ∈ Ann := ⟨ball_subset_closedBall hαρ, hα'⟩
  have hmem : ((z, α) : P × ℂ) ∈ n := huv (show ((z, α) : P × ℂ) ∈ u ×ˢ v from ⟨hz.1, hAv hαA⟩)
  exact hmem.2 hα

variable [FiniteDimensional ℂ P]

/-- **The boundary remainder coefficients are holomorphic on the interior.** -/
theorem differentiableOn_remCoeff_extendZero {K' : Set P} (hK' : K' ⊆ closure (interior K'))
    {ρ : ℝ} (hρ : 0 < ρ) [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)]
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) {U : Set P} (hU : IsOpen U) (hKU : K' ⊆ U)
    (hA : ∀ k, DifferentiableOn ℂ (A k) U) (hmon : ∀ z ∈ U, A b z = 1)
    (hroots : ∀ z ∈ U, ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ) {i : ℕ} (hi : i < b) :
    DifferentiableOn ℂ
      (remCoeff b A (extendZero _ (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ))) ρ i) (interior K') := by
  set h := extendZero (K' ×ˢ closedBall (0 : ℂ) ρ) (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ)) with hh
  have hfint : DifferentiableOn ℂ h (interior K' ×ˢ ball (0 : ℂ) ρ) := by
    have h0 := mem_holSubalgebra.mp f.2
    rwa [interior_prod_closedBall K' hρ] at h0
  intro z₀ hz₀
  have hz₀U : z₀ ∈ U := hKU (interior_subset hz₀)
  obtain ⟨ρ', hρ'pos, hρ'lt, V, hV, hz₀V, hVU, hVroots⟩ :=
    exists_root_radius hU (fun k => (hA k).continuousOn) hmon hρ hroots hz₀U
  -- work on `V' = V ∩ interior K'`
  set V' := V ∩ interior K' with hV'
  have hV'o : IsOpen V' := hV.inter isOpen_interior
  have hz₀V' : z₀ ∈ V' := ⟨hz₀V, hz₀⟩
  have hW' : ∀ z ∈ V', ∀ ζ ∈ sphere (0 : ℂ) ρ', polyEval b A z ζ ≠ 0 := by
    intro z hz ζ hζ h0
    have := hVroots z hz.1 ζ h0
    rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ] at this
    exact lt_irrefl _ this
  -- the small-contour remainder is holomorphic on `V'`
  have hsmall : DifferentiableOn ℂ (remCoeff b A h ρ' i) V' :=
    differentiableOn_remCoeff hV'o (fun k => (hA k).mono (hVU.trans' inter_subset_left |>.trans
      subset_rfl)) hρ'pos hρ'lt (hfint.mono (prod_mono inter_subset_right subset_rfl)) hW' i
  -- and it agrees with the boundary remainder on `V'`
  have hagree : ∀ z ∈ V', remCoeff b A h ρ i z = remCoeff b A h ρ' i z := by
    intro z hz
    have hzK : z ∈ K' := interior_subset hz.2
    have hfib : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 ρ) :=
      differentiableOn_fibre hK' hρ f hzK
    have hfibc : ContinuousOn (fun ζ => h (z, ζ)) (closedBall 0 ρ) := continuousOn_fibre _ hzK
    have hWρ : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0 := by
      intro ζ hζ h0
      have := hroots z (hVU hz.1) ζ h0
      rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ] at this
      exact lt_irrefl _ this
    have hq : ContinuousOn (fun w => divQuot b A h ρ (z, w)) (ball 0 ρ') :=
      ((differentiableOn_divQuot_slice_of_continuousOn hρ z (hfibc.mono sphere_subset_closedBall)
        hWρ).mono (ball_subset_ball hρ'lt.le)).continuousOn
    have hdiv : ∀ w ∈ ball (0 : ℂ) ρ', h (z, w) = polyEval b A z w * divQuot b A h ρ (z, w) +
        ∑ j ∈ Finset.range b, remCoeff b A h ρ j z * w ^ j := fun w hw =>
      division_eq_of_continuousOn hρ z hfibc hfib hWρ (ball_subset_ball hρ'lt.le hw)
    exact (eq_divQuot_remCoeff hρ'pos hρ'lt z hfib (hmon z (hVU hz.1)) (hVroots z hz.1) _ hq _
      hdiv).1 i hi
  have hev : remCoeff b A h ρ' i =ᶠ[𝓝 z₀] remCoeff b A h ρ i :=
    Filter.eventually_of_mem (hV'o.mem_nhds hz₀V') fun z hz => (hagree z hz).symm
  exact ((hsmall.differentiableAt (hV'o.mem_nhds hz₀V')).congr_of_eventuallyEq hev.symm
    ).differentiableWithinAt

/-- **The boundary remainder coefficients define elements of `B(K')`.** -/
theorem remCoeff_mem_holSubalgebra {K' : Set P} (hK' : K' ⊆ closure (interior K'))
    {ρ : ℝ} (hρ : 0 < ρ) [CompactSpace (K' ×ˢ closedBall (0 : ℂ) ρ)]
    (f : holSubalgebra (K' ×ˢ closedBall (0 : ℂ) ρ)) {U : Set P} (hU : IsOpen U) (hKU : K' ⊆ U)
    (hA : ∀ k, DifferentiableOn ℂ (A k) U) (hmon : ∀ z ∈ U, A b z = 1)
    (hroots : ∀ z ∈ U, ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ) {i : ℕ} (hi : i < b) :
    ∃ r : holSubalgebra K', ∀ z : K',
      (r : C(K', ℂ)) z = remCoeff b A (extendZero _ (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ))) ρ i z := by
  set g := remCoeff b A (extendZero _ (f : C(K' ×ˢ closedBall (0 : ℂ) ρ, ℂ))) ρ i
  have hW : ∀ z ∈ K', ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0 := by
    intro z hz ζ hζ h0
    have := hroots z (hKU hz) ζ h0
    rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ] at this
    exact lt_irrefl _ this
  have hc : ContinuousOn g K' :=
    continuousOn_remCoeff_extendZero hρ.le _ (fun k => (hA k).continuousOn.mono hKU) hW i
  refine ⟨⟨⟨fun z => g z, (continuousOn_iff_continuous_domRestrict.mp hc)⟩, ?_⟩, fun z => rfl⟩
  refine (differentiableOn_remCoeff_extendZero hK' hρ f hU hKU hA hmon hroots hi).congr
    fun z hz => ?_
  rw [extendZero_of_mem K' _ (interior_subset hz)]
  rfl

end
end Hironaka.HironakaG10FlatPolydiscRemainder
