import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.GlobalPotentialPullback
import Hironaka.Analytic.KahlerPerturbation
import Hironaka.Analytic.FormPullbackFunctorial
import Hironaka.Analytic.AnalyticGluingData
import Mathlib.Geometry.Manifold.ContMDiff.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Restriction of forms and theta-PSH potentials to an open submanifold

Let `M` be a complex manifold and `U` an open subset, a complex manifold with the restricted
charts `(chartAt x).subtypeRestr` (`TopologicalSpace.Opens.instChartedSpace`,
`AnalyticSubsetOpens.instIsComplexManifoldOpens`).  The inclusion `Subtype.val : U → M` is
holomorphic, and forms, Kähler backgrounds and theta-PSH functions restrict along it:

* `restrictForm U θ` — the closed real `(1,1)`-form `θ|_U` (the pullback along the inclusion);
  in the preferred chart of `U` at `y` its coefficient is that of `θ` in the preferred chart of
  `M` at `y` (`restrictForm_coeff_chartAt`);
* `restrictKahler U ω` — a Kähler background restricts to a Kähler background;
* `thetaPlurisubharmonic_restrict`, `locallyNondegenerate_restrict`,
  `isThetaPshPotential_restrict` — theta-PSH potentials restrict.

The converse is the point of this module.  A theta-PSH witness (a smooth local potential `ρ` of
`θ` with `u + ρ` PSH) in one chart transports to any other chart at the same point
(`exists_witness_of_chart`, holomorphic pullback along the chart transition), so:

* `thetaPlurisubharmonicOn_of_restrict` — if `G|_U` is `θ|_U`-PSH, then `G` is `θ`-PSH over `U`;
* `thetaPlurisubharmonic_piecewise` — on a clopen `U`, a function equal to a `θ|_U`-PSH
  function on `U` and to a `θ`-PSH function off `U` is `θ`-PSH on `M`.

This is the reusable half of the reduction of statements about compact Kähler manifolds to
their connected components (`Hironaka.OpensRestrictionMeasure` carries the measures and the
envelopes).  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.OpensRestriction

open Hironaka.HolomorphicMaps Hironaka.PositiveClasses
  Hironaka.AnalyticGluingData

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Transport of a theta-PSH witness between two charts -/

/-- **A theta-PSH witness transports between charts.**  If in the chart `d` the function `u`
has, near `d x`, a smooth local potential `ρ'` of `θ` with `u + ρ'` PSH, then so it has in any
other chart `e` containing `x`: pull everything back along the holomorphic transition
`d ∘ e⁻¹`. -/
theorem exists_witness_of_chart {θ : SmoothRealForm n M 2} {u : M → EReal}
    (e d : ComplexChart n M) {x : M} (hxe : x ∈ e.val.source) (hxd : x ∈ d.val.source)
    {W' : Set (ComplexModel n)} {ρ' : ComplexModel n → ℝ} (hxW : d.val x ∈ W')
    (hρ : IsSmoothLocalPotential θ d W' ρ')
    (hp : PlurisubharmonicOn (fun y => chartFunction u d y + (ρ' y : EReal)) W') :
    ∃ W ρ, e.val x ∈ W ∧ IsSmoothLocalPotential θ e W ρ ∧
      PlurisubharmonicOn (fun y => chartFunction u e y + (ρ y : EReal)) W := by
  have hid : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (id : M → M) :=
    contMDiff_id
  have hzd : e.val x ∈ coordinateDomain id e d := by
    refine ⟨e.val.map_source hxe, ?_⟩
    simpa [e.val.left_inv hxe] using hxd
  have hD := LocalPotentialPullback.potentialDomain_isOpen hid e d hρ.1
  refine ⟨LocalPotentialPullback.potentialDomain id e d W', ρ' ∘ coordinateMap id e d,
    ⟨hzd, ?_⟩, ?_, ?_⟩
  · simpa [coordinateMap, e.val.left_inv hxe] using hxW
  · exact ((SmoothRealForm.pullback_id_geometricallyEq θ).localPotential_iff e _ _).mp
      (LocalPotentialPullback.isSmoothLocalPotential_pullback hid e hρ)
  · have hpull := HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hD
      (((coordinateMap_contDiffOn hid e d).mono inter_subset_left).differentiableOn
        (by simp)) (fun _ hy => hy.2) hp
    intro y hy
    apply (hpull y hy).congr
    filter_upwards [hD.mem_nhds hy] with w hw
    change u (d.val.symm (d.val (id (e.val.symm w)))) + (ρ' (coordinateMap id e d w) : EReal) =
      u (e.val.symm w) + (ρ' (coordinateMap id e d w) : EReal)
    rw [d.val.left_inv hw.1.2]
    rfl

/-- **Theta-PSH is decided in the preferred charts.**  If at every point `x` the function has a
theta-PSH witness in the preferred chart at `x`, it is theta-PSH over `Ω`. -/
theorem thetaPlurisubharmonicOn_of_chartAt {θ : SmoothRealForm n M 2} {u : M → EReal}
    {Ω : Set M}
    (h : ∀ x ∈ Ω, ∃ W ρ, (complexChartAt (n := n) x).val x ∈ W ∧
      IsSmoothLocalPotential θ (complexChartAt (n := n) x) W ρ ∧
      PlurisubharmonicOn
        (fun y => chartFunction u (complexChartAt (n := n) x) y + (ρ y : EReal)) W) :
    ThetaPlurisubharmonicOn θ u Ω := by
  intro e z hz hzΩ
  obtain ⟨W', ρ', hxW, hρ, hp⟩ := h _ hzΩ
  have hxe : e.val.symm z ∈ e.val.source := e.val.map_target hz
  obtain ⟨W, ρ, hW, hρW, hpW⟩ := exists_witness_of_chart e (complexChartAt (n := n) _) hxe
    (mem_complexChartAt_source _) hxW hρ hp
  rw [e.val.right_inv hz] at hW
  exact ⟨W, ρ, hW, hρW, hpW⟩

/-! ### The inclusion of an open submanifold -/

variable (U : Opens M)

omit [IsComplexManifold n M] in
/-- The inclusion of an open submanifold is holomorphic. -/
theorem contMDiff_val :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : U → M) :=
  contMDiff_subtype_val

variable {U}

omit [IsComplexManifold n M] in
/-- The preferred chart of `U` at `y` is the preferred chart of `M` at `y`, restricted. -/
theorem complexChartAt_opens_val (y : U) :
    (complexChartAt (n := n) y).val =
      (chartAt (ComplexModel n) (y : M)).subtypeRestr ⟨y⟩ := rfl

/-- The target of the preferred chart of `U` at `y` lies in that of `M`. -/
theorem complexChartAt_opens_target_subset (y : U) :
    (complexChartAt (n := n) y).val.target ⊆ (complexChartAt (n := n) (y : M)).val.target := by
  rw [complexChartAt_opens_val]
  exact (chartAt (ComplexModel n) (y : M)).subtypeRestr_target_subset ⟨y⟩

/-- The inverse of the preferred chart of `U`, read in `M`. -/
theorem val_complexChartAt_opens_symm (y : U) {z : ComplexModel n}
    (hz : z ∈ (complexChartAt (n := n) y).val.target) :
    ((complexChartAt (n := n) y).val.symm z : M) =
      (complexChartAt (n := n) (y : M)).val.symm z := by
  rw [complexChartAt_opens_val] at hz ⊢
  exact (chartAt (ComplexModel n) (y : M)).subtypeRestr_symm_apply ⟨y⟩ hz

omit [IsComplexManifold n M] in
theorem complexChartAt_opens_apply (y : U) :
    (complexChartAt (n := n) y).val y = (complexChartAt (n := n) (y : M)).val (y : M) := rfl

/-- The coordinate expression of the inclusion in the preferred charts at `y` is the identity on
the chart target of `U`. -/
theorem coordinateMap_val_complexChartAt (y : U) {z : ComplexModel n}
    (hz : z ∈ (complexChartAt (n := n) y).val.target) :
    coordinateMap (Subtype.val : U → M) (complexChartAt (n := n) y)
      (complexChartAt (n := n) (y : M)) z = z := by
  simp only [coordinateMap, Function.comp_apply]
  rw [val_complexChartAt_opens_symm y hz]
  exact (complexChartAt (n := n) (y : M)).val.right_inv (complexChartAt_opens_target_subset y hz)

theorem mem_coordinateDomain_val (y : U) {z : ComplexModel n}
    (hz : z ∈ (complexChartAt (n := n) y).val.target) :
    z ∈ coordinateDomain (Subtype.val : U → M) (complexChartAt (n := n) y)
      (complexChartAt (n := n) (y : M)) := by
  refine ⟨hz, ?_⟩
  show ((complexChartAt (n := n) y).val.symm z : M) ∈ (complexChartAt (n := n) (y : M)).val.source
  rw [val_complexChartAt_opens_symm y hz]
  exact (complexChartAt (n := n) (y : M)).val.map_target (complexChartAt_opens_target_subset y hz)

theorem fderiv_coordinateMap_val_complexChartAt (y : U) {z : ComplexModel n}
    (hz : z ∈ (complexChartAt (n := n) y).val.target) :
    fderiv ℝ (coordinateMap (Subtype.val : U → M) (complexChartAt (n := n) y)
      (complexChartAt (n := n) (y : M))) z = ContinuousLinearMap.id ℝ (ComplexModel n) := by
  have h : coordinateMap (Subtype.val : U → M) (complexChartAt (n := n) y)
      (complexChartAt (n := n) (y : M)) =ᶠ[𝓝 z] id := by
    filter_upwards [(complexChartAt (n := n) y).val.open_target.mem_nhds hz] with w hw
    exact coordinateMap_val_complexChartAt y hw
  rw [h.fderiv_eq, fderiv_id]

/-- **The restricted form in the preferred charts**: its coefficient in the chart of `U` at `y`
is the coefficient of the original form in the chart of `M` at `y`. -/
theorem pullback_val_coeff_complexChartAt {p : ℕ} (a : SmoothRealForm n M p) (y : U)
    {z : ComplexModel n} (hz : z ∈ (complexChartAt (n := n) y).val.target) :
    (SmoothRealForm.pullback (contMDiff_val U) a).coeff (complexChartAt (n := n) y) z =
      a.coeff (complexChartAt (n := n) (y : M)) z := by
  rw [SmoothRealForm.pullback_coeff (contMDiff_val U) a _ _ (mem_coordinateDomain_val y hz),
    fderiv_coordinateMap_val_complexChartAt y hz, coordinateMap_val_complexChartAt y hz]
  ext v
  rfl

/-! ### Restriction of forms, Kähler backgrounds and potentials -/

variable (U) in
/-- The restriction `θ|_U` of a closed real `(1,1)`-form to an open submanifold. -/
def restrictForm (θ : ClosedRealOneOneForm n M) : ClosedRealOneOneForm n U :=
  ClosedRealOneOneForm.pullback (contMDiff_val U) θ

@[simp] theorem restrictForm_val (θ : ClosedRealOneOneForm n M) :
    (restrictForm U θ).val = SmoothRealForm.pullback (contMDiff_val U) θ.val := rfl

theorem restrictForm_coeff_chartAt (θ : ClosedRealOneOneForm n M) (y : U) {z : ComplexModel n}
    (hz : z ∈ (complexChartAt (n := n) y).val.target) :
    (restrictForm U θ).val.coeff (complexChartAt (n := n) y) z =
      θ.val.coeff (complexChartAt (n := n) (y : M)) z :=
  pullback_val_coeff_complexChartAt θ.val y hz

/-- Every chart of `U` is the restriction of the preferred chart of `M` at one of its points,
so the coordinate expression of the inclusion is a chart transition of `M`; its derivative is
injective. -/
theorem fderiv_coordinateMap_val_injective (e : ComplexChart n U) (d : ComplexChart n M)
    {z : ComplexModel n} (hz : z ∈ coordinateDomain (Subtype.val : U → M) e d) :
    Function.Injective (fderiv ℝ (coordinateMap (Subtype.val : U → M) e d) z) := by
  have hne : Nonempty U := ⟨e.val.symm z⟩
  obtain ⟨x, hx⟩ := TopologicalSpace.Opens.chart_eq hne e.property
  set c := complexChartAt (n := n) (x : M) with hc
  have hcval : c.val = chartAt (ComplexModel n) (x : M) := rfl
  have hzt : z ∈ ((chartAt (ComplexModel n) (x : M)).subtypeRestr hne).target := by
    rw [← hx]; exact hz.1
  have hzc : z ∈ c.val.target := by
    rw [hcval]; exact (chartAt (ComplexModel n) (x : M)).subtypeRestr_target_subset hne hzt
  have hsymm : ∀ w ∈ e.val.target, (e.val.symm w : M) = c.val.symm w := by
    intro w hw
    have hw' : w ∈ ((chartAt (ComplexModel n) (x : M)).subtypeRestr hne).target := by
      rw [← hx]; exact hw
    have := (chartAt (ComplexModel n) (x : M)).subtypeRestr_symm_apply hne hw'
    rw [hcval, ← this, hx]
    rfl
  have hzT : z ∈ (chartTransition c d).source := by
    refine ⟨hzc, ?_⟩
    have h2 := hz.2
    simp only [mem_preimage] at h2
    rw [hsymm z hz.1] at h2
    exact h2
  have heq : coordinateMap (Subtype.val : U → M) e d =ᶠ[𝓝 z] chartTransition c d := by
    filter_upwards [e.val.open_target.mem_nhds hz.1] with w hw
    simp only [coordinateMap, Function.comp_apply, chartTransition,
      OpenPartialHomeomorph.coe_trans, hsymm w hw]
  rw [heq.fderiv_eq]
  exact KahlerPerturbation.chartTransitionDerivative_injective c d hzT

variable (U) in
/-- The restriction of a Kähler background to an open submanifold. -/
def restrictKahler (omega : KahlerBackground n M) : KahlerBackground n U where
  form := restrictForm U omega.form
  isKahler := SmoothRealForm.IsKahler.pullback_of_injective (contMDiff_val U)
    (fun e d _ hz => fderiv_coordinateMap_val_injective e d hz) omega.isKahler

@[simp] theorem restrictKahler_form (omega : KahlerBackground n M) :
    (restrictKahler U omega).form = restrictForm U omega.form := rfl

/-- A theta-PSH function restricts to a `θ|_U`-PSH function. -/
theorem thetaPlurisubharmonic_restrict {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : ThetaPlurisubharmonic θ u) :
    ThetaPlurisubharmonic (SmoothRealForm.pullback (contMDiff_val U) θ)
      (fun y : U => u y) :=
  GlobalPotentialPullback.thetaPlurisubharmonic_comp (contMDiff_val U) hu

/-- Local nondegeneracy restricts to an open subset. -/
theorem locallyNondegenerate_restrict {u : M → EReal} (hu : LocallyNondegenerate u) :
    LocallyNondegenerate (fun y : U => u y) := by
  intro x V hV hxV
  obtain ⟨V', hV', hVeq⟩ := isOpen_induced_iff.mp hV
  have hxV' : (x : M) ∈ V' ∩ U := ⟨by rw [← hVeq] at hxV; exact hxV, x.2⟩
  obtain ⟨y, ⟨hyV', hyU⟩, hy⟩ := hu x (V' ∩ U) (hV'.inter U.2) hxV'
  refine ⟨⟨y, hyU⟩, ?_, hy⟩
  rw [← hVeq]
  exact hyV'

/-- A theta-PSH potential restricts to a `θ|_U`-PSH potential. -/
theorem isThetaPshPotential_restrict {θ : ClosedRealOneOneForm n M} {u : M → EReal}
    (hu : IsThetaPshPotential θ.val u) :
    IsThetaPshPotential (restrictForm U θ).val (fun y : U => u y) :=
  ⟨thetaPlurisubharmonic_restrict hu.1, locallyNondegenerate_restrict hu.2⟩

/-! ### From the open submanifold back to the manifold -/

/-- **A `θ|_U`-PSH function is `θ`-PSH over `U`.**  If `G ∘ val` is `θ|_U`-PSH on `U`, then
`G` satisfies the theta-PSH criterion at every chart point over `U`. -/
theorem thetaPlurisubharmonicOn_of_restrict {θ : SmoothRealForm n M 2} {G : M → EReal}
    (hG : ThetaPlurisubharmonic (SmoothRealForm.pullback (contMDiff_val U) θ)
      (fun y : U => G y)) :
    ThetaPlurisubharmonicOn θ G (U : Set M) := by
  apply thetaPlurisubharmonicOn_of_chartAt
  intro x hxU
  set y : U := ⟨x, hxU⟩
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hG (complexChartAt (n := n) y)
    ((complexChartAt (n := n) y).val y)
    ((complexChartAt (n := n) y).val.map_source (mem_complexChartAt_source y))
  have hWt : W ⊆ (complexChartAt (n := n) y).val.target := hρ.2.1
  refine ⟨W, ρ, hzW, ⟨hρ.1, hWt.trans (complexChartAt_opens_target_subset y), hρ.2.2.1,
    fun w hw => ?_⟩, ?_⟩
  · rw [hρ.2.2.2 hw, pullback_val_coeff_complexChartAt θ y (hWt hw)]
  · intro w hw
    apply (hp w hw).congr
    filter_upwards [hρ.1.mem_nhds hw] with w' hw'
    simp only [chartFunction]
    rw [val_complexChartAt_opens_symm y (hWt hw')]

/-- The theta-PSH criterion over an open set only sees the values on that set. -/
theorem thetaPlurisubharmonicOn_congr {θ : SmoothRealForm n M 2} {F G : M → EReal}
    {V : Set M} (hV : IsOpen V) (hF : ThetaPlurisubharmonicOn θ F V) (hFG : EqOn F G V) :
    ThetaPlurisubharmonicOn θ G V := by
  intro e z hz hzV
  obtain ⟨W, ρ, hzW, hρ, hp⟩ := hF e z hz hzV
  set W' : Set (ComplexModel n) := W ∩ (e.val.target ∩ e.val.symm ⁻¹' V) with hW'
  have hW'o : IsOpen W' := hρ.1.inter (e.val.isOpen_inter_preimage_symm hV)
  refine ⟨W', ρ, ⟨hzW, hz, hzV⟩, hρ.mono hW'o inter_subset_left, fun w hw => ?_⟩
  apply (hp w hw.1).congr
  filter_upwards [hW'o.mem_nhds hw] with w' hw'
  simp only [chartFunction]
  rw [hFG hw'.2.2]

/-- The theta-PSH criterion over two sets covering the manifold is theta-PSH. -/
theorem thetaPlurisubharmonic_of_on_union {θ : SmoothRealForm n M 2} {G : M → EReal}
    {V₁ V₂ : Set M} (h₁ : ThetaPlurisubharmonicOn θ G V₁) (h₂ : ThetaPlurisubharmonicOn θ G V₂)
    (hcover : ∀ x, x ∈ V₁ ∨ x ∈ V₂) : ThetaPlurisubharmonic θ G := by
  intro e z hz
  rcases hcover (e.val.symm z) with h | h
  · exact h₁ e z hz h
  · exact h₂ e z hz h

/-- A theta-PSH function is theta-PSH over every set. -/
theorem thetaPlurisubharmonicOn_of_thetaPlurisubharmonic {θ : SmoothRealForm n M 2}
    {G : M → EReal} (hG : ThetaPlurisubharmonic θ G) (V : Set M) :
    ThetaPlurisubharmonicOn θ G V :=
  fun e z hz _ => hG e z hz

/-- **Gluing across a clopen set.**  On a clopen `U`, the function equal to `ψ` on `U` and to
`φ` off `U` is `θ`-PSH if `ψ|_U` is `θ|_U`-PSH and `φ` is `θ`-PSH. -/
theorem thetaPlurisubharmonic_piecewise (hU : IsClopen (U : Set M)) {θ : SmoothRealForm n M 2}
    {ψ φ : M → EReal} [DecidablePred (· ∈ (U : Set M))]
    (hψ : ThetaPlurisubharmonic (SmoothRealForm.pullback (contMDiff_val U) θ)
      (fun y : U => ψ y))
    (hφ : ThetaPlurisubharmonic θ φ) :
    ThetaPlurisubharmonic θ ((U : Set M).piecewise ψ φ) := by
  refine thetaPlurisubharmonic_of_on_union (V₁ := (U : Set M)) (V₂ := (U : Set M)ᶜ) ?_ ?_
    (fun x => em (x ∈ (U : Set M)))
  · exact thetaPlurisubharmonicOn_congr U.2 (thetaPlurisubharmonicOn_of_restrict hψ)
      (fun x hx => (Set.piecewise_eq_of_mem _ _ _ hx).symm)
  · exact thetaPlurisubharmonicOn_congr hU.1.isOpen_compl (thetaPlurisubharmonicOn_of_thetaPlurisubharmonic hφ _)
      (fun x hx => (Set.piecewise_eq_of_notMem _ _ _ hx).symm)

/-- Local nondegeneracy of a piecewise function across a clopen set. -/
theorem locallyNondegenerate_piecewise (hU : IsClopen (U : Set M)) {ψ φ : M → EReal}
    [DecidablePred (· ∈ (U : Set M))]
    (hψ : LocallyNondegenerate (fun y : U => ψ y)) (hφ : LocallyNondegenerate φ) :
    LocallyNondegenerate ((U : Set M).piecewise ψ φ) := by
  intro x V hV hxV
  by_cases hx : x ∈ (U : Set M)
  · obtain ⟨y, hyV, hy⟩ := hψ ⟨x, hx⟩ (Subtype.val ⁻¹' V) (hV.preimage continuous_subtype_val)
      hxV
    exact ⟨y, hyV, by rw [Set.piecewise_eq_of_mem _ _ _ y.2]; exact hy⟩
  · obtain ⟨y, ⟨hyV, hyU⟩, hy⟩ := hφ x (V ∩ (U : Set M)ᶜ) (hV.inter hU.1.isOpen_compl) ⟨hxV, hx⟩
    exact ⟨y, hyV, by rw [Set.piecewise_eq_of_notMem _ _ _ hyU]; exact hy⟩

end

end Hironaka.OpensRestriction
