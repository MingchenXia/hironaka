import Hironaka.Analytic.ExteriorDerivative
import Hironaka.Analytic.HolomorphicDDC
import Hironaka.Analytic.PositiveClasses
import Hironaka.Analytic.CoordinateDensityGeometry

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Closed `(1,1)`-forms from local `ddᶜ`-potentials

A family of local smooth potentials `gₓ` on neighbourhoods `Wₓ ∋ x` whose pairwise differences
are pluriharmonic (`ddᶜ (gₓ - g_y) = 0` on overlaps) defines a global smooth real two-form,
equal to `ddᶜ gₓ` near `x`.  This is how the curvature form of a smooth Hermitian metric on a
line bundle, or `ddᶜ log |s|²` extended across the zeros of `s`, is built: the local weights
differ by `log |unit|²` (`Hironaka.PluriharmonicLogNorm`).

* `LocalDDCData`: the data;
* `LocalDDCData.form`, `LocalDDCData.closedForm`: the global form, with
  `form_coeff_eventuallyEq` (`= ddᶜ gₓ` near `x`);
* `LocalDDCData.form_isClosed`, `LocalDDCData.form_isTypeOneOne`.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.LocalPotentialForm



noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable (n M) in
/-- Local smooth potentials with pluriharmonic differences. -/
structure LocalDDCData where
  domain : M → Set M
  isOpen_domain : ∀ x, IsOpen (domain x)
  mem_domain : ∀ x, x ∈ domain x
  potential : M → M → ℝ
  smooth : ∀ (x : M) (e : ComplexChart n M),
    ContDiffOn ℝ ∞ (fun u => potential x (e.val.symm u))
      (e.val.target ∩ e.val.symm ⁻¹' domain x)
  pluriharmonic : ∀ (x y : M) (e : ComplexChart n M) (u : ComplexModel n),
    u ∈ e.val.target → e.val.symm u ∈ domain x → e.val.symm u ∈ domain y →
      smoothDDC (fun u' => potential x (e.val.symm u') - potential y (e.val.symm u')) u = 0

namespace LocalDDCData

variable (D : LocalDDCData n M)

theorem isOpen_chartDomain (x : M) (e : ComplexChart n M) :
    IsOpen (e.val.target ∩ e.val.symm ⁻¹' D.domain x) :=
  e.val.isOpen_inter_preimage_symm (D.isOpen_domain x)

/-- Near a point of the chart domain of `x`, `ddᶜ` of any admissible potential agrees with
`ddᶜ gₓ`. -/
theorem smoothDDC_eq (x y : M) (e : ComplexChart n M) {u : ComplexModel n}
    (hu : u ∈ e.val.target) (hx : e.val.symm u ∈ D.domain x) (hy : e.val.symm u ∈ D.domain y) :
    smoothDDC (fun u' => D.potential y (e.val.symm u')) u =
      smoothDDC (fun u' => D.potential x (e.val.symm u')) u := by
  have hU := (D.isOpen_chartDomain x e).inter (D.isOpen_chartDomain y e)
  have h := D.pluriharmonic y x e u hu hy hx
  rw [PositiveClasses.smoothDDC_sub hU ((D.smooth y e).mono inter_subset_right)
    ((D.smooth x e).mono inter_subset_left) ⟨⟨hu, hx⟩, hu, hy⟩] at h
  exact sub_eq_zero.mp h

/-- The coefficient of the glued form in the chart `e`. -/
def coeff (e : ComplexChart n M) (u : ComplexModel n) : ComplexModel n [⋀^Fin 2]→L[ℝ] ℝ :=
  smoothDDC (fun u' => D.potential (e.val.symm u) (e.val.symm u')) u

theorem coeff_eventuallyEq (x : M) (e : ComplexChart n M) {u : ComplexModel n}
    (hu : u ∈ e.val.target ∩ e.val.symm ⁻¹' D.domain x) :
    D.coeff e =ᶠ[𝓝 u] smoothDDC (fun u' => D.potential x (e.val.symm u')) := by
  filter_upwards [(D.isOpen_chartDomain x e).mem_nhds hu] with u' hu'
  exact D.smoothDDC_eq x (e.val.symm u') e hu'.1 hu'.2 (D.mem_domain _)

theorem coeff_contDiffOn (e : ComplexChart n M) : ContDiffOn ℝ ∞ (D.coeff e) e.val.target := by
  intro u hu
  have hmem : u ∈ e.val.target ∩ e.val.symm ⁻¹' D.domain (e.val.symm u) :=
    ⟨hu, D.mem_domain _⟩
  have hsm : ContDiffOn ℝ ∞ (smoothDDC (fun u' => D.potential (e.val.symm u) (e.val.symm u')))
      (e.val.target ∩ e.val.symm ⁻¹' D.domain (e.val.symm u)) := by
    have hderiv := (contDiffOn_infty_iff_fderiv_of_isOpen (D.isOpen_chartDomain _ e)).mp
      (smoothDc_contDiffOn (D.isOpen_chartDomain _ e) (D.smooth (e.val.symm u) e))
    exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ
      (ComplexModel n) ℝ).contDiff.comp_contDiffOn hderiv.2
  exact ((hsm.contDiffAt ((D.isOpen_chartDomain _ e).mem_nhds hmem)).congr_of_eventuallyEq
    (D.coeff_eventuallyEq _ e hmem)).contDiffWithinAt

theorem coeff_compatible (e f : ComplexChart n M) (u : ComplexModel n)
    (hu : u ∈ (chartTransition e f).source) (v : Fin 2 → ComplexModel n) :
    D.coeff e u v = D.coeff f (chartTransition e f u)
      (fun i => chartTransitionDerivative e f u (v i)) := by
  set x := e.val.symm u
  set T := chartTransition e f
  have hTu : T u ∈ f.val.target := HolomorphicMaps.coordinateMap_mem_target (f := id) hu
  have hfT : f.val.symm (T u) = x := f.val.left_inv hu.2
  set V := f.val.target ∩ f.val.symm ⁻¹' D.domain x
  have hV : IsOpen V := D.isOpen_chartDomain x f
  set U := T.source ∩ T ⁻¹' V
  have hU : IsOpen U := T.isOpen_inter_preimage hV
  have huU : u ∈ U := ⟨hu, hTu, by rw [mem_preimage, hfT]; exact D.mem_domain x⟩
  have hT : ContDiffOn ℂ ∞ T U := fun y hy =>
    (HolomorphicMaps.chartTransition_contDiffAt e f hy.1).contDiffWithinAt
  have heq : (fun u' => D.potential x (e.val.symm u')) =ᶠ[𝓝 u]
      fun u' => (fun w => D.potential x (f.val.symm w)) (T u') := by
    filter_upwards [T.open_source.mem_nhds hu] with y hy
    have hy' : e.val.symm y ∈ f.val.source := hy.2
    show D.potential x (e.val.symm y) = D.potential x (f.val.symm (f.val (e.val.symm y)))
    rw [f.val.left_inv hy']
  have hcomp := HolomorphicDDC.smoothDDC_comp hU hV hT (D.smooth x f) (fun y hy => hy.2) huU
  show smoothDDC (fun u' => D.potential x (e.val.symm u')) u v =
    smoothDDC (fun u' => D.potential (f.val.symm (T u)) (f.val.symm u')) (T u) _
  rw [hfT, smoothDDC_congr heq, hcomp]
  rfl

/-- **The glued form.** -/
def form : SmoothRealForm n M 2 where
  coeff := D.coeff
  smooth := D.coeff_contDiffOn
  compatible := D.coeff_compatible

theorem form_coeff_eventuallyEq (x : M) (e : ComplexChart n M) {u : ComplexModel n}
    (hu : u ∈ e.val.target) (hx : e.val.symm u ∈ D.domain x) :
    D.form.coeff e =ᶠ[𝓝 u] smoothDDC (fun u' => D.potential x (e.val.symm u')) :=
  D.coeff_eventuallyEq x e ⟨hu, hx⟩

theorem form_isClosed : D.form.IsClosed := by
  intro e u hu
  have hmem : u ∈ e.val.target ∩ e.val.symm ⁻¹' D.domain (e.val.symm u) := ⟨hu, D.mem_domain _⟩
  show extDeriv (D.coeff e) u = 0
  rw [(D.coeff_eventuallyEq _ e hmem).extDeriv_eq]
  exact extDeriv_extDeriv_apply
    ((smoothDc_contDiffOn (D.isOpen_chartDomain _ e) (D.smooth (e.val.symm u) e)).contDiffAt
      ((D.isOpen_chartDomain _ e).mem_nhds hmem))
    (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)

theorem form_isTypeOneOne : D.form.IsTypeOneOne := by
  intro e u hu v w
  have hmem : u ∈ e.val.target ∩ e.val.symm ⁻¹' D.domain (e.val.symm u) := ⟨hu, D.mem_domain _⟩
  exact MongeAmpere.smoothDDC_isOneOne
    (((D.smooth (e.val.symm u) e).contDiffAt ((D.isOpen_chartDomain _ e).mem_nhds hmem)).of_le
      (by simpa using ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) v w

/-- The glued form as a closed real `(1,1)`-form. -/
def closedForm : ClosedRealOneOneForm n M := ⟨D.form, D.form_isClosed, D.form_isTypeOneOne⟩

end LocalDDCData

end

end Hironaka.LocalPotentialForm
