import Hironaka.Blowup.BlowupFunctionTransform
import Hironaka.MarkedIdeal.DerivativeIdeal

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# A generator of the ideal of a submanifold has multiplicity one

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), Lemma `le:Gi` (2) (the controlled transform `u'`
of a tangent direction `u` is again of multiplicity one).  Blueprint `bcalc:multiplicity-one`.

* `exists_chartDeriv_ne_zero_of_vanishingIdeal_eq_span` -- if a set `N` is regular of dimension
  `k < n` at `y` and its ideal is generated at `y` by a holomorphic `g`, then some partial
  derivative of `g` in a chart does not vanish at `y` (`dg(y) ≠ 0`): a flat coordinate `Φ_k`
  vanishing on `N` is `a·g` near `y`, so `dΦ_k(y) = a(y)·dg(y)` since `g(y) = 0`, and `dΦ_k(y) ≠ 0`.
* `exists_chartDeriv_ne_zero_controlledTransform` -- **the controlled transform has multiplicity
  one**: for the blowup `π` along `C ⊆ N` (`N` a closed submanifold of dimension `k < n` at each of
  its points), if `𝓘_N = (u)` at `π z`, `u ∘ π = h · u'` near `z` and `z ∈ N'`, then `du'(z) ≠ 0`
  (in the form `MaximalContact.IsTangentDirection.multiplicity_one` uses).

Sorry-free; outside the import closure of the two Hironaka statements.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.GeneratorMultiplicityOne

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates BlowupStrictSubmanifold BlowupFunctionTransform DerivativeIdeal

noncomputable section

variable {n : ℕ}

/-- The differential of a local holomorphic equivalence is surjective at the points of its
source. -/
theorem surjective_fderiv_toFun {p : ComplexModel n} (Φ : LocalHolomorphicEquivAt (n := n) p)
    {q : ComplexModel n} (hq : q ∈ Φ.source) : Function.Surjective (fderiv ℂ Φ.toFun q) := by
  have hdq : DifferentiableAt ℂ Φ.toFun q :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds hq)
  have hqt : Φ.toFun q ∈ Φ.target := Φ.mapsTo_toFun hq
  have hdi : DifferentiableAt ℂ Φ.invFun (Φ.toFun q) :=
    Φ.invFun_holomorphic.differentiableAt (Φ.isOpen_target.mem_nhds hqt)
  have hcomp : HasFDerivAt (fun w => Φ.invFun (Φ.toFun w))
      ((fderiv ℂ Φ.invFun (Φ.toFun q)).comp (fderiv ℂ Φ.toFun q)) q :=
    hdi.hasFDerivAt.comp q hdq.hasFDerivAt
  have hid : HasFDerivAt (fun w => Φ.invFun (Φ.toFun w)) (ContinuousLinearMap.id ℂ _) q := by
    refine (hasFDerivAt_id q).congr_of_eventuallyEq ?_
    filter_upwards [Φ.isOpen_source.mem_nhds hq] with w hw
    exact Φ.left_inv w hw
  have hEq := hcomp.unique hid
  have hinj : Function.Injective (fderiv ℂ Φ.toFun q) := by
    intro v w hvw
    have := congrArg (fderiv ℂ Φ.invFun (Φ.toFun q)) hvw
    have h1 := DFunLike.congr_fun hEq v
    have h2 := DFunLike.congr_fun hEq w
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h1 h2
    rw [← h1, ← h2, this]
  set L : ComplexModel n →ₗ[ℂ] ComplexModel n := (fderiv ℂ Φ.toFun q).toLinearMap
  exact LinearMap.injective_iff_surjective (f := L) |>.mp hinj

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A generator of the ideal of a submanifold has nonvanishing differential.**  If `N` is regular
of dimension `k < n` at `y` and `𝓘_N = (g)` at `y` with `g` holomorphic, then some chart derivative of
`g` does not vanish at `y`. -/
theorem exists_chartDeriv_ne_zero_of_vanishingIdeal_eq_span {N : Set M} {y : M} {k : ℕ}
    (hN : RegularAtDim (n := n) N y k) (hk : k < n) {g : M → ℂ} (hg : HolomorphicAt n g y)
    (hgen : ∀ f, (vanishingIdeal (n := n) N).mem y f ↔ IsInSpanAt (n := n) (· = g) y f) :
    ∃ (e : ComplexChart n M) (v : ComplexModel n), y ∈ e.val.source ∧ chartDeriv e v g y ≠ 0 := by
  obtain ⟨-, hyN, Φ, hΦt, -, hflat⟩ := hN
  have hyΦ : y ∈ flatDomain Φ := mem_flatDomain_self Φ
  -- the flat coordinate `Φ_k` lies in `𝓘_N`, hence is a multiple of `g`
  have hΦmem := flatCoord_mem_vanishingIdeal Φ hflat (i := ⟨k, hk⟩) (le_refl k) hyΦ
  have hy : y ∈ (complexChartAt (n := n) y).val.source := mem_chart_source _ y
  set i : Fin n := ⟨k, hk⟩ with hidef
  obtain ⟨-, a, ha, haeq⟩ := isInSpanAt_eq_iff.mp ((hgen _).mp hΦmem)
  -- `g` vanishes at `y`
  have hg0 : g y = 0 := by
    have hgmem := (hgen g).mpr (isInSpanAt_of_eq_mul rfl hg (holomorphicAt_const 1)
      (Eventually.of_forall fun _ => by simp))
    exact hgmem.2.self_of_nhds hyN
  by_contra hcon
  have hall : ∀ (e' : ComplexChart n M) (v : ComplexModel n), y ∈ e'.val.source →
      chartDeriv e' v g y = 0 := fun e' v hy' => by
    by_contra h'
    exact hcon ⟨e', v, hy', h'⟩
  have hDg : fderiv ℂ (g ∘ (complexChartAt (n := n) y).val.symm) ((complexChartAt (n := n) y).val y) = 0 := by
    ext v
    simpa [chartDeriv] using hall (complexChartAt (n := n) y) v hy
  -- derivatives in the chart
  have hgd : DifferentiableAt ℂ (g ∘ (complexChartAt (n := n) y).val.symm) ((complexChartAt (n := n) y).val y) :=
    (eventually_differentiableAt_comp_symm (complexChartAt (n := n) y) hy hg).self_of_nhds
  have had : DifferentiableAt ℂ (a ∘ (complexChartAt (n := n) y).val.symm) ((complexChartAt (n := n) y).val y) :=
    (eventually_differentiableAt_comp_symm (complexChartAt (n := n) y) hy ha).self_of_nhds
  have hsymm : (complexChartAt (n := n) y).val.symm ((complexChartAt (n := n) y).val y) = y := (complexChartAt (n := n) y).val.left_inv hy
  have hprod : HasFDerivAt (fun ζ => (a ∘ (complexChartAt (n := n) y).val.symm) ζ * (g ∘ (complexChartAt (n := n) y).val.symm) ζ)
      (0 : ComplexModel n →L[ℂ] ℂ) ((complexChartAt (n := n) y).val y) := by
    have := had.hasFDerivAt.mul hgd.hasFDerivAt
    refine this.congr_fderiv ?_
    rw [hDg]
    simp only [Function.comp_apply, hsymm, hg0]
    ext v
    simp
  -- `ζ ↦ Φ(ζ)_k` agrees with `(a ∘ e⁻¹)(g ∘ e⁻¹)` near `e y`
  have hT : Tendsto (complexChartAt (n := n) y).val.symm (𝓝 ((complexChartAt (n := n) y).val y)) (𝓝 y) := by
    have := (complexChartAt (n := n) y).val.continuousAt_symm ((complexChartAt (n := n) y).val.map_source hy)
    rwa [ContinuousAt, hsymm] at this
  have hF : (fun ζ => Φ.toFun ζ i) =ᶠ[𝓝 ((complexChartAt (n := n) y).val y)]
      fun ζ => (a ∘ (complexChartAt (n := n) y).val.symm) ζ * (g ∘ (complexChartAt (n := n) y).val.symm) ζ := by
    filter_upwards [hT.eventually haeq, (complexChartAt (n := n) y).val.open_target.mem_nhds ((complexChartAt (n := n) y).val.map_source hy)] with
      ζ h1 h2
    simp only [Function.comp_apply]
    rw [← h1]
    simp only [flatCoord]
    rw [show (chartAt (ComplexModel n) y) ((complexChartAt (n := n) y).val.symm ζ) = ζ from (complexChartAt (n := n) y).val.right_inv h2]
  have hFd : HasFDerivAt (fun ζ => Φ.toFun ζ i) (0 : ComplexModel n →L[ℂ] ℂ) ((complexChartAt (n := n) y).val y) :=
    hprod.congr_of_eventuallyEq hF
  -- but the `k`-th component of `dΦ` is onto
  have hΦd : DifferentiableAt ℂ Φ.toFun ((complexChartAt (n := n) y).val y) :=
    Φ.toFun_holomorphic.differentiableAt (Φ.isOpen_source.mem_nhds Φ.center_mem_source)
  have hcomp : HasFDerivAt (fun ζ => Φ.toFun ζ i)
      ((EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).comp (fderiv ℂ Φ.toFun ((complexChartAt (n := n) y).val y)))
      ((complexChartAt (n := n) y).val y) :=
    (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).hasFDerivAt.comp _ hΦd.hasFDerivAt
  have hzero := hcomp.unique hFd
  obtain ⟨v, hv⟩ := surjective_fderiv_toFun Φ Φ.center_mem_source (EuclideanSpace.single i 1)
  have := DFunLike.congr_fun hzero v
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at this
  rw [hv] at this
  simp at this

/-! ### The controlled transform of a generator -/

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X} {hπ : IsBlowupAlong n C π} {U : Set Y}
  {h : Y → ℂ}

/-- **The controlled transform of a generator has multiplicity one** (Wlodarczyk `le:Gi` (2)): let
`N ⊇ C` be a closed submanifold of dimension `k < n` at each of its points, `𝓘_N = (u)` at `π z`,
`u ∘ π = h · u'` near `z` with `h` a local equation of the exceptional divisor, and `z ∈ N'`.  Then
`du'(z) ≠ 0`. -/
theorem exists_chartDeriv_ne_zero_controlledTransform (hh : IsLocalEquation hπ U h) {z : Y}
    (hz : z ∈ U) {N : Set X} (hN : IsClosedSubmanifold n N) {k : ℕ}
    (hNk : ∀ x ∈ N, RegularAtDim (n := n) N x k) (hk : k < n) (hCN : C ⊆ N) {u : X → ℂ}
    (hu : HolomorphicAt n u (π z))
    (hgen : ∀ g, (vanishingIdeal (n := n) N).mem (π z) g ↔ IsInSpanAt (n := n) (· = u) (π z) g)
    {u' : Y → ℂ} (hu' : HolomorphicAt n u' z) (heq : (u ∘ π) =ᶠ[𝓝 z] fun y => h y * u' y)
    (hzN : z ∈ geoStrictTransform π C N) :
    ∃ (e : ComplexChart n Y) (v : ComplexModel n), z ∈ e.val.source ∧ chartDeriv e v u' z ≠ 0 :=
  exists_chartDeriv_ne_zero_of_vanishingIdeal_eq_span
    (regularAtDim_geoStrictTransform hπ hN.1 hNk hCN hzN) hk hu'
    (vanishingIdeal_geoStrictTransform_mem_iff hh hz hN hCN hu hgen hu' heq)

end

end Hironaka.GeneratorMultiplicityOne
