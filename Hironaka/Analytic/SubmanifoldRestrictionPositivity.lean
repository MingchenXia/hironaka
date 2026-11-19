import Hironaka.Analytic.TubePositivityOneFlattening
import Hironaka.Analytic.ClosedFormPullback
import Hironaka.Analytic.HolomorphicDDC
import Hironaka.Analytic.RegularLocusDense

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Restriction of `(1,1)`-forms to a submanifold, and positivity along `T_W`

Source: Copy-4, `prop:principalization`, Steps 4 and 6
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1880-1984`).
Step 4 proves that the class `{θ_Y - Θ_D - ½δ₀π^*ω}|_W` is Kähler **on `W`**
(`lem:residual-nef` applied on the manifold `W`), and Step 6 uses it as
*"along `W` the restriction of `Ω_U` to `T_W` is `A_W`"*: the form
`β + ddᶜf̃` is strictly positive on the tangent directions of `W`.

The tube half of Step 6 consumes that positivity in the shape
`TubePositivityOneFlattening.PositiveOnOneFlattening W k (β + ddᶜf̃)`: one
nondegenerate holomorphic flattening `F` per point, and strict positivity on
`(dF)⁻¹(ℂᵏ × 0)`.  What Step 4 produces is a statement about the pulled-back
form on `W` itself.  This module is the bridge, for `W` given as the image of a
holomorphic immersion `ι : V → M` of a complex `k`-manifold.

## Results

* `range_fderiv_eq_comap` — the tangent space of `W` seen by a flattening,
  `(dF)⁻¹(ℂᵏ × 0)`, is exactly the image of the differential of `ι` in charts.
  One inclusion: `F ∘ ι` lands in the plane, so its derivative does.  The other
  is the rank squeeze of `Hironaka.FlatteningTangentSpace`: `dι` is injective, so
  its image has real rank `2k`, while `(dF)⁻¹(ℂᵏ × 0)` has rank at most that of
  the plane, which is at most `2k`.
* `positiveOnOneFlattening_of_isHermitian_pullback` — if `ι^*β` is a Hermitian
  form on `V` (strictly positive in every chart), then
  `PositiveOnOneFlattening W k β`.
* `pullback_ddcClosedForm_coeff` — `ι^*(ddᶜf) = ddᶜ(f ∘ ι)` in every chart of
  `V`, for chart-smooth `f` (from `Hironaka.HolomorphicDDC.smoothDDC_comp`,
  which is dimension-general).
* `positiveOnOneFlattening_add_ddc_of_isKahler` — the form Step 4 delivers: if
  `ι^*β + ddᶜh` is Kähler on `V` and `f̃ ∘ ι = h`, then
  `PositiveOnOneFlattening W k (β + ddᶜf̃)`.

Everything here is sorry-free.  Nothing here constructs the immersion `ι` or the
extension `f̃`; they are hypotheses of the theorems that use them.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.SubmanifoldRestrictionPositivity

open Hironaka.HolomorphicMaps Hironaka.HolomorphicDDC
  Hironaka.RegularLocusDense PositivityPerturbation ManifoldTubePositivity
  GlobalTubeFunction FlatteningTangentSpace FlatteningTangentSpaceIndependence
  TubePositivityOneFlattening

noncomputable section

/-! ### The coordinate plane has rank at most that of `ℂᵏ` -/

/-- `ℂᵏ × 0 ⊆ ℂⁿ` embeds `ℝ`-linearly into `ℂᵏ` (projection to the first `k`
coordinates is injective on it), so its real rank is at most `2k`. -/
theorem finrank_planeSubmodule_le {n k : ℕ} :
    Module.finrank ℝ (planeSubmodule n k) ≤ Module.finrank ℝ (ComplexModel k) := by
  let P : ComplexModel n →ₗ[ℝ] ComplexModel k :=
    ((coordinateProjection n k).restrictScalars ℝ : ComplexModel n →L[ℝ] ComplexModel k)
  refine LinearMap.finrank_le_finrank_of_injective
    (f := P.comp (planeSubmodule n k).subtype) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply Subtype.ext
  ext i
  by_cases hi : i.1 < k
  · have h := congrArg (fun w : ComplexModel k => w ⟨i.1, hi⟩) hz
    simpa [P, coordinateProjection_apply, i.2] using h
  · exact z.2 i (not_lt.mp hi)

/-! ### The image of `dι` is the flattening tangent space -/

variable {k n : ℕ} {V M : Type*}
  [TopologicalSpace V] [ChartedSpace (ComplexModel k) V] [IsComplexManifold k V]
  [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **Inclusion.**  If `ι` maps into `W` and `F` flattens `W` in the chart `d`,
then `dF` sends the image of `d(d ∘ ι ∘ e⁻¹)` into the coordinate plane. -/
theorem fderiv_comp_mem_plane {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {W : Set M} (hmaps : ∀ v, ι v ∈ W)
    (e : ComplexChart k V) (d : ComplexChart n M) {z₀ : ComplexModel k}
    (hz₀ : z₀ ∈ coordinateDomain ι e d)
    {F : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hz₀D : coordinateMap ι e d z₀ ∈ D)
    (hF : DifferentiableAt ℝ F (coordinateMap ι e d z₀))
    (hFflat : ∀ z ∈ D, (d.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k))
    (u : ComplexModel k) :
    fderiv ℝ F (coordinateMap ι e d z₀) (fderiv ℝ (coordinateMap ι e d) z₀ u) ∈
      planeSubmodule n k := by
  set c := coordinateMap ι e d with hc
  have hcd : DifferentiableAt ℝ c z₀ :=
    (coordinateMap_contDiffAt_real hι e d hz₀).differentiableAt (by simp)
  -- the line through `z₀` in direction `u`
  have hline : HasDerivAt (fun t : ℝ => z₀ + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add z₀
  have hline0 : (fun t : ℝ => z₀ + t • u) 0 = z₀ := by simp
  have hcF : HasFDerivAt c (fderiv ℝ c z₀) ((fun t : ℝ => z₀ + t • u) 0) := by
    rw [hline0]; exact hcd.hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => c (z₀ + t • u)) (fderiv ℝ c z₀ u) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := c) (0 : ℝ) hcF hline
  have hFF : HasFDerivAt F (fderiv ℝ F (c z₀)) (c (z₀ + (0 : ℝ) • u)) := by
    simpa using hF.hasFDerivAt
  have hh : HasDerivAt (fun t : ℝ => F (c (z₀ + t • u)))
      (fderiv ℝ F (c z₀) (fderiv ℝ c z₀ u)) 0 :=
    HasFDerivAt.comp_hasDerivAt (l := F) (0 : ℝ) hFF hcurve
  refine mem_of_hasDerivAt_of_eventually_mem
    (Submodule.closed_of_finiteDimensional (planeSubmodule n k)) hh ?_
  -- the curve stays in the coordinate domain and its image in `D`
  have h1 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), z₀ + t • u ∈ coordinateDomain ι e d := by
    refine hline.continuousAt.preimage_mem_nhds ?_
    rw [zero_smul, add_zero]
    exact (coordinateDomain_isOpen hι e d).mem_nhds hz₀
  have h2 : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), c (z₀ + t • u) ∈ D := by
    refine hcurve.continuousAt.preimage_mem_nhds ?_
    simpa using hD.mem_nhds hz₀D
  filter_upwards [h1, h2] with t ht htD
  have hW : d.val.symm (c (z₀ + t • u)) ∈ W := by
    rw [hc, coordinateMap, Function.comp_apply, Function.comp_apply,
      d.val.left_inv ht.2]
    exact hmaps _
  exact (hFflat _ htD).mp hW

/-- **The tangent space of `W` in a flattening is the image of `dι`.**  For an
immersion `ι` mapping into `W` and a nondegenerate flattening `F` of `W` in the
chart `d`, `(dF)⁻¹(ℂᵏ × 0)` is the range of the differential of `ι` in charts. -/
theorem range_fderiv_eq_comap {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {W : Set M} (hmaps : ∀ v, ι v ∈ W)
    (e : ComplexChart k V) (d : ComplexChart n M) {z₀ : ComplexModel k}
    (hz₀ : z₀ ∈ coordinateDomain ι e d)
    (hinj : Function.Injective (fderiv ℝ (coordinateMap ι e d) z₀))
    {F : ComplexModel n → ComplexModel n} {D : Set (ComplexModel n)}
    (hD : IsOpen D) (hz₀D : coordinateMap ι e d z₀ ∈ D)
    (hF : DifferentiableAt ℝ F (coordinateMap ι e d z₀))
    (hFinj : Function.Injective (fderiv ℝ F (coordinateMap ι e d z₀)))
    (hFflat : ∀ z ∈ D, (d.val.symm z ∈ W ↔ F z ∈ complexCoordinatePlane n k)) :
    LinearMap.range (fderiv ℝ (coordinateMap ι e d) z₀ :
        ComplexModel k →ₗ[ℝ] ComplexModel n) =
      (planeSubmodule n k).comap
        (fderiv ℝ F (coordinateMap ι e d z₀) : ComplexModel n →ₗ[ℝ] ComplexModel n) := by
  have hle : LinearMap.range (fderiv ℝ (coordinateMap ι e d) z₀ :
        ComplexModel k →ₗ[ℝ] ComplexModel n) ≤
      (planeSubmodule n k).comap
        (fderiv ℝ F (coordinateMap ι e d z₀) : ComplexModel n →ₗ[ℝ] ComplexModel n) := by
    rintro _ ⟨u, rfl⟩
    exact fderiv_comp_mem_plane hι hmaps e d hz₀ hD hz₀D hF hFflat u
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  rw [LinearMap.finrank_range_of_inj hinj]
  exact (finrank_comap_le _ hFinj (planeSubmodule n k)).trans finrank_planeSubmodule_le

/-! ### Positivity along `T_W` from positivity of the pullback -/

/-- **Restriction to `W` detects positivity along `T_W`.**  Let `ι : V → M` be a
holomorphic immersion of a complex `k`-manifold whose image is `W`, every point
of which is regular of dimension `k`.  If the pullback `ι^*β` is Hermitian on
`V`, then `β` is strictly positive on the flattening tangent directions of `W`
at every point, in the form `PositiveOnOneFlattening` consumed by Step 6. -/
theorem positiveOnOneFlattening_of_isHermitian_pullback {W : Set M}
    (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (himm : ∀ (e : ComplexChart k V) (d : ComplexChart n M) (z : ComplexModel k),
      z ∈ coordinateDomain ι e d → Function.Injective (fderiv ℝ (coordinateMap ι e d) z))
    (hmaps : ∀ v, ι v ∈ W) (hsurj : ∀ w ∈ W, ∃ v, ι v = w)
    {β : ClosedRealOneOneForm n M}
    (hpos : (SmoothRealForm.pullback hι β.val).IsHermitian) :
    PositiveOnOneFlattening W k β := by
  intro w hw
  obtain ⟨F, D, hD, hwD, hDsub, hFc, hFinj, hFflat⟩ := exists_admissible_flattening (hWreg w hw)
  refine ⟨F, D, hD, hwD, hDsub, hFc, hFinj, hFflat, ?_⟩
  intro v hv hvP
  obtain ⟨v₀, rfl⟩ := hsurj w hw
  set d := complexChartAt (n := n) (ι v₀) with hd
  set e := complexChartAt (n := k) v₀ with he
  have hv₀e : v₀ ∈ e.val.source := mem_complexChartAt_source v₀
  have hz₀ : e.val v₀ ∈ coordinateDomain ι e d :=
    mem_coordinateDomain hv₀e (mem_complexChartAt_source (ι v₀))
  have hcz₀ : coordinateMap ι e d (e.val v₀) = d.val (ι v₀) := coordinateMap_at hv₀e
  have hFd : DifferentiableAt ℝ F (d.val (ι v₀)) :=
    ((hFc.differentiableOn (by simp)).differentiableAt (hD.mem_nhds hwD)).restrictScalars ℝ
  have hrange := range_fderiv_eq_comap hι hmaps e d hz₀ (himm e d _ hz₀) hD
    (by rw [hcz₀]; exact hwD) (by rw [hcz₀]; exact hFd) (by rw [hcz₀]; exact hFinj) hFflat
  have hvmem : v ∈ LinearMap.range (fderiv ℝ (coordinateMap ι e d) (e.val v₀) :
      ComplexModel k →ₗ[ℝ] ComplexModel n) := by
    rw [hrange, hcz₀]
    exact hvP
  obtain ⟨u, hu⟩ := hvmem
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hv (by simpa using hu.symm)
  have hpull := (hpos e (e.val v₀) (e.val.map_source hv₀e)).2 u hu0
  rw [SmoothRealForm.pullback_coeff hι β.val e d hz₀] at hpull
  have hvec : (fderiv ℝ (coordinateMap ι e d) (e.val v₀)) ∘ ![u, Complex.I • u] =
      ![v, Complex.I • v] := by
    funext i
    fin_cases i
    · exact hu
    · show (fderiv ℝ (coordinateMap ι e d) (e.val v₀)) (Complex.I • u) = Complex.I • v
      rw [coordinateMap_fderiv_map_smul_complex hι e d hz₀ Complex.I u]
      exact congrArg (Complex.I • ·) hu
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at hpull
  rw [hvec, hcz₀] at hpull
  exact hpull

/-! ### `ι^*(ddᶜf) = ddᶜ(f ∘ ι)` -/

/-- A chart-smooth function composed with a holomorphic map is chart-smooth. -/
theorem chartSmooth_comp {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) :
    ChartSmooth (n := k) (fun v => f (ι v)) := by
  intro e z hz
  set d := complexChartAt (n := n) (ι (e.val.symm z))
  have hzd : z ∈ coordinateDomain ι e d := ⟨hz, mem_complexChartAt_source _⟩
  have hcomp : ContDiffAt ℝ ∞ (fun y => f (d.val.symm (coordinateMap ι e d y))) z :=
    ((hf d).contDiffAt (d.val.open_target.mem_nhds (coordinateMap_mem_target hzd))).comp z
      (coordinateMap_contDiffAt_real hι e d hzd)
  refine (hcomp.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [(coordinateDomain_isOpen hι e d).mem_nhds hzd] with y hy
  simp only [coordinateMap, Function.comp_apply, d.val.left_inv hy.2]

/-- **Pullback commutes with `ddᶜ`.**  In every chart of `V`, the pullback of
`ddᶜf` has the coefficients of `ddᶜ(f ∘ ι)`. -/
theorem pullback_ddcClosedForm_coeff {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f)
    (e : ComplexChart k V) {z : ComplexModel k} (hz : z ∈ e.val.target) :
    (SmoothRealForm.pullback hι (ddcClosedForm f hf).val).coeff e z =
      (ddcClosedForm (fun v => f (ι v)) (chartSmooth_comp hι hf)).val.coeff e z := by
  set d := complexChartAt (n := n) (ι (e.val.symm z))
  have hzd : z ∈ coordinateDomain ι e d := ⟨hz, mem_complexChartAt_source _⟩
  rw [SmoothRealForm.pullback_coeff hι _ e d hzd, ddcClosedForm_coeff, ddcClosedForm_coeff]
  have hcomp := smoothDDC_comp (coordinateDomain_isOpen hι e d) d.val.open_target
    (coordinateMap_contDiffOn hι e d) (hf d)
    (fun y hy => coordinateMap_mem_target hy) hzd
  rw [← hcomp]
  apply smoothDDC_congr
  filter_upwards [(coordinateDomain_isOpen hι e d).mem_nhds hzd] with y hy
  simp only [coordinateMap, Function.comp_apply, d.val.left_inv hy.2]

/-- **Step 4's output, in the shape Step 6 consumes.**  If `ι^*β + ddᶜh` is
Kähler on `V` and `f̃` is a chart-smooth extension of `h` (`f̃ ∘ ι = h`), then
`β + ddᶜf̃` is strictly positive along the tangent directions of `W = ι(V)`. -/
theorem positiveOnOneFlattening_add_ddc_of_isKahler {W : Set M}
    (hWreg : ∀ x ∈ W, RegularAtDim (n := n) W x k) {ι : V → M}
    (hι : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ ι)
    (himm : ∀ (e : ComplexChart k V) (d : ComplexChart n M) (z : ComplexModel k),
      z ∈ coordinateDomain ι e d → Function.Injective (fderiv ℝ (coordinateMap ι e d) z))
    (hmaps : ∀ v, ι v ∈ W) (hsurj : ∀ w ∈ W, ∃ v, ι v = w)
    (β : ClosedRealOneOneForm n M) {h : V → ℝ} (hh : ChartSmooth (n := k) h)
    (hK : (ClosedRealOneOneForm.pullback hι β + ddcClosedForm h hh).val.IsKahler)
    {f : M → ℝ} (hf : ChartSmooth (n := n) f) (hext : ∀ v, f (ι v) = h v) :
    PositiveOnOneFlattening W k (β + ddcClosedForm f hf) := by
  refine positiveOnOneFlattening_of_isHermitian_pullback hWreg hι himm hmaps hsurj ?_
  intro e z hz
  have hfun : (fun v => f (ι v)) = h := funext hext
  have hcoeff : (SmoothRealForm.pullback hι (β + ddcClosedForm f hf).val).coeff e z =
      (ClosedRealOneOneForm.pullback hι β + ddcClosedForm h hh).val.coeff e z := by
    set d := complexChartAt (n := n) (ι (e.val.symm z))
    have hzd : z ∈ coordinateDomain ι e d := ⟨hz, mem_complexChartAt_source _⟩
    have hdd := pullback_ddcClosedForm_coeff hι hf e hz
    have hβc := SmoothRealForm.pullback_coeff hι β.val e d hzd
    rw [SmoothRealForm.pullback_coeff hι _ e d hzd] at hdd ⊢
    rw [ClosedRealOneOneForm.coeff_add, ClosedRealOneOneForm.coeff_add,
      ClosedRealOneOneForm.pullback_val, hβc]
    subst hfun
    rw [← hdd]
    ext x
    simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [hcoeff]
  exact hK.1 e z hz

end

end Hironaka.SubmanifoldRestrictionPositivity
