import Hironaka.Analytic.QuantitativeRegularizationSingularWeight
import Hironaka.Analytic.BergmanHolomorphicMultiplier
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false

/-!
# Weighted Bergman kernels under biholomorphisms, domains and constant weights

Source: Copy-4, `lem:regularization`, Steps 1--2
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:873-967`);
blueprint `ana:regularization`.

Copy-4 defines the Bergman weights `φ_{j,m}` of its fixed cover with the Kähler volume
`dV_Z`, which does not depend on a chart, and compares two of them in the coordinates of one
ball `Ω_{jl}` containing both patches, "the uniform comparison between `dλ` and `dV_Z` being
absorbed into the constants".  The project's Bergman kernel `BergmanSupWeight.bergmanSup` is
a chart-level object (Lebesgue measure on a domain of `ℂᵈ`), so the manifold version of that
comparison needs three elementary facts, proved here.

* `bergmanSup_image`: **change of variables.**  For a biholomorphism `T : D → T(D)`,
  `bergmanSup (T(D)) w (T x) = bergmanSup D (J_T · w ∘ T) x`, with `J_T = |det_ℝ DT|` the
  real Jacobian.  `f ↦ f ∘ T` is an isometry of the weighted spaces
  (`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) preserving point values.
* `bergmanSup_ofReal_mul`: a constant factor `c > 0` in the weight divides the kernel by `c`
  (the constant case of `BergmanHolomorphicMultiplier.bergmanSup_exp_weight`); hence
  `bergmanSup_mul_le_of_le_mul` / `bergmanSup_le_mul_of_mul_le`: a factor bounded between
  `a` and `A` on the domain changes the kernel by at most `a⁻¹` and `A⁻¹`.  Applied to the
  Jacobian of a chart transition on a relatively compact set, this is Copy-4's "absorbed
  into the constants", and the bound does not depend on the weight.
* `bergmanSup_le_of_subset`: the kernel is antitone in the domain.

The logarithmic forms (`bergmanLog_image_le`, `bergmanLog_le_image`) are the shape the
overlap estimate consumes: after dividing by `m`, a bounded Jacobian costs `O(1/m)`.
-/

open Set MeasureTheory Filter
open scoped ENNReal Topology

namespace Hironaka.BergmanBiholomorphicTransport

noncomputable section

open BergmanSupWeight QuantitativeRegularizationSingularWeight

variable {d : ℕ} [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

/-! ### Change of variables -/

/-- The real Jacobian `|det_ℝ DT|` of a map, as a weight. -/
def realJacobian (T : ComplexModel d → ComplexModel d) (z : ComplexModel d) : ℝ≥0∞ :=
  ENNReal.ofReal |((fderiv ℂ T z).restrictScalars ℝ).det|

omit [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)] in
/-- A map holomorphic on an open set has its complex derivative, read over `ℝ`, as real
derivative there. -/
theorem hasFDerivWithinAt_restrictScalars {D : Set (ComplexModel d)} (hDo : IsOpen D)
    {T : ComplexModel d → ComplexModel d} (hT : DifferentiableOn ℂ T D) {z : ComplexModel d}
    (hz : z ∈ D) :
    HasFDerivWithinAt T ((fderiv ℂ T z).restrictScalars ℝ) D z :=
  ((hT.differentiableAt (hDo.mem_nhds hz)).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt

/-- **Change of variables in the weighted norm**: for `T` holomorphic and injective on the
open set `D`, `∫_{T(D)} |f|² w = ∫_D |f ∘ T|² J_T (w ∘ T)`. -/
theorem lintegral_image_normSq {D : Set (ComplexModel d)} (hDo : IsOpen D)
    {T : ComplexModel d → ComplexModel d} (hT : DifferentiableOn ℂ T D) (hTinj : InjOn T D)
    (f : ComplexModel d → ℂ) (w : ComplexModel d → ℝ≥0∞) :
    ∫⁻ y in T '' D, ENNReal.ofReal (‖f y‖ ^ 2) * w y =
      ∫⁻ z in D, ENNReal.ofReal (‖f (T z)‖ ^ 2) * (realJacobian T z * w (T z)) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hDo.measurableSet
    (fun z hz => hasFDerivWithinAt_restrictScalars hDo hT hz) hTinj]
  refine lintegral_congr fun z => ?_
  simp only [realJacobian]
  ring

/-- **Weighted Bergman kernels are invariant under biholomorphisms**, the Jacobian entering
the weight: if `T` is holomorphic on the open set `D` with a holomorphic left inverse `S` on
`T(D)`, then for `x ∈ D`

`bergmanSup (T(D)) w (T x) = bergmanSup D (J_T · w ∘ T) x`. -/
theorem bergmanSup_image {D : Set (ComplexModel d)} (hDo : IsOpen D)
    {T S : ComplexModel d → ComplexModel d} (hT : DifferentiableOn ℂ T D)
    (hS : DifferentiableOn ℂ S (T '' D)) (hST : ∀ z ∈ D, S (T z) = z)
    (w : ComplexModel d → ℝ≥0∞) {x : ComplexModel d} (hx : x ∈ D) :
    bergmanSup (T '' D) w (T x) = bergmanSup D (fun z => realJacobian T z * w (T z)) x := by
  have hTinj : InjOn T D := fun z hz z' hz' h => by rw [← hST z hz, h, hST z' hz']
  refine le_antisymm (bergmanSup_le fun f hf => ?_) (bergmanSup_le fun g hg => ?_)
  · -- pull back along `T`
    have hmem : (f ∘ T) ∈ bergmanBall D (fun z => realJacobian T z * w (T z)) := by
      refine ⟨hf.1.comp hT (mapsTo_image T D), ?_⟩
      have h := hf.2
      rw [lintegral_image_normSq hDo hT hTinj f w] at h
      exact h
    exact le_bergmanSup hmem x
  · -- push forward along `T`, i.e. pull back along `S`
    have hSmaps : MapsTo S (T '' D) D := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hST z hz]
      exact hz
    have hmem : (g ∘ S) ∈ bergmanBall (T '' D) w := by
      refine ⟨hg.1.comp hS hSmaps, ?_⟩
      rw [lintegral_image_normSq hDo hT hTinj (g ∘ S) w]
      refine le_trans (le_of_eq ?_) hg.2
      refine setLIntegral_congr_fun hDo.measurableSet fun z hz => ?_
      simp only [Function.comp_apply, hST z hz]
    have := le_bergmanSup hmem (T x)
    simpa only [Function.comp_apply, hST x hx] using this

/-! ### Constant factors in the weight, and the domain -/

/-- **A constant factor in the weight**: `bergmanSup D (c w) = c⁻¹ bergmanSup D w` for
`c > 0`. -/
theorem bergmanSup_ofReal_mul (D : Set (ComplexModel d)) {c : ℝ} (hc : 0 < c)
    (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    bergmanSup D (fun z => ENNReal.ofReal c * w z) y =
      ENNReal.ofReal c⁻¹ * bergmanSup D w y := by
  have h := BergmanHolomorphicMultiplier.bergmanSup_exp_weight
    (D := D) (a := fun _ => ((-(Real.log c) / 2 : ℝ) : ℂ)) (differentiableOn_const _) w y
  have h1 : Real.exp (-(2 * ((((-(Real.log c) / 2 : ℝ) : ℂ)).re))) = c := by
    rw [Complex.ofReal_re, show -(2 * (-(Real.log c) / 2)) = Real.log c by ring,
      Real.exp_log hc]
  have h2 : Real.exp (2 * ((((-(Real.log c) / 2 : ℝ) : ℂ)).re)) = c⁻¹ := by
    rw [Complex.ofReal_re, show 2 * (-(Real.log c) / 2) = -Real.log c by ring,
      Real.exp_neg, Real.exp_log hc]
  simpa only [h1, h2] using h

/-- **A factor bounded below by `a > 0` on `D`** multiplies the kernel by at most `a⁻¹`. -/
theorem bergmanSup_mul_le_of_le_mul {D : Set (ComplexModel d)} (hD : MeasurableSet D)
    {J : ComplexModel d → ℝ≥0∞} {a : ℝ} (ha : 0 < a) (hJ : ∀ z ∈ D, ENNReal.ofReal a ≤ J z)
    (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    bergmanSup D (fun z => J z * w z) y ≤ ENNReal.ofReal a⁻¹ * bergmanSup D w y := by
  rw [← bergmanSup_ofReal_mul D ha w y]
  exact bergmanSup_antitone_weight hD (fun z hz => mul_le_mul_left (hJ z hz) (w z)) y

/-- **A factor bounded above by `A > 0` on `D`** divides the kernel by at most `A`. -/
theorem bergmanSup_le_mul_of_mul_le {D : Set (ComplexModel d)} (hD : MeasurableSet D)
    {J : ComplexModel d → ℝ≥0∞} {A : ℝ} (hA : 0 < A) (hJ : ∀ z ∈ D, J z ≤ ENNReal.ofReal A)
    (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    ENNReal.ofReal A⁻¹ * bergmanSup D w y ≤ bergmanSup D (fun z => J z * w z) y := by
  rw [← bergmanSup_ofReal_mul D hA w y]
  exact bergmanSup_antitone_weight hD (fun z hz => mul_le_mul_left (hJ z hz) (w z)) y

/-- **The kernel is antitone in the domain**: a function in the unit ball of `D` restricts to
one in the unit ball of any `D' ⊆ D`. -/
theorem bergmanSup_le_of_subset {D D' : Set (ComplexModel d)} (h : D' ⊆ D)
    (w : ComplexModel d → ℝ≥0∞) (y : ComplexModel d) :
    bergmanSup D w y ≤ bergmanSup D' w y :=
  bergmanSup_le fun _f hf =>
    le_bergmanSup ⟨hf.1.mono h, le_trans (lintegral_mono_set h) hf.2⟩ y

/-! ### Logarithmic forms -/

/-- `log (c · S) ≤ log S + log c` for `c = ofReal r`, `r > 0`. -/
theorem log_ofReal_mul (r : ℝ) (hr : 0 < r) (S : ℝ≥0∞) :
    ENNReal.log (ENNReal.ofReal r * S) = ENNReal.log S + (Real.log r : EReal) := by
  rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hr, add_comm]

/-- **Transport with a Jacobian bounded below**: if `a ≤ J_T` on `D`, then
`log K_{T(D), w}(T x) ≤ log K_{D, w ∘ T}(x) + log a⁻¹`. -/
theorem bergmanLog_image_le {D : Set (ComplexModel d)} (hDo : IsOpen D)
    {T S : ComplexModel d → ComplexModel d} (hT : DifferentiableOn ℂ T D)
    (hS : DifferentiableOn ℂ S (T '' D)) (hST : ∀ z ∈ D, S (T z) = z)
    {a : ℝ} (ha : 0 < a) (hJ : ∀ z ∈ D, ENNReal.ofReal a ≤ realJacobian T z)
    (w : ComplexModel d → ℝ≥0∞) {x : ComplexModel d} (hx : x ∈ D) :
    bergmanLog (T '' D) w (T x) ≤
      bergmanLog D (fun z => w (T z)) x + (Real.log a⁻¹ : EReal) := by
  rw [bergmanLog, bergmanSup_image hDo hT hS hST w hx, bergmanLog,
    ← log_ofReal_mul a⁻¹ (inv_pos.mpr ha)]
  exact ENNReal.log_monotone
    (bergmanSup_mul_le_of_le_mul hDo.measurableSet ha hJ (fun z => w (T z)) x)

/-- **Transport with a Jacobian bounded above**: if `J_T ≤ A` on `D`, then
`log K_{D, w ∘ T}(x) ≤ log K_{T(D), w}(T x) + log A`. -/
theorem bergmanLog_le_image {D : Set (ComplexModel d)} (hDo : IsOpen D)
    {T S : ComplexModel d → ComplexModel d} (hT : DifferentiableOn ℂ T D)
    (hS : DifferentiableOn ℂ S (T '' D)) (hST : ∀ z ∈ D, S (T z) = z)
    {A : ℝ} (hA : 0 < A) (hJ : ∀ z ∈ D, realJacobian T z ≤ ENNReal.ofReal A)
    (w : ComplexModel d → ℝ≥0∞) {x : ComplexModel d} (hx : x ∈ D) :
    bergmanLog D (fun z => w (T z)) x ≤
      bergmanLog (T '' D) w (T x) + (Real.log A : EReal) := by
  have h := bergmanSup_le_mul_of_mul_le hDo.measurableSet hA hJ (fun z => w (T z)) x
  rw [← bergmanSup_image hDo hT hS hST w hx] at h
  have hlog := ENNReal.log_monotone h
  rw [log_ofReal_mul A⁻¹ (inv_pos.mpr hA), Real.log_inv] at hlog
  calc bergmanLog D (fun z => w (T z)) x
      = (ENNReal.log (bergmanSup D (fun z => w (T z)) x) + ((-Real.log A : ℝ) : EReal))
          + (Real.log A : EReal) := by
        rw [add_assoc, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, add_zero]; rfl
    _ ≤ bergmanLog (T '' D) w (T x) + (Real.log A : EReal) := add_le_add hlog le_rfl

end

end Hironaka.BergmanBiholomorphicTransport
